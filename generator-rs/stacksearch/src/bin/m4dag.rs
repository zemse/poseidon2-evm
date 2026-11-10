// The evaluation DAGs of the M4 of a block of t >= 8 (rows [5,7,1,3],
// [4,6,1,1], [1,3,5,7], [1,1,4,6] on u0..u3), cheapest first, in the
// copy-counting cost of `sblock`: every value but the inputs is made on top
// once and consumed once in place, so a DAG of B binary ops needs B copies
// (2B + U + 4 uses, B + U + 4 values, the 4 outputs each consumed by its
// lane). A binary ADD costs 6 (op and copy), ADDMOD 14 (with its PRIME
// copy), SHL by 1 or 2 6 (PUSH1, SHL), MUL by k 8, MULMOD by k 14. Values are
// forms with nonnegative integer coefficients (every op is a nonnegative
// combination, so a value that feeds an output is below it componentwise)
// and an inclusive bound in units of P - 1: a lazy op keeps the bound at
// most 5 (5(P - 1) < 2^256), ADDMOD and MULMOD reduce it to 1.
//
//   m4dag <input bounds> <output bounds> [budget=104] [max=50]
//
// e.g. `m4dag 2,2,2,2 4,4,4,4`: u = x + S at 2 units, kept outputs at most
// 4 (o + c then fits). Prints every DAG within the budget (up to max), as an
// `sblock` DAG= spec when its ops are ones sblock knows.

use std::collections::HashMap;

const ROWS: [[u8; 4]; 4] = [[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]];

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Op {
    In(u8),
    Add(u8, u8),
    Addmod(u8, u8),
    Shl(u8, u8),
    Mul(u8, u8),
    Mulmod(u8, u8),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Val {
    form: [u8; 4],
    bound: u8,
    op: Op,
}

struct Search {
    out_bound: [u8; 4],
    budget: u32,
    max: usize,
    seen: HashMap<Vec<(Vec<u8>, u8, Vec<u8>)>, u32>,
    found: Vec<(u32, Vec<Val>)>,
}

fn below_target(f: &[u8; 4]) -> bool {
    ROWS.iter().any(|r| (0..4).all(|i| f[i] <= r[i]))
}

impl Search {
    fn done(&self, vals: &[Val]) -> bool {
        (0..4).all(|r| {
            vals.iter()
                .any(|v| v.form == ROWS[r] && v.bound <= self.out_bound[r])
        })
    }

    fn missing(&self, vals: &[Val]) -> u32 {
        (0..4)
            .filter(|&r| {
                !vals
                    .iter()
                    .any(|v| v.form == ROWS[r] && v.bound <= self.out_bound[r])
            })
            .count() as u32
    }

    /// every value but the outputs is used by a later op
    fn all_used(&self, vals: &[Val]) -> bool {
        let mut used = vec![false; vals.len()];
        for v in vals {
            match v.op {
                Op::In(_) => {}
                Op::Add(a, b) | Op::Addmod(a, b) => {
                    used[a as usize] = true;
                    used[b as usize] = true;
                }
                Op::Shl(a, _) | Op::Mul(a, _) | Op::Mulmod(a, _) => used[a as usize] = true,
            }
        }
        vals.iter().enumerate().all(|(i, v)| {
            used[i] || (0..4).any(|r| v.form == ROWS[r] && v.bound <= self.out_bound[r])
        })
    }

    fn dfs(&mut self, vals: &mut Vec<Val>, cost: u32) {
        if self.found.len() >= self.max {
            return;
        }
        // every op costs 6 at least, and no DAG has fewer than 12 ops (OPS=11
        // finds none)
        let ops = vals.len() as u32 - 4;
        if cost + 6 * self.missing(vals).max(12u32.saturating_sub(ops)) > self.budget {
            return;
        }
        if self.done(vals) {
            if self.all_used(vals) {
                self.found.push((cost, vals.clone()));
            }
            return;
        }
        let mut key: Vec<(Vec<u8>, u8, Vec<u8>)> = vals
            .iter()
            .map(|v| (v.form.to_vec(), v.bound, operands(vals, v)))
            .collect();
        key.sort();
        if self.seen.get(&key).is_some_and(|&c| c <= cost) {
            return;
        }
        self.seen.insert(key, cost);
        let n = vals.len();
        let mut cands: Vec<(u32, Val)> = Vec::new();
        for i in 0..n {
            for j in i..n {
                let (a, b) = (vals[i], vals[j]);
                let mut f = [0u8; 4];
                for k in 0..4 {
                    f[k] = a.form[k] + b.form[k];
                }
                if !below_target(&f) {
                    continue;
                }
                if a.bound + b.bound <= 5 {
                    cands.push((
                        6,
                        Val {
                            form: f,
                            bound: a.bound + b.bound,
                            op: Op::Add(i as u8, j as u8),
                        },
                    ));
                }
                cands.push((
                    14,
                    Val {
                        form: f,
                        bound: 1,
                        op: Op::Addmod(i as u8, j as u8),
                    },
                ));
            }
            let a = vals[i];
            for k in 2..=7u8 {
                let mut f = [0u8; 4];
                for c in 0..4 {
                    f[c] = a.form[c] * k;
                }
                if !below_target(&f) {
                    continue;
                }
                if a.bound * k <= 5 {
                    let (cost, op) = match k {
                        2 => (6, Op::Shl(i as u8, 1)),
                        4 => (6, Op::Shl(i as u8, 2)),
                        _ => (8, Op::Mul(i as u8, k)),
                    };
                    cands.push((
                        cost,
                        Val {
                            form: f,
                            bound: a.bound * k,
                            op,
                        },
                    ));
                }
                cands.push((
                    14,
                    Val {
                        form: f,
                        bound: 1,
                        op: Op::Mulmod(i as u8, k),
                    },
                ));
            }
        }
        for (c, v) in cands {
            // a form already there with a bound no larger is no use
            if vals.iter().any(|w| w.form == v.form && w.bound <= v.bound) {
                continue;
            }
            vals.push(v);
            self.dfs(vals, cost + c);
            vals.pop();
        }
    }
}

/// OPS=n: whether n ops (an add of two values, or a value times 2..7) make
/// the four rows from u0..u3, bounds and reductions left out. Depth-first
/// with the sets of forms seen at each remaining depth.
fn ops_search(
    forms: &mut Vec<([u8; 4], bool)>,
    left: u32,
    seen: &mut HashMap<[u16; 16], u32>,
) -> bool {
    let missing = ROWS
        .iter()
        .filter(|r| !forms.iter().any(|f| f.0 == **r))
        .count() as u32;
    // values no op reads yet (rows need no reader): an op reads at most
    // two, and every op but those making the missing rows adds one
    let unused = forms
        .iter()
        .filter(|f| !f.1 && !ROWS.contains(&f.0))
        .count() as u32;
    if missing == 0 {
        return unused == 0;
    }
    if missing > left || unused > left + missing {
        return false;
    }
    // a form below (5, 7, 5, 7) and its used bit in a u16, the set sorted;
    // the mirror (u0, u1) <-> (u2, u3) maps the rows onto each other
    let pack = |f: [u8; 4], u: bool| {
        (((f[0] as u16 * 8 + f[1] as u16) * 6 + f[2] as u16) * 8 + f[3] as u16) | (u as u16) << 12
    };
    let packed = |m: bool| {
        let mut k = [u16::MAX; 16];
        for (i, &(f, u)) in forms.iter().enumerate() {
            k[i] = if m {
                pack([f[2], f[3], f[0], f[1]], u)
            } else {
                pack(f, u)
            };
        }
        k.sort();
        k
    };
    let key = packed(false).min(packed(true));
    if seen.get(&key).is_some_and(|&l| l >= left) {
        return false;
    }
    seen.insert(key, left);
    // the last op must make a row: with one op left, only rows
    let n = forms.len();
    let mut cands: Vec<([u8; 4], usize, usize)> = Vec::new();
    for i in 0..n {
        for j in i..n {
            let mut f = [0u8; 4];
            for k in 0..4 {
                f[k] = forms[i].0[k] + forms[j].0[k];
            }
            cands.push((f, i, j));
        }
        for k in 2..=7u8 {
            let mut f = [0u8; 4];
            for c in 0..4 {
                f[c] = forms[i].0[c] * k;
            }
            cands.push((f, i, i));
        }
    }
    for (f, i, j) in cands {
        if !below_target(&f) || forms.iter().any(|g| g.0 == f) {
            continue;
        }
        if left == missing && !ROWS.contains(&f) {
            continue;
        }
        let (ui, uj) = (forms[i].1, forms[j].1);
        forms[i].1 = true;
        forms[j].1 = true;
        forms.push((f, false));
        let ok = ops_search(forms, left - 1, seen);
        forms.pop();
        forms[i].1 = ui;
        forms[j].1 = uj;
        if ok {
            return true;
        }
    }
    false
}

fn name(vals: &[Val], i: usize) -> String {
    let v = &vals[i];
    if let Some(r) = ROWS.iter().position(|r| *r == v.form) {
        // the row's output: o0 = [5,7,1,3] .. as sblock names them
        let o = [0, 1, 2, 3][r];
        if !matches!(v.op, Op::In(_)) && i == last_of(vals, v.form) {
            return format!("o{o}");
        }
    }
    match v.op {
        Op::In(k) => format!("u{k}"),
        _ => format!(
            "v{}{}{}{}_{}",
            v.form[0], v.form[1], v.form[2], v.form[3], v.bound
        ),
    }
}

/// an op and the forms and bounds of its operands, independent of the order
/// the values were made in
fn operands(vals: &[Val], v: &Val) -> Vec<u8> {
    let f = |i: u8| {
        let w = &vals[i as usize];
        let mut x = w.form.to_vec();
        x.push(w.bound);
        x
    };
    match v.op {
        Op::In(k) => vec![0, k],
        Op::Add(a, b) => [vec![1], f(a), f(b)].concat(),
        Op::Addmod(a, b) => [vec![2], f(a), f(b)].concat(),
        Op::Shl(a, k) => [vec![3, k], f(a)].concat(),
        Op::Mul(a, k) => [vec![4, k], f(a)].concat(),
        Op::Mulmod(a, k) => [vec![5, k], f(a)].concat(),
    }
}

fn last_of(vals: &[Val], form: [u8; 4]) -> usize {
    vals.iter().rposition(|v| v.form == form).unwrap()
}

fn main() {
    if let Ok(n) = std::env::var("OPS") {
        let n: u32 = n.parse().unwrap();
        let mut forms: Vec<([u8; 4], bool)> = (0..4)
            .map(|i| {
                let mut f = [0; 4];
                f[i] = 1;
                (f, false)
            })
            .collect();
        let mut seen = HashMap::new();
        let ok = ops_search(&mut forms, n, &mut seen);
        println!("{n} ops: {}", if ok { "found" } else { "none" });
        eprintln!("{} sets", seen.len());
        return;
    }
    let args: Vec<String> = std::env::args().collect();
    let parse = |s: &str| -> [u8; 4] {
        let v: Vec<u8> = s.split(',').map(|x| x.parse().unwrap()).collect();
        [v[0], v[1], v[2], v[3]]
    };
    let ins = parse(&args[1]);
    let outs = parse(&args[2]);
    let budget: u32 = args.get(3).map_or(104, |s| s.parse().unwrap());
    let max: usize = args.get(4).map_or(50, |s| s.parse().unwrap());
    let mut s = Search {
        out_bound: outs,
        budget,
        max,
        seen: HashMap::new(),
        found: Vec::new(),
    };
    let mut vals: Vec<Val> = (0..4)
        .map(|i| {
            let mut f = [0; 4];
            f[i] = 1;
            Val {
                form: f,
                bound: ins[i],
                op: Op::In(i as u8),
            }
        })
        .collect();
    s.dfs(&mut vals, 0);
    s.found.sort_by_key(|f| f.0);
    let mut printed = std::collections::HashSet::new();
    for (cost, vals) in &s.found {
        let mut spec = Vec::new();
        let mut sblock_ok = true;
        for i in 4..vals.len() {
            let v = &vals[i];
            let rhs = match v.op {
                Op::Add(a, b) => {
                    format!("add({},{})", name(vals, a as usize), name(vals, b as usize))
                }
                Op::Addmod(a, b) => format!(
                    "addmod({},{})",
                    name(vals, a as usize),
                    name(vals, b as usize)
                ),
                Op::Shl(a, sft) => {
                    sblock_ok = false;
                    format!("shl{}({})", sft, name(vals, a as usize))
                }
                Op::Mul(a, k) => {
                    sblock_ok = false;
                    format!("mul{}({})", k, name(vals, a as usize))
                }
                Op::Mulmod(a, k) => {
                    if k != 4 {
                        sblock_ok = false;
                    }
                    if k == 4 {
                        format!("q({})", name(vals, a as usize))
                    } else {
                        format!("mulmod{}({})", k, name(vals, a as usize))
                    }
                }
                Op::In(_) => unreachable!(),
            };
            spec.push(format!("{}={}", name(vals, i), rhs));
        }
        let mut sorted = spec.clone();
        sorted.sort();
        if !printed.insert(sorted) {
            continue;
        }
        println!(
            "{cost} {} {}",
            if sblock_ok { "sblock" } else { "ext" },
            spec.join(";")
        );
    }
    eprintln!("{} found, {} states", s.found.len(), s.seen.len());
}
