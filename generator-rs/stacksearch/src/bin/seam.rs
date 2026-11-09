// An exact search over single opcodes for the seams of the t = 2, 3
// permutations: the last external round, which stores its outputs, or any
// round from a given layout to a given one. Values are linear forms with
// coefficients 0..2 and an inclusive bound in units of P - 1; only forms
// below a row still needed are kept (others become dead). Moves: PRIME
// copy, DUPn, SWAPn, EXCHANGE of two slots below the top (EXCHANGE=1), POP,
// ADD (bound at most 5), ADDMOD over a PRIME copy in slot 3, the S-box of a
// lane (its constant ADD and the five-opcode body, 45 gas, on a value of
// bound at most 4 over a PRIME copy) and `msize mstore` of the next output
// (reduced). Dead values below the window cost nothing; a PRIME copy is
// always reachable (a deep one or PUSH32).
//
//   seam <t> <init> <goal> [window=10] [ub]
//
// init: top first, comma separated: s<i>:<bound> (lane i before its
// S-box), x<i>, b<i>:<bound> (INTERNAL), P, G (a dead value). goal: `store`
// (s0', s1', ... stored in order, reduced) or a layout prefix of
// o<i>:<bound>, P and G (anything). Optimal within the window and these moves.
//
// The forms are over the S-box outputs x of one external round, unless:
// ROUNDS=2 (t = 2) searches two external rounds at once (the outputs of the
// first are the S-box inputs of the second, whose outputs y the goal
// takes), so the layout between them is free and the second may start
// before the first ends; INTERNAL=1 (t = 3) starts from the last internal
// round's values b0 = sum, b1 = x, b2 = s2, b3 = s1 and builds its outputs
// x + sum, s1 + sum, 2 s2 + sum as the S-box inputs of the external round
// after it. LOADS=0,1,... takes lane i from calldata reduced instead of its
// S-box (PRIME copy, PUSH, CALLDATALOAD, MOD: 14 gas).

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const G: u8 = 0;
const P: u8 = 1;
const RAW: u8 = 2; // + lane
const FORM: u8 = 8; // + (form index) * 6 + bound, first round then second

#[derive(Clone)]
struct Pb {
    t: usize,
    // per round: every useful coefficient vector, and the rows (round 0 of
    // two: the S-box inputs of round 1; the last: the outputs)
    forms: [Vec<Vec<u8>>; 2],
    rows: [Vec<Vec<u8>>; 2],
    base: [u8; 2],
    names: [&'static str; 2],
    raw_bound: Vec<u8>,
    store: bool,
    goal: Vec<(u8, u8)>, // (token class: P or output index + 2, max bound)
    w: usize,
    exch: bool,
    loads: u8,
    two: bool,
    // JUNCTION=1: the second round ends at its S-box outputs
    junction: bool,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct St {
    tok: Vec<u8>, // top first
    stored: u8,
    sboxed: u8,
    sboxed2: u8,
}

/// every nonzero vector with entries 0..2 below one of the rows
fn below_rows(rows: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let m = rows[0].len();
    let mut out = vec![];
    for k in 1..3usize.pow(m as u32) {
        let mut v = vec![0u8; m];
        let mut r = k;
        for e in v.iter_mut() {
            *e = (r % 3) as u8;
            r /= 3;
        }
        if rows
            .iter()
            .any(|row| v.iter().zip(row).all(|(a, b)| a <= b))
        {
            out.push(v);
        }
    }
    out
}

impl Pb {
    fn last(&self) -> u8 {
        self.two as u8
    }

    fn form(&self, round: u8, v: &[u8], b: u8) -> Option<u8> {
        let i = self.forms[round as usize].iter().position(|f| f == v)?;
        Some(self.base[round as usize] + i as u8 * 6 + b)
    }

    fn unit(&self, round: u8, l: usize) -> u8 {
        let mut e = vec![0; self.forms[round as usize][0].len()];
        e[l] = 1;
        self.form(round, &e, 1).expect("a unit form")
    }

    /// (round, coefficients, bound) of a form
    fn unform(&self, tok: u8) -> Option<(u8, &[u8], u8)> {
        for r in [1u8, 0] {
            let base = self.base[r as usize];
            let n = self.forms[r as usize].len();
            if tok >= base && ((tok - base) as usize) < 6 * n {
                let i = ((tok - base) / 6) as usize;
                return Some((r, &self.forms[r as usize][i], (tok - base) % 6));
            }
        }
        None
    }

    fn useful(&self, s: &St, round: u8, c: &[u8]) -> bool {
        let below = |r: &Vec<u8>| c.iter().zip(r).all(|(a, b)| a <= b);
        let rows = &self.rows[round as usize];
        if round < self.last() {
            return (0..rows.len()).any(|l| s.sboxed2 >> l & 1 == 0 && below(&rows[l]));
        }
        let first = if self.store { s.stored as usize } else { 0 };
        rows[first..].iter().any(below)
    }

    fn canon(&self, mut s: St) -> Option<St> {
        for i in 0..s.tok.len() {
            let v = s.tok[i];
            if (RAW..FORM).contains(&v) {
                if s.sboxed >> (v - RAW) & 1 == 1 {
                    s.tok[i] = G;
                }
            } else if let Some((r, c, _)) = self.unform(v) {
                if !self.useful(&s, r, c) {
                    s.tok[i] = G;
                }
            }
        }
        while s.tok.last() == Some(&G) {
            s.tok.pop();
        }
        // a lane not yet through its S-box must still be on the stack
        for l in 0..self.t {
            if s.sboxed >> l & 1 == 0
                && self.loads >> l & 1 == 0
                && !s.tok.contains(&(RAW + l as u8))
            {
                return None;
            }
        }
        (s.tok.len() <= self.w).then_some(s)
    }

    fn is_output(&self, v: u8, r: usize, reduced: bool) -> bool {
        self.unform(v).is_some_and(|(round, c, b)| {
            round == self.last()
                && c == self.rows[round as usize][r].as_slice()
                && (!reduced || b == 1)
        })
    }

    fn done(&self, s: &St) -> bool {
        if self.store {
            return s.stored as usize == self.t;
        }
        if s.tok.len() < self.goal.len() {
            return false;
        }
        self.goal.iter().zip(&s.tok).all(|(&(g, b), &v)| {
            if g == P {
                return v == P;
            }
            if g == G {
                return true;
            }
            self.is_output(v, (g - 2) as usize, false) && self.unform(v).unwrap().2 <= b
        })
    }

    fn h(&self, s: &St) -> u32 {
        let all = (1u8 << self.t) - 1;
        let left = (!s.sboxed & !self.loads & all).count_ones()
            + if self.two {
                (!s.sboxed2 & all).count_ones()
            } else {
                0
            };
        let loads = (!s.sboxed & self.loads).count_ones();
        // every output still to make takes an ADDMOD over a PRIME copy (store)
        // or at least an ADD (layout)
        let mut rest = 0;
        let mut missing = 0;
        let first = if self.store { s.stored as usize } else { 0 };
        for r in first..self.t {
            let have = s.tok.iter().any(|&v| self.is_output(v, r, self.store));
            rest += if self.store { 5 } else { 0 }
                + if have || self.junction {
                    0
                } else if self.store {
                    8
                } else {
                    3
                };
            missing += u32::from(self.store && !have);
        }
        // PRIME copies: one per missing ADDMOD and S-box and goal slot beyond
        // those on the stack
        let primes = s.tok.iter().filter(|&&v| v == P).count() as u32;
        let goal_primes = self.goal.iter().filter(|&&(g, _)| g == P).count() as u32;
        // value copies: every ADD or ADDMOD and store takes one value slot,
        // an S-box none, and the goal keeps its outputs; each output not on
        // the stack takes at least one more op
        let values = s.tok.iter().filter(|&&v| v != G && v != P).count() as u32 + loads;
        let outs = if self.store {
            self.t as u32 - s.stored as u32
        } else {
            self.t as u32
        };
        let built = (first..self.t)
            .filter(|&r| s.tok.iter().any(|&v| self.is_output(v, r, self.store)))
            .count() as u32;
        // two rounds: so does every S-box input of the second round not
        // yet made
        let first_ops = if self.two {
            (0..self.t)
                .filter(|&l| {
                    s.sboxed2 >> l & 1 == 0
                        && !s.tok.iter().any(|&v| {
                            self.unform(v)
                                .is_some_and(|(r, c, _)| r == 0 && c == self.rows[0][l].as_slice())
                        })
                })
                .count() as u32
        } else {
            0
        };
        let ops = if self.junction {
            0
        } else {
            (self.t - first) as u32 - built
        } + first_ops;
        let end = if self.store { 0 } else { self.t as u32 };
        let copies = (end + ops + if self.store { outs } else { 0 }).saturating_sub(values);
        45 * left
            + 14 * loads
            + rest
            + 3 * (missing + left + goal_primes).saturating_sub(primes)
            + 3 * copies
            + 3 * first_ops
    }

    fn moves(&self, s: &St, out: &mut Vec<(u32, St, String)>) {
        let n = s.tok.len();
        let mut emit = |cost: u32, ns: St, name: String| {
            if let Some(ns) = self.canon(ns) {
                out.push((cost, ns, name));
            }
        };
        let push = |s: &St, v: u8| {
            let mut ns = s.clone();
            ns.tok.insert(0, v);
            ns
        };
        // stack slots beyond tok are dead values
        let at = |k: usize| -> u8 { s.tok.get(k).copied().unwrap_or(G) };
        if n < self.w {
            emit(3, push(s, P), "P".into());
            for k in 0..n {
                if s.tok[k] != G && s.tok[k] != P {
                    emit(3, push(s, s.tok[k]), format!("dup{}", k + 1));
                }
            }
        }
        if n > 0 {
            for k in 1..n {
                if at(k) != s.tok[0] {
                    let mut ns = s.clone();
                    ns.tok.swap(0, k);
                    emit(3, ns, format!("swap{k}"));
                }
            }
            let mut ns = s.clone();
            ns.tok.remove(0);
            emit(2, ns, "pop".into());
        }
        for l in 0..self.t {
            if self.loads >> l & 1 == 1 && s.sboxed >> l & 1 == 0 && n < self.w {
                let mut ns = push(s, self.unit(0, l));
                ns.sboxed |= 1 << l;
                emit(14, ns, format!("load{l}"));
            }
        }
        if self.exch {
            for a in 1..n {
                for b in a + 1..n {
                    if s.tok[a] != s.tok[b] {
                        let mut ns = s.clone();
                        ns.tok.swap(a, b);
                        emit(3, ns, format!("exchange{a},{b}"));
                    }
                }
            }
        }
        let (a, b, c) = (at(0), at(1), at(2));
        if let (Some((ra, ca, ba)), Some((rb, cb, bb))) = (self.unform(a), self.unform(b)) {
            let sum: Vec<u8> = ca.iter().zip(cb).map(|(x, y)| x + y).collect();
            if ra == rb {
                if let Some(k) = self.form(ra, &sum, 1) {
                    if ba + bb <= 5 {
                        let mut ns = s.clone();
                        ns.tok.drain(0..2);
                        ns.tok.insert(0, k - 1 + ba + bb);
                        emit(3, ns, "add".into());
                    }
                    if c == P {
                        let mut ns = s.clone();
                        ns.tok.drain(0..3);
                        ns.tok.insert(0, k);
                        emit(8, ns, "addmod".into());
                    }
                }
            }
        }
        if (RAW..FORM).contains(&a) && b == P {
            let l = a - RAW;
            if self.raw_bound[l as usize] <= 4 {
                let mut ns = s.clone();
                ns.tok.drain(0..2);
                ns.tok.insert(0, self.unit(0, l as usize));
                ns.sboxed |= 1 << l;
                emit(45, ns, format!("sbox{l}"));
            }
        }
        if self.two && b == P {
            if let Some((0, ca, ba)) = self.unform(a) {
                for l in 0..self.t {
                    if s.sboxed2 >> l & 1 == 0 && ba <= 4 && ca == self.rows[0][l].as_slice() {
                        let mut ns = s.clone();
                        ns.tok.drain(0..2);
                        ns.tok.insert(0, self.unit(1, l));
                        ns.sboxed2 |= 1 << l;
                        emit(45, ns, format!("sbox{l}'"));
                    }
                }
            }
        }
        if self.store && (s.stored as usize) < self.t && self.is_output(a, s.stored as usize, true)
        {
            let mut ns = s.clone();
            ns.tok.remove(0);
            ns.stored += 1;
            emit(5, ns, "store".into());
        }
    }

    fn name(&self, v: u8) -> String {
        match self.unform(v) {
            None if v == G => "_".into(),
            None if v == P => "P".into(),
            None => format!("s{}", v - RAW),
            Some((r, c, b)) => {
                let x = self.names[r as usize];
                let terms: Vec<String> = c
                    .iter()
                    .enumerate()
                    .filter(|(_, &d)| d > 0)
                    .map(|(i, &d)| {
                        if d == 1 {
                            format!("{x}{i}")
                        } else {
                            format!("{d}{x}{i}")
                        }
                    })
                    .collect();
                format!("{}<{b}", terms.join("+"))
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let t: usize = args[1].parse().unwrap();
    assert!(t == 2 || t == 3);
    let internal = std::env::var("INTERNAL").is_ok_and(|v| v == "1");
    let junction = std::env::var("JUNCTION").is_ok_and(|v| v == "1");
    let two = internal || junction || std::env::var("ROUNDS").is_ok_and(|v| v == "2");
    assert!(
        !two || internal || junction || t == 2,
        "two external rounds only for t = 2"
    );
    assert!(!internal || t == 3, "INTERNAL is the t = 3 seam");
    let external: Vec<Vec<u8>> = (0..t)
        .map(|i| (0..t).map(|j| if i == j { 2 } else { 1 }).collect())
        .collect();
    // b0 = sum, b1 = x, b2 = s2, b3 = s1: x + sum, s1 + sum, 2 s2 + sum
    let rows0 = if internal {
        vec![vec![1, 1, 0, 0], vec![1, 0, 0, 1], vec![1, 0, 2, 0]]
    } else {
        external.clone()
    };
    // JUNCTION: the second round is made of its S-box outputs
    let rows1: Vec<Vec<u8>> = if junction {
        (0..t)
            .map(|i| (0..t).map(|j| u8::from(i == j)).collect())
            .collect()
    } else {
        external.clone()
    };
    let forms = [below_rows(&rows0), below_rows(&rows1)];
    let base = [FORM, FORM + 6 * forms[0].len() as u8];
    assert!(!two || base[1] as usize + 6 * forms[1].len() <= 256);
    let w: usize = args.get(4).and_then(|a| a.parse().ok()).unwrap_or(10);
    let ub: u32 = args.get(5).and_then(|a| a.parse().ok()).unwrap_or(u32::MAX);
    let mut pb = Pb {
        t,
        forms,
        rows: [rows0, rows1],
        base,
        names: [if internal { "b" } else { "x" }, "y"],
        raw_bound: vec![0u8; t],
        store: args[3] == "store",
        goal: vec![],
        w,
        exch: std::env::var("EXCHANGE").is_ok_and(|v| v == "1"),
        loads: std::env::var("LOADS").map_or(0, |v| {
            v.split(',')
                .map(|l| 1u8 << l.parse::<u8>().unwrap())
                .fold(0, |a, b| a | b)
        }),
        two,
        junction,
    };
    let mut tok = vec![];
    let mut sboxed = if internal { (1u8 << t) - 1 } else { 0 };
    for item in args[2].split(',') {
        let (name, b) = item.split_once(':').unwrap_or((item, "1"));
        let b: u8 = b.parse().unwrap();
        let v = match name {
            "G" => G,
            "P" => P,
            _ if name.starts_with('s') => {
                let l: usize = name[1..].parse().unwrap();
                pb.raw_bound[l] = b;
                RAW + l as u8
            }
            _ if name.starts_with('x') => {
                let l: usize = name[1..].parse().unwrap();
                sboxed |= 1 << l;
                pb.unit(0, l)
            }
            _ if name.starts_with('b') && internal => {
                let l: usize = name[1..].parse().unwrap();
                pb.unit(0, l) - 1 + b
            }
            _ => panic!("bad init token {name}"),
        };
        tok.push(v);
    }
    if !pb.store {
        pb.goal = args[3]
            .split(',')
            .map(|item| {
                let (name, b) = item.split_once(':').unwrap_or((item, "5"));
                if name == "P" {
                    (P, 0)
                } else if name == "G" {
                    (G, 0)
                } else {
                    (2 + name[1..].parse::<u8>().unwrap(), b.parse().unwrap())
                }
            })
            .collect();
    }
    let start = pb
        .canon(St {
            tok,
            stored: 0,
            sboxed,
            sboxed2: 0,
        })
        .expect("bad start");
    assert!(w <= 12, "the packed state holds 12 slots");
    // nodes: packed state and parent; the moves are found again on the way back
    let mut nodes: Vec<(u128, u32)> = vec![(pack(&start), u32::MAX)];
    let mut best: HashMap<u128, u32> = HashMap::new();
    best.insert(pack(&start), 0);
    let mut heap = BinaryHeap::new();
    heap.push(Reverse((pb.h(&start), 0u32, 0u32)));
    let mut out = vec![];
    let mut expanded = 0u64;
    while let Some(Reverse((f, g, i))) = heap.pop() {
        if f >= ub {
            break;
        }
        let key = nodes[i as usize].0;
        if best.get(&key).is_some_and(|&b| b < g) {
            continue;
        }
        let s = unpack(key);
        expanded += 1;
        if pb.done(&s) {
            let mut path = vec![];
            let mut j = i;
            while nodes[j as usize].1 != u32::MAX {
                path.push(j);
                j = nodes[j as usize].1;
            }
            path.reverse();
            println!("cost {g} ({expanded} expanded, {} states)", best.len());
            let mut prev = start.clone();
            for j in path {
                let next = nodes[j as usize].0;
                out.clear();
                pb.moves(&prev, &mut out);
                let name = out
                    .iter()
                    .filter(|(_, ns, _)| pack(ns) == next)
                    .min_by_key(|(c, _, _)| *c)
                    .map(|(_, _, n)| n.clone())
                    .unwrap_or_default();
                prev = unpack(next);
                let names: Vec<String> = prev.tok.iter().map(|&v| pb.name(v)).collect();
                println!("  {:12} [{}]", name, names.join(", "));
            }
            return;
        }
        out.clear();
        pb.moves(&s, &mut out);
        for (c, ns, _) in out.drain(..) {
            let ng = g + c;
            let nk = pack(&ns);
            if best.get(&nk).is_some_and(|&b| b <= ng) {
                continue;
            }
            best.insert(nk, ng);
            let nf = ng + pb.h(&ns);
            if nf >= ub {
                continue;
            }
            nodes.push((nk, i));
            heap.push(Reverse((nf, ng, (nodes.len() - 1) as u32)));
        }
    }
    println!(
        "no solution below {ub} ({expanded} expanded, {} states)",
        best.len()
    );
}

/// 12 token bytes, the length, the stores and both S-box masks in one key
fn pack(s: &St) -> u128 {
    let mut k: u128 = 0;
    for (i, &v) in s.tok.iter().enumerate() {
        k |= (v as u128) << (8 * i);
    }
    k | (s.tok.len() as u128) << 96
        | (s.stored as u128) << 100
        | (s.sboxed as u128) << 104
        | (s.sboxed2 as u128) << 112
}

fn unpack(k: u128) -> St {
    let len = (k >> 96 & 15) as usize;
    St {
        tok: (0..len).map(|i| (k >> (8 * i)) as u8).collect(),
        stored: (k >> 100 & 15) as u8,
        sboxed: (k >> 104) as u8,
        sboxed2: (k >> 112) as u8,
    }
}
