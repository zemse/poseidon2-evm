// An exact search over single opcodes for the seams of the t = 2, 3
// permutations: the last external round, which stores its outputs, or any
// round from a given layout to a given one. Values are linear forms over the
// S-box outputs x_i with coefficients 0..2 and an inclusive bound in units
// of P - 1; only forms below a row of the external matrix that is still
// needed are kept (others become dead). Moves: PRIME copy, DUPn, SWAPn,
// EXCHANGE of two slots below the top (EXCHANGE=1), POP, ADD (bound at most
// 5), ADDMOD over a PRIME copy in slot 3, the S-box of lane i (its constant
// ADD and the five-opcode body, 45 gas, on s_i over a PRIME copy) and
// `msize mstore` of the next output (reduced). Dead values below the window
// cost nothing; a PRIME copy is always reachable (a deep one or PUSH32).
//
//   seam <t> <init> <goal> [window=10] [ub]
//
// init: top first, comma separated: s<i>:<bound> (lane i before its
// S-box), x<i>, P, G (a dead value). goal: `store` (s0', s1', ... stored in
// order, reduced) or a layout prefix of o<i>:<bound> and P. Optimal within
// the window and these moves.
//
// ROUNDS=2 (t = 2) searches two external rounds at once: the outputs of the
// first (bound at most 4) are the S-box inputs of the second, whose forms
// (y<i> its S-box outputs) the goal takes, so the layout between the rounds
// is free and the second round may start before the first ends.
// LOADS=0,1,... takes lane i from calldata reduced instead of its S-box
// (PRIME copy, PUSH, CALLDATALOAD, MOD: 14 gas).

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const G: u8 = 0;
const P: u8 = 1;
const RAW: u8 = 2; // + lane
const FORM: u8 = 8; // + code * 6 + bound (first round)
const FORM2: u8 = 64; // the same for the second round (t = 2)

#[derive(Clone)]
struct Pb {
    t: usize,
    rows: Vec<Vec<u8>>,
    raw_bound: Vec<u8>,
    store: bool,
    goal: Vec<(u8, u8)>, // (token class: P or output index + 2, max bound)
    w: usize,
    exch: bool,
    loads: u8,
    two: bool,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct St {
    tok: Vec<u8>, // top first
    stored: u8,
    sboxed: u8,
    sboxed2: u8,
}

fn code(c: &[u8]) -> u8 {
    c.iter().rev().fold(0, |a, &d| a * 3 + d)
}
fn coeffs(t: usize, mut k: u8) -> Vec<u8> {
    let mut v = vec![0; t];
    for e in v.iter_mut() {
        *e = k % 3;
        k /= 3;
    }
    v
}
fn form(round: u8, c: u8, b: u8) -> u8 {
    [FORM, FORM2][round as usize] + c * 6 + b
}
/// (round, code, bound) of a form
fn unform(tok: u8) -> Option<(u8, u8, u8)> {
    if tok >= FORM2 {
        Some((1, (tok - FORM2) / 6, (tok - FORM2) % 6))
    } else if tok >= FORM {
        Some((0, (tok - FORM) / 6, (tok - FORM) % 6))
    } else {
        None
    }
}

impl Pb {
    fn last(&self) -> u8 {
        self.two as u8
    }

    fn useful(&self, s: &St, round: u8, c: &[u8]) -> bool {
        let below = |r: usize| c.iter().zip(&self.rows[r]).all(|(a, b)| a <= b);
        if round < self.last() {
            return (0..self.t).any(|r| s.sboxed2 >> r & 1 == 0 && below(r));
        }
        let first = if self.store { s.stored as usize } else { 0 };
        (first..self.t).any(below)
    }

    fn canon(&self, mut s: St) -> Option<St> {
        for i in 0..s.tok.len() {
            let v = s.tok[i];
            if (RAW..FORM).contains(&v) {
                if s.sboxed >> (v - RAW) & 1 == 1 {
                    s.tok[i] = G;
                }
            } else if let Some((r, c, _)) = unform(v) {
                if !self.useful(&s, r, &coeffs(self.t, c)) {
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
        unform(v).is_some_and(|(round, c, b)| {
            round == self.last() && coeffs(self.t, c) == self.rows[r] && (!reduced || b == 1)
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
            self.is_output(v, (g - 2) as usize, false) && unform(v).unwrap().2 <= b
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
                + if have {
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
        let ops = (self.t - first) as u32 - built;
        let end = if self.store { 0 } else { self.t as u32 };
        let copies = (end + ops + if self.store { outs } else { 0 }).saturating_sub(values);
        45 * left
            + 14 * loads
            + rest
            + 3 * (missing + left + goal_primes).saturating_sub(primes)
            + 3 * copies
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
        let unit = |l: usize| {
            let mut e = vec![0; self.t];
            e[l] = 1;
            code(&e)
        };
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
                let mut ns = push(s, form(0, unit(l), 1));
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
        if let (Some((ra, ca, ba)), Some((rb, cb, bb))) = (unform(a), unform(b)) {
            let sum: Vec<u8> = coeffs(self.t, ca)
                .iter()
                .zip(coeffs(self.t, cb))
                .map(|(x, y)| x + y)
                .collect();
            if ra == rb && sum.iter().all(|&d| d <= 2) {
                let k = code(&sum);
                if ba + bb <= 5 {
                    let mut ns = s.clone();
                    ns.tok.drain(0..2);
                    ns.tok.insert(0, form(ra, k, ba + bb));
                    emit(3, ns, "add".into());
                }
                if c == P {
                    let mut ns = s.clone();
                    ns.tok.drain(0..3);
                    ns.tok.insert(0, form(ra, k, 1));
                    emit(8, ns, "addmod".into());
                }
            }
        }
        if (RAW..FORM).contains(&a) && b == P {
            let l = a - RAW;
            if self.raw_bound[l as usize] <= 4 {
                let mut ns = s.clone();
                ns.tok.drain(0..2);
                ns.tok.insert(0, form(0, unit(l as usize), 1));
                ns.sboxed |= 1 << l;
                emit(45, ns, format!("sbox{l}"));
            }
        }
        if self.two && b == P {
            if let Some((0, ca, ba)) = unform(a) {
                let cs = coeffs(self.t, ca);
                for l in 0..self.t {
                    if s.sboxed2 >> l & 1 == 0 && ba <= 4 && cs == self.rows[l] {
                        let mut ns = s.clone();
                        ns.tok.drain(0..2);
                        ns.tok.insert(0, form(1, unit(l), 1));
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
        match unform(v) {
            None if v == G => "_".into(),
            None if v == P => "P".into(),
            None => format!("s{}", v - RAW),
            Some((r, c, b)) => {
                let x = if r == 0 { "x" } else { "y" };
                let terms: Vec<String> = coeffs(self.t, c)
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
    let two = std::env::var("ROUNDS").is_ok_and(|v| v == "2");
    assert!(!two || t == 2, "two rounds only for t = 2");
    let rows: Vec<Vec<u8>> = (0..t)
        .map(|i| (0..t).map(|j| if i == j { 2 } else { 1 }).collect())
        .collect();
    let w: usize = args.get(4).and_then(|a| a.parse().ok()).unwrap_or(10);
    let ub: u32 = args.get(5).and_then(|a| a.parse().ok()).unwrap_or(u32::MAX);
    let mut raw_bound = vec![0u8; t];
    let mut tok = vec![];
    let mut sboxed = 0u8;
    for item in args[2].split(',') {
        let (name, b) = item.split_once(':').unwrap_or((item, "1"));
        let b: u8 = b.parse().unwrap();
        let v = match name {
            "G" => G,
            "P" => P,
            _ if name.starts_with('s') => {
                let l: usize = name[1..].parse().unwrap();
                raw_bound[l] = b;
                RAW + l as u8
            }
            _ if name.starts_with('x') => {
                let l: usize = name[1..].parse().unwrap();
                sboxed |= 1 << l;
                let mut e = vec![0; t];
                e[l] = 1;
                form(0, code(&e), 1)
            }
            _ => panic!("bad init token {name}"),
        };
        tok.push(v);
    }
    let store = args[3] == "store";
    let goal: Vec<(u8, u8)> = if store {
        vec![]
    } else {
        args[3]
            .split(',')
            .map(|item| {
                let (name, b) = item.split_once(':').unwrap_or((item, "5"));
                if name == "P" {
                    (P, 0)
                } else {
                    (2 + name[1..].parse::<u8>().unwrap(), b.parse().unwrap())
                }
            })
            .collect()
    };
    let pb = Pb {
        t,
        rows,
        raw_bound,
        store,
        goal,
        w,
        exch: std::env::var("EXCHANGE").is_ok_and(|v| v == "1"),
        loads: std::env::var("LOADS").map_or(0, |v| {
            v.split(',')
                .map(|l| 1u8 << l.parse::<u8>().unwrap())
                .fold(0, |a, b| a | b)
        }),
        two,
    };
    let start = pb
        .canon(St {
            tok,
            stored: 0,
            sboxed,
            sboxed2: 0,
        })
        .expect("bad start");
    let mut nodes: Vec<(St, usize, String)> = vec![(start.clone(), usize::MAX, String::new())];
    let mut best: HashMap<St, u32> = HashMap::new();
    best.insert(start.clone(), 0);
    let mut heap = BinaryHeap::new();
    heap.push(Reverse((pb.h(&start), 0u32, 0usize)));
    let mut out = vec![];
    let mut expanded = 0u64;
    while let Some(Reverse((f, g, i))) = heap.pop() {
        if f >= ub {
            break;
        }
        let s = nodes[i].0.clone();
        if best.get(&s).is_some_and(|&b| b < g) {
            continue;
        }
        expanded += 1;
        if pb.done(&s) {
            let mut path = vec![];
            let mut j = i;
            while nodes[j].1 != usize::MAX {
                path.push(j);
                j = nodes[j].1;
            }
            path.reverse();
            println!("cost {g} ({expanded} expanded, {} states)", best.len());
            for j in path {
                let names: Vec<String> = nodes[j].0.tok.iter().map(|&v| pb.name(v)).collect();
                println!("  {:12} [{}]", nodes[j].2, names.join(", "));
            }
            return;
        }
        out.clear();
        pb.moves(&s, &mut out);
        for (c, ns, name) in out.drain(..) {
            let ng = g + c;
            if best.get(&ns).is_some_and(|&b| b <= ng) {
                continue;
            }
            best.insert(ns.clone(), ng);
            let nf = ng + pb.h(&ns);
            if nf >= ub {
                continue;
            }
            nodes.push((ns, i, name));
            heap.push(Reverse((nf, ng, nodes.len() - 1)));
        }
    }
    println!(
        "no solution below {ub} ({expanded} expanded, {} states)",
        best.len()
    );
}
