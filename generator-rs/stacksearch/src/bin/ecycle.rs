// A lower bound on the stack moves of the steady t = 4 external rounds with
// no layout fixed between rounds, the external counterpart of cycle.rs:
// the least mean cost per round over every cycle of rounds in the same
// relaxed stack machine.
//
// Only the values of the round are kept, as tokens: s_i (the inputs), x_i
// (the S-box outputs) and the linear layer's values. PRIME copies, the
// round constants and the constant 4 are left out (each costs the same in
// every program: 4 S-boxes 180, the linear layer's ops 62, its 8 PRIME
// copies 24, a fixed part of 266), so the S-box and the MULMOD by 4 are
// unary moves on the top token and a real SWAP that moves a PRIME copy or
// a constant becomes a move of one value from the top to any depth or from
// any depth to the top, 3 gas like a SWAP. What is counted: a copy of a
// value (DUP, 3), a SWAP or such a move (3), a POP (2). The linear layer
// is M4 as every t = 4 program in the repository builds it, t0 = x0 + x1,
// t1 = x2 + x3, 2x1, 2x3, t2 = 2x1 + t1, t3 = 2x3 + t0, 4t0, 4t1, s3' =
// 4t1 + t3, s1' = 4t0 + t2, with s0' = s1' + t3 and s2' = s3' + t2, or
// through t23 = t2 + t3 (s0' = t23 + 4t0, s2' = t23 + 4t1, 3 gas for its
// ADD): every production of stacksearch's macro graph (lazy) for these
// classes. The next round may start before this one ends (its S-boxes and
// linear-layer values from the outputs made so far).
//
//   ecycle [max_window=8] [layers=4]
//
// A state is the stack of tokens (dead ones as one garbage token, nothing
// below the deepest live one), what this round and the next have computed
// and which outputs are made. A round ends when its last output is made.
// Every layout a round can end in (closure from the inputs in every
// order) starts at D_0 = 0; D_k(b) is the cheapest k rounds ending in b
// (multi-source Dijkstra per round), and the least cycle mean lies between
// the least and the largest D_k(b) - D_(k-1)(b). A real round costs at
// least 266 + that mean.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const NJ: usize = 17; // nodes a round: s 0..3, x 4..7, then the linear layer
const G: u8 = 0;
const PT: u8 = (2 * NJ + 1) as u8; // a PRIME copy (PRIME=1)
const NT: usize = 2 * NJ + 2;
const MAXW: usize = 14;

// nodes
const X: usize = 4;
const T0: usize = 8;
const T1: usize = 9;
const D1: usize = 10;
const D3: usize = 11;
const T2: usize = 12;
const T3: usize = 13;
const F0: usize = 14;
const F1: usize = 15;
const T23: usize = 16;
const NAMES: [&str; NJ] = [
    "s0", "s1", "s2", "s3", "x0", "x1", "x2", "x3", "t0", "t1", "2x1", "2x3", "t2", "t3", "4t0",
    "4t1", "t23",
];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum N {
    C(usize), // this round's node
    O(usize), // output i: the next round's s_i
}

struct Op {
    res: N,
    args: Vec<N>,
    extra: u32,
    /// ADDMOD (or, unary, the S-box and MULMOD by 4): a PRIME copy under
    /// the operands
    modp: bool,
}

fn ops() -> Vec<Op> {
    use N::*;
    let op = |res: N, args: &[N], extra: u32| Op {
        res,
        args: args.to_vec(),
        extra,
        modp: args.len() == 1 || res == C(T2) || res == C(T3),
    };
    let mut v = Vec::new();
    for i in 0..4 {
        v.push(op(C(X + i), &[C(i)], 0));
    }
    v.push(op(C(T0), &[C(X), C(X + 1)], 0));
    v.push(op(C(T1), &[C(X + 2), C(X + 3)], 0));
    v.push(op(C(D1), &[C(X + 1), C(X + 1)], 0));
    v.push(op(C(D3), &[C(X + 3), C(X + 3)], 0));
    v.push(op(C(T2), &[C(D1), C(T1)], 0));
    v.push(op(C(T3), &[C(D3), C(T0)], 0));
    v.push(op(C(F0), &[C(T0)], 0));
    v.push(op(C(F1), &[C(T1)], 0));
    v.push(op(C(T23), &[C(T2), C(T3)], 3));
    v.push(op(O(3), &[C(F1), C(T3)], 0));
    v.push(op(O(1), &[C(F0), C(T2)], 0));
    v.push(op(O(0), &[O(1), C(T3)], 0));
    v.push(op(O(2), &[O(3), C(T2)], 0));
    v.push(op(O(0), &[C(T23), C(F0)], 0));
    v.push(op(O(2), &[C(T23), C(F1)], 0));
    v
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct St {
    tok: [u8; MAXW],
    len: u8,
    cur: u32,  // computed nodes of this round (x and the linear layer)
    out: u8,   // outputs made
    next: u32, // computed nodes of the next round
}

// token ids: 0 garbage, 1 + j this round's node j, 1 + NJ + j the next
// round's (the outputs are the next round's s_i)
fn tc(j: usize) -> u8 {
    (1 + j) as u8
}
fn tn(j: usize) -> u8 {
    (1 + NJ + j) as u8
}

struct Pb {
    ops: Vec<Op>,
    w: usize,
    sym: [u8; NT],
    prime: bool,
    memo: std::cell::RefCell<HashMap<u64, [u32; NT]>>,
}

impl Pb {
    fn tok_of(&self, n: N, next: bool) -> u8 {
        match (n, next) {
            (N::C(j), false) => tc(j),
            (N::O(i), false) => tn(i),
            (N::C(j), true) => tn(j),
            (N::O(_), true) => unreachable!("the next round's outputs"),
        }
    }
    fn done(&self, s: &St, n: N, next: bool) -> bool {
        match (n, next) {
            (N::C(j), false) => j < X || s.cur >> j & 1 == 1,
            (N::O(i), false) => s.out >> i & 1 == 1,
            (N::C(j), true) => (j < X && s.out >> j & 1 == 1) || s.next >> j & 1 == 1,
            (N::O(_), true) => false,
        }
    }
    /// an op that can still run (its result not made; t23 only while an
    /// output it feeds is missing); with `next` the next round's copy
    fn open(&self, s: &St, op: &Op, next: bool) -> bool {
        if next {
            if let N::O(_) = op.res {
                return true; // after this round, counted for the uses
            }
            if op.res == N::C(T23) {
                return s.next >> T23 & 1 == 0;
            }
            return !self.done(s, op.res, true);
        }
        if self.done(s, op.res, false) {
            return false;
        }
        if op.res == N::C(T23) {
            return s.out & 0b101 != 0b101;
        }
        true
    }
    /// the most uses every token can still have (they depend only on what
    /// is computed, memoized)
    fn uses(&self, s: &St) -> [u32; NT] {
        let key = s.cur as u64 | (s.out as u64) << 17 | (s.next as u64) << 21;
        if let Some(u) = self.memo.borrow().get(&key) {
            return *u;
        }
        let u = self.uses_of(s);
        self.memo.borrow_mut().insert(key, u);
        u
    }
    fn uses_of(&self, s: &St) -> [u32; NT] {
        let mut u = [0; NT];
        for next in [false, true] {
            for op in &self.ops {
                if !self.open(s, op, next) {
                    continue;
                }
                for &a in &op.args {
                    if next {
                        if let N::O(_) = a {
                            // the next round's outputs as operands
                            continue;
                        }
                    }
                    u[self.tok_of(a, next) as usize] += 1;
                }
            }
        }
        u[G as usize] = 0;
        u[PT as usize] = u32::MAX;
        u
    }
    /// false when a value made and still needed has no entry left: it
    /// cannot be made again, so no round after this one could end
    fn whole(&self, s: &St) -> bool {
        let u = self.uses(s);
        let n = s.len as usize;
        for v in 1..PT {
            if u[v as usize] == 0 || s.tok[..n].contains(&v) {
                continue;
            }
            let j = (v as usize - 1) % NJ;
            let made = if (v as usize) <= NJ {
                j < X || s.cur >> j & 1 == 1
            } else if j < X {
                s.out >> j & 1 == 1
            } else {
                s.next >> j & 1 == 1
            };
            if made {
                return false;
            }
        }
        true
    }
    fn canon(&self, s: &mut St) {
        let u = self.uses(s);
        for i in 0..s.len as usize {
            if u[s.tok[i] as usize] == 0 {
                s.tok[i] = G;
            }
        }
        // PRIME copies below every live value are left out too: one is
        // pushed for 3 when needed, and a SWAP with one is the reservoir
        // move below
        while s.len > 0 && matches!(s.tok[s.len as usize - 1], G | PT) {
            s.len -= 1;
        }
    }
    fn pack(s: &St) -> u128 {
        let mut k: u128 = 0;
        for i in 0..s.len as usize {
            k |= (s.tok[i] as u128 + 1) << (6 * i);
        }
        k | (s.cur as u128) << 84 | (s.out as u128) << 101 | (s.next as u128) << 105
    }
    fn unpack(k: u128) -> St {
        let mut s = St {
            tok: [0; MAXW],
            len: 0,
            cur: (k >> 84) as u32 & 0x1ffff,
            out: (k >> 101) as u8 & 15,
            next: (k >> 105) as u32 & 0x1ffff,
        };
        for i in 0..MAXW {
            let v = (k >> (6 * i)) & 63;
            if v == 0 {
                break;
            }
            s.tok[i] = v as u8 - 1;
            s.len += 1;
        }
        s
    }
    /// the least key over the lane symmetry (0 2)(1 3) of M4
    fn key(&self, s: &St) -> u128 {
        let a = Self::pack(s);
        let mut r = *s;
        for i in 0..s.len as usize {
            r.tok[i] = self.sym[s.tok[i] as usize];
        }
        let mm = |m: u32| -> u32 {
            let mut o = 0;
            for j in 0..NJ {
                if m >> j & 1 == 1 {
                    o |= 1 << (self.sym[1 + j] - 1);
                }
            }
            o
        };
        r.cur = mm(s.cur);
        r.next = mm(s.next);
        let mut o = 0;
        for i in 0..4 {
            if s.out >> i & 1 == 1 {
                o |= 1 << (i ^ 2);
            }
        }
        r.out = o;
        a.min(Self::pack(&r))
    }
    /// the round's end: the next round's tokens become this round's
    fn shift(&self, s: &St) -> St {
        let mut r = *s;
        for i in 0..s.len as usize {
            let v = s.tok[i];
            r.tok[i] = match v {
                PT => PT,
                v if v as usize > NJ => v - NJ as u8,
                _ => G,
            };
        }
        r.cur = s.next;
        r.next = 0;
        r.out = 0;
        self.canon(&mut r);
        r
    }
    /// children with their cost; `end` marks a round's end (shifted)
    fn moves(&self, s: &St, out: &mut Vec<(St, u32, bool)>) {
        out.clear();
        let n = s.len as usize;
        let push = |out: &mut Vec<(St, u32, bool)>, mut t: St, c: u32| {
            if !self.whole(&t) {
                return;
            }
            if t.out == 15 {
                let r = self.shift(&t);
                if (r.len as usize) <= self.w {
                    out.push((r, c, true));
                }
                return;
            }
            self.canon(&mut t);
            if (t.len as usize) <= self.w {
                out.push((t, c, false));
            }
        };
        let u = self.uses(s);
        let count = |v: u8| s.tok[..n].iter().filter(|&&x| x == v).count() as u32;
        // DUP of a value with fewer entries than uses left
        if n < self.w {
            for k in 0..n.min(16) {
                let v = s.tok[k];
                if v == G || v == PT {
                    continue;
                }
                if count(v) >= u[v as usize] {
                    continue;
                }
                let mut t = *s;
                t.tok.copy_within(0..n, 1);
                t.tok[0] = v;
                t.len += 1;
                push(out, t, 3);
            }
        }
        for k in 1..n.min(17) {
            if s.tok[k] != s.tok[0] {
                let mut t = *s;
                t.tok.swap(0, k);
                push(out, t, 3);
            }
            if k >= 2 {
                // the top to depth k, depth k to the top
                let mut t = *s;
                let v = t.tok[0];
                t.tok.copy_within(1..=k, 0);
                t.tok[k] = v;
                push(out, t, 3);
                let mut t = *s;
                let v = t.tok[k];
                t.tok.copy_within(0..k, 1);
                t.tok[0] = v;
                push(out, t, 3);
            }
        }
        if self.prime && n < self.w {
            // a PRIME copy on top (DUP or PUSH32)
            let mut t = *s;
            t.tok.copy_within(0..n, 1);
            t.tok[0] = PT;
            t.len += 1;
            push(out, t, 3);
        }
        if self.prime && n >= 1 && s.tok[0] != PT {
            // a SWAP with a PRIME copy below every live value: the top
            // goes to the bottom, the copy on top
            let mut t = *s;
            let v = t.tok[0];
            t.tok[0] = PT;
            if n < MAXW {
                t.tok[n] = v;
                t.len += 1;
                push(out, t, 3);
            }
        }
        // POP, but not of the last entry of a value still needed (it
        // cannot be made again)
        if n >= 1 && (matches!(s.tok[0], G | PT) || count(s.tok[0]) > 1) {
            let mut t = *s;
            t.tok.copy_within(1..n, 0);
            t.len -= 1;
            push(out, t, 2);
        }
        for next in [false, true] {
            for op in &self.ops {
                if next {
                    if let N::O(_) = op.res {
                        continue;
                    }
                }
                if !self.open(s, op, next) {
                    continue;
                }
                // operands available on top
                if op.args.iter().any(|&a| {
                    if next {
                        if let N::O(_) = a {
                            return true;
                        }
                    }
                    !self.done(s, a, next)
                }) {
                    continue;
                }
                let mut k = op.args.len();
                if n < k {
                    continue;
                }
                let a0 = self.tok_of(op.args[0], next);
                let ok = if k == 1 {
                    s.tok[0] == a0
                } else {
                    let a1 = self.tok_of(op.args[1], next);
                    (s.tok[0] == a0 && s.tok[1] == a1) || (s.tok[0] == a1 && s.tok[1] == a0)
                };
                if !ok {
                    continue;
                }
                if self.prime && op.modp {
                    if n <= k || s.tok[k] != PT {
                        continue;
                    }
                    k += 1;
                }
                let mut t = *s;
                t.tok.copy_within(k..n, 1);
                t.len = (n - k + 1) as u8;
                match (op.res, next) {
                    (N::C(j), false) => {
                        t.tok[0] = tc(j);
                        t.cur |= 1 << j;
                    }
                    (N::O(i), false) => {
                        t.tok[0] = tn(i);
                        t.out |= 1 << i;
                    }
                    (N::C(j), true) => {
                        t.tok[0] = tn(j);
                        t.next |= 1 << j;
                    }
                    _ => unreachable!(),
                }
                push(out, t, op.extra);
            }
        }
    }
    fn show(&self, s: &St) -> String {
        let mut v = Vec::new();
        for i in 0..s.len as usize {
            let t = s.tok[i] as usize;
            v.push(if t == 0 {
                "_".to_string()
            } else if t == PT as usize {
                "P".to_string()
            } else if t <= NJ {
                NAMES[t - 1].to_string()
            } else {
                format!("{}'", NAMES[t - 1 - NJ])
            });
        }
        format!("[{}] cur {:#x} next {:#x}", v.join(","), s.cur, s.next)
    }
    /// one round from every source (key -> cost): the cheapest cost of
    /// every end layout, and the states explored
    fn round(&self, sources: &HashMap<u128, u32>) -> (HashMap<u128, u32>, usize) {
        let mut dist: HashMap<u128, u32> = HashMap::new();
        let mut pq = BinaryHeap::new();
        for (&k, &c) in sources {
            dist.insert(k, c);
            pq.push(Reverse((c, k)));
        }
        let mut ends: HashMap<u128, u32> = HashMap::new();
        let mut buf = Vec::new();
        let mut expanded = 0usize;
        while let Some(Reverse((g, k))) = pq.pop() {
            if dist.get(&k).is_some_and(|&d| d < g) {
                continue;
            }
            expanded += 1;
            if expanded % 5_000_000 == 0 {
                eprintln!("expanded {expanded}, states {}, g {g}", dist.len());
            }
            let s = Self::unpack(k);
            self.moves(&s, &mut buf);
            for &(t, c, end) in &buf {
                let ng = g + c;
                let tk = self.key(&t);
                if end {
                    let e = ends.entry(tk).or_insert(u32::MAX);
                    if ng < *e {
                        *e = ng;
                    }
                    continue;
                }
                if dist.get(&tk).is_none_or(|&d| ng < d) {
                    dist.insert(tk, ng);
                    pq.push(Reverse((ng, tk)));
                }
            }
        }
        (ends, dist.len())
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let w: usize = args.get(1).map_or(8, |s| s.parse().unwrap());
    let layers: usize = args.get(2).map_or(4, |s| s.parse().unwrap());
    assert!(w <= MAXW);
    // (0 2)(1 3) on the lanes, on every node of both rounds
    let mut sym = [0u8; NT];
    sym[PT as usize] = PT;
    let jmap = |j: usize| -> usize {
        match j {
            0..=3 => j ^ 2,
            4..=7 => X + ((j - X) ^ 2),
            T0 => T1,
            T1 => T0,
            D1 => D3,
            D3 => D1,
            T2 => T3,
            T3 => T2,
            F0 => F1,
            F1 => F0,
            T23 => T23,
            _ => unreachable!(),
        }
    };
    for j in 0..NJ {
        sym[1 + j] = (1 + jmap(j)) as u8;
        sym[1 + NJ + j] = (1 + NJ + jmap(j)) as u8;
    }
    let prime = std::env::var("PRIME").is_ok();
    // PRIME=1 keeps the PRIME copies as tokens: the S-box and MULMOD by 4
    // take one under their operand, ADDMOD one under its two, each pushed
    // for 3 (so the fixed part drops their 24)
    let fixed = if prime { 242 } else { 266 };
    let pb = Pb {
        ops: ops(),
        w,
        sym,
        prime,
        memo: Default::default(),
    };
    // the inputs in every order
    let mut starts: HashMap<u128, u32> = HashMap::new();
    let mut perm = [0usize, 1, 2, 3];
    fn permute(k: usize, p: &mut [usize; 4], out: &mut Vec<[usize; 4]>) {
        if k == 4 {
            out.push(*p);
            return;
        }
        for i in k..4 {
            p.swap(k, i);
            permute(k + 1, p, out);
            p.swap(k, i);
        }
    }
    let mut perms = Vec::new();
    permute(0, &mut perm, &mut perms);
    for p in perms {
        let mut s = St {
            tok: [0; MAXW],
            len: 4,
            cur: 0,
            out: 0,
            next: 0,
        };
        for i in 0..4 {
            s.tok[i] = tc(p[i]);
        }
        starts.insert(pb.key(&s), 0);
    }
    // one round from the clean inputs, then the closure of end layouts
    let t0 = std::time::Instant::now();
    let (first, states) = pb.round(&starts);
    let d1 = first.values().min().copied().unwrap();
    println!(
        "window {w}: one round from the inputs in any order: least {d1} ({fixed} + {d1} = {}), {} end layouts, {states} states, {:.1} s",
        fixed + d1,
        first.len(),
        t0.elapsed().as_secs_f64()
    );
    // D_0 = 0 on every end layout, then value iteration; the first layer
    // also closes the set (an end layout not seen yet joins at D_0 = 0
    // and the layer runs again)
    let mut all: HashMap<u128, u32> = first.keys().map(|&k| (k, 0)).collect();
    let mut d = all.clone();
    let mut k = 1;
    while k <= layers {
        let (ends, states) = pb.round(&d);
        let new: Vec<u128> = ends
            .keys()
            .filter(|key| !all.contains_key(*key))
            .copied()
            .collect();
        if !new.is_empty() {
            assert_eq!(k, 1, "a closed set of end layouts stays closed");
            println!(
                "closure: {} new end layouts, {states} states, {:.1} s",
                new.len(),
                t0.elapsed().as_secs_f64()
            );
            for key in new {
                all.insert(key, 0);
            }
            d = all.clone();
            continue;
        }
        let mut lo = u32::MAX;
        let mut hi = 0;
        let mut least = u32::MAX;
        let mut arg = 0;
        for (key, &prev) in &d {
            let Some(&now) = ends.get(key) else {
                continue;
            };
            let diff = now - prev;
            lo = lo.min(diff);
            hi = hi.max(diff);
            if now < least {
                least = now;
                arg = *key;
            }
        }
        println!(
            "D_{k}: least {least}, D_k - D_(k-1) in [{lo}, {hi}], {} layouts reached, {states} states, {:.1} s; least ends in {}",
            ends.len(),
            t0.elapsed().as_secs_f64(),
            pb.show(&Pb::unpack(arg))
        );
        d = all
            .keys()
            .filter_map(|key| ends.get(key).map(|&c| (*key, c)))
            .collect();
        k += 1;
    }
}
