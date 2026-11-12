// A lower bound on the stack moves of the consuming internal rounds with
// the deferred sum (defer_sum in schedule.rs) against the plain ones, in
// the relaxed machine of cycle.rs: PRIME copies and constants left out,
// the S-box and every MULMOD by a constant one unary move, a SWAP that
// moves a PRIME copy a move of one value to or from the top (3 gas), a
// copy 3, a POP 2. No overlap of rounds: a round ends when its last output
// is made, its outputs become the next round's inputs.
//
//   defercycle <mode> <lanes> [window=10] [layers=4]
//
// mode `defer`: inputs s0, a_1..a_n, T. x = S(s0), k = (t - 1) T (unary),
// T' = a tree of merges over the leaves x, a_i, k; u_i = a_i + T, a_i' =
// d_i u_i (unary); m0 = d_0 x (unary), s0' = m0 + T'. Outputs s0', a_i',
// T'.
// mode `plain`: inputs s0, s_1..s_n. x = S(s0), T = a tree over x, s_i;
// m_i = d_i s_i (unary), s_i' = m_i + T, m0 = d_0 x, s0' = m0 + T.
//
// From every layout a round ends in, value iteration gives the least cycle
// mean between the least and the largest D_k - D_(k-1). The copies alone
// (uses - values) cost plain 3 (2n + 1), defer 3 (2n + 2).

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

#[derive(Default)]
struct Fx(u64);
impl Hasher for Fx {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for c in bytes.chunks(8) {
            let mut b = [0u8; 8];
            b[..c.len()].copy_from_slice(c);
            self.0 =
                (self.0.rotate_left(5) ^ u64::from_le_bytes(b)).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
    }
    fn write_u128(&mut self, v: u128) {
        let x = (v as u64) ^ ((v >> 64) as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}
type FxMap<K, V> = HashMap<K, V, BuildHasherDefault<Fx>>;

const MAXW: usize = 13;
const G: u8 = 0;
const S0: u8 = 1;
const X: u8 = 2;
const T: u8 = 3; // the old sum (defer)
const K: u8 = 4; // (t - 1) T (defer)
const A: u8 = 5; // + lane: a_i (defer) or s_i (plain)
const U: u8 = 9; // + lane: u_i (defer) or m_i (plain)
const AP: u8 = 13; // + lane: outputs
const M0: u8 = 17;
const S0P: u8 = 18;
const TP: u8 = 19; // the new sum
const PART: u8 = 20; // + mask of leaves: bit 0 x, bit i a_i, bit n + 1 k
const NV: usize = 20 + 64;
const OUT: u8 = 255;

#[derive(Clone, Copy, PartialEq, Eq, Default)]
struct Fl {
    xm: bool,
    km: bool,
    um: u8,
    am: u8,
    m0: bool,
    s0: bool,
    tm: bool,
}

#[derive(Clone, Copy)]
struct St {
    tok: [u8; MAXW],
    len: usize,
    f: Fl,
}

struct Pb {
    defer: bool,
    n: usize,
    w: usize,
    perms: Vec<Vec<usize>>,
    exch: bool,
    strict: bool,
}

impl Pb {
    fn lanes(&self) -> u8 {
        (1u8 << self.n) - 1
    }
    fn leaves(&self) -> u8 {
        let l = if self.defer { self.n + 2 } else { self.n + 1 };
        ((1u16 << l) - 1) as u8
    }
    fn leaf_of(&self, v: u8) -> Option<u8> {
        match v {
            X => Some(1),
            K if self.defer => Some(1 << (self.n + 1)),
            _ if (A..U).contains(&v) => Some(1 << (v - A + 1)),
            _ => None,
        }
    }

    fn covered(&self, s: &St) -> u8 {
        if s.f.tm {
            return self.leaves();
        }
        let mut c = 0;
        for &v in &s.tok[..s.len] {
            if v >= PART {
                c |= v - PART;
            }
        }
        c
    }

    fn uses(&self, s: &St) -> [u8; NV] {
        let mut u = [0u8; NV];
        let f = &s.f;
        let cov = self.covered(s);
        let c = |bit: u8| (cov & bit == 0) as u8;
        u[S0 as usize] = (!f.xm) as u8;
        if f.xm {
            u[X as usize] = c(1) + (!f.m0) as u8;
        }
        for i in 0..self.n {
            let b = 1u8 << i;
            u[(A + i as u8) as usize] = c(b << 1) + (f.um & b == 0) as u8;
            if f.um & b != 0 {
                u[(U + i as u8) as usize] = (f.am & b == 0) as u8;
            }
            if f.am & b != 0 {
                u[(AP + i as u8) as usize] = OUT;
            }
        }
        if self.defer {
            u[T as usize] = (!f.km) as u8 + (self.lanes() & !f.um).count_ones() as u8;
            if f.km {
                u[K as usize] = c(1 << (self.n + 1));
            }
            if f.tm {
                u[TP as usize] = OUT;
            }
        } else if f.tm {
            u[TP as usize] = (self.lanes() & !f.am).count_ones() as u8 + (!f.s0) as u8;
        }
        if f.m0 {
            u[M0 as usize] = (!f.s0) as u8;
        }
        if f.s0 {
            u[S0P as usize] = OUT;
        }
        for m in 1..64u8 {
            u[(PART + m) as usize] = 1;
        }
        u
    }

    /// dead values to G, nothing below the deepest live one; None when a
    /// needed value has no entry or the window overflows
    fn canon(&self, s: &mut St) -> Option<()> {
        let u = self.uses(s);
        let mut cnt = [0u8; NV];
        for i in 0..s.len {
            if u[s.tok[i] as usize] == 0 {
                s.tok[i] = G;
            }
            cnt[s.tok[i] as usize] += 1;
        }
        for v in 1..NV {
            if u[v] > 0 && v < PART as usize && cnt[v] == 0 {
                return None;
            }
        }
        while s.len > 0 && s.tok[s.len - 1] == G {
            s.len -= 1;
            s.tok[s.len] = 0;
        }
        (s.len <= self.w).then_some(())
    }

    fn end(&self, f: &Fl) -> bool {
        f.am == self.lanes() && f.s0 && (f.tm || !self.defer)
    }

    fn shift(&self, s: &mut St) {
        for i in 0..s.len {
            let v = s.tok[i];
            s.tok[i] = match v {
                _ if (AP..M0).contains(&v) => A + (v - AP),
                S0P => S0,
                TP if self.defer => T,
                _ => G,
            };
        }
        s.f = Fl::default();
    }

    fn pack(tok: &[u8], len: usize, f: &Fl) -> u128 {
        let mut k: u128 = 0;
        for (i, &v) in tok[..len].iter().enumerate() {
            k |= ((v + 1) as u128) << (7 * i);
        }
        let fl = f.xm as u128
            | (f.km as u128) << 1
            | (f.um as u128) << 2
            | (f.am as u128) << 6
            | (f.m0 as u128) << 10
            | (f.s0 as u128) << 11
            | (f.tm as u128) << 12;
        k | fl << 100
    }

    fn key(&self, s: &St) -> u128 {
        let mut best = u128::MAX;
        let n = self.n;
        for p in &self.perms {
            let mut tok = [0u8; MAXW];
            for i in 0..s.len {
                let v = s.tok[i];
                tok[i] = match v {
                    _ if (A..U).contains(&v) => A + p[(v - A) as usize] as u8,
                    _ if (U..AP).contains(&v) => U + p[(v - U) as usize] as u8,
                    _ if (AP..M0).contains(&v) => AP + p[(v - AP) as usize] as u8,
                    _ if v >= PART => {
                        let m = v - PART;
                        let mut r = m & 1;
                        for l in 0..n {
                            if m >> (l + 1) & 1 == 1 {
                                r |= 1 << (p[l] + 1);
                            }
                        }
                        r |= m & (1 << (n + 1));
                        PART + r
                    }
                    _ => v,
                };
            }
            let mut f = s.f;
            let mp = |m: u8| -> u8 {
                let mut r = 0;
                for l in 0..n {
                    if m >> l & 1 == 1 {
                        r |= 1 << p[l];
                    }
                }
                r
            };
            f.um = mp(s.f.um);
            f.am = mp(s.f.am);
            best = best.min(Self::pack(&tok, s.len, &f));
        }
        best
    }

    fn unpack(&self, k: u128) -> St {
        let mut s = St {
            tok: [0; MAXW],
            len: 0,
            f: Fl::default(),
        };
        for i in 0..MAXW {
            let v = (k >> (7 * i) & 127) as u8;
            if v == 0 {
                break;
            }
            s.tok[i] = v - 1;
            s.len += 1;
        }
        let fl = k >> 100;
        s.f = Fl {
            xm: fl & 1 == 1,
            km: fl >> 1 & 1 == 1,
            um: (fl >> 2 & 15) as u8,
            am: (fl >> 6 & 15) as u8,
            m0: fl >> 10 & 1 == 1,
            s0: fl >> 11 & 1 == 1,
            tm: fl >> 12 & 1 == 1,
        };
        s
    }

    /// (a, b or NONE for unary, result, flags after)
    fn ops(&self, s: &St, out: &mut Vec<(u8, u8, u8, Fl)>) {
        const NONE: u8 = 254;
        let f = s.f;
        if !f.xm {
            out.push((S0, NONE, X, Fl { xm: true, ..f }));
        }
        if f.xm && !f.m0 {
            out.push((X, NONE, M0, Fl { m0: true, ..f }));
        }
        let tsum = if self.defer { TP } else { TP };
        if f.tm && f.m0 && !f.s0 {
            out.push((M0, tsum, S0P, Fl { s0: true, ..f }));
        }
        for i in 0..self.n {
            let b = 1u8 << i;
            let (a, uu, ap) = (A + i as u8, U + i as u8, AP + i as u8);
            if self.defer {
                if f.um & b == 0 {
                    out.push((a, T, uu, Fl { um: f.um | b, ..f }));
                } else if f.am & b == 0 {
                    out.push((uu, NONE, ap, Fl { am: f.am | b, ..f }));
                }
            } else if f.um & b == 0 {
                out.push((a, NONE, uu, Fl { um: f.um | b, ..f }));
            } else if f.am & b == 0 && f.tm {
                out.push((uu, TP, ap, Fl { am: f.am | b, ..f }));
            }
        }
        if self.defer && !f.km {
            out.push((T, NONE, K, Fl { km: true, ..f }));
        }
        if f.tm {
            return;
        }
        // tree merges of the operands on the stack: uncovered leaves and
        // partial sums
        let cov = self.covered(s);
        let mut opnds: Vec<(u8, u8)> = vec![];
        let mut seen = 0u128;
        for &v in &s.tok[..s.len] {
            let m = if v >= PART {
                Some(v - PART)
            } else {
                self.leaf_of(v).filter(|&b| cov & b == 0)
            };
            if let Some(m) = m {
                if seen >> v & 1 == 0 {
                    seen |= 1 << v;
                    opnds.push((v, m));
                }
            }
        }
        for i in 0..opnds.len() {
            for j in i + 1..opnds.len() {
                let (a, ma) = opnds[i];
                let (b, mb) = opnds[j];
                if ma & mb != 0 {
                    continue;
                }
                let m = ma | mb;
                if m == self.leaves() {
                    out.push((a, b, TP, Fl { tm: true, ..f }));
                } else {
                    out.push((a, b, PART + m, f));
                }
            }
        }
    }

    fn moves(&self, s: &St, out: &mut Vec<(u32, St, bool)>, ops: &mut Vec<(u8, u8, u8, Fl)>) {
        const NONE: u8 = 254;
        let u = self.uses(s);
        let mut cnt = [0u8; NV];
        for i in 0..s.len {
            cnt[s.tok[i] as usize] += 1;
        }
        let emit = |mut ns: St, cost: u32, out: &mut Vec<(u32, St, bool)>| {
            if ns.len > self.w {
                return;
            }
            let end = self.end(&ns.f);
            if end {
                self.shift(&mut ns);
            }
            if self.canon(&mut ns).is_some() {
                out.push((cost, ns, end));
            }
        };
        let push = |s: &St, v: u8| -> St {
            let mut ns = *s;
            if s.len == MAXW {
                ns.len = MAXW + 1;
                return ns;
            }
            ns.tok.copy_within(0..s.len, 1);
            ns.tok[0] = v;
            ns.len += 1;
            ns
        };
        let drop = |s: &St, k: usize| -> St {
            let mut ns = *s;
            ns.tok.copy_within(k..s.len, 0);
            ns.len -= k;
            for i in ns.len..MAXW {
                ns.tok[i] = 0;
            }
            ns
        };
        ops.clear();
        self.ops(s, ops);
        let top0 = if s.len > 0 { s.tok[0] } else { G };
        let top1 = if s.len > 1 { s.tok[1] } else { G };
        for &(a, b, r, fl) in ops.iter() {
            let set = |mut ns: St| -> St {
                ns.f = fl;
                ns
            };
            if b == NONE {
                if s.len > 0 && top0 == a {
                    emit(set(push(&drop(s, 1), r)), 0, out);
                }
                if cnt[a as usize] > 0 {
                    emit(set(push(s, r)), 3, out);
                }
                continue;
            }
            if s.len > 1 && ((top0 == a && top1 == b) || (top0 == b && top1 == a)) {
                emit(set(push(&drop(s, 2), r)), 0, out);
            }
            if s.len > 0 && top0 == a && cnt[b as usize] > 0 {
                emit(set(push(&drop(s, 1), r)), 3, out);
            }
            if s.len > 0 && top0 == b && cnt[a as usize] > 0 {
                emit(set(push(&drop(s, 1), r)), 3, out);
            }
            if cnt[a as usize] > 0 && cnt[b as usize] > 0 {
                emit(set(push(s, r)), 6, out);
            }
        }
        // a copy kept for later
        for v in 1..NV {
            if cnt[v] > 0 && u[v] != OUT && cnt[v] < u[v] && s.len < self.w {
                emit(push(s, v as u8), 3, out);
            }
        }
        if s.len == 0 {
            return;
        }
        let top = s.tok[0];
        if top == G || (u[top as usize] != OUT && cnt[top as usize] > u[top as usize]) {
            emit(drop(s, 1), 2, out);
        }
        for k in 1..s.len {
            let y = s.tok[k];
            if y != top && !(y == G && top == G) {
                let mut ns = *s;
                ns.tok.swap(0, k);
                emit(ns, 3, out);
            }
            if k >= 2 && top != G && !self.strict {
                let mut ns = *s;
                ns.tok.copy_within(1..=k, 0);
                ns.tok[k] = top;
                if ns.tok != s.tok {
                    emit(ns, 3, out);
                }
            }
            if k >= 2 && y != G && !self.strict {
                let mut ns = *s;
                ns.tok.copy_within(0..k, 1);
                ns.tok[0] = y;
                if ns.tok != s.tok {
                    emit(ns, 3, out);
                }
            }
        }
        if self.exch {
            for j in 1..s.len {
                for k in j + 1..s.len {
                    let (a, b) = (s.tok[j], s.tok[k]);
                    if a != b {
                        let mut ns = *s;
                        ns.tok.swap(j, k);
                        emit(ns, 3, out);
                    }
                }
            }
        }
    }

    fn layer(&self, src: &FxMap<u128, u32>) -> (FxMap<u128, u32>, usize) {
        self.layer_traced(src, None)
    }

    /// with trace, the predecessor of every state and of every end layout
    fn layer_traced(
        &self,
        src: &FxMap<u128, u32>,
        mut trace: Option<&mut (FxMap<u128, (u128, u32)>, FxMap<u128, (u128, u32)>)>,
    ) -> (FxMap<u128, u32>, usize) {
        let mut dist: FxMap<u128, u32> = FxMap::default();
        let base = src.values().copied().min().unwrap_or(0);
        let mut buckets: Vec<Vec<u128>> = vec![];
        for (&k, &d) in src {
            dist.insert(k, d);
            let i = (d - base) as usize;
            if buckets.len() <= i {
                buckets.resize(i + 1, vec![]);
            }
            buckets[i].push(k);
        }
        let mut next: FxMap<u128, u32> = FxMap::default();
        let mut out = vec![];
        let mut ops = vec![];
        let mut i = 0;
        while i < buckets.len() {
            while let Some(k) = buckets[i].pop() {
                let d = base + i as u32;
                if dist[&k] < d {
                    continue;
                }
                let s = self.unpack(k);
                out.clear();
                self.moves(&s, &mut out, &mut ops);
                for &(c, ns, end) in &out {
                    let nd = d + c;
                    let nk = self.key(&ns);
                    if end {
                        let e = next.entry(nk).or_insert(u32::MAX);
                        if nd < *e {
                            *e = nd;
                            if let Some(tr) = trace.as_deref_mut() {
                                tr.1.insert(nk, (k, c));
                            }
                        }
                        continue;
                    }
                    if dist.get(&nk).is_some_and(|&x| x <= nd) {
                        continue;
                    }
                    dist.insert(nk, nd);
                    if let Some(tr) = trace.as_deref_mut() {
                        tr.0.insert(nk, (k, c));
                    }
                    let j = (nd - base) as usize;
                    if buckets.len() <= j {
                        buckets.resize(j + 1, vec![]);
                    }
                    buckets[j].push(nk);
                }
            }
            i += 1;
        }
        (next, dist.len())
    }

    fn show(&self, k: u128) -> String {
        let s = self.unpack(k);
        let names: Vec<String> = s.tok[..s.len].iter().map(|&v| self.name(v)).collect();
        format!("[{}]", names.join(","))
    }

    fn name(&self, v: u8) -> String {
        match v {
            G => "_".into(),
            S0 => "s0".into(),
            X => "x".into(),
            T => "T".into(),
            K => "kT".into(),
            _ if (A..U).contains(&v) => format!("a{}", v - A + 1),
            _ if (U..AP).contains(&v) => format!("u{}", v - U + 1),
            _ if (AP..M0).contains(&v) => format!("a{}'", v - AP + 1),
            M0 => "m0".into(),
            S0P => "s0'".into(),
            TP => "T'".into(),
            _ => format!("p{:b}", v - PART),
        }
    }
}

fn perms(k: usize, a: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    if k == a.len() {
        out.push(a.clone());
        return;
    }
    for i in k..a.len() {
        a.swap(k, i);
        perms(k + 1, a, out);
        a.swap(k, i);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let defer = args.get(1).map(String::as_str) == Some("defer");
    let n: usize = args.get(2).and_then(|a| a.parse().ok()).unwrap_or(3);
    let w: usize = args.get(3).and_then(|a| a.parse().ok()).unwrap_or(10);
    let layers: usize = args.get(4).and_then(|a| a.parse().ok()).unwrap_or(4);
    assert!(n <= 4 && w <= MAXW);
    let mut lp = vec![];
    perms(0, &mut (0..n).collect(), &mut lp);
    let pb = Pb {
        defer,
        n,
        w,
        perms: lp,
        exch: std::env::var_os("EXCHANGE").is_some(),
        strict: std::env::var_os("STRICT").is_some(),
    };
    let mut inputs: Vec<usize> = (0..n + 1 + defer as usize).collect();
    let mut ps = vec![];
    perms(0, &mut inputs, &mut ps);
    let mut src: FxMap<u128, u32> = FxMap::default();
    for p in ps {
        let mut s = St {
            tok: [0; MAXW],
            len: p.len(),
            f: Fl::default(),
        };
        for (i, &v) in p.iter().enumerate() {
            s.tok[i] = match v {
                0 => S0,
                _ if v <= n => A + (v - 1) as u8,
                _ => T,
            };
        }
        src.insert(pb.key(&s), 0);
    }
    let mut all: FxMap<u128, u32> = src.clone();
    loop {
        let (next, states) = pb.layer(&all);
        let before = all.len();
        for k in next.keys() {
            all.entry(*k).or_insert(0);
        }
        eprintln!(
            "closure: {} end layouts ({} new), {} states in the round",
            all.len(),
            all.len() - before,
            states
        );
        if all.len() == before {
            break;
        }
    }
    let (reach, _) = pb.layer(&all);
    let mut d: FxMap<u128, u32> = reach.keys().map(|&k| (k, 0)).collect();
    println!(
        "{} n = {n}, window {w}, exchange {}: {} end layouts",
        if defer { "defer" } else { "plain" },
        pb.exch as u8,
        d.len()
    );
    let tracing = std::env::var_os("TRACE").is_some();
    let mut traces = vec![];
    for k in 1..=layers {
        let mut tr = (FxMap::default(), FxMap::default());
        let (nd, states) = pb.layer_traced(&d, tracing.then_some(&mut tr));
        if tracing {
            traces.push(tr);
        }
        let mut lo = i64::MAX;
        let mut hi = i64::MIN;
        for (key, &v) in &nd {
            if let Some(&p) = d.get(key) {
                let diff = v as i64 - p as i64;
                lo = lo.min(diff);
                hi = hi.max(diff);
            }
        }
        let min = *nd.values().min().unwrap();
        println!(
            "k = {k}: min D_k {min} ({:.2} a round), D_k - D_(k-1) in [{lo}, {hi}], {} layouts, {states} states",
            min as f64 / k as f64,
            nd.len()
        );
        if k == layers {
            let mut best: Vec<(&u128, &u32)> = nd.iter().filter(|(_, &v)| v == min).collect();
            best.sort();
            for (key, _) in best.iter().take(3) {
                let s = pb.unpack(**key);
                let names: Vec<String> = s.tok[..s.len].iter().map(|&v| pb.name(v)).collect();
                println!("  ends in [{}]", names.join(","));
            }
            if tracing {
                // every round back from the cheapest end, latest first
                let mut end = *best[0].0;
                for (r, (parent, end_parent)) in traces.iter().enumerate().rev() {
                    println!("round {} (back to front):", r + 1);
                    let (mut at, mut c) = end_parent[&end];
                    let mut total = c;
                    loop {
                        println!("  +{c} after {}", pb.show(at));
                        match parent.get(&at) {
                            Some(&(p, pc)) => {
                                at = p;
                                c = pc;
                                total += pc;
                            }
                            None => break,
                        }
                    }
                    println!("  round cost {total}");
                    end = at;
                }
            }
        }
        d = nd;
    }
}
