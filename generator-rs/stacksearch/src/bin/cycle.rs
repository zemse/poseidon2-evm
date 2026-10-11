// A lower bound on the stack moves of the steady internal rounds, with no
// layout fixed between rounds: the minimum mean cost per round over every
// cycle of rounds (or any long sequence of them) in a relaxed stack machine.
//
// The relaxation keeps only the values of the linear layer: PRIME copies,
// the diag and round constants are left out (each costs the same in every
// program), the S-box of lane 0 is one unary move, and so is d_i * s_i
// (t = 4). A SWAP in the real program that moves a PRIME copy or a constant
// becomes a move of one value to the top or from the top to any depth, 3
// gas like a SWAP. What is counted: a copy of a value (DUP, 3), a SWAP or
// such a move (3), a POP (2). The arithmetic is fixed by the DAG: the sum of
// the lanes as merges of disjoint partial sums, s_i' = d_i * s_i + sum
// (t = 4), and for t = 3 s0' = x + sum, s1' = s1 + sum, s2' = (sum + s2) +
// s2 or (s2 + s2) + sum. The next round may start before this one ends (its
// S-box, products, doubling and partial sums of the outputs already made).
//
//   cycle <t> [max_window=12] [layers=4]
//
// A state is the stack of values (dead ones as one garbage class, nothing
// below the deepest live value) and what both rounds have done. A round
// ends when its last output is made. From every layout a round can end in
// (found from the four inputs in any order, layer by layer until no new one
// appears), D_0 = 0 and D_k(b) is the cheapest k rounds ending in b. Then
// for every k the minimum cycle mean lies between the least and the largest
// D_k(b) - D_(k-1)(b), and min_b D_k(b) / k is below it too. Per round the
// real program costs at least the fixed part plus that mean: t = 4 133 gas
// (154 floor B less the 21 of its seven copies), t = 3 82 (two ADDMODs).
//
// Relaxations outside that model, each by an environment variable (any
// value), all keep the bound valid for the programs the base model covers:
//   SPLIT  the S-box is two moves: s0 consumed on top (its ADD of the round
//          constant), x pushed on top later (its last MULMOD), free; its
//          intermediates are left out like the PRIME copies, so linear-layer
//          moves may run between its MULMODs. Too loose: an intermediate
//          left under other values costs a copy or a SWAP it does not see
//   SBOX   the S-box as v = s0 + c (unary), v^2 = v v, v^4 = v^2 v^2, x =
//          v^4 v, with v, v^2, v^4 values on the stack whose copies count
//          (the fixed part less its 9 gas of S-box copies: t = 4 124, t = 3
//          73), any linear-layer move allowed between them
//   SHL    t = 3: 2 s2 also as PUSH1 1 SHL, a unary move of 3 (6 against the
//          ADD the fixed part counts)
//   COMP   t = 4: s_i' also as mu_i * s_i + (the sum of the other lanes),
//          when that partial sum is a block of the sum tree

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

const MAXW: usize = 16;

// values: the current round, then the next one (its inputs are the outputs)
const G: u8 = 0; // dead
const I0: u8 = 1; // lane 0 before its S-box
const LEAF: u8 = 2; // + lane: x (lane 0) or s_i
const BLK: u8 = 6; // + index of a mask of two lanes or more
const M: u8 = 17; // + lane: d_i * s_i
const DV: u8 = 21; // 2 s2 (t = 3)
const TV: u8 = 22; // sum + s2 (t = 3)
const O: u8 = 23; // + lane: outputs
const XN: u8 = 27; // next round's x
const BLKN: u8 = 28;
const MN: u8 = 39;
const DN: u8 = 43;
// SBOX: v = s0 + c, v^2, v^4 of this round and of the next one
const SV: u8 = 44;
const SV2: u8 = 45;
const SV4: u8 = 46;
const SVN: u8 = 47;
const SV2N: u8 = 48;
const SV4N: u8 = 49;
const NV: usize = 50;

const MASKS: [u8; 11] = [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15];
fn bidx(m: u8) -> u8 {
    MASKS.iter().position(|&x| x == m).unwrap() as u8
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Mul,
    Ident,
    Dbl,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, Debug)]
struct Prog {
    sbox: bool,
    // S-box in progress: 1 v = s0 + c made (SPLIT: s0 consumed, x not
    // made yet), 2 v^2, 3 v^4 (SBOX)
    stg: u8,
    blk: [u8; 4], // mask of the block of every lane
    m: u8,        // products (or nothing)
    d: bool,      // 2 s2
    t: bool,      // sum + s2
    o: u8,        // outputs
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct St {
    tok: [u8; MAXW], // top first
    len: usize,
    c: Prog,
    n: Prog,
}

struct Pb {
    t: usize,
    kinds: Vec<Kind>,
    w: usize,
    parts: Vec<[u8; 4]>,
    pidx: HashMap<[u8; 4], u8>,
    // the renamings of the interchangeable lanes: values, lane masks
    syms: Vec<([u8; NV], [u8; 16])>,
    split: bool,
    sb: bool,
    shl: bool,
    comp: bool,
}

const NONE: u8 = 254; // an op with no result, or a result with no operand
const SHLM: u8 = 253; // second operand of a unary op that costs 3 (SHL)

fn partitions(t: usize) -> Vec<[u8; 4]> {
    // every set partition of 0..t as the block mask of each lane
    let mut out = vec![];
    fn rec(i: usize, t: usize, blocks: &mut Vec<u8>, out: &mut Vec<[u8; 4]>) {
        if i == t {
            let mut b = [0u8; 4];
            for &m in blocks.iter() {
                for l in 0..t {
                    if m >> l & 1 == 1 {
                        b[l] = m;
                    }
                }
            }
            out.push(b);
            return;
        }
        for k in 0..blocks.len() {
            blocks[k] |= 1 << i;
            rec(i + 1, t, blocks, out);
            blocks[k] &= !(1 << i);
        }
        blocks.push(1 << i);
        rec(i + 1, t, blocks, out);
        blocks.pop();
    }
    rec(0, t, &mut vec![], &mut out);
    out
}

fn fresh(t: usize) -> Prog {
    let mut p = Prog::default();
    for l in 0..t {
        p.blk[l] = 1 << l;
    }
    p
}

impl Pb {
    fn full(&self) -> u8 {
        (1u8 << self.t) - 1
    }

    fn pack(&self, s: &St) -> u128 {
        let mut k: u128 = 0;
        for i in 0..s.len {
            k |= ((s.tok[i] + 1) as u128) << (6 * i);
        }
        let pc = |p: &Prog, full: bool| -> u128 {
            let mut v = p.sbox as u128;
            v |= (self.pidx[&p.blk] as u128) << 1;
            v |= (p.m as u128) << 5;
            v |= (p.d as u128) << 9;
            if full {
                v |= (p.t as u128) << 10;
                v |= (p.o as u128) << 11;
            }
            v
        };
        k | pc(&s.c, true) << 96
            | pc(&s.n, false) << 111
            | (s.c.stg as u128) << 121
            | (s.n.stg as u128) << 123
    }

    /// the least key over the renamings of the interchangeable lanes
    fn key(&self, s: &St) -> u128 {
        let mut best = self.pack(s);
        for (tv, tm) in &self.syms[1..] {
            let mut r = *s;
            for i in 0..s.len {
                r.tok[i] = tv[s.tok[i] as usize];
            }
            for (p, q) in [(&s.c, &mut r.c), (&s.n, &mut r.n)] {
                for l in 0..self.t {
                    let nl = tm[1 << l].trailing_zeros() as usize;
                    q.blk[nl] = tm[p.blk[l] as usize];
                }
                q.m = tm[p.m as usize];
                q.o = tm[p.o as usize];
            }
            best = best.min(self.pack(&r));
        }
        best
    }

    fn unpack(&self, k: u128) -> St {
        let mut s = St {
            tok: [0; MAXW],
            len: 0,
            c: Prog::default(),
            n: Prog::default(),
        };
        for i in 0..MAXW {
            let v = (k >> (6 * i) & 63) as u8;
            if v == 0 {
                break;
            }
            s.tok[i] = v - 1;
            s.len += 1;
        }
        let up = |v: u128| -> Prog {
            Prog {
                sbox: v & 1 == 1,
                stg: 0,
                blk: self.parts[(v >> 1 & 15) as usize],
                m: (v >> 5 & 15) as u8,
                d: v >> 9 & 1 == 1,
                t: v >> 10 & 1 == 1,
                o: (v >> 11 & 15) as u8,
            }
        };
        s.c = up(k >> 96 & 0x7fff);
        s.n = up(k >> 111 & 0x3ff);
        s.c.stg = (k >> 121 & 3) as u8;
        s.n.stg = (k >> 123 & 3) as u8;
        s
    }

    fn blk_val(&self, mask: u8, next: bool) -> u8 {
        if mask.count_ones() == 1 {
            let l = mask.trailing_zeros() as u8;
            match (next, l) {
                (false, _) => LEAF + l,
                (true, 0) => XN,
                (true, _) => O + l,
            }
        } else if next {
            BLKN + bidx(mask)
        } else {
            BLK + bidx(mask)
        }
    }

    /// the most uses a value can still have (a copy kept for later only
    /// below it, dead at 0) and the fewest (a POP only above it, no entry
    /// left only at 0); they differ only with SHL and COMP
    fn uses(&self, c: &Prog, n: &Prog) -> ([u8; NV], [u8; NV]) {
        let mut u = self.uses_max(c, n);
        let mut lo = u;
        let full = self.full();
        for i in 0..self.t {
            let bit = 1u8 << i;
            if self.shl && self.kinds[i] == Kind::Dbl {
                let li = (LEAF + i as u8) as usize;
                if c.o & bit == 0 && !c.d && !c.t && lo[li] > 0 {
                    lo[li] -= 1;
                }
                let oi = (O + i as u8) as usize;
                if c.o & bit != 0 && !n.d && lo[oi] > 0 {
                    lo[oi] -= 1;
                }
            }
            if self.comp && self.kinds[i] == Kind::Mul && c.o & bit == 0 {
                // the sum of the other lanes: one more use, and one fewer
                // of the full sum
                let cb = full ^ bit;
                u[(BLK + bidx(cb)) as usize] += 1;
            }
            if self.comp && self.kinds[i] == Kind::Mul {
                let nb = n.blk[(i + 1) % self.t];
                if nb == full ^ bit {
                    u[(BLKN + bidx(nb)) as usize] += 1;
                }
            }
        }
        if self.comp {
            let s = (BLK + bidx(full)) as usize;
            lo[s] = lo[s].saturating_sub(1);
        }
        (u, lo)
    }

    fn uses_max(&self, c: &Prog, n: &Prog) -> [u8; NV] {
        let mut u = [0u8; NV];
        let full = self.full();
        u[I0 as usize] = (!c.sbox && c.stg == 0) as u8;
        if self.sb {
            for (p, v, v2, v4) in [(c, SV, SV2, SV4), (n, SVN, SV2N, SV4N)] {
                let (a, b, d) = match p.stg {
                    1 => (3, 0, 0),
                    2 => (1, 2, 0),
                    3 => (1, 0, 1),
                    _ => (0, 0, 0),
                };
                u[v as usize] = a;
                u[v2 as usize] = b;
                u[v4 as usize] = d;
            }
        }
        for i in 0..self.t {
            let bit = 1u8 << i;
            if i > 0 || c.sbox {
                let s = (c.blk[i] == bit) as u8;
                let lane = match self.kinds[i] {
                    Kind::Mul => (c.m & bit == 0) as u8,
                    Kind::Ident => (c.o & bit == 0) as u8,
                    Kind::Dbl => {
                        if c.o & bit != 0 || c.d {
                            0
                        } else if c.t {
                            1
                        } else {
                            2
                        }
                    }
                };
                u[(LEAF + i as u8) as usize] = s + lane;
            }
            let b = c.blk[i];
            if b.count_ones() > 1 && b.trailing_zeros() as usize == i {
                if b == full {
                    let mut k = 0;
                    for j in 0..self.t {
                        let missing = c.o >> j & 1 == 0;
                        k += match self.kinds[j] {
                            Kind::Dbl => (missing && !c.t) as u8,
                            _ => missing as u8,
                        };
                    }
                    u[(BLK + bidx(b)) as usize] = k;
                } else {
                    u[(BLK + bidx(b)) as usize] = 1;
                }
            }
            if c.m & bit != 0 && c.o & bit == 0 {
                u[(M + i as u8) as usize] = 1;
            }
            if self.kinds[i] == Kind::Dbl && c.o & bit == 0 {
                u[DV as usize] = c.d as u8;
                u[TV as usize] = c.t as u8;
            }
            if c.o & bit != 0 {
                u[(O + i as u8) as usize] = if i == 0 {
                    (!n.sbox && n.stg == 0) as u8
                } else {
                    let s = (n.blk[i] == bit) as u8;
                    s + match self.kinds[i] {
                        Kind::Mul => (n.m & bit == 0) as u8,
                        Kind::Ident => 1,
                        Kind::Dbl => {
                            if n.d {
                                0
                            } else {
                                2
                            }
                        }
                    }
                };
            }
            let nb = n.blk[i];
            if nb.count_ones() > 1 && nb.trailing_zeros() as usize == i {
                u[(BLKN + bidx(nb)) as usize] = 1;
            }
            if n.m & bit != 0 {
                u[(MN + i as u8) as usize] = 1;
            }
        }
        if n.sbox {
            u[XN as usize] = (n.blk[0] == 1) as u8
                + match self.kinds[0] {
                    Kind::Mul => (n.m & 1 == 0) as u8,
                    _ => 1,
                };
        }
        if n.d {
            u[DN as usize] = 1;
        }
        u
    }

    /// dead values to G, nothing below the deepest live value; None when a
    /// live value has no entry left or the window overflows
    fn canon(&self, s: &mut St) -> Option<()> {
        let (u, lo) = self.uses(&s.c, &s.n);
        let mut cnt = [0u8; NV];
        for i in 0..s.len {
            if u[s.tok[i] as usize] == 0 {
                s.tok[i] = G;
            } else {
                cnt[s.tok[i] as usize] += 1;
            }
        }
        while s.len > 0 && s.tok[s.len - 1] == G {
            s.len -= 1;
        }
        for v in 0..NV {
            if lo[v] > 0 && cnt[v] == 0 {
                return None;
            }
        }
        (s.len <= self.w).then_some(())
    }

    /// the round is over: the next one becomes the current one
    fn shift(&self, s: &mut St) {
        for i in 0..s.len {
            let v = s.tok[i];
            s.tok[i] = match v {
                _ if v == O => {
                    if s.n.sbox || s.n.stg > 0 {
                        G
                    } else {
                        I0
                    }
                }
                _ if (O + 1..O + 4).contains(&v) => LEAF + (v - O),
                XN => LEAF,
                _ if (BLKN..MN).contains(&v) => BLK + (v - BLKN),
                _ if (MN..DN).contains(&v) => M + (v - MN),
                DN => DV,
                SVN => SV,
                SV2N => SV2,
                SV4N => SV4,
                _ => G,
            };
        }
        s.c = Prog {
            t: false,
            o: 0,
            ..s.n
        };
        s.n = fresh(self.t);
    }

    /// arithmetic moves: (operands, result, progress after)
    fn ops(&self, s: &St, out: &mut Vec<(u8, u8, u8, Prog, Prog)>) {
        const NO: u8 = 255;
        let (c, n) = (s.c, s.n);
        let full = self.full();
        let t = self.t;
        if self.sb {
            let st = |stg: u8| Prog { stg, ..c };
            match c.stg {
                _ if c.sbox => {}
                0 => out.push((I0, NO, SV, st(1), n)),
                1 => out.push((SV, SV, SV2, st(2), n)),
                2 => out.push((SV2, SV2, SV4, st(3), n)),
                _ => out.push((
                    SV4,
                    SV,
                    LEAF,
                    Prog {
                        sbox: true,
                        ..st(0)
                    },
                    n,
                )),
            }
        } else if self.split {
            if !c.sbox && c.stg == 0 {
                out.push((I0, NO, NONE, Prog { stg: 1, ..c }, n));
            }
            if c.stg == 1 {
                out.push((
                    NONE,
                    NO,
                    LEAF,
                    Prog {
                        sbox: true,
                        stg: 0,
                        ..c
                    },
                    n,
                ));
            }
        } else if !c.sbox {
            out.push((I0, NO, LEAF, Prog { sbox: true, ..c }, n));
        }
        // merges of two blocks of a round
        for (next, p) in [(false, c), (true, n)] {
            let avail = |b: u8| -> bool {
                if b.count_ones() > 1 {
                    return true;
                }
                let l = b.trailing_zeros() as usize;
                if next {
                    if l == 0 {
                        p.sbox
                    } else {
                        c.o >> l & 1 == 1
                    }
                } else {
                    l > 0 || p.sbox
                }
            };
            let mut blocks: Vec<u8> = vec![];
            for l in 0..t {
                if !blocks.contains(&p.blk[l]) {
                    blocks.push(p.blk[l]);
                }
            }
            for a in 0..blocks.len() {
                for b in a + 1..blocks.len() {
                    let (x, y) = (blocks[a], blocks[b]);
                    if !avail(x) || !avail(y) {
                        continue;
                    }
                    let mut np = p;
                    for l in 0..t {
                        if (x | y) >> l & 1 == 1 {
                            np.blk[l] = x | y;
                        }
                    }
                    let r = self.blk_val(x | y, next);
                    let (vx, vy) = (self.blk_val(x, next), self.blk_val(y, next));
                    if next {
                        out.push((vx, vy, r, c, np));
                    } else {
                        out.push((vx, vy, r, np, n));
                    }
                }
            }
        }
        let sfull = c.blk[0] == full;
        let sval = BLK + if t > 1 { bidx(full) } else { 0 };
        for i in 0..t {
            let bit = 1u8 << i;
            let li = LEAF + i as u8;
            let leaf_ok = i > 0 || c.sbox;
            match self.kinds[i] {
                Kind::Mul => {
                    if c.m & bit == 0 && leaf_ok {
                        out.push((li, NO, M + i as u8, Prog { m: c.m | bit, ..c }, n));
                    }
                    if c.m & bit != 0 && c.o & bit == 0 && sfull {
                        out.push((
                            M + i as u8,
                            sval,
                            O + i as u8,
                            Prog { o: c.o | bit, ..c },
                            n,
                        ));
                    }
                    if self.comp && c.m & bit != 0 && c.o & bit == 0 {
                        out.push((
                            M + i as u8,
                            BLK + bidx(full ^ bit),
                            O + i as u8,
                            Prog { o: c.o | bit, ..c },
                            n,
                        ));
                    }
                }
                Kind::Ident => {
                    if c.o & bit == 0 && sfull && leaf_ok {
                        out.push((li, sval, O + i as u8, Prog { o: c.o | bit, ..c }, n));
                    }
                }
                Kind::Dbl => {
                    if c.o & bit == 0 {
                        if !c.d && !c.t {
                            out.push((li, li, DV, Prog { d: true, ..c }, n));
                            if self.shl {
                                out.push((li, SHLM, DV, Prog { d: true, ..c }, n));
                            }
                            if sfull {
                                out.push((sval, li, TV, Prog { t: true, ..c }, n));
                            }
                        }
                        if c.d && sfull {
                            out.push((DV, sval, O + i as u8, Prog { o: c.o | bit, ..c }, n));
                        }
                        if c.t {
                            out.push((TV, li, O + i as u8, Prog { o: c.o | bit, ..c }, n));
                        }
                    }
                }
            }
            // the next round on the outputs made so far
            if c.o & bit != 0 {
                if i == 0 && self.sb {
                    let st = |stg: u8| Prog { stg, ..n };
                    match n.stg {
                        _ if n.sbox => {}
                        0 => out.push((O, NO, SVN, c, st(1))),
                        1 => out.push((SVN, SVN, SV2N, c, st(2))),
                        2 => out.push((SV2N, SV2N, SV4N, c, st(3))),
                        _ => out.push((
                            SV4N,
                            SVN,
                            XN,
                            c,
                            Prog {
                                sbox: true,
                                ..st(0)
                            },
                        )),
                    }
                } else if i == 0 && self.split {
                    if !n.sbox && n.stg == 0 {
                        out.push((O, NO, NONE, c, Prog { stg: 1, ..n }));
                    }
                    if n.stg == 1 {
                        let nn = Prog {
                            sbox: true,
                            stg: 0,
                            ..n
                        };
                        out.push((NONE, NO, XN, c, nn));
                    }
                } else if i == 0 && !n.sbox {
                    out.push((O, NO, XN, c, Prog { sbox: true, ..n }));
                }
                let nleaf = if i == 0 { XN } else { O + i as u8 };
                let nok = i > 0 || n.sbox;
                match self.kinds[i] {
                    Kind::Mul if n.m & bit == 0 && nok => {
                        out.push((nleaf, NO, MN + i as u8, c, Prog { m: n.m | bit, ..n }));
                    }
                    Kind::Dbl if !n.d => {
                        out.push((nleaf, nleaf, DN, c, Prog { d: true, ..n }));
                        if self.shl {
                            out.push((nleaf, SHLM, DN, c, Prog { d: true, ..n }));
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// every move from s: (cost, next state, the round ended)
    fn moves(
        &self,
        s: &St,
        out: &mut Vec<(u32, St, bool)>,
        ops: &mut Vec<(u8, u8, u8, Prog, Prog)>,
    ) {
        const NO: u8 = 255;
        let (u, lo) = self.uses(&s.c, &s.n);
        let mut cnt = [0u8; NV];
        for i in 0..s.len {
            cnt[s.tok[i] as usize] += 1;
        }
        let all = (1u8 << self.t) - 1;
        let emit = |mut ns: St, cost: u32, out: &mut Vec<(u32, St, bool)>| {
            let end = ns.c.o == all;
            if end {
                self.shift(&mut ns);
            }
            if self.canon(&mut ns).is_some() {
                out.push((cost, ns, end));
            }
        };
        let push = |s: &St, v: u8| -> St {
            let mut ns = *s;
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
        for &(a, b, r, c, n) in ops.iter() {
            let set = |mut ns: St| -> St {
                ns.c = c;
                ns.n = n;
                ns
            };
            let top0 = if s.len > 0 { s.tok[0] } else { G };
            let top1 = if s.len > 1 { s.tok[1] } else { G };
            if a == NONE {
                emit(set(push(s, r)), 0, out);
                continue;
            }
            if r == NONE {
                if top0 == a && s.len > 0 {
                    emit(set(drop(s, 1)), 0, out);
                }
                continue;
            }
            if b == NO || b == SHLM {
                let x = if b == SHLM { 3 } else { 0 };
                if top0 == a && s.len > 0 {
                    emit(set(push(&drop(s, 1), r)), x, out);
                }
                if cnt[a as usize] > 0 {
                    emit(set(push(s, r)), 3 + x, out);
                }
                continue;
            }
            if s.len > 1 && ((top0 == a && top1 == b) || (top0 == b && top1 == a)) {
                emit(set(push(&drop(s, 2), r)), 0, out);
            }
            // a copy onto one operand in place
            if s.len > 0 && top0 == a && cnt[b as usize] > 0 {
                emit(set(push(&drop(s, 1), r)), 3, out);
            }
            if s.len > 0 && top0 == b && a != b && cnt[a as usize] > 0 {
                emit(set(push(&drop(s, 1), r)), 3, out);
            }
            if cnt[a as usize] > 0 && cnt[b as usize] > 0 {
                emit(set(push(s, r)), 6, out);
            }
        }
        // a copy kept for later
        for v in 1..NV {
            if cnt[v] > 0 && cnt[v] < u[v] && s.len < self.w {
                emit(push(s, v as u8), 3, out);
            }
        }
        if s.len == 0 {
            return;
        }
        let top = s.tok[0];
        if top == G || cnt[top as usize] > lo[top as usize] {
            emit(drop(s, 1), 2, out);
        }
        for k in 1..s.len {
            let y = s.tok[k];
            if y != top && !(y == G && top == G) {
                let mut ns = *s;
                ns.tok.swap(0, k);
                emit(ns, 3, out);
            }
            if k >= 2 && top != G {
                // the top to depth k
                let mut ns = *s;
                ns.tok.copy_within(1..=k, 0);
                ns.tok[k] = top;
                if ns.tok != s.tok {
                    emit(ns, 3, out);
                }
            }
            if k >= 2 && y != G {
                // depth k to the top
                let mut ns = *s;
                ns.tok.copy_within(0..k, 1);
                ns.tok[0] = y;
                if ns.tok != s.tok {
                    emit(ns, 3, out);
                }
            }
        }
    }

    /// one round from every source: the cheapest cost of every layout a
    /// round ends in, and the states it went through
    fn layer(&self, src: &FxMap<u128, u32>) -> (FxMap<u128, u32>, usize) {
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
                        *e = (*e).min(nd);
                        continue;
                    }
                    if dist.get(&nk).is_some_and(|&x| x <= nd) {
                        continue;
                    }
                    dist.insert(nk, nd);
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

    fn name(&self, v: u8) -> String {
        let lanes = |m: u8| -> String {
            (0..self.t)
                .filter(|l| m >> l & 1 == 1)
                .map(|l| if l == 0 { "x".into() } else { format!("s{l}") })
                .collect::<Vec<String>>()
                .join("+")
        };
        match v {
            G => "_".into(),
            I0 => "s0".into(),
            _ if (LEAF..BLK).contains(&v) => lanes(1 << (v - LEAF)),
            _ if (BLK..M).contains(&v) => lanes(MASKS[(v - BLK) as usize]),
            _ if (M..DV).contains(&v) => format!("m{}", v - M),
            DV => "2s2".into(),
            TV => "sum+s2".into(),
            _ if (O..XN).contains(&v) => format!("s{}'", v - O),
            XN => "x'".into(),
            _ if (BLKN..MN).contains(&v) => format!("({})'", lanes(MASKS[(v - BLKN) as usize])),
            _ if (MN..DN).contains(&v) => format!("m{}'", v - MN),
            DN => "2s2'".into(),
            SV => "v".into(),
            SV2 => "v2".into(),
            SV4 => "v4".into(),
            SVN => "v'".into(),
            SV2N => "v2'".into(),
            _ => "v4'".into(),
        }
    }

    fn show(&self, k: u128) -> String {
        let s = self.unpack(k);
        let names: Vec<String> = s.tok[..s.len].iter().map(|&v| self.name(v)).collect();
        format!(
            "[{}] next: sbox {} m {:04b} d {} parts {:?}",
            names.join(","),
            s.n.sbox as u8,
            s.n.m,
            s.n.d as u8,
            &s.n.blk[..self.t]
        )
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let t: usize = args.get(1).and_then(|a| a.parse().ok()).unwrap_or(4);
    let w: usize = args.get(2).and_then(|a| a.parse().ok()).unwrap_or(12);
    let layers: usize = args.get(3).and_then(|a| a.parse().ok()).unwrap_or(4);
    assert!(w < MAXW && (t == 3 || t == 4));
    let kinds = if t == 4 {
        vec![Kind::Mul; 4]
    } else {
        vec![Kind::Ident, Kind::Ident, Kind::Dbl]
    };
    let parts = partitions(t);
    let mut pidx = HashMap::new();
    for (i, p) in parts.iter().enumerate() {
        pidx.insert(*p, i as u8);
    }
    // t = 4: lanes 1, 2, 3 are alike here (their diag constants only differ)
    let mut syms = vec![];
    let lperms: Vec<[usize; 4]> = if t == 4 {
        vec![
            [0, 1, 2, 3],
            [0, 1, 3, 2],
            [0, 2, 1, 3],
            [0, 2, 3, 1],
            [0, 3, 1, 2],
            [0, 3, 2, 1],
        ]
    } else {
        vec![[0, 1, 2, 3]]
    };
    for pi in &lperms {
        let mut tm = [0u8; 16];
        for (m, e) in tm.iter_mut().enumerate() {
            for l in 0..4 {
                if m >> l & 1 == 1 {
                    *e |= 1 << pi[l];
                }
            }
        }
        let mut tv = [0u8; NV];
        for (v, e) in tv.iter_mut().enumerate() {
            let v = v as u8;
            *e = match v {
                _ if (LEAF..BLK).contains(&v) => LEAF + pi[(v - LEAF) as usize] as u8,
                _ if (BLK..M).contains(&v) => BLK + bidx(tm[MASKS[(v - BLK) as usize] as usize]),
                _ if (M..DV).contains(&v) => M + pi[(v - M) as usize] as u8,
                _ if (O..XN).contains(&v) => O + pi[(v - O) as usize] as u8,
                _ if (BLKN..MN).contains(&v) => {
                    BLKN + bidx(tm[MASKS[(v - BLKN) as usize] as usize])
                }
                _ if (MN..DN).contains(&v) => MN + pi[(v - MN) as usize] as u8,
                _ => v,
            };
        }
        syms.push((tv, tm));
    }
    let pb = Pb {
        t,
        kinds,
        w,
        parts,
        pidx,
        syms,
        split: std::env::var_os("SPLIT").is_some(),
        sb: std::env::var_os("SBOX").is_some(),
        shl: t == 3 && std::env::var_os("SHL").is_some(),
        comp: t == 4 && std::env::var_os("COMP").is_some(),
    };
    // the inputs in every order, nothing else on the stack
    let mut src: FxMap<u128, u32> = FxMap::default();
    let mut lanes: Vec<u8> = (0..t as u8).collect();
    fn perms(k: usize, a: &mut Vec<u8>, out: &mut Vec<Vec<u8>>) {
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
    let mut ps = vec![];
    perms(0, &mut lanes, &mut ps);
    for p in ps {
        let mut s = St {
            tok: [0; MAXW],
            len: t,
            c: fresh(t),
            n: fresh(t),
        };
        for (i, &l) in p.iter().enumerate() {
            s.tok[i] = if l == 0 { I0 } else { LEAF + l };
        }
        src.insert(pb.key(&s), 0);
    }
    if layers == 0 {
        // one round from s0, s1, ... back to the same layout (the layout of
        // the programs in the repository)
        let mut s = St {
            tok: [0; MAXW],
            len: t,
            c: fresh(t),
            n: fresh(t),
        };
        for l in 0..t {
            s.tok[l] = if l == 0 { I0 } else { LEAF + l as u8 };
        }
        let k = pb.key(&s);
        let one: FxMap<u128, u32> = [(k, 0)].into_iter().collect();
        let (nd, states) = pb.layer(&one);
        println!(
            "same layout {:?}, cheapest end {:?}, {states} states",
            nd.get(&k),
            nd.values().min()
        );
        return;
    }
    // every layout a round can end in
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
    // keep only the layouts some round ends in
    let (reach, _) = pb.layer(&all);
    let mut d: FxMap<u128, u32> = reach.keys().map(|&k| (k, 0)).collect();
    println!(
        "t = {t}, window {w} (split {}, sbox {}, shl {}, comp {}): {} end layouts",
        pb.split as u8,
        pb.sb as u8,
        pb.shl as u8,
        pb.comp as u8,
        d.len()
    );
    for k in 1..=layers {
        let (nd, states) = pb.layer(&d);
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
            for (key, _) in best.iter().take(5) {
                println!("  ends in {}", pb.show(**key));
            }
        }
        d = nd;
    }
}
