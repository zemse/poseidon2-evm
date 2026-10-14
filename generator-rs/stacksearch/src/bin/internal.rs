// A* over single EVM opcodes for one Poseidon2 internal round with three or
// four lanes, each lane i > 0 scaled by its own diag constant d_i (t = 4;
// with three lanes it is the analogue of t = 4, not the t = 3 round, whose
// diag is 1, 1, 2): s0 + c and its S-box as one move (on [s0, P], 45 gas, or
// on [s0], 54), the sum of x = (s0 + c)^5 and the other lanes, and s_i' =
// d_i * s_i + sum (x for lane 0), from a given layout to a given layout.
// Values are classes: the partial sums of the lanes (a lane mask with a
// bound in units of P, so an ADD is allowed only while the bound stays at
// most 5, 2^256 / P being 5.29), the products d_i * s_i and the outputs with
// their bound. Every opcode costs its gas: DUP / SWAP / PUSH 3, POP 2, ADD 3,
// ADDMOD / MULMOD 8 (their third operand a PRIME copy). A PRIME copy is one
// move of 3 gas wherever it comes from (a DUP of a deep copy or a PUSH32).
//
//   internal <lanes> <init> <goal> [max_garbage=0] [max_depth=16] [bounds]
//
// init / goal: comma separated classes, top first: s<i> the lanes before the
// round (in the goal output i), P a PRIME copy, O any unplaced output. The
// goal requires each output once. UNORDERED=1 accepts any permutation of
// its outputs and PRIME copies. UB=<gas> prunes f >= gas before insertion.
// `bounds` is
// `s=<b0>,<b1>,...` for the input bounds in units of P (default 2 for every
// lane: m_i + sum below 2P), optionally followed by `;o=<b0>,...` for the
// outputs' (default the inputs'). Below the goal prefix at most
// max_garbage dead values may remain.
//
// The heuristic counts only a final ADD per missing output, a MULMOD per
// missing product, and the greater of net stack supply and mandatory diag /
// PRIME supply. It does not charge copies, garbage, placement, sum formation
// or S-box work at arbitrary states. At the raw five-slot t = 4 boundary
// with bounds 2 it retains the fixed-arithmetic relaxation of 154 gas.
// This bound can decrease faster than a move costs; the queue revisits lower
// f buckets. It is not a certificate over arbitrary EVM implementations.
//
// A DUP is only made while the entries of a value are fewer than its uses
// left, or as many when every entry is frozen (LOOSE_DUP=1 allows one more
// in any case). These generation restrictions are not proved complete.
// SINGLE=1 runs the S-box as single opcodes, NO_POP=1 leaves POP out,
// MAXF=<gas> stops past that f, and REPLAY="<program>" prints g, h and the
// stack after every move of a program in the template DSL instead of
// searching. NO_SUM_WASTE is retained for compatibility but has no effect.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

const MAXD: usize = 24;
const MAXT: usize = 4;

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
}
type FxMap<K, V> = HashMap<K, V, BuildHasherDefault<Fx>>;

// ---- classes ----------------------------------------------------------------

const P: u8 = 0;
const RC: u8 = 1;
const D0: u8 = 2; // ..D0 + 3
const S0: u8 = 6;
const A: u8 = 7;
const A2: u8 = 8;
const A4: u8 = 9;
const PART: u8 = 10; // + (mask - 1) * 5 + (b - 1), mask 1..15, b 1..5
const PROD: u8 = 85; // + i
const OUT: u8 = 89; // + i * 5 + (b - 1)
const NCLASS: usize = 109;
const MAXB: u8 = 5;

fn part(mask: u8, b: u8) -> u8 {
    PART + (mask - 1) * 5 + (b - 1)
}
fn is_part(c: u8) -> bool {
    (PART..PROD).contains(&c)
}
fn part_mask(c: u8) -> u8 {
    (c - PART) / 5 + 1
}
fn part_b(c: u8) -> u8 {
    (c - PART) % 5 + 1
}
fn out(i: usize, b: u8) -> u8 {
    OUT + i as u8 * 5 + (b - 1)
}
fn is_out(c: u8) -> bool {
    c >= OUT && (c as usize) < NCLASS
}
fn out_lane(c: u8) -> usize {
    ((c - OUT) / 5) as usize
}
fn out_b(c: u8) -> u8 {
    (c - OUT) % 5 + 1
}

fn class_name(c: u8) -> String {
    match c {
        P => "P".into(),
        RC => "c".into(),
        _ if (D0..D0 + 4).contains(&c) => format!("d{}", c - D0),
        S0 => "s0".into(),
        A => "s0+c".into(),
        A2 => "x2".into(),
        A4 => "x4".into(),
        _ if is_part(c) => {
            let m = part_mask(c);
            let names: Vec<String> = (0..MAXT)
                .filter(|i| m >> i & 1 == 1)
                .map(|i| if i == 0 { "x".into() } else { format!("s{i}") })
                .collect();
            let n = names.join("+");
            // ~ marks a reduced sum
            if m.count_ones() > 1 && part_b(c) == 1 {
                format!("{n}~")
            } else {
                n
            }
        }
        _ if (PROD..PROD + 4).contains(&c) => format!("m{}", c - PROD),
        _ => format!("s{}'", out_lane(c)),
    }
}

// ---- problem ----------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Move {
    Dup(u8),
    Swap(u8),
    Pop,
    PushP,
    PushC,
    PushD(u8),
    Add,
    Addmod,
    Mulmod,
    // s0 + c and its S-box on [s0, P] (both consumed) or on [s0]
    Sbox,
    SboxN,
}

impl Move {
    fn cost(self) -> u32 {
        match self {
            Move::Sbox => 45,
            Move::SboxN => 54,
            Move::Pop => 2,
            Move::Addmod | Move::Mulmod => 8,
            _ => 3,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Stack {
    len: u8,
    // bottom first
    s: [u8; MAXD],
}

impl Stack {
    fn top(&self, k: usize) -> u8 {
        self.s[self.len as usize - 1 - k]
    }
    fn push(&mut self, c: u8) {
        self.s[self.len as usize] = c;
        self.len += 1;
    }
    fn pop(&mut self) -> u8 {
        self.len -= 1;
        let c = self.s[self.len as usize];
        self.s[self.len as usize] = 0;
        c
    }
    fn slice(&self) -> &[u8] {
        &self.s[..self.len as usize]
    }
}

enum GoalSlot {
    Class(u8),
    // output lane, max bound
    Out(usize, u8),
    AnyOut,
}

fn parse_goal(names: &[String], bounds: &[u8]) -> (Vec<GoalSlot>, u32) {
    let mut goal = Vec::new();
    let mut goal_p = 0;
    let mut seen = vec![false; bounds.len()];
    let mut any = 0;
    for n in names {
        if n == "P" {
            goal.push(GoalSlot::Class(P));
            goal_p += 1;
        } else if n == "O" {
            goal.push(GoalSlot::AnyOut);
            any += 1;
        } else {
            let i: usize = n
                .strip_prefix('s')
                .expect("output name")
                .parse()
                .expect("output index");
            assert!(
                n == &format!("s{i}") && i < bounds.len() && !seen[i],
                "duplicate or invalid output"
            );
            seen[i] = true;
            goal.push(GoalSlot::Out(i, bounds[i]));
        }
    }
    assert_eq!(
        seen.iter().filter(|&&b| b).count() + any,
        bounds.len(),
        "goal must contain every output once"
    );
    (goal, goal_p)
}

struct Problem {
    t: usize,
    full: u8,
    init: Stack,
    goal: Vec<GoalSlot>, // top first
    goal_p: u32,
    unordered_goal: bool,
    in_bound: Vec<u8>,
    out_bound: Vec<u8>,
    max_garbage: u32,
    max_depth: usize,
    single_ops: bool,
    #[allow(dead_code)] // legacy toggle; all heuristic placement charges are disabled
    no_sum_waste: bool,
    strict_dup: bool,
    no_pop: bool,
}

/// what the stack holds, for liveness and the heuristic
struct Info {
    has_out: [bool; MAXT],
    has_prod: [bool; MAXT],
    // singleton entries per lane (x for lane 0) and their least bound
    single: [u32; MAXT],
    single_b: [u8; MAXT],
    full: u32,
    n_a: u32,
    n_a2: u32,
    n_a4: u32,
    has_s0: bool,
    // least bound of the present parts of two lanes or more, by mask
    part_b: [u8; 16],
    missing: u32,
    min_out_b: u8,
    p_count: u32,
    has_c: bool,
    has_d: [bool; MAXT],
}

/// what is still to be done from a stack (lower bounds)
struct Need {
    adds: u32,
    addmods: u32,
    mods: u32,
    pushes: u32,
    copies: u32,
    feasible: bool,
}

impl Problem {
    fn info(&self, st: &Stack) -> Info {
        let mut i = Info {
            has_out: [false; MAXT],
            has_prod: [false; MAXT],
            single: [0; MAXT],
            single_b: [MAXB + 1; MAXT],
            full: 0,
            n_a: 0,
            n_a2: 0,
            n_a4: 0,
            has_s0: false,
            part_b: [MAXB + 1; 16],
            missing: 0,
            min_out_b: MAXB,
            p_count: 0,
            has_c: false,
            has_d: [false; MAXT],
        };
        for &c in st.slice() {
            match c {
                P => i.p_count += 1,
                RC => i.has_c = true,
                S0 => i.has_s0 = true,
                _ if (D0..D0 + 4).contains(&c) => i.has_d[(c - D0) as usize] = true,
                A => i.n_a += 1,
                A2 => i.n_a2 += 1,
                A4 => i.n_a4 += 1,
                _ if is_part(c) => {
                    let m = part_mask(c);
                    let b = part_b(c);
                    if m == self.full {
                        i.full += 1;
                    } else if m.count_ones() == 1 {
                        let l = m.trailing_zeros() as usize;
                        i.single[l] += 1;
                        i.single_b[l] = i.single_b[l].min(b);
                    }
                    if m.count_ones() > 1 {
                        i.part_b[m as usize] = i.part_b[m as usize].min(b);
                    }
                }
                _ if (PROD..PROD + 4).contains(&c) => i.has_prod[(c - PROD) as usize] = true,
                _ if is_out(c) => i.has_out[out_lane(c)] = true,
                _ => {}
            }
        }
        for l in 0..self.t {
            if !i.has_out[l] {
                i.missing += 1;
                i.min_out_b = i.min_out_b.min(self.out_bound[l]);
            }
        }
        i
    }

    fn prod_needed(&self, inf: &Info, l: usize) -> bool {
        !inf.has_out[l] && !inf.has_prod[l]
    }
    fn sum_needed(&self, inf: &Info) -> bool {
        inf.missing > 0 && inf.full == 0
    }
    // lane l goes into the sum on its own: no present part holds it
    fn lane_sum_use(&self, inf: &Info, l: usize) -> bool {
        if !self.sum_needed(inf) {
            return false;
        }
        for m in 1..16usize {
            if m >> l & 1 == 1 && inf.part_b[m] <= MAXB {
                return false;
            }
        }
        true
    }
    fn lane_uses(&self, inf: &Info, l: usize) -> u32 {
        self.prod_needed(inf, l) as u32 + self.lane_sum_use(inf, l) as u32
    }
    fn x_needed(&self, inf: &Info) -> bool {
        self.prod_needed(inf, 0) || self.sum_needed(inf)
    }
    fn chain_needed(&self, inf: &Info) -> bool {
        self.x_needed(inf) && inf.single[0] == 0
    }
    fn sum_uses(&self, inf: &Info) -> u32 {
        inf.missing
    }

    /// entries a class may still use (a DUP beyond them is useless)
    fn uses(&self, inf: &Info, c: u8) -> u32 {
        match c {
            A => {
                if !self.chain_needed(inf) {
                    0
                } else if inf.n_a4 > 0 || inf.n_a2 > 0 {
                    1
                } else {
                    3
                }
            }
            A2 => {
                if self.chain_needed(inf) && inf.n_a4 == 0 {
                    2
                } else {
                    0
                }
            }
            _ if is_part(c) => {
                let m = part_mask(c);
                if m == self.full {
                    self.sum_uses(inf)
                } else if m.count_ones() == 1 {
                    self.lane_uses(inf, m.trailing_zeros() as usize)
                } else if self.sum_needed(inf) {
                    1
                } else {
                    0
                }
            }
            _ => 0,
        }
    }

    fn uses_left(&self, inf: &Info, c: u8) -> u32 {
        if (PROD..PROD + 4).contains(&c) {
            return !inf.has_out[(c - PROD) as usize] as u32;
        }
        self.uses(inf, c)
    }

    fn entries(&self, inf: &Info, c: u8) -> u32 {
        match c {
            A => inf.n_a,
            A2 => inf.n_a2,
            _ if is_part(c) => {
                let m = part_mask(c);
                if m == self.full {
                    inf.full
                } else if m.count_ones() == 1 {
                    inf.single[m.trailing_zeros() as usize]
                } else {
                    1
                }
            }
            _ => u32::MAX,
        }
    }

    fn live(&self, inf: &Info, c: u8) -> bool {
        match c {
            P => true,
            RC | S0 | A | A2 | A4 => self.chain_needed(inf),
            _ if (D0..D0 + 4).contains(&c) => self.prod_needed(inf, (c - D0) as usize),
            _ if is_part(c) => {
                let m = part_mask(c);
                if m == self.full {
                    inf.missing > 0
                } else if m.count_ones() == 1 {
                    let l = m.trailing_zeros() as usize;
                    self.sum_needed(inf) || self.prod_needed(inf, l)
                } else {
                    self.sum_needed(inf)
                }
            }
            _ if (PROD..PROD + 4).contains(&c) => !inf.has_out[(c - PROD) as usize],
            _ => true, // outputs
        }
    }

    // cheapest cover of the full mask by present parts and lanes: fewest
    // parts, and the least total bound among covers
    fn cover(&self, inf: &Info) -> (u32, u8) {
        let full = self.full as usize;
        let mut best = [u32::MAX; 16];
        let mut bb = [u8::MAX; 16];
        best[0] = 0;
        bb[0] = 0;
        for m in 0..=full {
            if best[m] == u32::MAX {
                continue;
            }
            for q in 1..=full {
                if q & m != 0 || q & !full != 0 {
                    continue;
                }
                let b = if q.count_ones() == 1 {
                    let l = q.trailing_zeros() as usize;
                    if l == 0 {
                        1
                    } else {
                        inf.single_b[l].min(self.in_bound[l])
                    }
                } else {
                    inf.part_b[q]
                };
                if b > MAXB {
                    continue;
                }
                let n = m | q;
                best[n] = best[n].min(best[m] + 1);
                bb[n] = bb[n].min(bb[m].saturating_add(b));
            }
        }
        (best[full], bb[full])
    }

    fn need(&self, inf: &Info) -> Need {
        let mut n = Need {
            adds: 0,
            addmods: 0,
            mods: 0,
            pushes: 0,
            copies: 0,
            feasible: true,
        };
        for l in 0..self.t {
            if !inf.has_out[l] {
                n.adds += 1;
                if !inf.has_prod[l] {
                    n.mods += 1;
                    if !inf.has_d[l] {
                        n.pushes += 1;
                    }
                }
            }
        }
        if self.sum_needed(inf) {
            let (parts, bound) = self.cover(inf);
            n.adds += parts - 1;
            // m + sum within the outputs' bound needs a reduction somewhere
            if bound as u32 + 1 > inf.min_out_b as u32 {
                n.addmods += 1;
            }
            // the sum's own copies
            n.copies += inf.missing.saturating_sub(1);
        } else if inf.missing > 0 {
            n.copies += inf.missing.saturating_sub(inf.full);
            // a sum present above the outputs' bound needs reducing outputs
        }
        for l in 0..self.t {
            let u = self.lane_uses(inf, l);
            let e = if l == 0 && inf.single[0] == 0 {
                1
            } else {
                inf.single[l]
            };
            if l > 0 && e == 0 && u > 0 {
                n.feasible = false;
            }
            n.copies += u.saturating_sub(e);
        }
        if self.chain_needed(inf) {
            if inf.n_a4 > 0 {
                n.mods += 1;
                if inf.n_a == 0 {
                    n.feasible = false;
                }
            } else if inf.n_a2 > 0 {
                n.mods += 2;
                if inf.n_a == 0 {
                    n.feasible = false;
                }
                n.copies += 2u32.saturating_sub(inf.n_a2);
            } else if inf.n_a > 0 {
                n.mods += 3;
                n.copies += 3u32.saturating_sub(inf.n_a) + 1;
            } else {
                if !inf.has_s0 {
                    n.feasible = false;
                }
                n.mods += 3;
                n.adds += 1;
                n.copies += 3;
                if !inf.has_c {
                    n.pushes += 1;
                }
            }
        }
        // the outputs reduced by an ADDMOD count as adds already; only the
        // extra cost of one ADDMOD
        if n.addmods > 0 {
            n.adds -= 1;
        }
        n
    }

    /// placement categories used by the restricted DUP filter, not a bound
    /// on which entries can be consumed by a completion
    fn placement(&self, st: &Stack, inf: &Info) -> ([bool; NCLASS], [bool; NCLASS], u32) {
        let mut dead = 0u32;
        let mut seen_out = false;
        let mut free = [false; NCLASS];
        let mut frozen = [false; NCLASS];
        // The DUP filter treats the deepest sum as frozen while two outputs
        // remain. Recomputation can consume other entries classified dead.
        let mut deepest_full = usize::MAX;
        if inf.missing >= 2 {
            for k in 0..st.len as usize {
                let c = st.top(k);
                if is_part(c) && part_mask(c) == self.full {
                    deepest_full = k;
                }
            }
        }
        for k in 0..st.len as usize {
            let c = st.top(k);
            if is_out(c) || k == deepest_full {
                seen_out = true;
                continue;
            }
            if !self.live(inf, c) {
                dead += 1;
                continue;
            }
            if seen_out {
                frozen[c as usize] = true;
            } else {
                free[c as usize] = true;
            }
        }
        (free, frozen, dead)
    }

    fn heuristic(&self, st: &Stack, inf: &Info) -> u32 {
        // Only MULMOD creates a product and ADD / ADDMOD creates an output.
        let adds = inf.missing;
        let mut mods = 0;
        let mut diag = 0;
        for l in 0..self.t {
            if !inf.has_out[l] && !inf.has_prod[l] {
                mods += 1;
                diag += !inf.has_d[l] as u32;
            }
        }
        // Other arithmetic and POPs consume more slots, never supply them.
        let slots = self.goal.len() as i64 - st.len as i64 + adds as i64 + 2 * mods as i64;
        let primes = (mods + self.goal_p).saturating_sub(inf.p_count);
        let supply = (slots.max(0) as u32).max(diag + primes);
        let bound = 3 * adds + 8 * mods + 3 * supply;
        let raw = [S0, P, part(2, 2), part(4, 2), part(8, 2)];
        if self.t == 4
            && st.len == 5
            && self.goal.len() == 5
            && self.goal_p == 1
            && self.in_bound.as_slice() == [2; 4]
            && self.out_bound.as_slice() == [2; 4]
            && raw.iter().all(|c| st.slice().contains(c))
        {
            // Seven ADDs, eight mod ops: 85 gas and 23 net consumed slots.
            // The sum's bound 7 needs at least one ADDMOD in this class graph.
            bound.max(85 + 3 * 23)
        } else {
            bound
        }
    }

    fn is_goal(&self, st: &Stack) -> bool {
        if (st.len as usize) < self.goal.len() {
            return false;
        }
        if self.unordered_goal {
            let mut seen = [false; MAXT];
            let mut primes = 0;
            for k in 0..self.goal.len() {
                let c = st.top(k);
                if c == P {
                    primes += 1;
                } else if is_out(c) {
                    let l = out_lane(c);
                    if l >= self.t || seen[l] || out_b(c) > self.out_bound[l] {
                        return false;
                    }
                    seen[l] = true;
                } else {
                    return false;
                }
            }
            return seen[..self.t].iter().all(|&b| b)
                && primes == self.goal_p
                && (st.len as usize - self.goal.len()) as u32 <= self.max_garbage;
        }
        let mut seen = [false; MAXT];
        for (k, g) in self.goal.iter().enumerate() {
            let c = st.top(k);
            if is_out(c) {
                let l = out_lane(c);
                if l >= self.t || seen[l] {
                    return false;
                }
                seen[l] = true;
            }
            match *g {
                GoalSlot::Class(x) => {
                    if c != x {
                        return false;
                    }
                }
                GoalSlot::Out(l, b) => {
                    if !is_out(c) || out_lane(c) != l || out_b(c) > b {
                        return false;
                    }
                }
                GoalSlot::AnyOut => {
                    if !is_out(c) || out_b(c) > self.out_bound[out_lane(c)] {
                        return false;
                    }
                }
            }
        }
        let rest = st.len as usize - self.goal.len();
        rest as u32 <= self.max_garbage
    }

    fn apply(&self, st: &Stack, inf: &Info, m: Move) -> Option<Stack> {
        let mut s = *st;
        let len = s.len as usize;
        match m {
            Move::Dup(k) => {
                let c = s.top(k as usize - 1);
                if !self.live(inf, c) || is_out(c) {
                    return None;
                }
                // one copy beyond the uses left, for an entry that cannot
                // be consumed in place
                if c != P {
                    let (e, u) = (self.entries(inf, c), self.uses_left(inf, c));
                    if e > u {
                        return None;
                    }
                    if e == u && self.strict_dup {
                        let (free, frozen, _) = self.placement(st, inf);
                        if !frozen[c as usize] || free[c as usize] {
                            return None;
                        }
                    }
                }
                if len >= self.max_depth {
                    return None;
                }
                s.push(c);
            }
            Move::Swap(k) => {
                let a = len - 1;
                let b = len - 1 - k as usize;
                if s.s[a] == s.s[b] {
                    return None;
                }
                s.s.swap(a, b);
            }
            Move::Pop => {
                s.pop();
            }
            Move::PushP => {
                if len >= self.max_depth {
                    return None;
                }
                let n = self.need(inf);
                if inf.p_count >= n.mods + n.adds + n.addmods + self.goal_p {
                    return None;
                }
                s.push(P);
            }
            Move::PushC => {
                if len >= self.max_depth || inf.has_c || !self.chain_needed(inf) || !inf.has_s0 {
                    return None;
                }
                s.push(RC);
            }
            Move::PushD(i) => {
                if len >= self.max_depth || !self.prod_needed(inf, i as usize) {
                    return None;
                }
                s.push(D0 + i);
            }
            Move::Add | Move::Addmod => {
                let need = if m == Move::Add { 2 } else { 3 };
                if len < need {
                    return None;
                }
                if m == Move::Addmod && s.top(2) != P {
                    return None;
                }
                let (a, b) = (s.top(0), s.top(1));
                let r = self.add(a, b, m == Move::Addmod)?;
                for _ in 0..need {
                    s.pop();
                }
                s.push(r);
            }
            Move::Sbox | Move::SboxN => {
                if len < 1 || s.top(0) != S0 {
                    return None;
                }
                s.pop();
                if m == Move::Sbox {
                    if len < 2 || s.top(0) != P {
                        return None;
                    }
                    s.pop();
                }
                s.push(part(1, 1));
            }
            Move::Mulmod => {
                if len < 3 || s.top(2) != P {
                    return None;
                }
                let (a, b) = (s.top(0), s.top(1));
                let r = self.mul(inf, a, b)?;
                s.pop();
                s.pop();
                s.pop();
                s.push(r);
            }
        }
        Some(s)
    }

    fn add(&self, a: u8, b: u8, reduce: bool) -> Option<u8> {
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        // s0 + c
        if a == RC && b == S0 {
            return if reduce { None } else { Some(A) };
        }
        if is_part(a) && is_part(b) {
            let (ma, mb) = (part_mask(a), part_mask(b));
            if ma & mb != 0 {
                return None;
            }
            let bb = part_b(a) + part_b(b);
            if !reduce && bb > MAXB {
                return None;
            }
            return Some(part(ma | mb, if reduce { 1 } else { bb }));
        }
        // m_i + sum
        let (pr, sm) = if (PROD..PROD + 4).contains(&a) && is_part(b) {
            (a, b)
        } else if (PROD..PROD + 4).contains(&b) && is_part(a) {
            (b, a)
        } else {
            return None;
        };
        if part_mask(sm) != self.full {
            return None;
        }
        let bb = 1 + part_b(sm);
        if !reduce && bb > MAXB {
            return None;
        }
        Some(out((pr - PROD) as usize, if reduce { 1 } else { bb }))
    }

    fn mul(&self, inf: &Info, a: u8, b: u8) -> Option<u8> {
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        match (a, b) {
            (A, A) => Some(A2),
            (A2, A2) => Some(A4),
            (A, A4) => Some(part(1, 1)),
            _ => {
                if (D0..D0 + 4).contains(&a) && is_part(b) {
                    let l = (a - D0) as usize;
                    if part_mask(b) == 1 << l && self.prod_needed(inf, l) {
                        return Some(PROD + l as u8);
                    }
                }
                None
            }
        }
    }

    fn moves(&self, st: &Stack) -> Vec<Move> {
        let len = st.len as usize;
        let mut v = Vec::new();
        for k in 1..=len.min(16) {
            v.push(Move::Dup(k as u8));
        }
        for k in 1..len.min(17) {
            v.push(Move::Swap(k as u8));
        }
        if len > 0 && !self.no_pop {
            v.push(Move::Pop);
        }
        v.push(Move::PushP);
        if self.single_ops {
            v.push(Move::PushC);
        } else {
            v.push(Move::Sbox);
            v.push(Move::SboxN);
        }
        for i in 0..self.t {
            v.push(Move::PushD(i as u8));
        }
        v.extend([Move::Add, Move::Addmod, Move::Mulmod]);
        v
    }
}

fn parse_layout(s: &str) -> Vec<String> {
    s.split(',').map(|x| x.trim().to_string()).collect()
}

fn class_of_input(name: &str, bounds: &[u8]) -> u8 {
    if name == "P" {
        return P;
    }
    let i: usize = name
        .strip_prefix('s')
        .expect("input name")
        .parse()
        .expect("lane index");
    assert!(
        name == format!("s{i}") && i < bounds.len(),
        "input lane index"
    );
    if i == 0 {
        S0
    } else {
        part(1 << i, bounds[i])
    }
}

struct Node {
    st: Stack,
    g: u16,
    parent: u32,
    mv: Move,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 3 {
        eprintln!(
            "internal <lanes> <init> <goal> [max_garbage=0] [max_depth=16] [s=b0,b1,..;o=b0,..]"
        );
        std::process::exit(2);
    }
    let t: usize = args[0].parse().unwrap();
    assert!(t == 3 || t == 4, "three or four lanes");
    let max_garbage: u32 = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(0);
    let max_depth: usize = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(16);
    let mut in_b = vec![2u8; t];
    let mut out_bd: Option<Vec<u8>> = None;
    if let Some(b) = args.get(5) {
        for part_s in b.split(';') {
            let (k, v) = part_s.split_once('=').expect("bounds");
            let vals: Vec<u8> = v.split(',').map(|x| x.parse().unwrap()).collect();
            match k {
                "s" => in_b = vals,
                "o" => out_bd = Some(vals),
                _ => panic!("bounds key {k}"),
            }
        }
    }
    let out_b = out_bd.unwrap_or_else(|| in_b.clone());
    let init_names = parse_layout(&args[1]);
    let goal_names = parse_layout(&args[2]);
    assert_eq!(in_b.len(), t, "input bounds length");
    assert_eq!(out_b.len(), t, "output bounds length");
    assert!(
        in_b.iter().chain(&out_b).all(|&b| (1..=MAXB).contains(&b)),
        "bounds must be in 1..=5"
    );
    assert!(in_b[0] <= 4, "constant ADD bound");
    assert!(
        max_depth <= MAXD && init_names.len() <= max_depth,
        "depth limit"
    );
    let mut init = Stack {
        len: 0,
        s: [0; MAXD],
    };
    let mut seen_inputs = vec![false; t];
    for n in init_names.iter().rev() {
        let c = class_of_input(n, &in_b);
        if c != P {
            let l = if c == S0 {
                0
            } else {
                part_mask(c).trailing_zeros() as usize
            };
            assert!(!seen_inputs[l], "duplicate input lane");
            seen_inputs[l] = true;
        }
        init.push(c);
    }
    assert!(
        seen_inputs.iter().all(|&b| b),
        "initial layout must contain every lane once"
    );
    let (goal, goal_p) = parse_goal(&goal_names, &out_b);
    let p = Problem {
        t,
        full: ((1u32 << t) - 1) as u8,
        init,
        goal,
        goal_p,
        unordered_goal: std::env::var("UNORDERED").is_ok(),
        in_bound: in_b.clone(),
        out_bound: out_b.clone(),
        max_garbage,
        max_depth,
        single_ops: std::env::var("SINGLE").is_ok(),
        no_sum_waste: std::env::var("NO_SUM_WASTE").is_ok(),
        strict_dup: std::env::var("LOOSE_DUP").is_err(),
        no_pop: std::env::var("NO_POP").is_ok(),
    };

    if let Ok(prog) = std::env::var("REPLAY") {
        let show = |st: &Stack| {
            st.slice()
                .iter()
                .rev()
                .map(|&c| class_name(c))
                .collect::<Vec<_>>()
                .join(",")
        };
        let mut st = p.init;
        let mut g = 0u32;
        let inf = p.info(&st);
        println!(
            "{:<16} g {g:>4} h {:>4} [{}]",
            "init",
            p.heuristic(&st, &inf),
            show(&st)
        );
        for tok in prog.split_whitespace() {
            let name = tok.split('=').next().unwrap();
            let m = match name {
                "P" => Move::PushP,
                "c" => Move::PushC,
                "pop" => Move::Pop,
                "add" => Move::Add,
                "addmod" => Move::Addmod,
                "mulmod" => Move::Mulmod,
                "sbox0" => Move::Sbox,
                "sbox0n" => Move::SboxN,
                _ if name.starts_with("dup") => Move::Dup(name[3..].parse().unwrap()),
                _ if name.starts_with("swap") => Move::Swap(name[4..].parse().unwrap()),
                _ if name.starts_with('d') => Move::PushD(name[1..].parse().unwrap()),
                _ => panic!("move {tok}"),
            };
            let inf = p.info(&st);
            let Some(n) = p.apply(&st, &inf, m) else {
                println!("{tok}: not applicable on [{}]", show(&st));
                std::process::exit(1);
            };
            st = n;
            g += m.cost();
            let inf = p.info(&st);
            let h = p.heuristic(&st, &inf);
            println!("{tok:<16} g {g:>4} h {h:>4} f {:>4} [{}]", g + h, show(&st));
        }
        let goal = p.is_goal(&st);
        println!("goal {goal}");
        println!("cost {g}");
        println!("layout {}", show(&st));
        println!("dsl {prog}");
        if !goal {
            std::process::exit(1);
        }
        return;
    }
    let ub: u32 = std::env::var("UB")
        .ok()
        .map(|v| v.parse().unwrap())
        .unwrap_or(u32::MAX);
    let max_f: u32 = std::env::var("MAXF")
        .ok()
        .map(|v| v.parse().unwrap())
        .unwrap_or(u32::MAX);
    let mut nodes: Vec<Node> = Vec::new();
    let mut index: FxMap<Stack, u32> = FxMap::default();
    let mut buckets: Vec<Vec<Vec<u32>>> = Vec::new();
    let inf0 = p.info(&p.init);
    let h0 = p.heuristic(&p.init, &inf0);
    nodes.push(Node {
        st: p.init,
        g: 0,
        parent: u32::MAX,
        mv: Move::Pop,
    });
    index.insert(p.init, 0);
    let push = |buckets: &mut Vec<Vec<Vec<u32>>>, f: u32, g: u16, i: u32| {
        let f = f as usize;
        if buckets.len() <= f {
            buckets.resize_with(f + 1, Vec::new);
        }
        let g = g as usize;
        if buckets[f].len() <= g {
            buckets[f].resize_with(g + 1, Vec::new);
        }
        buckets[f][g].push(i);
    };
    if h0 < ub && h0 <= max_f {
        push(&mut buckets, h0, 0, 0);
    }
    eprintln!("h0 {h0}, UB {ub}, MAXF {max_f}");
    let mut f = 0usize;
    let mut expanded = 0usize;
    let mut last_f = 0u32;
    let moves_cache: Vec<Vec<Move>> = (0..=MAXD)
        .map(|len| {
            let st = Stack {
                len: len as u8,
                s: [0; MAXD],
            };
            p.moves(&st)
        })
        .collect();
    let found = loop {
        // larger g first within an f bucket, then LIFO
        while f < buckets.len() {
            while buckets[f].last().is_some_and(|v| v.is_empty()) {
                buckets[f].pop();
            }
            if !buckets[f].is_empty() {
                break;
            }
            f += 1;
        }
        if f >= buckets.len() || f as u32 > max_f {
            break None;
        }
        let g = (buckets[f].len() - 1) as u16;
        let idx = buckets[f][g as usize].pop().unwrap();
        let node = &nodes[idx as usize];
        if node.g != g {
            continue;
        }
        let st = node.st;
        if p.is_goal(&st) {
            break Some(idx);
        }
        let inf = p.info(&st);
        expanded += 1;
        if expanded.is_multiple_of(1_000_000) || f as u32 > last_f {
            last_f = f as u32;
            eprintln!("expanded {expanded}, states {}, f {f}", nodes.len());
        }
        for &m in &moves_cache[st.len as usize] {
            let Some(ch) = p.apply(&st, &inf, m) else {
                continue;
            };
            let g2 = g as u32 + m.cost();
            let inf2 = p.info(&ch);
            let h = p.heuristic(&ch, &inf2);
            if h >= u32::MAX / 8 {
                continue;
            }
            let f2 = g2 + h;
            if f2 >= ub || f2 > max_f {
                continue;
            }
            match index.get(&ch) {
                Some(&j) => {
                    if nodes[j as usize].g as u32 <= g2 {
                        continue;
                    }
                    nodes[j as usize].g = g2 as u16;
                    nodes[j as usize].parent = idx;
                    nodes[j as usize].mv = m;
                    push(&mut buckets, f2, g2 as u16, j);
                }
                None => {
                    let j = nodes.len() as u32;
                    nodes.push(Node {
                        st: ch,
                        g: g2 as u16,
                        parent: idx,
                        mv: m,
                    });
                    index.insert(ch, j);
                    push(&mut buckets, f2, g2 as u16, j);
                }
            }
            // The conservative bound is admissible but not consistent.
            f = f.min(f2 as usize);
        }
    };
    eprintln!("expanded {expanded} nodes, {} states", nodes.len());
    let Some(idx) = found else {
        println!("no program");
        std::process::exit(1);
    };
    let mut path = Vec::new();
    let mut i = idx;
    while nodes[i as usize].parent != u32::MAX {
        path.push(i);
        i = nodes[i as usize].parent;
    }
    path.reverse();
    println!("cost {}", nodes[idx as usize].g);
    let show = |st: &Stack| {
        st.slice()
            .iter()
            .rev()
            .map(|&c| class_name(c))
            .collect::<Vec<_>>()
            .join(",")
    };
    println!("layout {}", show(&nodes[idx as usize].st));
    let mut dsl = Vec::new();
    for &j in &path {
        let n = &nodes[j as usize];
        let tok = match n.mv {
            Move::Dup(k) => format!("dup{k}"),
            Move::Swap(k) => format!("swap{k}"),
            Move::Pop => "pop".into(),
            Move::PushP => "P".into(),
            Move::PushC => "c".into(),
            Move::PushD(i) => format!("d{i}"),
            Move::Add => format!("add={}", class_name(n.st.top(0))),
            Move::Addmod => format!("addmod={}", class_name(n.st.top(0))),
            Move::Mulmod => format!("mulmod={}", class_name(n.st.top(0))),
            Move::Sbox => "sbox0".into(),
            Move::SboxN => "sbox0n".into(),
        };
        println!("{tok:<16} {:>4} [{}]", n.g, show(&n.st));
        dsl.push(tok);
    }
    println!("dsl {}", dsl.join(" "));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn problem(goal: &str) -> Problem {
        let bounds = vec![2; 4];
        let (goal, goal_p) = parse_goal(&parse_layout(goal), &bounds);
        Problem {
            t: 4,
            full: 15,
            init: Stack {
                len: 0,
                s: [0; MAXD],
            },
            goal,
            goal_p,
            unordered_goal: false,
            in_bound: bounds.clone(),
            out_bound: bounds,
            max_garbage: 1,
            max_depth: 16,
            single_ops: false,
            no_sum_waste: false,
            strict_dup: true,
            no_pop: false,
        }
    }

    fn stack(top: &[u8]) -> Stack {
        let mut st = Stack {
            len: 0,
            s: [0; MAXD],
        };
        for &c in top.iter().rev() {
            st.push(c);
        }
        st
    }

    fn check_completion(p: &Problem, mut st: Stack, moves: &[Move]) {
        let mut remaining: u32 = moves.iter().map(|&m| m.cost()).sum();
        assert!(p.heuristic(&st, &p.info(&st)) <= remaining);
        for &m in moves {
            st = p
                .apply(&st, &p.info(&st), m)
                .expect("completion move allowed");
            remaining -= m.cost();
            assert!(p.heuristic(&st, &p.info(&st)) <= remaining);
        }
        assert!(p.is_goal(&st));
        assert_eq!(p.heuristic(&st, &p.info(&st)), 0);
    }

    #[test]
    fn recomputation_consumes_entries_classified_dead() {
        let mut p = problem("s1,s0,P,s2,s3");
        p.out_bound = vec![3; 4];
        p.goal = parse_goal(&parse_layout("s1,s0,P,s2,s3"), &p.out_bound).0;
        p.max_garbage = 0;
        let st = stack(&[
            part(3, 1),
            part(12, 1),
            PROD,
            PROD + 1,
            part(15, 1),
            P,
            out(2, 2),
            out(3, 2),
        ]);
        p.init = st;
        assert!(p.strict_dup);
        assert_eq!(p.heuristic(&st, &p.info(&st)), 6);
        check_completion(&p, st, &[Move::Add, Move::Add, Move::Swap(2), Move::Add]);
    }

    #[test]
    fn dead_entries_above_outputs_can_be_swapped_below() {
        let mut p = problem("s0,P,s1,s2,s3");
        p.max_garbage = 2;
        let st = stack(&[
            part(1, 1),
            P,
            out(1, 2),
            out(2, 2),
            out(3, 2),
            part(2, 2),
            out(0, 2),
        ]);
        p.init = st;
        assert!(p.strict_dup);
        assert_eq!(p.heuristic(&st, &p.info(&st)), 0);
        check_completion(&p, st, &[Move::Swap(6)]);
    }

    #[test]
    fn small_product_and_output_completions() {
        let mut p = problem("s0,P,s1,s2,s3");
        p.max_garbage = 0;
        check_completion(
            &p,
            stack(&[PROD, part(15, 1), P, out(1, 2), out(2, 2), out(3, 2)]),
            &[Move::Add],
        );
        check_completion(
            &p,
            stack(&[
                D0,
                part(1, 1),
                P,
                part(15, 1),
                P,
                out(1, 2),
                out(2, 2),
                out(3, 2),
            ]),
            &[Move::Mulmod, Move::Add],
        );
    }

    #[test]
    fn raw_floor_and_incumbent_prefix_completions() {
        let mut p = problem("s0,P,s1,s2,s3");
        let st = stack(&[S0, P, part(2, 2), part(4, 2), part(8, 2)]);
        p.init = st;
        assert_eq!(p.heuristic(&st, &p.info(&st)), 154);
        let after_sbox = p.apply(&st, &p.info(&st), Move::Sbox).unwrap();
        assert!(45 + p.heuristic(&after_sbox, &p.info(&after_sbox)) < 154);
        let text = include_str!("../../results/t4-internal-incumbent.txt");
        let program = text
            .lines()
            .find_map(|line| line.strip_prefix("dsl "))
            .unwrap();
        let moves: Vec<Move> = program
            .split_whitespace()
            .map(|token| {
                let name = token.split('=').next().unwrap();
                match name {
                    "P" => Move::PushP,
                    "sbox0" => Move::Sbox,
                    "add" => Move::Add,
                    "addmod" => Move::Addmod,
                    "mulmod" => Move::Mulmod,
                    _ if name.starts_with("dup") => Move::Dup(name[3..].parse().unwrap()),
                    _ if name.starts_with("swap") => Move::Swap(name[4..].parse().unwrap()),
                    _ if name.starts_with('d') => Move::PushD(name[1..].parse().unwrap()),
                    _ => panic!("move {token}"),
                }
            })
            .collect();
        check_completion(&p, st, &moves);
    }

    #[test]
    fn wildcard_requires_distinct_bounded_outputs() {
        let p = problem("s0,P,O,O,O");
        assert!(p.is_goal(&stack(&[out(0, 2), P, out(3, 1), out(1, 2), out(2, 2)])));
        assert!(!p.is_goal(&stack(&[out(0, 2), P, out(3, 1), out(3, 2), out(2, 2)])));
        assert!(!p.is_goal(&stack(&[out(0, 2), P, out(3, 3), out(1, 2), out(2, 2)])));
        assert!(!p.is_goal(&stack(&[out(0, 2), P, part(8, 2), out(1, 2), out(2, 2)])));
    }

    #[test]
    fn fixed_goal_and_garbage_limit() {
        let p = problem("s0,P,s1,s2,s3");
        let mut st = stack(&[out(0, 2), P, out(1, 2), out(2, 2), out(3, 2), part(8, 2)]);
        assert!(p.is_goal(&st));
        st.s[0] = part(4, 2);
        st.push(part(8, 2));
        assert!(!p.is_goal(&st));
        assert!(!p.is_goal(&stack(&[out(0, 2), P, out(2, 2), out(1, 2), out(3, 2)])));
    }

    #[test]
    fn unordered_goal_charges_the_same_boundary_slots() {
        let mut p = problem("s0,P,s1,s2,s3");
        let st = stack(&[out(3, 2), out(0, 2), out(2, 1), P, out(1, 2), part(8, 2)]);
        assert!(!p.is_goal(&st));
        p.unordered_goal = true;
        assert!(p.is_goal(&st));
        assert_eq!(p.heuristic(&st, &p.info(&st)), 0);
        assert!(!p.is_goal(&stack(&[out(3, 2), out(0, 2), P, P, out(1, 2)])));
        assert!(!p.is_goal(&stack(&[out(3, 2), out(0, 2), out(2, 3), P, out(1, 2)])));
    }

    #[test]
    fn truncated_and_nonuniform_goals() {
        let mut p = problem("s0,P,O,O,O");
        p.out_bound[2] = 1;
        for unordered in [false, true] {
            p.unordered_goal = unordered;
            assert!(!p.is_goal(&stack(&[out(0, 2), P, out(1, 2), out(2, 1)])));
            assert!(!p.is_goal(&stack(&[out(0, 2), P, out(1, 2), out(2, 2), out(3, 2)])));
            assert!(p.is_goal(&stack(&[out(0, 2), P, out(1, 2), out(2, 1), out(3, 2)])));
        }
    }

    #[test]
    #[should_panic(expected = "duplicate or invalid output")]
    fn invalid_goal_lane_rejected() {
        problem("s0,P,s1,s2,s4");
    }

    #[test]
    #[should_panic(expected = "goal must contain every output once")]
    fn incomplete_goal_rejected() {
        problem("s0,P,O,O");
    }

    #[test]
    #[should_panic(expected = "duplicate or invalid output")]
    fn duplicate_goal_rejected() {
        problem("s0,P,s1,s1,O");
    }
}
