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
// round (in the goal output i), P a PRIME copy. `bounds` is
// `s=<b0>,<b1>,...` for the input bounds in units of P (default 2 for every
// lane: m_i + sum below 2P), optionally followed by `;o=<b0>,...` for the
// outputs' (default the inputs'). Below the goal prefix at most
// max_garbage dead values may remain.
//
// The heuristic counts the ops still needed (an ADD per missing output, the
// adds of the cheapest cover of the sum by the partial sums present, one
// ADDMOD when that cover is over the outputs' bound, a MULMOD per missing
// product and the S-box steps left) and the pushes and DUPs both the copies
// of every value still to be used and the stack balance force (every op
// takes one slot, the mod ops two, the goal needs its slots), 3 gas each.
// On top of that it counts one DUP or SWAP more while two outputs or more
// are to go: the deepest entry of the sum can only be consumed by the first
// output, after which no entry is left for the others, so it stays (or a
// SWAP moves an output under it); and it freezes what is under it like an
// output, so a value still needed whose every entry is frozen takes one copy
// more (or a SWAP), counted once with the sum's. Dead values above an
// output must be popped.
//
// A DUP is only made while the entries of a value are fewer than its uses
// left, or as many when every entry is frozen (LOOSE_DUP=1 allows one more
// in any case); so the search is optimal within that rule, the depth and the
// garbage limit. SINGLE=1 runs the S-box as single opcodes, NO_POP=1 leaves
// POP out, MAXF=<gas> stops past that f, and REPLAY="<program>" prints g, h
// and the stack after every move of a program in the template DSL instead
// of searching.

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
}

struct Problem {
    t: usize,
    full: u8,
    init: Stack,
    goal: Vec<GoalSlot>, // top first
    goal_p: u32,
    in_bound: Vec<u8>,
    out_bound: Vec<u8>,
    max_garbage: u32,
    max_depth: usize,
    single_ops: bool,
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

    /// classes with an entry free to be consumed in place, classes with an
    /// entry under an output (or under the sum's deepest entry while two
    /// outputs or more are to go, which is never consumed), and the dead
    /// entries
    fn placement(&self, st: &Stack, inf: &Info) -> ([bool; NCLASS], [bool; NCLASS], u32) {
        let mut dead = 0u32;
        let mut seen_out = false;
        let mut free = [false; NCLASS];
        let mut frozen = [false; NCLASS];
        // with two outputs or more to go, the deepest entry of the sum is
        // never consumed (see the sum's waste below), so it freezes what is
        // under it like an output
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
        let n = self.need(inf);
        if !n.feasible {
            return u32::MAX / 4;
        }
        // dead entries above the deepest output must leave (POP at least)
        let mut dead_above = 0u32;
        let (free, frozen, dead) = self.placement(st, inf);
        let mut deepest_out = None;
        for k in 0..st.len as usize {
            if is_out(st.top(k)) {
                deepest_out = Some(k);
            }
        }
        if let Some(d) = deepest_out {
            for k in 0..d {
                let c = st.top(k);
                if c != P && !is_out(c) && !self.live(inf, c) {
                    dead_above += 1;
                }
            }
        }
        let mut stuck = false;
        for c in 0..NCLASS {
            if frozen[c] && !free[c] {
                let c = c as u8;
                let used = match c {
                    _ if is_part(c) || (PROD..PROD + 4).contains(&c) => self.uses_left(inf, c) > 0,
                    _ => false,
                };
                if used {
                    stuck = true;
                }
            }
        }
        let pops = dead.saturating_sub(self.max_garbage).max(dead_above);
        let goal_len = self.goal.len() as i64;
        let slot = goal_len - st.len as i64
            + n.adds as i64
            + 2 * (n.addmods + n.mods) as i64
            + pops as i64;
        let pneed = (n.mods + n.addmods + self.goal_p).saturating_sub(inf.p_count);
        let pd = (slot.max(0) as u32).max(n.copies + n.pushes + pneed);
        // the sum's deepest entry and what is stuck (see the top), once
        let waste = if (inf.missing >= 2 || stuck) && !self.no_sum_waste {
            3
        } else {
            0
        };
        3 * n.adds + 8 * (n.mods + n.addmods) + 2 * pops + 3 * pd + waste
    }

    fn is_goal(&self, st: &Stack) -> bool {
        if (st.len as usize) < self.goal.len() {
            return false;
        }
        for (k, g) in self.goal.iter().enumerate() {
            let c = st.top(k);
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
    let i: usize = name[1..].parse().expect("lane index");
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
    let mut init = Stack {
        len: 0,
        s: [0; MAXD],
    };
    for n in init_names.iter().rev() {
        init.push(class_of_input(n, &in_b));
    }
    let mut goal = Vec::new();
    let mut goal_p = 0;
    for n in &goal_names {
        if n == "P" {
            goal.push(GoalSlot::Class(P));
            goal_p += 1;
        } else {
            let i: usize = n[1..].parse().expect("output index");
            goal.push(GoalSlot::Out(i, out_b[i]));
        }
    }
    let p = Problem {
        t,
        full: ((1u32 << t) - 1) as u8,
        init,
        goal,
        goal_p,
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
        println!("goal {}", p.is_goal(&st));
        return;
    }
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
    push(&mut buckets, h0, 0, 0);
    eprintln!("h0 {h0}");
    let mut f = 0usize;
    let mut expanded = 0usize;
    let mut last_f = 0u32;
    let max_f: u32 = std::env::var("MAXF")
        .ok()
        .map(|v| v.parse().unwrap())
        .unwrap_or(u32::MAX);
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
