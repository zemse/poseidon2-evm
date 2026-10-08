// Stack schedule for the Poseidon2 permutation (huff/schedule.ts).
//
// Results are produced on top of the stack, operands are DUPed rather than
// SWAPed, PRIME copies and other operands are pushed early so later results
// land in place on top of them, and dead values are left behind as garbage.
// Every ADD / MUL is backed by the emitter's bound check; the schedule only
// chooses when to reduce, it never asserts safety by itself.
//
// A build covers a range of steps (step 0 is the initial linear layer, step
// r + 1 is round r) so that a permutation too large for the fork's code size
// can be cut into parts.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use rayon::prelude::*;

use super::emitter::{Emitter, Id, Key, Operand};
use super::fork::Fork;
use crate::bail;
use crate::error::{Error, Result};
use crate::field::{PRIME, U256, U512, UINT256_MAX, u256, wide};
use crate::reference::permutation_steps;
use crate::round_constants::Params;
use crate::value::Op;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BuildOptions {
    /// keep the internal diag constants in memory instead of PUSH32 (t >= 4)
    pub diag_in_memory: bool,
    /// reclaim the old state slot after each element's S-box
    pub gc_external: bool,
    /// reclaim the M4 temporaries t0, t1, t2 (and t3 when it does not
    /// disturb the in-place layout)
    pub gc_m4: bool,
    /// reclaim old state slots in internal rounds as each element is replaced
    pub gc_internal: bool,
    /// reduce the internal sum with [PRIME] swap1 mod instead of pre-placing
    /// ADDMOD operands under the chain
    pub chain_swap_mod: bool,
    /// t = 4k external layer as out_b = M4(s_b + S) with S = sum of blocks
    pub external_d: bool,
    /// leave a PRIME copy under the outputs of an external layer when
    /// another external round follows
    pub prime_under_external: bool,
    /// internal rounds: keep the sum lazy and reduce every output but s0
    /// with ADDMOD (t <= 3)
    pub internal_reduce_outputs: bool,
    /// internal rounds: leave a PRIME copy under the new state only when the
    /// nearest copy would leave the reach
    pub float_prime_internal: bool,
    /// internal rounds consume the old state in place
    pub internal_consume: bool,
    /// with gc_internal, leave the garbage of the first gc_internal_from
    /// internal rounds in place as far as the depth allows
    pub gc_internal_from: usize,
    /// with diag_in_memory, keep the last diag_push32 diag constants as
    /// PUSH32 as far as the code size allows
    pub diag_push32: usize,
    /// shadow the values the reach cannot DUP in memory and hand the outputs
    /// over in memory instead of on the stack
    pub shadow: bool,
}

pub const DEFAULT_OPTIONS: BuildOptions = BuildOptions {
    diag_in_memory: false,
    gc_external: false,
    gc_m4: false,
    gc_internal: false,
    chain_swap_mod: false,
    external_d: false,
    prime_under_external: true,
    internal_reduce_outputs: false,
    float_prime_internal: false,
    internal_consume: false,
    gc_internal_from: 0,
    diag_push32: 0,
    shadow: false,
};

/// Steps [from, to) of the permutation (see permutation_steps).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub from: usize,
    pub to: usize,
}

pub fn step_count(params: &Params) -> usize {
    1 + params.rounds_f + params.rounds_p
}

/// The enabled options in declaration order, numbers with their value:
/// "gcInternal, diagPush32=6"
pub fn describe_options(opts: &BuildOptions) -> String {
    let flags = [
        ("diagInMemory", opts.diag_in_memory),
        ("gcExternal", opts.gc_external),
        ("gcM4", opts.gc_m4),
        ("gcInternal", opts.gc_internal),
        ("chainSwapMod", opts.chain_swap_mod),
        ("externalD", opts.external_d),
        ("primeUnderExternal", opts.prime_under_external),
        ("internalReduceOutputs", opts.internal_reduce_outputs),
        ("floatPrimeInternal", opts.float_prime_internal),
        ("internalConsume", opts.internal_consume),
    ];
    let mut enabled: Vec<String> = flags
        .iter()
        .filter(|(_, on)| *on)
        .map(|(k, _)| k.to_string())
        .collect();
    if opts.gc_internal_from > 0 {
        enabled.push(format!("gcInternalFrom={}", opts.gc_internal_from));
    }
    if opts.diag_push32 > 0 {
        enabled.push(format!("diagPush32={}", opts.diag_push32));
    }
    if opts.shadow {
        enabled.push("shadow".to_string());
    }
    if enabled.is_empty() {
        "none".to_string()
    } else {
        enabled.join(", ")
    }
}

#[derive(Debug, Clone)]
pub struct BuildResult {
    pub lines: Vec<String>,
    pub gas: u64,
    pub bytes: usize,
    pub max_depth: usize,
    pub max_dup: usize,
    pub swaps: usize,
    pub pops: usize,
    pub stores: usize,
    pub loads: usize,
    pub range: Range,
    /// the state ends in memory at [0, 32t) (a part that hands over, or
    /// shadow)
    pub state_in_memory: bool,
    /// memory slot of each input the entry must shadow, by index
    pub input_slots: Vec<Option<usize>>,
    /// code bytes at the end of each step of the range
    pub step_bytes: Vec<usize>,
    pub memory: usize,
}

pub const DIAG_MEMORY_BASE: usize = 0;

fn wmax() -> U512 {
    wide(UINT256_MAX)
}

fn p1() -> U256 {
    PRIME - u256(1)
}

/// Hooks of m4: the TS passes closures, every one of which pushes a PRIME
/// copy, so they are flags here.
#[derive(Default)]
struct M4Hooks {
    before_outputs: bool,
    before_last: bool,
    /// keep [o0, o1, o2, o3] in order (final round)
    keep_order: bool,
    /// dead values below the temporaries that may be collected as well
    extra_garbage: Vec<Id>,
    /// collect garbage regardless of the gcM4 option
    force_gc: bool,
}

struct Builder<'a> {
    e: Emitter,
    t: usize,
    params: &'a Params,
    opts: BuildOptions,
    range: Range,
    state_in_memory: bool,
    diag_base: usize,
    input_slots: Vec<Option<usize>>,
    step_bytes: Vec<usize>,
    state: Vec<Id>,
    /// dead values left near the top of the state by the previous round
    dead: Vec<Id>,
}

fn val(v: Id) -> Operand {
    Operand::Val(v)
}

fn inplace(v: Id) -> Operand {
    Operand::Inplace(v)
}

fn constant(c: U256, name: &str) -> Operand {
    Operand::Const(c, name.to_string())
}

fn constant_hex(c: U256) -> Operand {
    Operand::Const(c, format!("0x{}", crate::field::hex_digits(c)))
}

impl<'a> Builder<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        params: &'a Params,
        inputs: &[Vec<U256>],
        opts: BuildOptions,
        fork: Fork,
        range: Range,
        shadow: HashSet<Key>,
        permissive: bool,
        text: bool,
    ) -> Result<Builder<'a>> {
        let t = params.t;
        let state_in_memory = opts.shadow || range.to < step_count(params);
        let mut e = Emitter::new(inputs.len(), fork, shadow, permissive, text);
        // the hand-off region [0, 32t) comes first, then the diag table and
        // the shadow slots
        let diag_base = if state_in_memory {
            32 * t
        } else {
            DIAG_MEMORY_BASE
        };
        e.slot_base = diag_base
            + if opts.diag_in_memory {
                32 * (t - opts.diag_push32)
            } else {
                0
            };
        // takes: [s0, s1, ..., s(t-1), PRIME]
        let mut state = Vec::with_capacity(t);
        let mut input_slots = vec![None; t];
        for (i, slot) in input_slots.iter_mut().enumerate() {
            let vals = inputs.iter().map(|inp| inp[i]).collect();
            let v = e.alloc(crate::value::Value::new(format!("s{i}"), p1(), vals, None)?);
            e.key(v, Key::In(i));
            if e.shadows(Key::In(i)) {
                *slot = Some(e.declare(v));
            }
            state.push(v);
        }
        let mut stack = state.clone();
        stack.push(e.p);
        e.set_stack(&stack);
        e.max_depth = stack.len();
        Ok(Builder {
            e,
            t,
            params,
            opts,
            range,
            state_in_memory,
            diag_base,
            input_slots,
            step_bytes: Vec::new(),
            state,
            dead: Vec::new(),
        })
    }

    fn p(&self) -> Id {
        self.e.p
    }

    fn bound(&self, v: Id) -> U256 {
        self.e.bound(v)
    }

    fn fits(&self, a: Id, b: Id) -> bool {
        self.e.fits_add(self.bound(a), self.bound(b))
    }

    /// true when diag constant i is loaded from memory rather than pushed
    fn diag_stored(&self, i: usize) -> bool {
        self.opts.diag_in_memory && i < self.t - self.opts.diag_push32
    }

    fn diag(&self, i: usize) -> Operand {
        let d = self.params.internal_diag_minus_one[i];
        if !self.diag_stored(i) {
            return constant(d, &format!("d{i}"));
        }
        Operand::Mload(d, self.diag_base + 32 * i, format!("d{i}"))
    }

    /// Indices of values sorted by stack depth, deepest first, so that each
    /// DUP happens before the shallower ones push it further down.
    fn by_depth(&self, values: &[Id]) -> Vec<usize> {
        let mut order: Vec<(usize, usize)> = values
            .iter()
            .enumerate()
            .map(|(i, &v)| (i, self.e.find(v)))
            .collect();
        order.sort_by_key(|a| std::cmp::Reverse(a.1));
        order.into_iter().map(|(i, _)| i).collect()
    }

    /// Reclaim the slot of a dead value: the top moves into its place. With
    /// shadow, garbage the reach cannot swap is left behind.
    fn gc(&mut self, v: Id) -> Result<()> {
        let pos = self.e.find(v);
        if self.opts.shadow && (pos < 2 || pos > self.e.max_reach + 1) {
            return Ok(());
        }
        self.gc_at(pos)
    }

    fn gc_at(&mut self, pos: usize) -> Result<()> {
        if pos < 2 {
            bail!("cannot gc slot {pos}");
        }
        self.e.swap(pos - 1)?;
        self.e.pop()
    }

    /// SWAP the nearest copy of v to the top.
    fn swap_up(&mut self, v: Id) -> Result<()> {
        match self.e.find(v) {
            0 => bail!("swap-1 out of range"),
            n => self.e.swap(n - 1),
        }
    }

    // ---- building blocks ---------------------------------------------------

    /// Computes a via make_a (which must leave it on top) then a + b, either
    /// as a plain ADD with b DUPed on top, or as ADDMOD with b and PRIME
    /// placed under a beforehand so the result lands in place.
    fn add_to(
        &mut self,
        make_a: impl FnOnce(&mut Self) -> Result<Id>,
        b: Id,
        name: &str,
        reduce: bool,
    ) -> Result<Id> {
        if reduce {
            self.e.push_prime()?;
            self.e.dup(b)?;
            let a = make_a(self)?;
            let p = self.p();
            return self
                .e
                .compute(Op::Addmod, &[inplace(a), inplace(b), inplace(p)], name);
        }
        let a = make_a(self)?;
        self.e.compute(Op::Add, &[val(b), inplace(a)], name)
    }

    /// a + b from two existing values
    fn pair_add(&mut self, a: Id, b: Id, name: &str, reduce: bool) -> Result<Id> {
        if reduce || !self.fits(a, b) {
            let p = self.p();
            return self.e.compute(Op::Addmod, &[val(a), val(b), val(p)], name);
        }
        self.e.compute(Op::Add, &[val(a), val(b)], name)
    }

    /// Sum of values as a chain, reducing only when a partial sum would
    /// overflow or when the final sum would exceed cap.
    fn chain_sum(&mut self, values: &[Id], name: &str, cap: U256) -> Result<Id> {
        let n = values.len();
        if n < 2 {
            bail!("chainSum needs two values");
        }
        let cap = wide(cap);
        // plan both directions, keep the one with fewer reductions; on a tie
        // start from the last value so the deepest DUPs happen first
        let plan = |order: &[Id]| -> Vec<bool> {
            let mut reduce = Vec::with_capacity(n);
            let mut bound = wide(self.bound(order[0]));
            for (j, &v) in order.iter().enumerate().skip(1) {
                let last = j == n - 1;
                let lazy = bound + wide(self.bound(v));
                let r = lazy > wmax() || (last && lazy > cap);
                reduce.push(r);
                bound = if r { wide(p1()) } else { lazy };
            }
            reduce
        };
        let reversed: Vec<Id> = values.iter().rev().copied().collect();
        let count = |r: &[bool]| r.iter().filter(|x| **x).count();
        let plan_fwd = plan(values);
        let plan_rev = plan(&reversed);
        let (order, reduce) = if count(&plan_fwd) < count(&plan_rev) {
            (values.to_vec(), plan_fwd)
        } else {
            (reversed, plan_rev)
        };
        let p = self.p();
        if self.opts.chain_swap_mod {
            // reduce the accumulator with MOD right before an ADD would
            // overflow, and once more at the end if the cap demands it
            let mut acc = self.e.dup(order[0])?;
            for &v in &order[1..] {
                if !self.fits(acc, v) {
                    acc = self.mod_top(acc)?;
                }
                acc = self.e.compute(Op::Add, &[val(v), inplace(acc)], name)?;
            }
            if wide(self.bound(acc)) > cap {
                acc = self.mod_top(acc)?;
            }
            return Ok(acc);
        }
        // [value, PRIME] for every reduced step, last step deepest
        for j in (2..n).rev() {
            if reduce[j - 1] {
                self.e.push_prime()?;
                self.e.dup(order[j])?;
            }
        }
        let mut acc = if reduce[0] {
            self.e
                .compute(Op::Addmod, &[val(order[0]), val(order[1]), val(p)], name)?
        } else {
            self.e
                .compute(Op::Add, &[val(order[0]), val(order[1])], name)?
        };
        for j in 2..n {
            acc = if reduce[j - 1] {
                self.e.compute(
                    Op::Addmod,
                    &[inplace(acc), inplace(order[j]), inplace(p)],
                    name,
                )?
            } else {
                self.e
                    .compute(Op::Add, &[val(order[j]), inplace(acc)], name)?
            };
        }
        Ok(acc)
    }

    /// Sum of values with every operand DUPed in advance, deepest value
    /// first, so the chain runs in place and leaves nothing behind. A
    /// reduction is an ADDMOD with a PRIME copy placed under its operand
    /// while the reach allows, then a MOD of the accumulator before the ADD;
    /// the one the cap forces at the end is a MOD after it.
    fn chain_sum_in_place(&mut self, values: &[Id], name: &str, cap: U256) -> Result<Id> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Step {
            Add,
            Addmod,
            Mod,
        }
        let n = values.len();
        if n < 2 {
            bail!("chainSumInPlace needs two values");
        }
        let order: Vec<Id> = self
            .by_depth(values)
            .into_iter()
            .rev()
            .map(|i| values[i])
            .collect();
        let primes = self.e.max_reach as i64 - self.e.find(order[n - 1]) as i64;
        let cap = wide(cap);
        let mut steps = Vec::with_capacity(n);
        let mut used = 0i64;
        let mut bound = wide(self.bound(order[0]));
        for (j, &v) in order.iter().enumerate().skip(1) {
            let vb = wide(self.bound(v));
            let lazy = bound + vb;
            let last = j == n - 1;
            if lazy <= wmax() && !(last && lazy > cap) {
                steps.push(Step::Add);
                bound = lazy;
            } else if used < primes {
                steps.push(Step::Addmod);
                used += 1;
                bound = wide(p1());
            } else if lazy <= wmax() {
                steps.push(Step::Add);
                bound = lazy;
            } else {
                steps.push(Step::Mod);
                bound = wide(p1()) + vb;
            }
        }
        for j in (1..n).rev() {
            if steps[j - 1] == Step::Addmod {
                self.e.push_prime()?;
            }
            self.e.dup(order[j])?;
        }
        self.e.dup(order[0])?;
        let p = self.p();
        let mut acc = order[0];
        for j in 1..n {
            if steps[j - 1] == Step::Addmod {
                acc = self.e.compute(
                    Op::Addmod,
                    &[inplace(acc), inplace(order[j]), inplace(p)],
                    name,
                )?;
            } else {
                if steps[j - 1] == Step::Mod {
                    acc = self.mod_top(acc)?;
                }
                acc = self
                    .e
                    .compute(Op::Add, &[inplace(acc), inplace(order[j])], name)?;
            }
        }
        if wide(self.bound(acc)) > cap {
            return self.mod_top(acc);
        }
        Ok(acc)
    }

    /// v % PRIME for v on top: [PRIME] swap1 mod
    fn mod_top(&mut self, v: Id) -> Result<Id> {
        if self.e.top(0)? != v {
            bail!("modTop expects the value on top");
        }
        self.e.push_prime()?;
        self.e.swap(1)?;
        let p = self.p();
        let name = self.e.name(v).to_string();
        self.e.compute(Op::Mod, &[inplace(v), inplace(p)], &name)
    }

    /// x^5 for y sitting on top with a PRIME copy right under it, which the
    /// last MULMOD consumes together with y itself.
    fn sbox(&mut self, y: Id, name: &str) -> Result<Id> {
        let p = self.p();
        if self.e.top(0)? != y || self.e.top(1)? != p {
            bail!("sbox expects [y, P] on top");
        }
        self.e.push_prime()?;
        let x2 = self
            .e
            .compute(Op::Mulmod, &[val(y), val(y), val(p)], "x2")?;
        let x4 = self
            .e
            .compute(Op::Mulmod, &[val(x2), inplace(x2), inplace(p)], "x4")?;
        self.e
            .compute(Op::Mulmod, &[inplace(x4), inplace(y), inplace(p)], name)
    }

    /// Keeps a PRIME copy near the top so later copies stay within reach.
    fn float_prime(&mut self) -> Result<()> {
        let n = self.e.find_prime();
        // n > reach / 2 in the TS doubles
        if n == 0 || 2 * n > self.e.max_reach {
            self.e.push_prime()?;
        }
        Ok(())
    }

    // ---- external rounds ---------------------------------------------------

    /// s_i + c_i then x^5 for every element, last element first so the
    /// results end up in state order.
    fn add_constants_and_sbox(&mut self, round: usize) -> Result<()> {
        let t = self.t;
        if self.opts.gc_external {
            for v in std::mem::take(&mut self.dead) {
                let pos = self.e.find(v);
                if pos >= 2 && pos <= self.e.max_reach + 1 {
                    self.gc(v)?;
                }
            }
        }
        self.float_prime()?;
        self.e.end_line();
        let mut out = vec![0; t];
        // with shadow the results replace the old slots in place, so the
        // shallow elements go first and every slot stays within the reach of
        // the swap
        let mut order = self.by_depth(&self.state);
        if self.opts.shadow && self.opts.gc_external {
            order.reverse();
        }
        let mut memory: Vec<usize> = order
            .iter()
            .copied()
            .filter(|&i| self.e.find(self.state[i]) == 0)
            .collect();
        if !memory.is_empty() {
            // elements the consuming rounds keep in memory (the first
            // indices): loaded last, highest index first, so that the blocks
            // come out in order with block 0 on top
            let mut next: Vec<usize> = order
                .iter()
                .copied()
                .filter(|&i| i != 0 && !memory.contains(&i))
                .collect();
            memory.sort_by(|a, b| b.cmp(a));
            next.extend(memory);
            next.push(0);
            order = next;
        }
        let p = self.p();
        for i in order {
            let s = self.state[i];
            let c = self.params.round_constants[round][i];
            self.e.push_prime()?;
            let name = format!("s{i}+c");
            let y = if self.e.fits_add(self.bound(s), c) {
                self.e
                    .compute(Op::Add, &[constant(c, "c"), val(s)], &name)?
            } else {
                self.e
                    .compute(Op::Addmod, &[constant(c, "c"), val(s), val(p)], &name)?
            };
            out[i] = self.sbox(y, &format!("s{i}'"))?;
            if self.opts.gc_external {
                self.gc(s)?;
            }
            self.e.end_line();
        }
        if self.opts.gc_external {
            // PRIME copies would otherwise sit above the state and cost reach
            // in the linear layer
            while self.e.top(0)? == p {
                self.e.pop()?;
            }
            self.e.end_line();
        }
        self.state = out;
        Ok(())
    }

    /// Poseidon2 M4 on four values.
    ///   t0 = v0 + v1, t1 = v2 + v3, t2 = 2 v1 + t1, t3 = 2 v3 + t0
    ///   t4 = 4 t1 + t3, t5 = 4 t0 + t2, t6 = t3 + t5, t7 = t2 + t4
    ///   out = [t6, t5, t7, t4]
    fn m4(&mut self, v: [Id; 4], names: &[String], clean: bool, hooks: M4Hooks) -> Result<[Id; 4]> {
        let four = constant_hex(u256(4));
        let p = self.p();
        // the standard order DUPs v3 again under four temporaries
        let deepest = v.iter().map(|&x| self.e.find(x)).max().unwrap_or(0);
        let deep = deepest + 4 > self.e.max_reach;
        let (t0, t1, t2, t3);
        let mut temps: Vec<Id> = Vec::new();
        if deep {
            let d3 = self.e.compute(Op::Add, &[val(v[3]), val(v[3])], "2s3")?;
            self.e.end_line();
            let d1 = self.e.compute(Op::Add, &[val(v[1]), val(v[1])], "2s1")?;
            self.e.end_line();
            t1 = self.e.compute(Op::Add, &[val(v[2]), val(v[3])], "t1")?;
            self.e.end_line();
            t0 = self.e.compute(Op::Add, &[val(v[0]), val(v[1])], "t0")?;
            self.e.end_line();
            t3 = self
                .e
                .compute(Op::Addmod, &[val(d3), val(t0), val(p)], "t3")?;
            self.e.end_line();
            t2 = self
                .e
                .compute(Op::Addmod, &[val(d1), val(t1), val(p)], "t2")?;
            self.e.end_line();
            temps.push(d3);
            temps.push(d1);
        } else {
            t1 = self.e.compute(Op::Add, &[val(v[2]), val(v[3])], "t1")?;
            self.e.end_line();
            t0 = self.e.compute(Op::Add, &[val(v[0]), val(v[1])], "t0")?;
            self.e.end_line();
            t3 = self.add_to(
                |b| b.e.compute(Op::Add, &[val(v[3]), val(v[3])], "2s3"),
                t0,
                "t3",
                true,
            )?;
            self.e.end_line();
            t2 = self.add_to(
                |b| b.e.compute(Op::Add, &[val(v[1]), val(v[1])], "2s1"),
                t1,
                "t2",
                true,
            )?;
            self.e.end_line();
        }
        if hooks.before_outputs {
            self.e.push_prime()?;
        }
        let reduce4 = clean || !self.fits(t3, p);
        let f4 = four.clone();
        let t4 = self.add_to(
            |b| b.e.compute(Op::Mulmod, &[val(t1), f4, val(p)], "4t1"),
            t3,
            &names[3],
            reduce4,
        )?;
        self.e.end_line();
        let t7 = self.pair_add(t2, t4, &names[2], clean)?;
        self.e.end_line();
        let reduce5 = clean || !self.fits(t2, p);
        let t5 = self.add_to(
            |b| b.e.compute(Op::Mulmod, &[val(t0), four, val(p)], "4t0"),
            t2,
            &names[1],
            reduce5,
        )?;
        self.e.end_line();
        let gc = (self.opts.gc_m4 || hooks.force_gc) && !hooks.before_outputs;
        let mut extra = temps;
        extra.extend_from_slice(&hooks.extra_garbage);
        if gc && !hooks.keep_order {
            // three live outputs on top, order does not matter here
            for g in [t2, t0, t1].into_iter().chain(extra.iter().copied()) {
                self.gc(g)?;
            }
            self.e.end_line();
        }
        if hooks.before_last {
            self.e.push_prime()?;
        }
        let t6 = self.pair_add(t3, t5, &names[0], clean)?;
        self.e.end_line();
        if gc && hooks.keep_order {
            // always take the slot right under the four outputs: a uniform
            // rotation, applied a multiple of four times, restores their order
            let mut dead: HashSet<Id> = [t2, t3, t0, t1].into_iter().collect();
            dead.extend(extra.iter().copied());
            let mut run = 0;
            while run + 4 < self.e.depth() && dead.contains(&self.e.top(4 + run)?) {
                run += 1;
            }
            let count = run - run % 4;
            for _ in 0..count {
                self.gc_at(5)?;
            }
            self.e.end_line();
        } else if gc && !hooks.before_last {
            self.gc(t3)?;
            self.e.end_line();
        } else if gc {
            self.dead.push(t3);
        }
        Ok([t6, t5, t7, t4])
    }

    /// prime_under leaves a PRIME copy right under the outputs: required for
    /// the returned layout [s0', ..., s(t-1)', PRIME] at t <= 4, and used
    /// before another external round so its elements find PRIME within
    /// reach.
    fn external_matrix(&mut self, clean: bool, before_last: bool, prime_under: bool) -> Result<()> {
        let t = self.t;
        let names: Vec<String> = (0..t).map(|i| format!("s{i}'")).collect();
        let before_outputs =
            (clean && t <= 4) || (prime_under && !clean && self.opts.prime_under_external);
        if t == 2 || t == 3 {
            // circ(2, 1[, 1]): out_i = s_i + sum
            let state = self.state.clone();
            let sum = self.chain_sum(&state, "sum", UINT256_MAX)?;
            self.e.end_line();
            let mut out = vec![0; t];
            if before_outputs {
                self.e.push_prime()?;
            }
            for i in (0..t).rev() {
                if i == 0 && before_last {
                    self.e.push_prime()?;
                }
                out[i] = self.pair_add(state[i], sum, &names[i], clean)?;
                self.e.end_line();
            }
            self.state = out;
            return Ok(());
        }
        if t == 4 {
            let v = [self.state[0], self.state[1], self.state[2], self.state[3]];
            let res = self.m4(
                v,
                &names,
                clean,
                M4Hooks {
                    before_outputs,
                    before_last,
                    ..Default::default()
                },
            )?;
            self.state = res.to_vec();
            return Ok(());
        }
        let k = t / 4;
        if self.opts.external_d {
            // out_b = M4(s_b + S) with S_i = sum over blocks of s_{b,i}; S is
            // reduced so that the block inputs stay within 2p
            let mut sums = [0; 4];
            for i in (0..4).rev() {
                let column: Vec<Id> = (0..k).map(|b| self.state[4 * b + i]).collect();
                sums[i] = self.chain_sum(&column, &format!("S{i}"), p1())?;
                self.e.end_line();
            }
            let mut out = vec![0; t];
            for b in (0..k).rev() {
                let mut u = [0; 4];
                if b == 0 && before_outputs {
                    self.e.push_prime()?;
                }
                let block: Vec<Id> = self.state[4 * b..4 * b + 4].to_vec();
                for i in self.by_depth(&block) {
                    u[i] = self.pair_add(block[i], sums[i], &format!("u{}", 4 * b + i), false)?;
                    self.e.end_line();
                }
                let res = self.m4(
                    u,
                    &names[4 * b..4 * b + 4],
                    clean,
                    M4Hooks {
                        keep_order: clean,
                        extra_garbage: u.to_vec(),
                        force_gc: true,
                        before_last: b == 0 && before_last,
                        before_outputs: false,
                    },
                )?;
                out[4 * b..4 * b + 4].copy_from_slice(&res);
            }
            self.state = out;
            return Ok(());
        }
        // y = M4 per block, z_i = sum over blocks of y_{b,i},
        // out_{b,i} = y_{b,i} + z_i
        let mut y = vec![0; t];
        for b in (0..k).rev() {
            let block = [
                self.state[4 * b],
                self.state[4 * b + 1],
                self.state[4 * b + 2],
                self.state[4 * b + 3],
            ];
            let y_names: Vec<String> = (0..4).map(|i| format!("y{}", 4 * b + i)).collect();
            let res = self.m4(
                block,
                &y_names,
                false,
                M4Hooks {
                    keep_order: clean,
                    force_gc: clean,
                    ..Default::default()
                },
            )?;
            y[4 * b..4 * b + 4].copy_from_slice(&res);
        }
        let mut z = [0; 4];
        let three_p = U256::from(3u64) * PRIME;
        for i in (0..4).rev() {
            let column: Vec<Id> = (0..k).map(|b| y[4 * b + i]).collect();
            // leave room so that y + z stays lazy
            z[i] = self.chain_sum(&column, &format!("z{i}"), UINT256_MAX - three_p)?;
            self.e.end_line();
        }
        let mut out = vec![0; t];
        if before_outputs {
            self.e.push_prime()?;
        }
        if clean && !self.state_in_memory {
            // final round: outputs replace their y in ascending order so they
            // end up on top in state order once the z values are popped
            for j in 0..t {
                out[j] = self.pair_add(y[j], z[j % 4], &names[j], true)?;
                self.gc(y[j])?;
                self.e.end_line();
            }
            for _ in 0..4 {
                self.e.pop()?;
            }
            self.e.end_line();
        } else {
            for j in (0..t).rev() {
                if j == 0 && before_last {
                    self.e.push_prime()?;
                }
                out[j] = self.pair_add(y[j], z[j % 4], &names[j], clean)?;
                if self.opts.gc_external && j > 0 {
                    self.gc(y[j])?;
                }
                self.e.end_line();
            }
        }
        self.state = out;
        Ok(())
    }

    /// Writes the state to [0, 32t) for the next part or the caller.
    fn store_state(&mut self) -> Result<()> {
        self.e.comment("State to memory");
        for i in 0..self.t {
            self.e.dup(self.state[i])?;
            self.e.mstore(32 * i)?;
            self.e.end_line();
        }
        Ok(())
    }

    // ---- internal rounds ---------------------------------------------------

    fn round_start(&mut self, round: usize) -> Result<Id> {
        let s0 = self.state[0];
        let p = self.p();
        if self.e.top(0)? != s0 || self.e.top(1)? != p {
            bail!("internal round expects [s0, P] on top");
        }
        let c = self.params.round_constants[round][0];
        if !self.e.fits_add(self.bound(s0), c) {
            bail!("s0 + c does not fit");
        }
        let y = self
            .e
            .compute(Op::Add, &[constant(c, "c"), inplace(s0)], "s0+c")?;
        let x5 = self.sbox(y, "s0^5")?;
        self.e.end_line();
        Ok(x5)
    }

    /// Expects s0 on top with a PRIME copy under it (placed by the previous
    /// round) so that s0 + c lands in place for the S-box.
    fn internal_round(&mut self, round: usize, next_internal: bool) -> Result<()> {
        let t = self.t;
        let x5 = self.round_start(round)?;
        let collect =
            self.opts.gc_internal && round - self.params.rounds_f / 2 >= self.opts.gc_internal_from;
        if collect {
            // the previous round's garbage sits above the state; x5 may move
            for v in self.dead.clone() {
                let pos = self.e.find(v);
                if pos >= 2 && pos <= self.e.max_reach + 1 {
                    self.gc(v)?;
                }
            }
            self.e.end_line();
        }
        self.dead.clear();

        let mut old = vec![x5];
        old.extend_from_slice(&self.state[1..]);
        // the sum is reduced, or with internalReduceOutputs lazy as far as the
        // next round's s0 + c still fits
        let lazy = self.opts.internal_reduce_outputs;
        let cap = if lazy {
            UINT256_MAX - self.bound(x5) - p1()
        } else {
            p1()
        };
        let sum = self.chain_sum(&old, "sum", cap)?;
        self.e.end_line();

        let mut out = vec![0; t];
        // deepest element first, s0 last so it lands on the pre-placed PRIME;
        // shallowest first when the results replace the old slots in place
        // with shadow, so the swap of every slot stays within reach
        let mut others: Vec<usize> = self
            .by_depth(&old)
            .into_iter()
            .filter(|&i| i != 0)
            .collect();
        if self.opts.shadow && collect {
            others.reverse();
        }
        others.push(0);
        let p = self.p();
        for (n, &i) in others.iter().enumerate() {
            let s = old[i];
            let d = self.params.internal_diag_minus_one[i];
            if n == 1.min(t - 2) {
                // PRIME copy that ends up under the new state, within reach
                // of the next round; placed one element late so the deepest
                // DUP fits
                if !collect || self.e.find_prime() == 0 {
                    if self.opts.float_prime_internal {
                        self.float_prime()?;
                    } else {
                        self.e.push_prime()?;
                    }
                }
            }
            if i == 0 && next_internal {
                // PRIME copy under the next round's s0 + c
                self.e.push_prime()?;
            }
            let reduce = lazy && i > 0;
            let name = format!("s{i}'");
            out[i] = if d == u256(1) {
                self.pair_add(s, sum, &name, reduce)?
            } else if d == u256(2) {
                if self.fits(s, s) {
                    let wide_sum = wide(self.bound(sum)) + wide(self.bound(s)) * U512::from(2u64);
                    let r = reduce || wide_sum > wmax();
                    let dname = format!("2s{i}");
                    self.add_to(
                        |b| b.e.compute(Op::Add, &[val(s), val(s)], &dname),
                        sum,
                        &name,
                        r,
                    )?
                } else {
                    let r = reduce || !self.fits(sum, p);
                    let dname = format!("2s{i}");
                    self.add_to(
                        |b| {
                            b.e.compute(
                                Op::Mulmod,
                                &[val(s), constant_hex(u256(2)), val(p)],
                                &dname,
                            )
                        },
                        sum,
                        &name,
                        r,
                    )?
                }
            } else {
                let r = reduce || !self.fits(sum, p);
                let mname = format!("m{i}");
                let diag = self.diag(i);
                self.add_to(
                    |b| b.e.compute(Op::Mulmod, &[val(s), diag, val(p)], &mname),
                    sum,
                    &name,
                    r,
                )?
            };
            if collect && i > 0 {
                self.gc(s)?;
            }
            self.e.end_line();
        }
        self.dead.push(sum);
        self.dead.push(x5);
        self.state = out;
        Ok(())
    }

    /// Order in which the consuming round takes the elements of `old` the
    /// stack holds but s0: the one under the sum first, then slot order for
    /// the rounds in between, and for the last internal round an Eulerian
    /// circuit of the blocks (Hierholzer's algorithm) that leaves every
    /// element in the slots of its block of the external layer.
    fn consume_order(&self, old: &[Id], mem: usize, next_internal: bool) -> Result<Vec<usize>> {
        let t = self.t;
        let slots = t - 1 - mem;
        // slot s holds index s - 2 + mem in the block order
        let mut at: BTreeMap<usize, usize> = BTreeMap::new();
        for (i, &v) in old.iter().enumerate().skip(1) {
            let s = self.e.find(v);
            if s >= 3 && s <= slots + 2 {
                at.insert(s, i);
            }
        }
        if !at.contains_key(&3) {
            bail!("no element under the sum");
        }
        let order: Vec<usize> = at.keys().copied().collect();
        if next_internal {
            return Ok(order.iter().map(|s| at[s]).collect());
        }
        let block = |i: usize| i >> 2;
        let mut out: HashMap<usize, Vec<usize>> = HashMap::new();
        for &s in &order {
            out.entry(block(s - 2 + mem)).or_default().push(s);
        }
        let mut circuit: Vec<usize> = Vec::new();
        // (node, via)
        let mut stack: Vec<(usize, usize)> = vec![(block(1 + mem), 0)];
        while let Some(&(node, _)) = stack.last() {
            match out.get_mut(&node).and_then(Vec::pop) {
                Some(s) => stack.push((block(at[&s]), s)),
                None => {
                    let (_, via) = stack.pop().expect("non-empty stack");
                    circuit.push(via);
                }
            }
        }
        circuit.pop();
        circuit.reverse();
        if circuit.len() != slots {
            bail!("the blocks are not connected");
        }
        let start = circuit
            .iter()
            .position(|&s| s == 3)
            .unwrap_or(circuit.len().saturating_sub(1));
        Ok(circuit[start..]
            .iter()
            .chain(&circuit[..start])
            .map(|s| at[s])
            .collect())
    }

    /// Internal round that consumes the old state in place. Expects [s0, P]
    /// on top, the other elements right under them and a PRIME copy under
    /// the state. Beyond reach - 4 elements the first indices live in memory,
    /// loaded for the chain and their MULMOD and stored again.
    fn internal_round_consume(&mut self, round: usize, next_internal: bool) -> Result<()> {
        let t = self.t;
        let p = self.p();
        let slots = (t - 1).min(self.e.max_reach - 4);
        let mem = t - 1 - slots;
        let x5 = self.round_start(round)?;
        // the external round before leaves an M4 temporary among the state;
        // its slot takes s0^5, which is swapped back on top
        for v in std::mem::take(&mut self.dead) {
            self.gc(v)?;
        }
        if self.e.top(0)? != x5 {
            self.swap_up(x5)?;
        }
        if mem == 0 && self.e.at(t) != Some(p) {
            // the PRIME copy the rounds DUP from, in place of the slot under
            // the state
            self.e.push_prime()?;
            self.e.swap(t + 1)?;
            self.e.pop()?;
        }
        self.e.end_line();

        let mut old = vec![x5];
        old.extend_from_slice(&self.state[1..]);
        if mem > 0 {
            self.e.spill(x5)?;
        }
        self.e.push_prime()?;
        let sum = self.chain_sum_in_place(&old, "sum", p1())?;
        self.e.end_line();
        // [sum, P, s0^5, ...]: s0^5 on top of the PRIME copy, m0 lands on the
        // sum
        if mem > 0 {
            self.e.swap(1)?;
            self.e.dup(x5)?;
        } else {
            self.e.swap(2)?;
        }
        let d0 = self.diag(0);
        self.e
            .compute(Op::Mulmod, &[d0, inplace(x5), inplace(p)], "m0")?;
        self.e.end_line();

        let mut out = vec![0; t];
        let mut loads: Vec<usize> = Vec::new();
        for (i, &v) in old.iter().enumerate().skip(1) {
            let s = self.e.find(v);
            if s < 3 || s > slots + 2 {
                loads.push(i);
            }
        }
        let mut to_stack: VecDeque<usize> = loads.iter().copied().filter(|&i| i > mem).collect();
        let order = self.consume_order(&old, mem, next_internal)?;
        for (k, &i) in order.iter().enumerate() {
            let s = old[i];
            self.swap_up(s)?;
            self.e.push_prime()?;
            self.e.swap(1)?;
            self.consume_finish(i, s, sum, mem, &mut out)?;
            if i <= mem {
                // the output went to memory: one that comes back to the stack
                // takes its place on top
                let Some(j) = to_stack.pop_front() else {
                    bail!("no element to load on top");
                };
                self.consume_load(j, &old, sum, mem, &mut out)?;
            }
            if k == 0 {
                for &j in &loads {
                    if j <= mem {
                        self.consume_load(j, &old, sum, mem, &mut out)?;
                    }
                }
            }
        }
        if !to_stack.is_empty() {
            bail!("elements left to load on top");
        }
        self.e.swap(2)?;
        let (a, b) = (self.e.top(0)?, self.e.top(1)?);
        out[0] = self.e.compute(Op::Add, &[inplace(a), inplace(b)], "s0'")?;
        if mem > 0 && self.e.at(slots + 1) != Some(p) {
            // the PRIME copy the rounds DUP from, in place of the slot under
            // the region
            self.e.push_prime()?;
            self.e.swap(slots + 2)?;
            self.e.pop()?;
        }
        if next_internal {
            // PRIME copy under the next round's s0 + c
            self.e.push_prime()?;
            self.e.swap(1)?;
        }
        self.e.end_line();
        self.state = out;
        Ok(())
    }

    /// m_i + sum on top; the output of an index in memory goes there
    fn consume_finish(
        &mut self,
        i: usize,
        s: Id,
        sum: Id,
        mem: usize,
        out: &mut [Id],
    ) -> Result<()> {
        let p = self.p();
        let di = self.diag(i);
        let m = self
            .e
            .compute(Op::Mulmod, &[di, inplace(s), inplace(p)], &format!("m{i}"))?;
        out[i] = self
            .e
            .compute(Op::Add, &[val(sum), inplace(m)], &format!("s{i}'"))?;
        if i <= mem {
            self.e.spill(out[i])?;
        }
        self.e.end_line();
        Ok(())
    }

    /// an element not held by the region: loaded under a PRIME copy
    fn consume_load(
        &mut self,
        i: usize,
        old: &[Id],
        sum: Id,
        mem: usize,
        out: &mut [Id],
    ) -> Result<()> {
        self.e.push_prime()?;
        self.e.dup(old[i])?;
        self.consume_finish(i, old[i], sum, mem, out)
    }

    // ---- whole permutation -------------------------------------------------

    fn build(&mut self) -> Result<Vec<Id>> {
        let rf_half = self.params.rounds_f / 2;
        let p_end = rf_half + self.params.rounds_p;
        let total = self.params.rounds_f + self.params.rounds_p;
        let Range { from, to } = self.range;
        let has_internal = from <= p_end && to > rf_half + 1;

        if has_internal && self.diag_stored(0) {
            self.e
                .comment("Internal diag constants, loaded with MLOAD in the internal rounds");
            let mut i = 0;
            while self.diag_stored(i) {
                let d = self.params.internal_diag_minus_one[i];
                self.e.mstore_const(d, self.diag_base + 32 * i)?;
                self.e.end_line();
                i += 1;
            }
            self.e.comment("");
        }

        if from == 0 {
            self.e.next_round();
            self.e.comment("Initial linear layer");
            self.external_matrix(false, false, true)?;
            self.e.comment("");
            self.step_bytes.push(self.e.bytes);
        }

        let mut r = from.saturating_sub(1);
        while r + 1 < to {
            self.e.next_round();
            // round r + 1 belongs to this part too
            let next = r + 2 < to;
            if r < rf_half {
                self.e.comment(&format!("Round {r} (external)"));
                self.add_constants_and_sbox(r)?;
                let last = r == rf_half - 1;
                self.external_matrix(false, last && next, !last)?;
            } else if r < p_end {
                self.e.comment(&format!("Round {r} (internal)"));
                if from == r + 1 {
                    // the entry leaves [s0, ..., PRIME]: place the PRIME copy
                    // the round expects under s0
                    self.e.push_prime()?;
                    self.e.swap(1)?;
                }
                let next_internal = r < p_end - 1 && next;
                if self.opts.internal_consume {
                    self.internal_round_consume(r, next_internal)?;
                } else {
                    self.internal_round(r, next_internal)?;
                }
            } else {
                self.e.comment(&format!("Round {r} (external)"));
                self.add_constants_and_sbox(r)?;
                self.external_matrix(r == total - 1, false, true)?;
            }
            self.e.comment("");
            self.step_bytes.push(self.e.bytes);
            r += 1;
        }

        if self.state_in_memory {
            self.store_state()?;
        }
        self.e.end_line();
        Ok(self.state.clone())
    }
}

/// Builds steps [range.from, range.to) and checks the emitted stream against
/// the reference on every input. With shadow a permissive pass first finds
/// the values DUPed out of reach, then the real pass shadows them. `text`
/// records the lines (the option search only needs the numbers).
pub fn build_permutation(
    params: &Params,
    inputs: &[Vec<U256>],
    opts: &BuildOptions,
    fork: Fork,
    range: Range,
    text: bool,
) -> Result<BuildResult> {
    let mut shadow = HashSet::new();
    if opts.shadow {
        let mut probe = Builder::new(params, inputs, *opts, fork, range, shadow, true, false)?;
        probe.build()?;
        shadow = std::mem::take(&mut probe.e.needed);
    }
    let mut b = Builder::new(params, inputs, *opts, fork, range, shadow, false, text)?;
    let outputs = b.build()?;
    let e = &b.e;
    let t = params.t;
    let is_final = range.to == step_count(params);

    if !b.state_in_memory {
        // the outputs must sit on top in state order and be clean
        for (i, &out) in outputs.iter().enumerate() {
            if e.at(i) != Some(out) {
                bail!("output {i} is not at slot {}", i + 1);
            }
            if e.bound(out) >= PRIME {
                bail!("output {i} is not clean");
            }
        }
        if t <= 4 && e.at(t) != Some(e.p) {
            bail!("PRIME expected under outputs");
        }
    } else if is_final {
        for (i, &out) in outputs.iter().enumerate() {
            if e.bound(out) >= PRIME {
                bail!("output {i} is not clean");
            }
        }
    }

    // concrete check of the emitted stream against the reference permutation
    // (a part that hands over leaves lazy values, the next entry reduces
    // them)
    for (k, input) in inputs.iter().enumerate() {
        let want = permutation_steps(params, input, range.from, range.to);
        for (i, &out) in outputs.iter().enumerate() {
            let v = e.value(out).vals[k];
            let got = if is_final { v } else { v.reduce_mod(PRIME) };
            if got != want[i] {
                bail!("vector {k} output {i} mismatch");
            }
        }
    }

    let e = b.e;
    Ok(BuildResult {
        lines: e.lines,
        gas: e.gas,
        bytes: e.bytes,
        max_depth: e.max_depth,
        max_dup: e.max_dup,
        swaps: e.swaps,
        pops: e.pops,
        stores: e.stores,
        loads: e.loads,
        range,
        state_in_memory: b.state_in_memory,
        input_slots: b.input_slots,
        step_bytes: b.step_bytes,
        memory: e.memory,
    })
}

/// Largest n in [0, hi] accepted by ok, which must be monotone (true up to
/// some n, false after) and true for 0.
pub fn largest(hi: usize, mut ok: impl FnMut(usize) -> bool) -> usize {
    let mut lo = 0;
    let mut hi = hi;
    while lo < hi {
        let mid = (lo + hi).div_ceil(2);
        if ok(mid) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}

#[derive(Debug, Clone)]
pub struct Best {
    pub result: BuildResult,
    pub opts: BuildOptions,
}

/// The option combinations that make sense for t, in the TS enumeration
/// order.
fn candidates(t: usize, shadow: bool) -> Vec<BuildOptions> {
    let bools = [false, true];
    let only_false: &[bool] = &[false];
    let pick = |cond: bool| -> &[bool] { if cond { &bools } else { only_false } };
    let mut list = Vec::new();
    for &diag_in_memory in pick(t >= 4) {
        for &gc_external in &bools {
            for &gc_m4 in pick(t >= 4) {
                for &gc_internal in &bools {
                    for &chain_swap_mod in &bools {
                        for &external_d in pick(t >= 8) {
                            for &prime_under_external in &bools {
                                for &internal_reduce_outputs in pick(t <= 3) {
                                    for &float_prime_internal in &bools {
                                        // the consuming round neither collects
                                        // garbage nor floats PRIME copies
                                        let consume =
                                            t >= 8 && !gc_internal && !float_prime_internal;
                                        for &internal_consume in pick(consume) {
                                            list.push(BuildOptions {
                                                diag_in_memory,
                                                gc_external,
                                                gc_m4,
                                                gc_internal,
                                                chain_swap_mod,
                                                external_d,
                                                prime_under_external,
                                                internal_reduce_outputs,
                                                float_prime_internal,
                                                internal_consume,
                                                gc_internal_from: 0,
                                                diag_push32: 0,
                                                shadow,
                                            });
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    list
}

/// What the search learns from one candidate: whether its first build
/// succeeded, and its final options and gas or the reason it fails.
struct Outcome {
    built: bool,
    result: std::result::Result<(BuildOptions, u64), String>,
}

/// Tries the option combinations that make sense for t and returns the
/// cheapest build of the range that stays within reach, depth and code size,
/// or None when the schedules that build are too large or too deep. The
/// candidates are evaluated in parallel; the winner is the first strictly
/// cheaper one in enumeration order, as in the TS, and is rebuilt with its
/// lines. Fails when nothing builds at all.
pub fn build_best(
    params: &Params,
    inputs: &[Vec<U256>],
    max_bytes: usize,
    fork: Fork,
    range: Range,
) -> Result<Option<Best>> {
    let build = |opts: &BuildOptions| build_permutation(params, inputs, opts, fork, range, false);
    let attempt = |opts: &BuildOptions| build(opts).ok();
    let evaluate = |opts: &BuildOptions| -> Outcome {
        let mut opts = *opts;
        let mut result = match build(&opts) {
            Ok(r) => r,
            Err(err) => {
                return Outcome {
                    built: false,
                    result: Err(err.0),
                };
            }
        };
        let mut finish = || -> std::result::Result<(BuildOptions, u64), String> {
            if result.max_depth <= 1000 {
                if opts.gc_internal && fork.reach > 16 {
                    let gc_internal_from = largest(params.rounds_p, |n| {
                        attempt(&BuildOptions {
                            gc_internal_from: n,
                            ..opts
                        })
                        .is_some_and(|r| r.max_depth <= 1000)
                    });
                    opts.gc_internal_from = gc_internal_from;
                    result = build(&opts).map_err(|e| e.0)?;
                }
                if opts.diag_in_memory && result.bytes <= max_bytes {
                    let diag_push32 = largest(params.t, |n| {
                        attempt(&BuildOptions {
                            diag_push32: n,
                            ..opts
                        })
                        .is_some_and(|r| r.bytes <= max_bytes)
                    });
                    opts.diag_push32 = diag_push32;
                    result = build(&opts).map_err(|e| e.0)?;
                }
            }
            if result.max_depth > 1000 {
                return Err(format!("depth {}", result.max_depth));
            }
            if result.bytes > max_bytes {
                return Err(format!("{} bytes", result.bytes));
            }
            Ok((opts, result.gas))
        };
        Outcome {
            built: true,
            result: finish(),
        }
    };

    let mut best: Option<(BuildOptions, u64)> = None;
    let mut failures: Vec<String> = Vec::new();
    let search = |list: Vec<BuildOptions>,
                  best: &mut Option<(BuildOptions, u64)>,
                  failures: &mut Vec<String>|
     -> usize {
        let outcomes: Vec<Outcome> = list.par_iter().map(evaluate).collect();
        let mut built = 0;
        for outcome in outcomes {
            if outcome.built {
                built += 1;
            }
            match outcome.result {
                Ok((opts, gas)) => {
                    if best.is_none_or(|(_, g)| gas < g) {
                        *best = Some((opts, gas));
                    }
                }
                Err(reason) => failures.push(reason),
            }
        }
        built
    };
    let mut built = search(candidates(params.t, false), &mut best, &mut failures);
    if built == 0 {
        built += search(candidates(params.t, true), &mut best, &mut failures);
    }
    if built == 0 {
        let mut reasons: Vec<(String, usize)> = Vec::new();
        for f in &failures {
            match reasons.iter_mut().find(|(r, _)| r == f) {
                Some((_, n)) => *n += 1,
                None => reasons.push((f.clone(), 1)),
            }
        }
        let summary: Vec<String> = reasons.iter().map(|(r, n)| format!("{n}x {r}")).collect();
        return Err(Error(format!(
            "no schedule works for t = {} on {} ({} option combinations tried):\n  {}",
            params.t,
            fork.name,
            failures.len(),
            summary.join("\n  ")
        )));
    }
    match best {
        Some((opts, gas)) => {
            let result = build_permutation(params, inputs, &opts, fork, range, true)?;
            assert_eq!(
                result.gas, gas,
                "the rebuilt winner costs what the search measured"
            );
            Ok(Some(Best { result, opts }))
        }
        None => Ok(None),
    }
}
