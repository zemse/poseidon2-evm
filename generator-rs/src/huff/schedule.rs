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
//
// The consuming internal rounds rotate the stack layout by one slot per
// round, so after `period` rounds (the elements the stack holds) the layout
// is back where it started and the bounds are a fixed point after the first
// round. With shared_body the steady internal rounds (all but the first and
// the last of the range) are therefore emitted once as a body of one period
// that every call reaches by JUMP with its return label in memory and its
// round constants CODECOPYed from a code table to a memory scratch; a last
// call of fewer rounds leaves the body at a mid exit. With consume_group the
// round consumes the elements in sub-chains of that many slots, each
// rotating on its own (one SWAP more per chain), so the period is the
// chains' lcm and the body shorter, which is what lets a part hold its
// rounds within the legacy code size.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use rayon::prelude::*;

use super::emitter::{Emitter, Id, Key, Operand, Table};
use super::fork::Fork;
use super::render::memory_gas;
use super::templates::{
    BlockKind, Internal3Kind, Template, TemplateKind, blocks, hash_forms, internal3,
    internal3_periodic, internal4, linear_final4, round4, templates,
};
use crate::bail;
use crate::error::{Error, Result};
use crate::field::{PRIME, U256, U512, UINT256_MAX, u256, wide};
use crate::reference::{permutation_steps, sponge_state};
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
    /// nearest copy would leave the reach; t = 2 with internal_mul3 omits
    /// backing copies when false
    pub float_prime_internal: bool,
    /// internal rounds consume the old state in place
    pub internal_consume: bool,
    /// with internal_consume, stack the PRIME copies of a round under m0 at
    /// once so each swapped element lands on its own instead of getting one
    /// swapped under it
    pub prime_stack: bool,
    /// with gc_internal, leave the garbage of the first gc_internal_from
    /// internal rounds in place as far as the depth allows
    pub gc_internal_from: usize,
    /// with gc_m4, leave the M4 temporaries of the first gc_m4_from external
    /// layers in place as far as the depth allows
    pub gc_m4_from: usize,
    /// with diag_in_memory, keep the last diag_push32 diag constants as
    /// PUSH32 as far as the code size allows
    pub diag_push32: usize,
    /// shadow the values the reach cannot DUP in memory and hand the outputs
    /// over in memory instead of on the stack
    pub shadow: bool,
    /// with internal_consume, run the steady internal rounds through one
    /// body of a period reached by JUMP (see above)
    pub shared_body: bool,
    /// with shared_body, keep the first body_inline steady rounds inline as
    /// far as the code size allows
    pub body_inline: usize,
    /// with internal_consume, consume the elements of a round that leads to
    /// another in sub-chains of consume_group slots (the last takes the
    /// rest), each rotating on its own, for a shorter body (0: one chain)
    pub consume_group: usize,
    /// with internal_consume, the elements the stack holds when the reach
    /// cannot hold them all (0: reach - 4); each one more takes a slot of
    /// the sum chain's PRIME copies and saves its loads and store
    pub consume_slots: usize,
    /// external rounds (t <= 4) and, with external_d, the M4 of every block
    /// as the stack programs of templates.rs, from restricted searches:
    /// the lanes are S-boxed in place and the linear layer consumes its
    /// operands, so a round leaves at most one dead value and a block none
    pub external_template: bool,
    /// t = 4 internal rounds as the stack program of templates.rs
    /// (internal4): one dead value a round instead of five, for three SWAPs;
    /// t = 3 uses periodic bound-checked reductions, with internal3 fallbacks
    pub internal_template: bool,
    /// t = 2 internal rounds: s1' = (3 s1 mod P) + s0^5 and
    /// s0' = 2 s0^5 + s1 lazy, instead of a shared lazy sum
    /// (one op less per round, after the first generic bridge)
    pub internal_mul3: bool,
    /// store PRIME in memory once and load it (PUSH, MLOAD) where no copy
    /// is within reach instead of PUSH32 (3 gas more, 30 bytes less)
    pub prime_in_memory: bool,
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
    prime_stack: false,
    gc_internal_from: 0,
    gc_m4_from: 0,
    diag_push32: 0,
    shadow: false,
    shared_body: false,
    body_inline: 0,
    consume_group: 0,
    consume_slots: 0,
    external_template: false,
    internal_template: false,
    internal_mul3: false,
    prime_in_memory: false,
};

/// Steps [from, to) of the permutation (see permutation_steps).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub from: usize,
    pub to: usize,
}

/// What a build takes and what its caller reads: the bound of every input
/// (clean, PRIME - 1, by default), whether the inputs sit in calldata at
/// [0, 32t) as the stack holds them (a part after the first, whose entry
/// loads them as they are: a shadowed input is then loaded from there
/// instead of a memory slot the entry fills) and the outputs the caller
/// uses (all by default). The t = 4 hash entry starts its rounds from the
/// lazy values of its round 0 and reads s0' alone, so its last linear layer
/// computes only that row (final_round_row0).
#[derive(Debug, Clone, Default)]
pub struct Boundary {
    pub bounds: Option<Vec<U256>>,
    pub calldata: bool,
    pub live: Option<Vec<usize>>,
    /// the inputs as [s0, PRIME, s1, ...] rather than over the PRIME copy
    pub prime_second: bool,
    /// with prime_second, a PRIME copy this many dead values below them
    pub prime_below: Option<usize>,
}

/// A part hands its state over below 2p: an internal round leaves m_i + sum
/// with both reduced, and any output above the bound is reduced before it
/// is stored. The next part takes the words as they are, within that bound.
pub fn handover_bound() -> U256 {
    PRIME * u256(2) - u256(1)
}
pub const HANDOVER_BOUND_TEXT: &str = "2p";

/// the boundary of part `from` of a split: lazy inputs from calldata
pub fn part_boundary(t: usize, from: usize) -> Boundary {
    if from == 0 {
        return Boundary::default();
    }
    Boundary {
        bounds: Some(vec![handover_bound(); t]),
        calldata: true,
        live: None,
        prime_second: false,
        prime_below: None,
    }
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
        ("primeStack", opts.prime_stack),
    ];
    let mut enabled: Vec<String> = flags
        .iter()
        .filter(|(_, on)| *on)
        .map(|(k, _)| k.to_string())
        .collect();
    if opts.gc_internal_from > 0 {
        enabled.push(format!("gcInternalFrom={}", opts.gc_internal_from));
    }
    if opts.gc_m4_from > 0 {
        enabled.push(format!("gcM4From={}", opts.gc_m4_from));
    }
    if opts.diag_push32 > 0 {
        enabled.push(format!("diagPush32={}", opts.diag_push32));
    }
    if opts.shadow {
        enabled.push("shadow".to_string());
    }
    if opts.shared_body {
        enabled.push("sharedBody".to_string());
    }
    if opts.body_inline > 0 {
        enabled.push(format!("bodyInline={}", opts.body_inline));
    }
    if opts.consume_group > 0 {
        enabled.push(format!("consumeGroup={}", opts.consume_group));
    }
    if opts.consume_slots > 0 {
        enabled.push(format!("consumeSlots={}", opts.consume_slots));
    }
    if opts.external_template {
        enabled.push("externalTemplate".to_string());
    }
    if opts.internal_template {
        enabled.push("internalTemplate".to_string());
    }
    if opts.internal_mul3 {
        enabled.push("internalMul3".to_string());
    }
    if opts.prime_in_memory {
        enabled.push("primeInMemory".to_string());
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
    /// the round constants of the shared body's calls
    pub tables: Vec<Table>,
}

pub const DIAG_MEMORY_BASE: usize = 0;

/// The internal rounds of the range but its first and last, whose code
/// differs (the entry's PRIME copy, the final round's layout): the ones the
/// shared body may run, from round `first`.
pub fn steady_rounds(params: &Params, range: Range) -> (usize, usize) {
    let rf_half = params.rounds_f / 2;
    let first = (range.from as i64 - 1).max(rf_half as i64) + 1;
    let last = (range.to as i64 - 2).min((rf_half + params.rounds_p) as i64 - 1) - 1;
    (first as usize, (last - first + 1).max(0) as usize)
}

/// elements the consuming round holds on the stack: consume_slots, or as
/// many as leave 4 slots of the reach ([output, sum, m0] and a PRIME copy)
pub fn held_slots(t: usize, reach: usize, consume_slots: usize) -> usize {
    if consume_slots > 0 {
        return consume_slots.min(t - 1);
    }
    (t - 1).min(reach - 4)
}

/// elements the consuming round holds on the stack: the rounds the layout
/// takes to rotate back, the length of the shared body; in sub-chains of
/// `group` slots each rotates on its own, so the lcm of their lengths
pub fn body_period(params: &Params, fork: &Fork, consume_slots: usize, group: usize) -> usize {
    let slots = held_slots(params.t, fork.reach, consume_slots);
    if group == 0 || group >= slots {
        return slots;
    }
    let rem = slots % group;
    if rem == 0 { group } else { lcm(group, rem) }
}

fn lcm(a: usize, b: usize) -> usize {
    fn gcd(x: usize, y: usize) -> usize {
        if y == 0 { x } else { gcd(y, x % y) }
    }
    a / gcd(a, b) * b
}

/// The sub-chain lengths worth trying, by the period they give, shortest
/// first: the one with the fewest chains per period (the chains cost a
/// SWAP each, the calls of a shorter body their overhead)
pub fn group_candidates(params: &Params, fork: &Fork, consume_slots: usize) -> Vec<usize> {
    let slots = body_period(params, fork, consume_slots, 0);
    let mut by_period: BTreeMap<usize, usize> = BTreeMap::new();
    for group in 1..slots {
        let period = body_period(params, fork, consume_slots, group);
        if period >= slots {
            continue;
        }
        match by_period.get(&period) {
            Some(&prev) if slots.div_ceil(group) >= slots.div_ceil(prev) => {}
            _ => {
                by_period.insert(period, group);
            }
        }
    }
    by_period.into_values().collect()
}

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
    vectors: usize,
    state_in_memory: bool,
    diag_base: usize,
    /// the shared body's scratch: the round constants of a call, then the
    /// return offsets of its mid exit and of its end
    rc_base: usize,
    period: usize,
    input_slots: Vec<Option<usize>>,
    step_bytes: Vec<usize>,
    state: Vec<Id>,
    /// dead values left near the top of the state by the previous round
    dead: Vec<Id>,
    /// the outputs the caller reads, in state order (all when None)
    live: Option<Vec<usize>>,
    /// external layers built so far
    layers: usize,
    /// what the S-boxes of a template add in place of the round constants
    /// (the hash entry's round 0, Builder::hash_round0)
    lane_constants: Option<Vec<U256>>,
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
        boundary: &Boundary,
    ) -> Result<Builder<'a>> {
        let t = params.t;
        let state_in_memory = opts.shadow || range.to < step_count(params);
        let mut e = Emitter::new(inputs.len(), fork, shadow, permissive, text);
        // the hand-off region [0, 32t) comes first, then the diag table, the
        // body scratch and the shadow slots
        let diag_base = if state_in_memory {
            32 * t
        } else {
            DIAG_MEMORY_BASE
        };
        let rc_base = diag_base
            + if opts.diag_in_memory {
                32 * (t - opts.diag_push32)
            } else {
                0
            };
        let period = body_period(params, &fork, opts.consume_slots, opts.consume_group);
        e.slot_base = rc_base
            + if opts.shared_body {
                32 * (period + 2)
            } else {
                0
            };
        if opts.prime_in_memory {
            e.slot_base += 32;
        }
        // takes: [s0, s1, ..., s(t-1), PRIME]
        let mut state = Vec::with_capacity(t);
        let mut input_slots = vec![None; t];
        for (i, slot) in input_slots.iter_mut().enumerate() {
            let vals = inputs.iter().map(|inp| inp[i]).collect();
            let bound = boundary.bounds.as_ref().map_or(p1(), |b| b[i]);
            let v = e.alloc(crate::value::Value::new(
                format!("s{i}"),
                bound,
                vals,
                None,
            )?);
            e.key(v, Key::In(i));
            if e.shadows(Key::In(i)) {
                if boundary.calldata {
                    e.declare_calldata(v, 32 * i);
                } else {
                    *slot = Some(e.declare(v));
                }
            }
            state.push(v);
        }
        let mut stack = state.clone();
        if boundary.prime_second {
            stack.insert(1, e.p);
            if let Some(dead) = boundary.prime_below {
                for k in 0..dead {
                    let vals = vec![U256::ZERO; inputs.len()];
                    let g = crate::value::Value::new(format!("g{k}"), U256::ZERO, vals, None)?;
                    stack.push(e.alloc(g));
                }
                stack.push(e.p);
            }
        } else {
            stack.push(e.p);
        }
        e.set_stack(&stack);
        e.max_depth = stack.len();
        Ok(Builder {
            e,
            t,
            params,
            opts,
            range,
            vectors: inputs.len(),
            state_in_memory,
            diag_base,
            rc_base,
            period,
            input_slots,
            step_bytes: Vec::new(),
            state,
            dead: Vec::new(),
            live: boundary.live.clone(),
            layers: 0,
            lane_constants: None,
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
    /// reduction (where a partial sum would overflow or the final one exceed
    /// cap) is an ADDMOD with a PRIME copy placed under its operand while
    /// the reach of the later DUPs allows (loads from memory have none), the
    /// first steps first, else an ADDMOD with a copy DUPed on top and
    /// swapped under the accumulator (3 gas more, no slot).
    fn chain_sum_in_place(&mut self, values: &[Id], name: &str, cap: U256) -> Result<Id> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Step {
            Add,
            Addmod,
            AddmodTop,
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
        let cap = wide(cap);
        let mut steps = Vec::with_capacity(n);
        let mut bound = wide(self.bound(order[0]));
        for (j, &v) in order.iter().enumerate().skip(1) {
            let lazy = bound + wide(self.bound(v));
            let last = j == n - 1;
            if lazy <= wmax() && !(last && lazy > cap) {
                steps.push(Step::Add);
                bound = lazy;
            } else {
                steps.push(Step::AddmodTop);
                bound = wide(p1());
            }
        }
        // the slots each DUPed operand has left: order[i] is DUPed after
        // the n - 1 - i operands below it and the copies placed under them
        let mut room: Vec<Option<usize>> = (0..n)
            .map(|i| {
                let at = self.e.find(order[i]);
                let index = at + (n - 1 - i);
                (at > 0 && index <= self.e.max_reach).then(|| self.e.max_reach - index)
            })
            .collect();
        for j in 1..n {
            if steps[j - 1] == Step::AddmodTop && room[..j].iter().all(|r| r.is_none_or(|r| r > 0))
            {
                steps[j - 1] = Step::Addmod;
                for r in room[..j].iter_mut().flatten() {
                    *r -= 1;
                }
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
            acc = match steps[j - 1] {
                Step::Add => self
                    .e
                    .compute(Op::Add, &[inplace(acc), inplace(order[j])], name)?,
                Step::Addmod => self.e.compute(
                    Op::Addmod,
                    &[inplace(acc), inplace(order[j]), inplace(p)],
                    name,
                )?,
                Step::AddmodTop => {
                    self.e.push_prime()?;
                    self.e.swap(2)?;
                    self.e.compute(
                        Op::Addmod,
                        &[inplace(order[j]), inplace(acc), inplace(p)],
                        name,
                    )?
                }
            };
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

    /// x^5 for y on top without a PRIME copy under it: the copies are DUPed
    /// and SWAPped under the operands instead, same gas as sbox with its
    /// copy pre-placed.
    fn sbox_no_prime(&mut self, y: Id, name: &str) -> Result<Id> {
        let p = self.p();
        if self.e.top(0)? != y {
            bail!("sboxNoPrime expects y on top");
        }
        self.e.push_prime()?;
        let x2 = self
            .e
            .compute(Op::Mulmod, &[val(y), val(y), inplace(p)], "x2")?;
        self.e.push_prime()?;
        self.e.swap(1)?;
        let x4 = self
            .e
            .compute(Op::Mulmod, &[val(x2), inplace(x2), inplace(p)], "x4")?;
        self.e.push_prime()?;
        self.e.swap(2)?;
        self.e
            .compute(Op::Mulmod, &[inplace(y), inplace(x4), inplace(p)], name)
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

    // ---- external rounds from templates ------------------------------------

    /// The template of a list whose layout the stack holds for `inputs` (the
    /// s<i> of the layout), if any.
    fn template(&self, list: &'static [Template], inputs: &[Id]) -> Option<&'static Template> {
        let p = self.p();
        list.iter().find(|tpl| {
            tpl.init
                .split(',')
                .enumerate()
                .all(|(k, name)| match self.e.at(k) {
                    None => false,
                    Some(v) => {
                        if name == "P" {
                            v == p
                        } else {
                            let i: usize = name[1..].parse().expect("state index");
                            v == inputs[i]
                        }
                    }
                })
        })
    }

    /// Replays the stack program of a template (templates.rs) on `inputs`;
    /// `round` names the round constants of its lanes. Returns the values
    /// its moves name s<i>', as names[i], which end in the template's final
    /// layout.
    fn run_template(
        &mut self,
        list: &'static [Template],
        inputs: &[Id],
        names: &[String],
        round: Option<usize>,
    ) -> Result<Vec<Id>> {
        let Some(tpl) = self.template(list, inputs) else {
            bail!("no template fits the layout");
        };
        let p = self.p();
        let mut out: Vec<Option<Id>> = vec![None; names.len()];
        for mv in tpl.ops.split(' ') {
            if let Some(n) = mv.strip_prefix("dup") {
                let n: usize = n.parse().expect("dup slot");
                let v = self.e.top(n - 1)?;
                self.e.dup(v)?;
            } else if let Some(n) = mv.strip_prefix("swap") {
                let n: usize = n.parse().expect("swap slot");
                self.e.swap(n)?;
            } else if mv == "P" {
                self.e.push_prime()?;
            } else if let Some(i) = mv.strip_prefix('d').and_then(|i| i.parse::<usize>().ok()) {
                let d = self.params.internal_diag_minus_one[i];
                if self.diag_stored(i) {
                    self.e.mload(d, self.diag_base + 32 * i, &format!("d{i}"))?;
                } else {
                    self.e.push(d, Some(&format!("d{i}")))?;
                }
            } else if mv == "4" {
                self.e.push(u256(4), None)?;
            } else if mv == "pop" {
                self.e.pop()?;
            } else if let Some((op, name)) = mv.split_once('=') {
                let op = match op {
                    "add" => Op::Add,
                    "addmod" => Op::Addmod,
                    "mulmod" => Op::Mulmod,
                    _ => bail!("unknown template move {mv}"),
                };
                let mut operands = vec![inplace(self.e.top(0)?), inplace(self.e.top(1)?)];
                if op != Op::Add {
                    operands.push(inplace(p));
                }
                let index = name
                    .strip_prefix('s')
                    .and_then(|r| r.strip_suffix('\''))
                    .and_then(|i| i.parse::<usize>().ok());
                let name = match index {
                    Some(i) => names[i].as_str(),
                    None => name,
                };
                let v = self.e.compute(op, &operands, name)?;
                if let Some(i) = index {
                    out[i] = Some(v);
                }
                self.e.end_line();
            } else if let Some(lane) = mv.strip_prefix("sbox") {
                let Some(round) = round else {
                    bail!("sbox needs a round");
                };
                let (i, prime_under) = match lane.strip_suffix('n') {
                    Some(i) => (i, false),
                    None => (lane, true),
                };
                let i: usize = i.parse().expect("lane");
                self.template_lane(inputs, i, round, prime_under)?;
                self.e.end_line();
            } else {
                bail!("unknown template move {mv}");
            }
        }
        self.e.end_line();
        let mut res = Vec::with_capacity(names.len());
        for (i, v) in out.into_iter().enumerate() {
            match v {
                Some(v) => res.push(v),
                None => bail!("template leaves s{i}' unnamed"),
            }
        }
        Ok(res)
    }

    /// An external round of t <= 4 from its template. Unmatched t = 4
    /// layouts use separate S-boxes and a linear template or generic M4.
    fn external_template(&mut self, kind: TemplateKind, round: Option<usize>) -> Result<()> {
        let names: Vec<String> = (0..self.t).map(|i| format!("s{i}'")).collect();
        if self.t == 4 {
            let full = templates(4, kind);
            let inputs = self.state.clone();
            if self.template(full, &inputs).is_some() {
                self.state = self.run_template(full, &inputs, &names, round)?;
                return Ok(());
            }
            if let Some(round) = round {
                self.add_constants_and_sbox(round)?;
            }
            let linear = match kind {
                TemplateKind::Final => linear_final4(),
                TemplateKind::Exit => blocks(BlockKind::Exit),
                _ => blocks(BlockKind::Block),
            };
            let inputs = self.state.clone();
            if self.template(linear, &inputs).is_some() {
                self.state = self.run_template(linear, &inputs, &names, None)?;
            } else {
                self.external_matrix(
                    kind == TemplateKind::Final,
                    kind == TemplateKind::Exit,
                    kind != TemplateKind::Exit,
                )?;
            }
            return Ok(());
        }
        let inputs = self.state.clone();
        self.state = self.run_template(templates(self.t, kind), &inputs, &names, round)?;
        Ok(())
    }

    /// s_i + c then x^5 for lane i on top, consumed in place; with
    /// prime_under the PRIME copy under it is consumed as well. A lazy input
    /// that does not fit the ADD takes an ADDMOD with that copy (or a
    /// swapped-in one) and the S-box without it, leaving the same stack.
    fn template_lane(
        &mut self,
        inputs: &[Id],
        i: usize,
        round: usize,
        prime_under: bool,
    ) -> Result<Id> {
        let p = self.p();
        let s = inputs[i];
        if self.e.top(0)? != s {
            bail!("template expects s{i} on top");
        }
        if prime_under && self.e.top(1)? != p {
            bail!("template expects PRIME under s{i}");
        }
        let c = match &self.lane_constants {
            Some(k) => k[i],
            None => self.params.round_constants[round][i],
        };
        let name = format!("s{i}+c");
        let mut prime_under = prime_under;
        let y = if self.e.fits_add(self.bound(s), c) {
            self.e
                .compute(Op::Add, &[constant(c, "c"), inplace(s)], &name)?
        } else {
            if !prime_under {
                self.e.push_prime()?;
                self.e.swap(1)?;
            }
            prime_under = false;
            self.e.compute(
                Op::Addmod,
                &[constant(c, "c"), inplace(s), inplace(p)],
                &name,
            )?
        };
        let xname = format!("x{i}");
        if prime_under {
            self.sbox(y, &xname)
        } else {
            self.sbox_no_prime(y, &xname)
        }
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
        let gc_m4 = self.opts.gc_m4 && self.layers > self.opts.gc_m4_from;
        let gc = (gc_m4 || hooks.force_gc) && !hooks.before_outputs;
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
        self.layers += 1;
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
                if self.opts.external_template {
                    // the block's inputs on top in order, consumed by its
                    // template
                    for i in (0..4).rev() {
                        u[i] =
                            self.pair_add(block[i], sums[i], &format!("u{}", 4 * b + i), false)?;
                        self.e.end_line();
                    }
                    let kind = if clean {
                        BlockKind::Final
                    } else if b == 0 && before_last {
                        BlockKind::Exit
                    } else {
                        BlockKind::Block
                    };
                    let res =
                        self.run_template(blocks(kind), &u, &names[4 * b..4 * b + 4], None)?;
                    out[4 * b..4 * b + 4].copy_from_slice(&res);
                    continue;
                }
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

    /// Last round when the caller reads s0' alone (t = 4): row 0 of M4 on
    /// the S-box outputs, s0' = 5 x0 + 7 x1 + x2 + 3 x3, taken straight from
    /// the S-boxes instead of the M4 temporaries. A PRIME copy for the final
    /// MOD goes down first; each lane, last first, is S-boxed on top of its
    /// coefficient and a PRIME copy, MULMODed by the coefficient in place
    /// and ADDed to the row so far, which stays under 4p.
    fn final_round_row0(&mut self, round: usize) -> Result<()> {
        if self.t != 4 {
            bail!("finalRoundRow0 is t = 4 only");
        }
        let row = [5u64, 7, 1, 3];
        let p = self.p();
        self.e.push_prime()?;
        let mut acc: Option<Id> = None;
        for i in (0..4).rev() {
            let s = self.state[i];
            let k = row[i];
            let mut coeff = None;
            if k != 1 {
                self.e.push_prime()?;
                coeff = Some(self.e.push(u256(k), None)?);
            }
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
            let mut term = self.sbox(y, &format!("s{i}'"))?;
            if let Some(coeff) = coeff {
                term = self.e.compute(
                    Op::Mulmod,
                    &[inplace(term), inplace(coeff), inplace(p)],
                    &format!("{k}s{i}'"),
                )?;
            }
            acc = Some(match acc {
                Some(acc) => self
                    .e
                    .compute(Op::Add, &[inplace(term), inplace(acc)], "row0")?,
                None => term,
            });
            self.e.end_line();
        }
        let acc = acc.expect("four lanes");
        let out = self
            .e
            .compute(Op::Mod, &[inplace(acc), inplace(p)], "s0'")?;
        self.e.end_line();
        self.state = vec![out];
        Ok(())
    }

    /// Round 0 of the hash entry for n inputs, from the PRIME copy SETUP
    /// leaves. The other lanes are the sponge constants (zeros, then the
    /// capacity n << 64), so the initial linear layer and the constant
    /// addition fold into y_i = p_i + K_i, p_i = sum_j M4[i][j] in_j and
    /// K_i = M4[i][3] (n << 64) + c_i. The forms program of
    /// templates::hash_forms loads the inputs and leaves p_i over the
    /// PRIME copy SETUP pushed, then ROUND4 adds K_i in the S-boxes, leaving
    /// [s0', PRIME, s1', s2', s3', 3 dead values, PRIME] for the rounds
    /// after.
    fn hash_round0(&mut self, n: usize, words: &[Vec<U256>]) -> Result<()> {
        if self.t != 4 {
            bail!("hashRound0 is t = 4 only");
        }
        let Some(program) = hash_forms(n) else {
            bail!("hash arity {n}");
        };
        let p = self.p();
        // the words as CALLDATALOAD leaves them, not reduced
        let raw: Vec<Id> = (0..n)
            .map(|i| {
                let vals = words.iter().map(|w| w[i]).collect();
                let v = self.e.alloc(crate::value::Value::new(
                    format!("r{i}"),
                    UINT256_MAX,
                    vals,
                    None,
                )?);
                self.e.declare_calldata(v, 4 + 32 * i);
                Ok(v)
            })
            .collect::<Result<_>>()?;
        self.e.set_stack(&[p]);
        self.e.max_depth = 1;
        let mut forms: HashMap<String, Id> = HashMap::new();
        for mv in program.split(" ") {
            if let Some(k) = mv.strip_prefix("dup") {
                let k: usize = k.parse().expect("dup slot");
                let v = self.e.top(k - 1)?;
                self.e.dup(v)?;
            } else if let Some(k) = mv.strip_prefix("swap") {
                self.e.swap(k.parse().expect("swap slot"))?;
            } else if mv == "P" {
                self.e.push_prime()?;
            } else if mv == "4" {
                self.e.push(u256(4), None)?;
            } else if let Some(i) = mv.strip_prefix('r') {
                let i: usize = i.parse().expect("input");
                self.e.calldata_load(raw[i])?;
            } else if let Some((op, name)) = mv.split_once('=') {
                let op = match op {
                    "add" => Op::Add,
                    "addmod" => Op::Addmod,
                    "mulmod" => Op::Mulmod,
                    "mod" => Op::Mod,
                    _ => bail!("unknown forms move {mv}"),
                };
                let mut operands = vec![inplace(self.e.top(0)?), inplace(self.e.top(1)?)];
                if matches!(op, Op::Addmod | Op::Mulmod) {
                    operands.push(inplace(p));
                }
                let v = self.e.compute(op, &operands, name)?;
                forms.insert(name.to_string(), v);
                self.e.end_line();
            } else {
                bail!("unknown forms move {mv}");
            }
        }
        self.e.end_line();
        let form = |name: &str| match forms.get(name) {
            Some(&v) => Ok(v),
            None => bail!("hash_{n} round 0 leaves no {name}"),
        };
        let p2 = form("p2")?;
        let inputs = vec![
            form("p0")?,
            form("p1")?,
            p2,
            forms.get("p3").copied().unwrap_or(p2),
        ];
        // M4[i][3], the capacity's column
        let column: [u64; 4] = [3, 1, 7, 6];
        let iv = u256(n as u64) << 64;
        self.lane_constants = Some(
            (0..4)
                .map(|i| {
                    crate::field::reduce(u256(column[i]) * iv + self.params.round_constants[0][i])
                })
                .collect(),
        );
        let names: Vec<String> = (0..4).map(|i| format!("s{i}'")).collect();
        let round = round4();
        self.state = self.run_template(round, &inputs, &names, Some(0))?;
        self.lane_constants = None;
        Ok(())
    }

    /// Writes the state to [0, 32t) for the next part or the caller.
    /// Writes the state to [0, 32t) for the next part or the caller. DUP and
    /// MSTORE leave the stack as it was, so every element is fetched from
    /// the same layout (shadowed ones with MLOAD). A hand-over reduces an
    /// element above the bound the next part takes.
    fn store_state(&mut self, hands_over: bool) -> Result<()> {
        self.e.comment("State to memory");
        for i in 0..self.t {
            self.e.dup(self.state[i])?;
            if hands_over && self.bound(self.state[i]) > handover_bound() {
                self.state[i] = self.mod_top(self.state[i])?;
            }
            self.e.mstore(32 * i)?;
            self.e.end_line();
        }
        Ok(())
    }

    // ---- internal rounds ---------------------------------------------------

    /// s0 + c and its S-box. In the shared body the round constant is
    /// MLOADed from slot `rc` of the scratch, with the bound of any field
    /// element so that the body never depends on the constant of one call.
    fn round_start(&mut self, round: usize, rc: Option<usize>) -> Result<Id> {
        let s0 = self.state[0];
        let p = self.p();
        if self.e.top(0)? != s0 || self.e.top(1)? != p {
            bail!("internal round expects [s0, P] on top");
        }
        let c0 = self.params.round_constants[round][0];
        let c = match rc {
            None => {
                if !self.e.fits_add(self.bound(s0), c0) {
                    bail!("s0 + c does not fit");
                }
                constant(c0, "c")
            }
            Some(rc) => {
                if !self.e.fits_add(self.bound(s0), p1()) {
                    bail!("s0 + c does not fit");
                }
                Operand::Load {
                    offset: self.rc_base + 32 * rc,
                    name: "c".to_string(),
                    bound: p1(),
                    vals: vec![c0; self.vectors],
                }
            }
        };
        let y = self.e.compute(Op::Add, &[c, inplace(s0)], "s0+c")?;
        let x5 = self.sbox(y, "s0^5")?;
        self.e.end_line();
        Ok(x5)
    }

    /// Expects s0 on top with a PRIME copy under it (placed by the previous
    /// round) so that s0 + c lands in place for the S-box.
    fn internal_round(&mut self, round: usize, next_internal: bool) -> Result<()> {
        let t = self.t;
        if self.opts.internal_template && t == 4 {
            let list = internal4();
            let state = self.state.clone();
            // x + s1 + s3 is a lazy ADD in the program
            let lazy = wide(self.bound(state[1])) + wide(self.bound(state[3])) + wide(p1());
            if lazy <= wmax() && self.template(list, &state).is_some() {
                let names: Vec<String> = (0..t).map(|i| format!("s{i}'")).collect();
                self.state = self.run_template(list, &state, &names, Some(round))?;
                self.dead.clear();
                return Ok(());
            }
        }
        if self.opts.internal_template && t == 3 {
            let list = internal3();
            let state = self.state.clone();
            let b1 = wide(self.bound(state[1]));
            let b2 = wide(self.bound(state[2]));
            if b1 <= wide(p1()) * U512::from(4u64) && b2 <= wide(p1()) * U512::from(5u64) {
                let final_round =
                    !next_internal || round == self.params.rounds_f / 2 + self.params.rounds_p - 1;
                let kind = if b1 > wide(p1()) * U512::from(3u64) {
                    Internal3Kind::Reset
                } else if b2 > wide(p1()) * U512::from(2u64) {
                    Internal3Kind::High
                } else if final_round {
                    Internal3Kind::Final
                } else {
                    Internal3Kind::Low
                };
                let periodic = internal3_periodic(kind);
                if self.template(periodic, &state).is_some() {
                    let names: Vec<String> = (0..t).map(|i| format!("s{i}'")).collect();
                    self.state = self.run_template(periodic, &state, &names, Some(round))?;
                    self.dead.clear();
                    return Ok(());
                }
            }
            // the lazy ADDs: x + s1 + 2 s2 and 2 x + s1 + s2 (+ c in the next
            // round) from reduced inputs, x + s2 and s2 + sum from lazy ones
            let steady = wide(p1()) + b1 + b2 + b2 <= wmax()
                && wide(p1()) * U512::from(3u64) + b1 + b2 <= wmax();
            let lazy = wide(p1()) + b2 <= wmax();
            let pick = if steady {
                Some(&list[..1])
            } else if lazy {
                Some(&list[1..])
            } else {
                None
            };
            if let Some(list) = pick
                && self.template(list, &state).is_some()
            {
                let names: Vec<String> = (0..t).map(|i| format!("s{i}'")).collect();
                self.state = self.run_template(list, &state, &names, Some(round))?;
                self.dead.clear();
                return Ok(());
            }
        }
        let x5 = self.round_start(round, None)?;
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

        let p = self.p();
        let s1 = self.state[1];
        if self.opts.internal_mul3
            && t == 2
            && !collect
            && wide(p1()) * U512::from(3u64) + wide(self.bound(s1)) <= wmax()
        {
            // s1' = (3 s1 mod P) + s0^5 lazy on the PRIME copy for the next
            // round, s0' = 2 s0^5 + s1 lazy on its own copy: no sum to share
            if self.opts.float_prime_internal {
                self.float_prime()?;
            }
            self.e.push_prime()?;
            let m = self.e.compute(
                Op::Mulmod,
                &[constant_hex(u256(3)), val(s1), inplace(p)],
                "3s1",
            )?;
            let out1 = self.e.compute(Op::Add, &[val(x5), inplace(m)], "s1'")?;
            self.e.end_line();
            if next_internal {
                self.e.push_prime()?;
            }
            let d = self.e.compute(Op::Add, &[val(x5), val(x5)], "2s0^5")?;
            let out0 = self.e.compute(Op::Add, &[val(s1), inplace(d)], "s0'")?;
            self.e.end_line();
            self.dead.push(x5);
            self.state = vec![out0, out1];
            return Ok(());
        }

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

        // the round program after the last internal round adds its round
        // constants with an ADD only to an output that fits, otherwise an
        // ADDMOD and an S-box without its PRIME copy (14 gas) instead of
        // reducing here (8)
        let rf_half = self.params.rounds_f / 2;
        let next_c = (self.opts.external_template
            && t <= 3
            && next_internal
            && round == rf_half + self.params.rounds_p - 1)
            .then(|| self.params.round_constants[round + 1].clone());
        let tight = |bound: U512, i: usize| {
            next_c
                .as_ref()
                .is_some_and(|c| i > 0 && bound + wide(c[i]) > wmax())
        };

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
                    } else if !(t == 2 && self.opts.internal_mul3 && !collect) {
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
                let r = reduce || tight(wide(self.bound(s)) + wide(self.bound(sum)), i);
                self.pair_add(s, sum, &name, r)?
            } else if d == u256(2) {
                if self.fits(s, s) {
                    let wide_sum = wide(self.bound(sum)) + wide(self.bound(s)) * U512::from(2u64);
                    let r = reduce || wide_sum > wmax() || tight(wide_sum, i);
                    let dname = format!("2s{i}");
                    self.add_to(
                        |b| b.e.compute(Op::Add, &[val(s), val(s)], &dname),
                        sum,
                        &name,
                        r,
                    )?
                } else {
                    let lazy_bound = wide(self.bound(sum)) + wide(p1());
                    let r = reduce || !self.fits(sum, p) || tight(lazy_bound, i);
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
                let lazy_bound = wide(self.bound(sum)) + wide(p1());
                let r = reduce || !self.fits(sum, p) || tight(lazy_bound, i);
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

    /// The chains in which the consuming round takes the elements of `old`
    /// the stack holds but s0, as index lists (huff/schedule.ts
    /// consumeChains): slot order from the slot under the sum for the
    /// rounds in between, as one chain or in sub-chains of consume_group
    /// slots, and for the last internal round Eulerian circuits of the
    /// blocks (Hierholzer's algorithm), one per connected component from
    /// the lowest slot left, that leave every element in the slots of its
    /// block of the external layer.
    fn consume_chains(
        &self,
        old: &[Id],
        mem: usize,
        next_internal: bool,
    ) -> Result<Vec<Vec<usize>>> {
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
            let group = if self.opts.consume_group > 0 {
                self.opts.consume_group
            } else {
                order.len()
            };
            return Ok(order
                .chunks(group)
                .map(|chunk| chunk.iter().map(|s| at[s]).collect())
                .collect());
        }
        let block = |i: usize| i >> 2;
        let mut out: HashMap<usize, Vec<usize>> = HashMap::new();
        for &s in &order {
            out.entry(block(s - 2 + mem)).or_default().push(s);
        }
        let mut chains: Vec<Vec<usize>> = Vec::new();
        let mut used: HashSet<usize> = HashSet::new();
        for &first in &order {
            if used.contains(&first) {
                continue;
            }
            let mut circuit: Vec<usize> = Vec::new();
            // (node, via)
            let mut stack: Vec<(usize, usize)> = vec![(block(first - 2 + mem), 0)];
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
            let start = circuit.iter().position(|&s| s == first).unwrap_or(0);
            let chain: Vec<usize> = circuit[start..]
                .iter()
                .chain(&circuit[..start])
                .copied()
                .collect();
            used.extend(&chain);
            chains.push(chain.iter().map(|s| at[s]).collect());
        }
        if used.len() != slots {
            bail!("the blocks have no circuit");
        }
        Ok(chains)
    }

    /// Internal round that consumes the old state in place. Expects [s0, P]
    /// on top, the other elements right under them and a PRIME copy under
    /// the state. Beyond reach - 4 elements (or consume_slots) the first
    /// indices live in memory, loaded for the chain and their MULMOD and
    /// stored again. Each element
    /// swapped to the top gets a PRIME copy swapped under it, or with
    /// prime_stack lands on one of the copies stacked under m0 beforehand.
    fn internal_round_consume(
        &mut self,
        round: usize,
        next_internal: bool,
        rc: Option<usize>,
    ) -> Result<()> {
        let t = self.t;
        let p = self.p();
        let slots = held_slots(t, self.e.max_reach, self.opts.consume_slots);
        let mem = t - 1 - slots;
        let x5 = self.round_start(round, rc)?;
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
        let m0 = self
            .e
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
        let chains = self.consume_chains(&old, mem, next_internal)?;
        let order: Vec<usize> = chains.iter().flatten().copied().collect();
        // a chain closes with m0 back on top, its last output into the slot
        // of its first element (the sum is then right under m0 after the
        // last chain)
        if self.opts.prime_stack {
            // the elements in memory first, then the PRIME copies of the
            // first `stacked` swapped elements under m0: [m0, P, ..., P,
            // sum, ...]. The k-th element sits under the copies left over
            // its turn, so its swap must still reach it; the elements
            // after the stacked ones get their copy swapped under them.
            for &j in &loads {
                if j <= mem {
                    self.consume_load(j, &old, sum, mem, &mut out)?;
                }
            }
            let depths: Vec<usize> = order.iter().map(|&i| self.e.find(old[i])).collect();
            let fits = |n: usize| (0..n).all(|k| depths[k] + n - k - 1 <= self.e.max_reach);
            let stacked = (0..=order.len()).rev().find(|&n| fits(n)).unwrap_or(0);
            if stacked > 0 {
                for _ in 0..stacked {
                    self.e.push_prime()?;
                }
                self.e.swap(stacked)?;
                self.e.end_line();
            }
            let mut k = 0;
            for chain in &chains {
                for &i in chain {
                    let s = old[i];
                    self.swap_up(s)?;
                    if k >= stacked {
                        self.e.push_prime()?;
                        self.e.swap(1)?;
                    }
                    self.consume_finish(i, s, sum, mem, &mut out)?;
                    if i <= mem {
                        // the output went to memory: one that comes back to
                        // the stack takes its place on top, with its own
                        // PRIME copy
                        let Some(j) = to_stack.pop_front() else {
                            bail!("no element to load on top");
                        };
                        self.consume_load(j, &old, sum, mem, &mut out)?;
                    }
                    k += 1;
                }
                self.swap_up(m0)?;
            }
        } else {
            let mut k = 0;
            for chain in &chains {
                for &i in chain {
                    let s = old[i];
                    self.swap_up(s)?;
                    self.e.push_prime()?;
                    self.e.swap(1)?;
                    self.consume_finish(i, s, sum, mem, &mut out)?;
                    if i <= mem {
                        // the output went to memory: one that comes back to
                        // the stack takes its place on top
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
                    k += 1;
                }
                self.swap_up(m0)?;
            }
        }
        if !to_stack.is_empty() {
            bail!("elements left to load on top");
        }
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

    /// The steady internal rounds of the range that run through the shared
    /// body, as the rounds of each call: full calls of a period, then the
    /// remainder as a last call that leaves at the mid exit. None when the
    /// body would run once at most.
    fn body_calls(&self) -> Result<Option<Vec<Vec<usize>>>> {
        let (first, steady) = steady_rounds(self.params, self.range);
        if self.opts.body_inline > steady {
            bail!("bodyInline exceeds the steady rounds");
        }
        let start = first + self.opts.body_inline;
        let rest = steady - self.opts.body_inline;
        let full = rest / self.period;
        if full == 0 {
            return Ok(None);
        }
        let mut calls: Vec<Vec<usize>> = (0..full)
            .map(|c| {
                let r = start + c * self.period;
                (r..r + self.period).collect()
            })
            .collect();
        let rem = rest % self.period;
        if rem > 0 {
            let r = start + full * self.period;
            calls.push((r..r + rem).collect());
        }
        Ok(Some(calls))
    }

    /// Emits the calls of the shared body. A call CODECOPYs its round
    /// constants from its code table to the scratch, stores its return
    /// label and JUMPs to the body, which the last call falls into instead;
    /// the body's text goes out there. The emitter simulates the body at
    /// every call, recording it at the first (emitter.rs). A remainder call
    /// stores its return label at the mid exit's slot, which the full calls
    /// had set to the label right after the exit.
    fn emit_body_calls(&mut self, calls: &[Vec<usize>]) -> Result<()> {
        let period = self.period;
        let ret_mid = self.rc_base + 32 * period;
        let ret_end = ret_mid + 32;
        let rem = calls[calls.len() - 1].len() % period;
        self.e
            .comment("Shared body of the steady internal rounds (see the calls)");
        if rem > 0 {
            self.e.push_label("body_mid");
            self.e.mstore(ret_mid)?;
            self.e.end_line();
        }
        for (c, rounds) in calls.iter().enumerate() {
            let n = rounds.len();
            let last_call = c == calls.len() - 1;
            self.e.comment(&format!(
                "Rounds {} to {} (internal): body call {c}",
                rounds[0],
                rounds[n - 1]
            ));
            let name = format!("RC{c}");
            let words = rounds
                .iter()
                .map(|&r| self.params.round_constants[r][0])
                .collect();
            self.e.table(&name, words);
            self.e.codecopy(&name, n, self.rc_base)?;
            self.e.push_label(&format!("ret{c}"));
            self.e.mstore(if n < period { ret_mid } else { ret_end })?;
            if !last_call {
                self.e.push_label("body");
                self.e.jump();
            }
            self.e.end_line();

            self.e.begin_body(c == 0)?;
            self.e.label("body");
            self.e.end_line();
            for (k, &r) in rounds.iter().enumerate() {
                if k > 0 {
                    self.e.segment();
                }
                if k == rem && k > 0 {
                    // the mid exit: a remainder call returns, a full one
                    // goes on
                    self.e.jump_via(ret_mid)?;
                    self.e.end_line();
                    self.e.label("body_mid");
                    self.e.end_line();
                }
                self.e.next_round();
                self.e.comment(&format!("Round {r} (internal)"));
                self.internal_round_consume(r, true, Some(k))?;
                self.e.comment("");
                self.step_bytes.push(self.e.bytes);
            }
            self.e.segment();
            self.e
                .jump_via(if n < period { ret_mid } else { ret_end })?;
            self.e.end_line();
            self.e.end_body()?;
            if last_call {
                self.e
                    .comment("Shared body, entered by the calls above (the last falls in)");
                let lines: Vec<String> = self.e.body_lines.iter().flatten().cloned().collect();
                self.e.lines.extend(lines);
            }
            self.e.label(&format!("ret{c}"));
            self.e.end_line();
        }
        Ok(())
    }

    // ---- whole permutation -------------------------------------------------

    fn build(&mut self) -> Result<Vec<Id>> {
        let rf_half = self.params.rounds_f / 2;
        let p_end = rf_half + self.params.rounds_p;
        let total = self.params.rounds_f + self.params.rounds_p;
        let Range { from, to } = self.range;
        let has_internal = from <= p_end && to > rf_half + 1;

        if self.opts.prime_in_memory {
            // the slot below the shadow slots
            let offset = self.e.slot_base - 32;
            self.e
                .comment("PRIME in memory, loaded where no copy is within reach");
            self.e.push_prime()?;
            self.e.mstore(offset)?;
            self.e.end_line();
            self.e.comment("");
            self.e.prime_slot = Some(offset);
        }

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
            if self.opts.external_template && self.t <= 4 {
                self.external_template(TemplateKind::Entry, None)?;
            } else {
                self.external_matrix(false, false, true)?;
            }
            self.e.comment("");
            self.step_bytes.push(self.e.bytes);
        }

        let body = if self.opts.shared_body {
            if !self.opts.internal_consume {
                bail!("sharedBody needs internalConsume");
            }
            match self.body_calls()? {
                Some(calls) => Some(calls),
                None => bail!("the body would run once at most"),
            }
        } else {
            None
        };

        let mut r = from.saturating_sub(1);
        while r + 1 < to {
            if let Some(calls) = &body
                && r == calls[0][0]
            {
                self.emit_body_calls(calls)?;
                r += calls.iter().map(Vec::len).sum::<usize>();
                continue;
            }
            self.e.next_round();
            // round r + 1 belongs to this part too
            let next = r + 2 < to;
            if r < rf_half {
                self.e.comment(&format!("Round {r} (external)"));
                let last = r == rf_half - 1;
                if self.opts.external_template && self.t <= 4 {
                    let kind = if last && next {
                        TemplateKind::Exit
                    } else {
                        TemplateKind::Round
                    };
                    self.external_template(kind, Some(r))?;
                } else {
                    self.add_constants_and_sbox(r)?;
                    self.external_matrix(false, last && next, !last)?;
                }
            } else if r < p_end {
                self.e.comment(&format!("Round {r} (internal)"));
                if from == r + 1 {
                    // the entry leaves [s0, ..., PRIME]: place the PRIME copy
                    // the round expects under s0
                    self.e.push_prime()?;
                    self.e.swap(1)?;
                }
                let next_internal = r < p_end - 1 && next;
                // the round programs of t <= 3 expect the PRIME copy under
                // s0 as well
                let prime_under =
                    (r < p_end - 1 || (self.opts.external_template && self.t <= 3)) && next;
                if self.opts.internal_consume {
                    self.internal_round_consume(r, next_internal, None)?;
                } else {
                    self.internal_round(r, prime_under)?;
                }
            } else if r == total - 1 && self.live.is_some() {
                self.e.comment(&format!("Round {r} (external, s0' only)"));
                if self.live.as_deref() != Some(&[0]) {
                    bail!("only s0' can be the live output");
                }
                self.final_round_row0(r)?;
            } else {
                self.e.comment(&format!("Round {r} (external)"));
                if self.opts.external_template && self.t <= 4 {
                    let kind = if r == total - 1 {
                        TemplateKind::Final
                    } else {
                        TemplateKind::Round
                    };
                    self.external_template(kind, Some(r))?;
                } else {
                    self.add_constants_and_sbox(r)?;
                    self.external_matrix(r == total - 1, false, true)?;
                }
            }
            self.e.comment("");
            self.step_bytes.push(self.e.bytes);
            r += 1;
        }

        if self.state_in_memory {
            self.store_state(self.range.to < step_count(self.params))?;
        }
        self.e.end_line();
        Ok(self.state.clone())
    }
}

/// The dead values hash round 0 leaves between its outputs and the PRIME
/// copy under them, which the rounds after copy from
pub const HASH_DEAD: usize = 3;

/// The round 0 the hash entry runs for n inputs (Builder::hash_round0)
/// with its gas, bytes, stack depth and lazy outputs, checked against the
/// reference before anything is written.
#[derive(Debug, Clone)]
pub struct Prologue {
    pub n: usize,
    pub lines: Vec<String>,
    pub gas: u64,
    pub bytes: usize,
    /// stack depth at the end: the rounds after run on top of it
    pub depth: usize,
    /// bound of [s0', s1', s2', s3'] after round 0, lazy
    pub bounds: Vec<U256>,
    /// their values per vector
    pub outputs: Vec<Vec<U256>>,
}

pub fn build_hash_prologue(params: &Params, inputs: &[Vec<U256>], fork: Fork) -> Result<Prologue> {
    let n = inputs[0].len();
    let states: Vec<Vec<U256>> = inputs
        .iter()
        .map(|input| sponge_state(params, input))
        .collect();
    let range = Range { from: 0, to: 2 };
    let mut b = Builder::new(
        params,
        &states,
        DEFAULT_OPTIONS,
        fork,
        range,
        HashSet::new(),
        false,
        true,
        &Boundary::default(),
    )?;
    b.hash_round0(n, inputs)?;
    for (k, state) in states.iter().enumerate() {
        let want = permutation_steps(params, state, 0, 2);
        for (i, &w) in want.iter().enumerate() {
            if crate::field::reduce(b.e.value(b.state[i]).vals[k]) != w {
                bail!("hash_{n} round 0: vector {k} output {i} mismatch");
            }
        }
    }
    let mut layout: Vec<Option<Id>> = b.state.iter().map(|&v| Some(v)).collect();
    layout.insert(1, Some(b.p()));
    layout.extend([None; HASH_DEAD]);
    layout.push(Some(b.p()));
    for (i, v) in layout.iter().enumerate() {
        if v.is_some() && b.e.at(i) != *v {
            bail!("hash_{n} round 0: outputs are not [s0', PRIME, s1', s2', s3', 3 dead, PRIME]");
        }
    }
    let bounds = b.state.iter().map(|&v| b.e.bound(v)).collect();
    let outputs = (0..states.len())
        .map(|k| b.state.iter().map(|&v| b.e.value(v).vals[k]).collect())
        .collect();
    let depth = b.e.depth();
    Ok(Prologue {
        n,
        lines: b.e.lines,
        gas: b.e.gas,
        bytes: b.e.bytes,
        depth,
        bounds,
        outputs,
    })
}

/// The rounds after round 0 shared by the hash entry's arities, built from
/// the lazy values every prologue leaves (their bounds joined, their
/// vectors concatenated) and reading s0' alone.
pub fn build_hash_rounds(
    params: &Params,
    prologues: &[Prologue],
    max_bytes: usize,
    fork: Fork,
) -> Result<Best> {
    let t = params.t;
    let mut inputs: Vec<Vec<U256>> = Vec::new();
    let mut bounds = vec![U256::ZERO; t];
    for p in prologues {
        for (bound, &b) in bounds.iter_mut().zip(&p.bounds) {
            if b > *bound {
                *bound = b;
            }
        }
        inputs.extend(p.outputs.iter().cloned());
    }
    let boundary = Boundary {
        bounds: Some(bounds),
        calldata: false,
        live: Some(vec![0]),
        prime_second: true,
        prime_below: Some(HASH_DEAD),
    };
    let range = Range {
        from: 2,
        to: step_count(params),
    };
    match build_best_with(params, &inputs, max_bytes, fork, range, &boundary)? {
        Some(best) => Ok(best),
        None => bail!("the hash rounds do not fit on {}", fork.name),
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
    build_permutation_with(
        params,
        inputs,
        opts,
        fork,
        range,
        text,
        &Boundary::default(),
    )
}

/// build_permutation from lazy inputs and for the outputs the caller reads.
pub fn build_permutation_with(
    params: &Params,
    inputs: &[Vec<U256>],
    opts: &BuildOptions,
    fork: Fork,
    range: Range,
    text: bool,
    boundary: &Boundary,
) -> Result<BuildResult> {
    let expected = expected_outputs(params, inputs, range);
    build_checked(params, inputs, &expected, opts, fork, range, text, boundary)
}

/// The reference state after the range, per input (which may be lazy).
fn expected_outputs(params: &Params, inputs: &[Vec<U256>], range: Range) -> Vec<Vec<U256>> {
    inputs
        .iter()
        .map(|input| {
            let clean: Vec<U256> = input.iter().map(|&x| crate::field::reduce(x)).collect();
            permutation_steps(params, &clean, range.from, range.to)
        })
        .collect()
}

/// build_permutation against reference outputs computed once per range.
#[allow(clippy::too_many_arguments)]
fn build_checked(
    params: &Params,
    inputs: &[Vec<U256>],
    expected: &[Vec<U256>],
    opts: &BuildOptions,
    fork: Fork,
    range: Range,
    text: bool,
    boundary: &Boundary,
) -> Result<BuildResult> {
    let mut shadow = HashSet::new();
    let mut last_load = HashMap::new();
    if opts.shadow {
        let mut probe = Builder::new(
            params, inputs, *opts, fork, range, shadow, true, false, boundary,
        )?;
        probe.build()?;
        shadow = std::mem::take(&mut probe.e.needed);
        last_load = std::mem::take(&mut probe.e.last_load);
    }
    let mut b = Builder::new(
        params, inputs, *opts, fork, range, shadow, false, text, boundary,
    )?;
    b.e.last_load = last_load;
    let outputs = b.build()?;
    let e = &b.e;
    let t = params.t;
    let is_final = range.to == step_count(params);
    // the state indices the outputs hold
    let live: Vec<usize> = boundary
        .live
        .clone()
        .unwrap_or_else(|| (0..outputs.len()).collect());

    if !b.state_in_memory {
        // the outputs must sit on top in state order and be clean
        for (i, &out) in outputs.iter().enumerate() {
            if e.at(i) != Some(out) {
                bail!("output {} is not at slot {}", live[i], i + 1);
            }
            if e.bound(out) >= PRIME {
                bail!("output {} is not clean", live[i]);
            }
        }
        if boundary.live.is_none() && t <= 4 && e.at(t) != Some(e.p) {
            bail!("PRIME expected under outputs");
        }
    } else if is_final {
        for (i, &out) in outputs.iter().enumerate() {
            if e.bound(out) >= PRIME {
                bail!("output {} is not clean", live[i]);
            }
        }
    } else {
        for (i, &out) in outputs.iter().enumerate() {
            if e.bound(out) > handover_bound() {
                bail!("output {} is above the hand-over bound", live[i]);
            }
        }
    }

    // concrete check of the emitted stream against the reference permutation
    // (a part that hands over leaves lazy values, the next entry reduces
    // them; the inputs may be lazy as well)
    for (k, want) in expected.iter().enumerate() {
        for (i, &out) in outputs.iter().enumerate() {
            let v = e.value(out).vals[k];
            let got = if is_final { v } else { crate::field::reduce(v) };
            if got != want[live[i]] {
                bail!("vector {k} output {} mismatch", live[i]);
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
        tables: e.tables,
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
/// order; with shadow, a consuming schedule whose elements the reach
/// cannot hold all also with one and two more on the stack.
fn candidates(t: usize, shadow: bool, reach: usize) -> Vec<BuildOptions> {
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
                                            for &prime_stack in pick(internal_consume) {
                                                for &shared_body in pick(internal_consume) {
                                                    // the templates replace the
                                                    // external rounds (t <= 4) or
                                                    // the M4 of every block (with
                                                    // external_d), so the options
                                                    // those would collect or
                                                    // pre-place are moot
                                                    let templated = if t <= 4 {
                                                        !gc_external
                                                            && !gc_m4
                                                            && !prime_under_external
                                                    } else {
                                                        external_d && !gc_m4
                                                    };
                                                    for &external_template in pick(templated) {
                                                        for &internal_template in
                                                            pick((t == 3 || t == 4) && !gc_internal)
                                                        {
                                                            for &internal_mul3 in pick(
                                                                t == 2 && internal_reduce_outputs,
                                                            ) {
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
                                                                    prime_stack,
                                                                    gc_internal_from: 0,
                                                                    gc_m4_from: 0,
                                                                    diag_push32: 0,
                                                                    shadow,
                                                                    shared_body,
                                                                    body_inline: 0,
                                                                    consume_group: 0,
                                                                    consume_slots: 0,
                                                                    external_template,
                                                                    internal_template,
                                                                    internal_mul3,
                                                                    prime_in_memory: false,
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
                    }
                }
            }
        }
    }
    let extra: Vec<usize> = (reach - 3..=reach - 2).filter(|&n| n < t).collect();
    list.into_iter()
        .flat_map(|opts| {
            let more: &[usize] = if shadow && opts.prime_stack && opts.shared_body {
                &extra
            } else {
                &[]
            };
            std::iter::once(opts).chain(more.iter().map(move |&consume_slots| BuildOptions {
                consume_slots,
                ..opts
            }))
        })
        .collect()
}

/// What the search learns from one candidate: whether its first build
/// succeeded, and its final options and cost or the reason it fails.
struct Outcome {
    built: bool,
    result: std::result::Result<(BuildOptions, u64), String>,
}

/// Tries the option combinations that make sense for t and returns the
/// cheapest build of the range (code and memory expansion) that stays within
/// reach, depth and code size, or None when the schedules that build are too
/// large or too deep. The
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
    build_best_with(params, inputs, max_bytes, fork, range, &Boundary::default())
}

/// build_best from lazy inputs and for the outputs the caller reads.
pub fn build_best_with(
    params: &Params,
    inputs: &[Vec<U256>],
    max_bytes: usize,
    fork: Fork,
    range: Range,
    boundary: &Boundary,
) -> Result<Option<Best>> {
    let expected = expected_outputs(params, inputs, range);
    let build = |opts: &BuildOptions| {
        build_checked(
            params, inputs, &expected, opts, fork, range, false, boundary,
        )
    };
    let attempt = |opts: &BuildOptions| build(opts).ok();
    // the code and the memory it expands (the state region at least)
    let cost = |result: &BuildResult| result.gas + memory_gas(result.memory.max(32 * params.t));
    let evaluate = |opts: &BuildOptions| -> Outcome {
        let mut opts = *opts;
        let mut first = build(&opts);
        // the round after a part's entry still loads from the entry's
        // shadow slots (a memory layout of its own), so the body starts at
        // the first count of inline rounds that builds
        while opts.shared_body && first.is_err() && opts.body_inline < 2 {
            opts.body_inline += 1;
            first = build(&opts);
        }
        let result = match first {
            Ok(r) => r,
            Err(err) => {
                return Outcome {
                    built: false,
                    result: Err(err.0),
                };
            }
        };
        let finish = |mut opts: BuildOptions,
                      mut result: BuildResult|
         -> std::result::Result<(BuildOptions, u64), String> {
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
                if opts.gc_m4 && fork.reach > 16 {
                    let gc_m4_from = largest(params.rounds_f + 1, |n| {
                        attempt(&BuildOptions {
                            gc_m4_from: n,
                            ..opts
                        })
                        .is_some_and(|r| r.max_depth <= 1000)
                    });
                    opts.gc_m4_from = gc_m4_from;
                    result = build(&opts).map_err(|e| e.0)?;
                }
                if opts.shared_body && result.bytes > max_bytes {
                    // a body too large for the code size: sub-chains shorten
                    // it, the longest period that fits (the shorter, the
                    // more chains and calls)
                    let groups = group_candidates(params, &fork, opts.consume_slots);
                    let fits = |n: usize| {
                        attempt(&BuildOptions {
                            consume_group: groups[n],
                            ..opts
                        })
                        .is_some_and(|r| r.bytes <= max_bytes)
                    };
                    if !groups.is_empty() && fits(0) {
                        opts.consume_group = groups[largest(groups.len() - 1, fits)];
                        result = build(&opts).map_err(|e| e.0)?;
                    }
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
                if opts.shared_body && result.bytes <= max_bytes {
                    let (_, steady) = steady_rounds(params, range);
                    let fits = |n: usize| {
                        attempt(&BuildOptions {
                            body_inline: n,
                            ..opts
                        })
                        .is_some_and(|r| r.bytes <= max_bytes)
                    };
                    let base = opts.body_inline;
                    let mut body_inline = base + largest(steady - base, |n| fits(base + n));
                    // a remainder call and the mid exit cost more than the
                    // 3 gas per round the body charges, so the largest count
                    // that leaves none when one fits
                    let period = body_period(params, &fork, opts.consume_slots, opts.consume_group);
                    let extra = (period - (steady - body_inline) % period) % period;
                    if body_inline >= extra && fits(body_inline - extra) {
                        body_inline -= extra;
                    }
                    opts.body_inline = body_inline;
                    result = build(&opts).map_err(|e| e.0)?;
                }
            }
            if result.max_depth > 1000 {
                return Err(format!("depth {}", result.max_depth));
            }
            if result.bytes > max_bytes {
                return Err(format!("{} bytes", result.bytes));
            }
            Ok((opts, cost(&result)))
        };
        let plain = finish(opts, result);
        // where the code size binds (a shorter body, diag constants in
        // memory, or no fit at all), PRIME from memory frees 30 bytes per
        // PUSH32 for 3 gas
        let binding = match &plain {
            Ok((o, _)) => {
                (o.shared_body && o.consume_group > 0)
                    || (o.diag_in_memory && o.diag_push32 < params.t)
            }
            Err(reason) => reason.ends_with(" bytes"),
        };
        let mut chosen = plain;
        if binding {
            let pim = BuildOptions {
                prime_in_memory: true,
                ..opts
            };
            if let Ok(r) = build(&pim) {
                let alt = finish(pim, r);
                if let Ok((_, gas)) = alt
                    && chosen.as_ref().map_or(true, |&(_, g)| gas < g)
                {
                    chosen = alt;
                }
            }
        }
        Outcome {
            built: true,
            result: chosen,
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
    let mut built = search(
        candidates(params.t, false, fork.reach),
        &mut best,
        &mut failures,
    );
    if built == 0 {
        built += search(
            candidates(params.t, true, fork.reach),
            &mut best,
            &mut failures,
        );
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
            let result = build_checked(
                params, inputs, &expected, &opts, fork, range, true, boundary,
            )?;
            assert_eq!(
                cost(&result),
                gas,
                "the rebuilt winner costs what the search measured"
            );
            Ok(Some(Best { result, opts }))
        }
        None => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field;
    use crate::huff::fork::fork;
    use crate::round_constants::generate_params_uncached;

    #[test]
    fn internal3_periodic_bounds_and_boundaries() {
        let mut params = generate_params_uncached(3);
        for rc in &mut params.round_constants {
            rc[0] = p1();
        }
        for name in ["osaka", "amsterdam"] {
            for (bb, cb, rounds) in [
                (p1(), p1() * u256(2), 1),
                (p1() * u256(2), p1() * u256(5), 1),
                (p1() * u256(3), p1() * u256(2), 1),
                (p1() * u256(4), p1() * u256(5), 1),
                (p1() * u256(3) + u256(1), p1() * u256(2), 1),
                (p1(), p1() * u256(2) + u256(1), 1),
                (p1() * u256(4) + u256(1), p1() * u256(4), 1),
                (p1() * u256(4), p1() * u256(4), 56),
            ] {
                for final_prime in [false, true] {
                    let bounds = vec![p1() * u256(4), bb, cb];
                    let inputs = vec![vec![U256::ZERO; 3], bounds.clone()];
                    let mut builder = Builder::new(
                        &params,
                        &inputs,
                        BuildOptions {
                            internal_template: true,
                            ..DEFAULT_OPTIONS
                        },
                        fork(name).unwrap(),
                        Range {
                            from: 0,
                            to: step_count(&params),
                        },
                        HashSet::new(),
                        false,
                        true,
                        &Boundary {
                            bounds: Some(bounds),
                            ..Boundary::default()
                        },
                    )
                    .unwrap();
                    builder.e.set_stack(&[
                        builder.state[0],
                        builder.p(),
                        builder.state[2],
                        builder.state[1],
                    ]);
                    let mut reference = inputs.clone();
                    let mut total = 0;
                    for r in 0..rounds {
                        let round = if rounds == 1 { 59 } else { 4 + r };
                        let next = r + 1 < rounds || final_prime;
                        let b = builder.bound(builder.state[1]);
                        let c = builder.bound(builder.state[2]);
                        let reset = b > p1() * u256(3);
                        let high = c > p1() * u256(2);
                        let final_round = !next || round == 59;
                        let periodic = b <= p1() * u256(4) && c <= p1() * u256(5);
                        let expected_bounds = if !periodic {
                            vec![p1() * u256(2), p1(), p1()]
                        } else {
                            vec![
                                p1() * u256(2),
                                if reset { p1() } else { p1() + b },
                                if reset || high {
                                    p1() * u256(2)
                                } else if final_round {
                                    p1()
                                } else {
                                    p1() + c + c
                                },
                            ]
                        };
                        for state in &mut reference {
                            let x = field::pow(field::add(state[0], p1()), u256(5));
                            let sum = field::add(field::add(x, state[1]), state[2]);
                            *state = vec![
                                field::add(sum, x),
                                field::add(sum, state[1]),
                                field::add(sum, field::add(state[2], state[2])),
                            ];
                        }
                        let gas = builder.e.gas;
                        builder.internal_round(round, next).unwrap();
                        let cost = builder.e.gas - gas;
                        assert_eq!(
                            cost,
                            if reset || !periodic {
                                117
                            } else if high || final_round {
                                109
                            } else {
                                101
                            }
                        );
                        total += cost;
                        for (i, &id) in builder.state.iter().enumerate() {
                            let value = &builder.e.values[id];
                            assert_eq!(value.bound, expected_bounds[i]);
                            for (k, state) in reference.iter().enumerate() {
                                assert_eq!(field::reduce(value.vals[k]), state[i]);
                            }
                        }
                        assert_eq!(builder.e.top(0).unwrap(), builder.state[0]);
                        assert_eq!(builder.e.top(1).unwrap(), builder.p());
                        assert_eq!(builder.e.top(2).unwrap(), builder.state[2]);
                        assert_eq!(builder.e.top(3).unwrap(), builder.state[1]);
                        assert_eq!(builder.e.depth(), 5 + r);
                        assert!(wide(builder.bound(builder.state[0])) + wide(p1()) <= wmax());
                    }
                    if rounds == 56 {
                        assert_eq!(total, 6000);
                        assert_eq!(builder.bound(builder.state[1]), p1() * u256(4));
                        assert_eq!(builder.bound(builder.state[2]), p1());
                    }
                }
            }
        }
    }

    #[test]
    fn internal_mul3_lazy_bounds_and_boundaries() {
        let mut params = generate_params_uncached(2);
        for rc in &mut params.round_constants {
            rc[0] = p1();
        }
        for name in ["osaka", "amsterdam"] {
            for b in 1..=3 {
                for (final_prime, float_prime_internal) in
                    [(false, false), (false, true), (true, false), (true, true)]
                {
                    let bounds = vec![PRIME * u256(3) - u256(1), PRIME * u256(b) - u256(1)];
                    let inputs = vec![
                        vec![U256::ZERO, U256::ZERO],
                        vec![u256(1), bounds[1]],
                        bounds.clone(),
                    ];
                    let opts = BuildOptions {
                        internal_mul3: true,
                        float_prime_internal,
                        internal_reduce_outputs: true,
                        ..DEFAULT_OPTIONS
                    };
                    let mut builder = Builder::new(
                        &params,
                        &inputs,
                        opts,
                        fork(name).unwrap(),
                        Range {
                            from: 0,
                            to: step_count(&params),
                        },
                        HashSet::new(),
                        false,
                        true,
                        &Boundary {
                            bounds: Some(bounds),
                            ..Boundary::default()
                        },
                    )
                    .unwrap();
                    builder.e.push_prime().unwrap();
                    builder.e.swap(1).unwrap();
                    let mut reference = inputs.clone();
                    for round in 4..60 {
                        for state in &mut reference {
                            let x = field::pow(field::add(state[0], p1()), u256(5));
                            *state = vec![
                                field::add(field::add(x, x), state[1]),
                                field::add(x, field::mul(u256(3), state[1])),
                            ];
                        }
                        let old_bound = builder.bound(builder.state[1]);
                        let bridge = round == 4 && b == 3;
                        builder
                            .internal_round(round, round < 59 || final_prime)
                            .unwrap();
                        let expected = if bridge {
                            vec![p1() * u256(2), p1()]
                        } else {
                            vec![p1() * u256(2) + old_bound, p1() * u256(2)]
                        };
                        for (i, &id) in builder.state.iter().enumerate() {
                            let value = &builder.e.values[id];
                            assert_eq!(value.bound, expected[i]);
                            for (k, state) in reference.iter().enumerate() {
                                assert_eq!(field::reduce(value.vals[k]), state[i]);
                            }
                        }
                        assert!(wide(builder.bound(builder.state[0])) + wide(p1()) <= wmax());
                        assert_eq!(builder.e.top(0).unwrap(), builder.state[0]);
                        if round < 59 || final_prime {
                            assert_eq!(builder.e.top(1).unwrap(), builder.p());
                        }
                    }
                    assert!(builder.bound(builder.state[0]) < PRIME * u256(4));
                    assert!(builder.bound(builder.state[1]) < PRIME * u256(2));
                }
            }
        }
    }
}
