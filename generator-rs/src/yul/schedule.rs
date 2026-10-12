// Poseidon2 permutation as straight-line Yul (yul/schedule.ts).
//
// The schedule only decides the order of the field operations and where the
// state lives (Yul locals or the caller's memory array); whether an addition
// is ADD or ADDMOD, and a doubling ADD or MULMOD, is decided per operation
// from the exact bounds the Program tracks. The text is shaped for the
// legacy solc pipeline: results are written once per statement as nested
// expressions, temporaries live in blocks that end right after their last
// use, the deepest local is the outermost operand, and every local is kept
// within DUP16 / SWAP16 by the reach model below.

use super::program::Program;
use crate::bail;
use crate::error::Result;
use crate::field::{PRIME, U256, U512, UINT256_MAX, add, reduce, u256, wide};
use crate::reference::{matmul_external, permutation};
use crate::round_constants::Params;
use crate::value::{Op, Value};

#[derive(Debug, Clone, Copy)]
pub struct Layout {
    /// elements 0 .. stack_elements - 1 live in Yul locals state0, state1,
    /// ...; the rest stay in the state array in memory (array mode only)
    pub stack_elements: usize,
    /// how many of the trailing internal diag constants are kept in a memory
    /// table (loaded with MLOAD) instead of PUSH32 literals
    pub diag_in_memory: usize,
    /// how many of the last diag constants in memory are kept at 0x40 and
    /// 0x60 instead of the table (PUSH1 and MLOAD instead of an ADD to the
    /// table pointer); the free memory pointer and the zero slot are
    /// restored after the internal rounds
    pub diag_fixed: usize,
    /// how many of the leading internal diag constants are locals declared
    /// for the internal rounds: solc's constant optimizer turns a PUSH32
    /// used more than once into a CODECOPY and MLOAD with few runs (200)
    pub diag_lets: usize,
    /// how many of the following diag constants are kept in the scratch
    /// space (mload(0) and mload(0x20))
    pub diag_scratch: usize,
    /// M4 with two temporaries (t2, t3) instead of four
    pub m4_temps: usize,
    /// keep the internal round's x^5 in a `let` that lives through the round
    pub internal_let: bool,
    /// declare PRIME before the state locals (the deepest slot) and reduce
    /// the inputs with it: one PUSH32 instead of one per input
    pub prime_first: bool,
    /// internal rounds: keep the sum lazy and reduce every output but state0
    pub internal_reduce_outputs: bool,
    /// t = 3 internal rounds: the sum as (x5 + s1) + s2 and s1 reduced once
    /// the next round's x5 + s1 would overflow (the Huff periodic policy)
    pub periodic_internal: bool,
    /// how many of the last locals take the raw input words, reduced where
    /// the initial linear layer first adds or doubles them (ADDMOD /
    /// MULMOD), instead of a MOD with a PRIME literal each
    pub raw_inputs: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// t = 4 library: the inputs are the function arguments s0 .. s3 and
    /// only element 0 is returned, as `result`
    Hash,
    /// the t = 4 library from round 0's S-boxes on (`poseidon2_rest`): the
    /// arguments state0 .. state3 are the initial linear layer plus round
    /// 0's constants, any uint256, folded per arity by `build_hash_entry`
    HashRest,
    /// in-place permutation of the memory array `state`
    Array,
}

pub struct BuildResult {
    pub lines: Vec<String>,
}

/// rank of a value that is not a local: always within reach
const UNRANKED: usize = usize::MAX;

struct Builder<'a> {
    p: Program,
    t: usize,
    params: &'a Params,
    layout: Layout,
    mode: Mode,
    inputs: &'a [Vec<U256>],
    state: Vec<Value>,
    diag_locals: Vec<Value>,
}

/// An operand of a chain statement and whether the step that adds it
/// reduces.
#[derive(Clone)]
struct Step {
    v: Value,
    reduce: bool,
}

impl<'a> Builder<'a> {
    fn new(
        params: &'a Params,
        inputs: &'a [Vec<U256>],
        layout: Layout,
        mode: Mode,
        indent: usize,
    ) -> Result<Builder<'a>> {
        if mode != Mode::Array && (params.t != 4 || layout.stack_elements != 4) {
            bail!("hash mode is the t = 4 library with all locals");
        }
        if layout.stack_elements > params.t
            || layout.diag_scratch > 2
            || layout.diag_fixed > 2
            || layout.diag_fixed > layout.diag_in_memory
            || layout.diag_lets + layout.diag_scratch + layout.diag_in_memory > params.t
        {
            bail!("layout exceeds t");
        }
        Ok(Builder {
            p: Program::new(inputs.len(), indent),
            t: params.t,
            params,
            layout,
            mode,
            inputs,
            state: Vec::new(),
            diag_locals: Vec::new(),
        })
    }

    // ---- state placement ---------------------------------------------------

    fn is_local(&self, i: usize) -> bool {
        i < self.layout.stack_elements
    }

    fn name(i: usize) -> String {
        format!("state{i}")
    }

    /// address of element i in the state array; `mem` aliases `state` once
    /// the locals are declared
    fn addr(i: usize, base: &str) -> String {
        if i == 0 {
            base.to_string()
        } else {
            format!("add({base}, 0x{:x})", 32 * i)
        }
    }

    fn in_memory(&self) -> usize {
        self.t - self.layout.stack_elements
    }

    fn set(&mut self, i: usize, v: &Value) -> Result<Value> {
        let value = if self.is_local(i) {
            self.p.assign(&Self::name(i), v)?
        } else {
            self.p.mstore(&Self::addr(i, "mem"), v)?
        };
        self.state[i] = value.clone();
        Ok(value)
    }

    /// Locals are stack slots in declaration order: state0 is the deepest,
    /// then the `mem` pointer that loads of memory elements go through.
    /// Anything else is within easy reach.
    fn rank(&self, v: &Value) -> usize {
        let shift = usize::from(self.layout.prime_first);
        if v.name == "PRIME" && self.layout.prime_first {
            return 0;
        }
        if let Some(digits) = v.name.strip_prefix("state")
            && !digits.is_empty()
            && digits.bytes().all(|b| b.is_ascii_digit())
            && let Ok(i) = digits.parse::<usize>()
            && self.is_local(i)
        {
            return i + shift;
        }
        if v.name.starts_with("mload(mem") || v.name.starts_with("mload(add(mem") {
            return self.mem_rank();
        }
        UNRANKED
    }

    fn mem_rank(&self) -> usize {
        self.layout.stack_elements + usize::from(self.layout.prime_first)
    }

    /// Whether v can be DUPed with `intermediates` values pushed above the
    /// live lets.
    fn reachable(&self, v: &Value, intermediates: usize) -> bool {
        let i = self.rank(v);
        if i == UNRANKED {
            return true;
        }
        let offset = if i == self.mem_rank() { 1 } else { 0 };
        let above = self.p.live() as i64 - 1 - i as i64;
        above + (intermediates + offset + 1) as i64 <= 16
    }

    // ---- arithmetic --------------------------------------------------------

    fn fits(a: &Value, b: &Value) -> bool {
        a.bound.checked_add(b.bound).is_some()
    }

    /// a + b, lazily unless the bound says otherwise or a reduction is asked
    /// for
    fn add(&self, a: &Value, b: &Value, reduce: bool) -> Result<Value> {
        if reduce || !Self::fits(a, b) {
            return self.p.expr(Op::Addmod, &[a, b, &self.p.p]);
        }
        self.p.expr(Op::Add, &[a, b])
    }

    /// d * s for the internal diagonal: 1 and 2 are the fixed t <= 3
    /// diagonals
    fn scaled(&self, s: &Value, i: usize) -> Result<Value> {
        let d = self.params.internal_diag_minus_one[i];
        if d == u256(1) {
            return Ok(s.clone());
        }
        if d == u256(2) && Self::fits(s, s) {
            return self.p.expr(Op::Shl, &[&self.p.constant(u256(1)), s]);
        }
        let diag = self.diag(i)?;
        self.p.expr(Op::Mulmod, &[&diag, s, &self.p.p])
    }

    fn diag(&self, i: usize) -> Result<Value> {
        let d = self.params.internal_diag_minus_one[i];
        if i < self.layout.diag_lets {
            return Ok(self.diag_locals[i].clone());
        }
        if i < self.layout.diag_lets + self.layout.diag_scratch {
            return self.p.mload(self.scratch_addr(i));
        }
        if i < self.t - self.layout.diag_in_memory {
            return Ok(self.p.constant(d));
        }
        if i >= self.t - self.layout.diag_fixed {
            return self.p.mload(self.fixed_addr(i));
        }
        self.p.mload(&self.table_addr(i))
    }

    fn scratch_addr(&self, i: usize) -> &'static str {
        if i == self.layout.diag_lets {
            "0"
        } else {
            "0x20"
        }
    }

    fn fixed_addr(&self, i: usize) -> &'static str {
        if i == self.t - self.layout.diag_fixed {
            "0x40"
        } else {
            "0x60"
        }
    }

    fn table_addr(&self, i: usize) -> String {
        let k = i - (self.t - self.layout.diag_in_memory);
        if k == 0 {
            "table".to_string()
        } else {
            format!("add(table, 0x{:x})", 32 * k)
        }
    }

    /// Sum of values into the variable `name`, reducing only when a partial
    /// sum would overflow or the total would exceed cap. Shallow values go
    /// innermost and the deepest local outermost, and the nesting is cut
    /// into further statements whenever an operand would otherwise be read
    /// with too many intermediates on the stack to reach it.
    fn chain_sum(&mut self, values: &[Value], name: &str, cap: U256) -> Result<Value> {
        let mut order: Vec<Value> = values.to_vec();
        // descending rank, the unranked (infinite) first; stable like the TS
        // sort, where two infinities compare as equal
        order.sort_by_key(|a| std::cmp::Reverse(self.rank(a)));
        let cap = wide(cap);
        let mut window: Vec<Step> = Vec::new();
        let mut acc: Option<Value> = None;
        // whether acc is the variable (a flush has happened)
        let mut acc_is_variable = false;
        let mut bound = U512::ZERO;
        let mut variable: Option<Value> = None;

        for (j, v) in order.iter().enumerate() {
            if acc.is_none() {
                acc = Some(v.clone());
                bound = wide(v.bound);
                continue;
            }
            let last = j == order.len() - 1;
            let lazy = bound + wide(v.bound);
            let reduce = lazy > wide(UINT256_MAX) || (last && lazy > cap);
            bound = if reduce { wide(PRIME - u256(1)) } else { lazy };
            let step = Step {
                v: v.clone(),
                reduce,
            };
            let mut extended = window.clone();
            extended.push(step.clone());
            let a = acc.as_ref().expect("acc set");
            if !self.window_fits(a, acc_is_variable, &extended) {
                let flushed = self.flush(a, &window, &variable, name)?;
                variable = Some(flushed.clone());
                acc = Some(flushed);
                acc_is_variable = true;
                window.clear();
                let a = acc.as_ref().expect("acc set");
                if !self.window_fits(a, acc_is_variable, std::slice::from_ref(&step)) {
                    bail!("{} is out of reach", v.name);
                }
            }
            window.push(step);
        }
        if !window.is_empty() || variable.is_none() {
            let a = acc.as_ref().expect("acc set");
            let flushed = self.flush(a, &window, &variable, name)?;
            variable = Some(flushed);
        }
        let variable = variable.expect("flushed");
        if wide(variable.bound) > cap {
            bail!("chain sum exceeds cap");
        }
        Ok(variable)
    }

    fn flush(
        &mut self,
        acc: &Value,
        window: &[Step],
        variable: &Option<Value>,
        name: &str,
    ) -> Result<Value> {
        let mut e = acc.clone();
        for Step { v, reduce } in window {
            e = if *reduce {
                self.p.expr(Op::Addmod, &[&e, v, &self.p.p])?
            } else {
                self.p.expr(Op::Add, &[&e, v])?
            };
        }
        if variable.is_some() {
            self.p.assign(name, &e)
        } else {
            self.p.let_(name, &e)
        }
    }

    /// Intermediates on the stack when operand j of a window is read: the
    /// operands outside it, plus PRIME for each reducing step from j out.
    /// The first value of the chain is innermost of all and read last.
    fn window_fits(&self, acc: &Value, acc_is_variable: bool, w: &[Step]) -> bool {
        let reach = |v: &Value, outer: &[Step], own: usize| {
            let reducing = outer.iter().filter(|o| o.reduce).count();
            self.reachable(v, outer.len() - own + reducing)
        };
        (acc_is_variable || reach(acc, w, 0))
            && w.iter().enumerate().all(|(j, s)| reach(&s.v, &w[j..], 1))
    }

    /// (s_i + c)^5 written back to element i; y and x2 are popped with the
    /// block
    fn sbox(&mut self, i: usize, c: Option<U256>) -> Result<()> {
        self.p.open();
        let y = match c {
            Some(c) => {
                let y = self.add(&self.state[i], &self.p.constant(c), false)?;
                self.p.let_("y", &y)?
            }
            None => self.state[i].clone(),
        };
        let x2 = self.p.expr(Op::Mulmod, &[&y, &y, &self.p.p])?;
        let x2 = self.p.let_("x2", &x2)?;
        let x4 = self.p.expr(Op::Mulmod, &[&x2, &x2, &self.p.p])?;
        let x5 = self.p.expr(Op::Mulmod, &[&x4, &y, &self.p.p])?;
        self.set(i, &x5)?;
        self.p.close();
        Ok(())
    }

    // ---- linear layers -----------------------------------------------------

    /// Poseidon2 M4 on the four elements idx, in place.
    ///   t0 = v0 + v1, t1 = v2 + v3, t2 = 2 v1 + t1, t3 = 2 v3 + t0
    ///   t4 = 4 t1 + t3, t5 = 4 t0 + t2, t6 = t3 + t5, t7 = t2 + t4
    ///   out = [t6, t5, t7, t4]
    fn m4(&mut self, idx: [usize; 4], clean: bool, needed: [bool; 4]) -> Result<()> {
        let v: Vec<Value> = idx.iter().map(|&i| self.state[i].clone()).collect();
        let one = self.p.constant(u256(1));
        let two_c = self.p.constant(u256(2));
        let four = self.p.constant(u256(4));
        let four_temps = self.layout.m4_temps == 4;
        self.p.open();
        // t0 and t1 as locals, or recomputed where they are used
        let (l0, l1) = if four_temps {
            let t0 = sum2(&self.p, &v[1], &v[0])?;
            let l0 = self.p.let_("t0", &t0)?;
            let t1 = sum2(&self.p, &v[3], &v[2])?;
            let l1 = self.p.let_("t1", &t1)?;
            (Some(l0), Some(l1))
        } else {
            (None, None)
        };
        let t0 = |p: &Program| -> Result<Value> {
            match &l0 {
                Some(l) => Ok(l.clone()),
                None => sum2(p, &v[1], &v[0]),
            }
        };
        let t1 = |p: &Program| -> Result<Value> {
            match &l1 {
                Some(l) => Ok(l.clone()),
                None => sum2(p, &v[3], &v[2]),
            }
        };
        let two =
            |p: &Program, x: &Value, t: &dyn Fn(&Program) -> Result<Value>| -> Result<Value> {
                // a raw input word is doubled with MULMOD
                let raw = !Self::fits(x, x);
                if four_temps {
                    let xx = if raw {
                        p.expr(Op::Mulmod, &[x, &two_c, &p.p])?
                    } else {
                        p.expr(Op::Add, &[x, x])?
                    };
                    p.expr(Op::Addmod, &[&xx, &t(p)?, &p.p])
                } else {
                    let tt = t(p)?;
                    let sh = if raw {
                        p.expr(Op::Mulmod, &[&two_c, x, &p.p])?
                    } else {
                        p.expr(Op::Shl, &[&one, x])?
                    };
                    p.expr(Op::Addmod, &[&tt, &sh, &p.p])
                }
            };
        let e2 = two(&self.p, &v[1], &t1)?;
        let t2 = self.p.let_("t2", &e2)?;
        let e3 = two(&self.p, &v[3], &t0)?;
        let t3 = self.p.let_("t3", &e3)?;
        // the deep operands of the recomputed sums go innermost so they are
        // read before the modulus and the other summand are on the stack
        let quad = |p: &Program, t: &dyn Fn(&Program) -> Result<Value>| -> Result<Value> {
            if four_temps {
                p.expr(Op::Mulmod, &[&t(p)?, &four, &p.p])
            } else {
                p.expr(Op::Mulmod, &[&four, &t(p)?, &p.p])
            }
        };
        let mut t4: Option<Value> = None;
        let mut t5: Option<Value> = None;
        if needed[3] || needed[2] {
            let q = quad(&self.p, &t1)?;
            let e = if four_temps {
                self.add(&q, &t3, clean)?
            } else {
                self.add(&t3, &q, clean)?
            };
            t4 = Some(if needed[3] {
                self.set(idx[3], &e)?
            } else {
                self.p.let_("t4", &e)?
            });
        }
        if needed[1] || needed[0] {
            let q = quad(&self.p, &t0)?;
            let e = if four_temps {
                self.add(&q, &t2, clean)?
            } else {
                self.add(&t2, &q, clean)?
            };
            t5 = Some(if needed[1] {
                self.set(idx[1], &e)?
            } else {
                self.p.let_("t5", &e)?
            });
        }
        if needed[0] {
            let e = self.add(&t3, t5.as_ref().expect("t5"), clean)?;
            self.set(idx[0], &e)?;
        }
        if needed[2] {
            let e = self.add(&t2, t4.as_ref().expect("t4"), clean)?;
            self.set(idx[2], &e)?;
        }
        self.p.close();
        Ok(())
    }

    fn external_matrix(&mut self, clean: bool, needed: [bool; 4]) -> Result<()> {
        let t = self.t;
        if t == 2 || t == 3 {
            // circ(2, 1[, 1]): out_i = s_i + sum
            self.p.open();
            let state = self.state.clone();
            let sum = self.chain_sum(&state, "sum", UINT256_MAX)?;
            for i in 0..t {
                let e = self.add(&sum, &self.state[i], clean)?;
                self.set(i, &e)?;
            }
            self.p.close();
            return Ok(());
        }
        if t == 4 {
            return self.m4([0, 1, 2, 3], clean, needed);
        }
        // y = M4 per block, z_i = sum over blocks of y_{b,i},
        // out_{b,i} = y_{b,i} + z_i; z_i is reduced far enough for the last
        // addition to stay lazy
        let k = t / 4;
        for b in 0..k {
            self.m4([4 * b, 4 * b + 1, 4 * b + 2, 4 * b + 3], false, [true; 4])?;
        }
        for i in 0..4 {
            self.p.open();
            let column: Vec<Value> = (0..k).map(|b| self.state[4 * b + i].clone()).collect();
            let widest = column.iter().map(|y| y.bound).max().unwrap_or(U256::ZERO);
            let cap = if clean {
                UINT256_MAX
            } else {
                UINT256_MAX - widest
            };
            let z = self.chain_sum(&column, "z", cap)?;
            for b in 0..k {
                let e = self.add(&z, &self.state[4 * b + i], clean)?;
                self.set(4 * b + i, &e)?;
            }
            self.p.close();
        }
        Ok(())
    }

    // ---- rounds ------------------------------------------------------------

    fn external_round(&mut self, round: usize, clean: bool, needed: [bool; 4]) -> Result<()> {
        for i in 0..self.t {
            // HashRest takes round 0's constants already added
            let c = self.params.round_constants[round][i];
            let c = if self.mode == Mode::HashRest && round == 0 {
                None
            } else {
                Some(c)
            };
            self.sbox(i, c)?;
        }
        self.external_matrix(clean, needed)
    }

    fn internal_outputs(&mut self, x5: &Value) -> Result<()> {
        let lazy = self.layout.internal_reduce_outputs;
        let mut old = vec![x5.clone()];
        old.extend_from_slice(&self.state[1..]);
        if self.layout.periodic_internal && self.t == 3 && !lazy && Self::fits(x5, &old[1]) {
            return self.periodic_outputs(&old);
        }
        let cap = if lazy {
            UINT256_MAX - x5.bound - (PRIME - u256(1))
        } else {
            PRIME - u256(1)
        };
        let sum = self.chain_sum(&old, "sum", cap)?;
        for (i, s) in old.iter().enumerate() {
            let scaled = self.scaled(s, i)?;
            let e = self.add(&sum, &scaled, lazy && i > 0)?;
            self.set(i, &e)?;
        }
        Ok(())
    }

    /// t = 3: sum = (x5 + s1 + s2) mod p with x5 + s1 lazy, so that s2 may
    /// grow to 5p; s1 + sum stays lazy while the next round's x5 + s1 fits.
    fn periodic_outputs(&mut self, old: &[Value]) -> Result<()> {
        let q = self.p.expr(Op::Add, &[&old[0], &old[1]])?;
        let e = self.p.expr(Op::Addmod, &[&q, &old[2], &self.p.p])?;
        let sum = self.p.let_("sum", &e)?;
        for (i, s) in old.iter().enumerate() {
            let scaled = self.scaled(s, i)?;
            let reduce = i == 1
                && wide(sum.bound) + wide(s.bound) + wide(PRIME - u256(1)) > wide(UINT256_MAX);
            let e = self.add(&sum, &scaled, reduce)?;
            self.set(i, &e)?;
        }
        Ok(())
    }

    /// s0 = (s0 + c)^5, then s_i = d_i s_i + sum with the sum reduced so
    /// that every output stays within 2p, or with internal_reduce_outputs
    /// the sum lazy as far as the next round's s0 + c fits and every other
    /// output reduced.
    fn internal_round(&mut self, round: usize) -> Result<()> {
        let c = self.params.round_constants[round][0];
        if !self.layout.internal_let {
            self.sbox(0, Some(c))?;
            self.p.open();
            let x5 = self.state[0].clone();
            self.internal_outputs(&x5)?;
            self.p.close();
            return Ok(());
        }
        self.p.open();
        let y = self.add(&self.state[0], &self.p.constant(c), false)?;
        let y = self.p.let_("y", &y)?;
        let x2 = self.p.expr(Op::Mulmod, &[&y, &y, &self.p.p])?;
        let x2 = self.p.let_("x2", &x2)?;
        let x4 = self.p.expr(Op::Mulmod, &[&x2, &x2, &self.p.p])?;
        let x5 = self.p.expr(Op::Mulmod, &[&x4, &y, &self.p.p])?;
        let x5 = self.p.let_("x5", &x5)?;
        self.internal_outputs(&x5)?;
        self.p.close();
        Ok(())
    }

    // ---- whole permutation -------------------------------------------------

    /// Inputs reduced mod PRIME and the initial linear layer. PRIME is
    /// declared after the state locals (unless prime_first) so that the
    /// locals, which are read with temporaries on top, are the deeper slots.
    fn entry(&mut self) -> Result<()> {
        let t = self.t;
        let raw_inputs = self.layout.raw_inputs;
        if raw_inputs >= self.layout.stack_elements {
            self.p.comment("inputs reduced mod PRIME by the first addmod or mulmod of the initial linear layer");
        } else if raw_inputs > 0 {
            self.p.comment(&format!(
                "inputs reduced mod PRIME (the last {raw_inputs} by the first addmod or mulmod of the initial linear layer)"
            ));
        } else {
            self.p.comment("inputs reduced mod PRIME");
        }
        let prime = if self.layout.prime_first {
            let c = self.p.constant(PRIME);
            self.p.let_("PRIME", &c)?
        } else {
            self.p.constant(PRIME)
        };
        let raw = |b: &Builder, i: usize| {
            let name = if b.mode == Mode::Hash {
                format!("s{i}")
            } else {
                format!("mload({})", Self::addr(i, "state"))
            };
            b.p.input(&name, b.inputs.iter().map(|input| input[i]).collect())
        };
        self.state = vec![prime.clone(); t];
        for i in 0..self.layout.stack_elements {
            let e = if i + self.layout.raw_inputs >= self.layout.stack_elements {
                raw(self, i)
            } else {
                self.p.expr(Op::Mod, &[&raw(self, i), &prime])?
            };
            self.state[i] = self.p.let_(&Self::name(i), &e)?;
        }
        if self.in_memory() > 0 {
            let mem = self.p.input("state", Vec::new());
            self.p.let_("mem", &mem)?;
        }
        if !self.layout.prime_first {
            self.p.let_("PRIME", &prime)?;
        }
        for i in self.layout.stack_elements..t {
            let e = self.p.expr(Op::Mod, &[&raw(self, i), &self.p.p])?;
            self.state[i] = self.p.mstore(&Self::addr(i, "mem"), &e)?;
        }
        self.p.blank();

        self.p.comment("initial linear layer");
        self.external_matrix(false, [true; 4])?;
        self.p.blank();
        Ok(())
    }

    fn build(mut self) -> Result<BuildResult> {
        let t = self.t;
        let rf_half = self.params.rounds_f / 2;
        let p_end = rf_half + self.params.rounds_p;
        let total = self.params.rounds_f + self.params.rounds_p;

        if self.mode == Mode::HashRest {
            let c = self.p.constant(PRIME);
            self.p.let_("PRIME", &c)?;
            let folded: Vec<Vec<U256>> = self
                .inputs
                .iter()
                .map(|input| round0_input(self.params, input))
                .collect();
            self.state = (0..t)
                .map(|i| {
                    let vals = folded.iter().map(|y| y[i]).collect();
                    self.p.input(&Self::name(i), vals)
                })
                .collect();
            self.p.blank();
        } else {
            self.entry()?;
        }

        for r in 0..rf_half {
            self.p.comment(&format!("round {r} (external)"));
            self.external_round(r, r == rf_half - 1, [true; 4])?;
            self.p.blank();
        }

        let internal = |b: &mut Builder| -> Result<()> {
            for r in rf_half..p_end {
                b.p.comment(&format!("round {r} (internal)"));
                b.internal_round(r)?;
                b.p.blank();
            }
            Ok(())
        };
        let Layout {
            diag_lets,
            diag_scratch,
            diag_in_memory,
            diag_fixed,
            ..
        } = self.layout;
        if diag_lets + diag_scratch + diag_in_memory > 0 {
            self.p.open();
            let d = self.params.internal_diag_minus_one.clone();
            if diag_lets > 0 {
                self.p.comment(
                    "diag constants as locals: solc copies a PUSH32 used more than once from code with few optimizer runs",
                );
                for (i, &d) in d.iter().enumerate().take(diag_lets) {
                    let local = self.p.let_(&format!("diag{i}"), &self.p.constant(d))?;
                    self.diag_locals.push(local);
                }
            }
            if diag_scratch > 0 {
                self.p.comment("diag constants in the scratch space");
                for (i, &d) in d.iter().enumerate().skip(diag_lets).take(diag_scratch) {
                    let addr = self.scratch_addr(i);
                    self.p.mstore(addr, &self.p.constant(d))?;
                }
            }
            if diag_in_memory > 0 {
                self.p.comment(
                    "diag constants that would not fit the code size as PUSH32, in free memory",
                );
                let table = self.p.input("mload(0x40)", Vec::new());
                self.p.let_("table", &table)?;
                let table = d.iter().enumerate().skip(t - diag_in_memory);
                for (i, &d) in table.take(diag_in_memory - diag_fixed) {
                    let addr = self.table_addr(i);
                    self.p.mstore(&addr, &self.p.constant(d))?;
                }
            }
            if diag_fixed > 0 {
                self.p.comment(
                    "diag constants in the free memory pointer and the zero slot, restored after the internal rounds",
                );
                for (i, &d) in d.iter().enumerate().skip(t - diag_fixed) {
                    let addr = self.fixed_addr(i);
                    self.p.mstore(addr, &self.p.constant(d))?;
                }
            }
            self.p.blank();
            internal(&mut self)?;
            if diag_fixed > 0 {
                self.p.line("mstore(0x40, table)");
            }
            if diag_fixed > 1 {
                self.p.line("mstore(0x60, 0)");
            }
            self.p.close();
        } else {
            internal(&mut self)?;
        }

        let needed = if self.mode != Mode::Array {
            [true, false, false, false]
        } else {
            [true; 4]
        };
        for r in p_end..total {
            self.p.comment(&format!("round {r} (external)"));
            let last = r == total - 1;
            self.external_round(r, last, if last { needed } else { [true; 4] })?;
            if !last {
                self.p.blank();
            }
        }

        self.p.blank();
        if self.mode != Mode::Array {
            let s0 = self.state[0].clone();
            self.p.assign("result", &s0)?;
        } else {
            let base = if self.in_memory() > 0 { "mem" } else { "state" };
            for i in 0..self.layout.stack_elements {
                let line = format!("mstore({}, {})", Self::addr(i, base), self.state[i].name);
                self.p.line(&line);
            }
        }

        // outputs must be clean and match the reference permutation
        let checked = if self.mode != Mode::Array { 1 } else { t };
        let outputs = &self.state[..checked];
        for (i, out) in outputs.iter().enumerate() {
            if out.bound >= PRIME {
                bail!("output {i} is not clean");
            }
        }
        for (k, input) in self.inputs.iter().enumerate() {
            let want = permutation(self.params, input);
            for (i, (out, want)) in outputs.iter().zip(&want).enumerate() {
                if out.vals[k] != *want {
                    bail!("vector {k} output {i} mismatch");
                }
            }
        }

        Ok(BuildResult {
            lines: self.p.lines,
        })
    }
}

pub fn build_permutation(
    params: &Params,
    inputs: &[Vec<U256>],
    layout: Layout,
    mode: Mode,
    indent: usize,
) -> Result<BuildResult> {
    Builder::new(params, inputs, layout, mode, indent)?.build()
}

/// a + b, with ADDMOD when a raw input word could overflow it
fn sum2(p: &Program, a: &Value, b: &Value) -> Result<Value> {
    if a.bound.checked_add(b.bound).is_some() {
        p.expr(Op::Add, &[a, b])
    } else {
        p.expr(Op::Addmod, &[a, b, &p.p])
    }
}

/// The state after the initial linear layer and round 0's constants, mod p.
fn round0_input(params: &Params, input: &[U256]) -> Vec<U256> {
    let mut s: Vec<U256> = input.iter().map(|&x| reduce(x)).collect();
    matmul_external(&mut s);
    for (x, &c) in s.iter_mut().zip(&params.round_constants[0]) {
        *x = add(*x, c);
    }
    s
}

/// hash_n's entry into `poseidon2_rest` (t = 4): the initial linear layer
/// and round 0's constants on [x, y, z, 0 .., n << 64] folded into four
/// linear forms over the reduced inputs, assigned to s0 .. s3. The test
/// inputs supply x, y, z.
pub fn build_hash_entry(
    params: &Params,
    inputs: &[Vec<U256>],
    n: usize,
    indent: usize,
) -> Result<BuildResult> {
    let mut p = Program::new(inputs.len(), indent);
    let prime = p.constant(PRIME);
    p.let_("PRIME", &prime)?;
    let arg = |p: &Program, i: usize| -> Result<Value> {
        let name = ["x", "y", "z"][i];
        let raw = p.input(name, inputs.iter().map(|input| input[i]).collect());
        p.expr(Op::Mod, &[&raw, &p.p])
    };
    // the constant part of each form
    let mut capacity = vec![U256::ZERO; 4];
    capacity[3] = u256(n as u64) << 64;
    let k: Vec<Value> = round0_input(params, &capacity)
        .into_iter()
        .map(|c| p.constant(c))
        .collect();
    let [one, two, four, five] = [1, 2, 4, 5].map(|v| p.constant(u256(v)));
    let ys = match n {
        // [5a, 4a, a, a]
        1 => {
            let a = arg(&p, 0)?;
            let a = p.let_("a", &a)?;
            vec![
                p.expr(Op::Mulmod, &[&a, &five, &p.p])?,
                p.expr(Op::Shl, &[&two, &a])?,
                a.clone(),
                a,
            ]
        }
        // with t0 = a + b: [5 t0 + 2b, 4 t0 + 2b, t0 + 2b, t0]
        2 => {
            let b = arg(&p, 1)?;
            let b = p.let_("b", &b)?;
            let t0 = p.expr(Op::Add, &[&b, &arg(&p, 0)?])?;
            let t0 = p.let_("t0", &t0)?;
            let b2 = p.expr(Op::Shl, &[&one, &b])?;
            let b2 = p.let_("b2", &b2)?;
            vec![
                p.expr(Op::Add, &[&p.expr(Op::Mulmod, &[&t0, &five, &p.p])?, &b2])?,
                p.expr(Op::Add, &[&p.expr(Op::Mulmod, &[&t0, &four, &p.p])?, &b2])?,
                p.expr(Op::Add, &[&t0, &b2])?,
                t0,
            ]
        }
        // with t0 = a + b, u = 2b + c, v = 4c + t0:
        // [5 t0 + u, 4 t0 + u, v + u, v]
        3 => {
            let b = arg(&p, 1)?;
            let b = p.let_("b", &b)?;
            let cz = arg(&p, 2)?;
            let cz = p.let_("c", &cz)?;
            let t0 = p.expr(Op::Add, &[&b, &arg(&p, 0)?])?;
            let t0 = p.let_("t0", &t0)?;
            let u = p.expr(Op::Add, &[&p.expr(Op::Shl, &[&one, &b])?, &cz])?;
            let u = p.let_("u", &u)?;
            let v = p.expr(Op::Add, &[&p.expr(Op::Mulmod, &[&cz, &four, &p.p])?, &t0])?;
            let v = p.let_("v", &v)?;
            vec![
                p.expr(Op::Add, &[&p.expr(Op::Mulmod, &[&t0, &five, &p.p])?, &u])?,
                p.expr(Op::Add, &[&p.expr(Op::Mulmod, &[&t0, &four, &p.p])?, &u])?,
                p.expr(Op::Addmod, &[&v, &u, &p.p])?,
                v,
            ]
        }
        _ => bail!("hash_{n} has no entry"),
    };
    // hash_1 in order, the others y3 first
    let order: [usize; 4] = if n == 1 { [0, 1, 2, 3] } else { [3, 2, 1, 0] };
    let mut out: Vec<Option<Value>> = vec![None; 4];
    for i in order {
        let e = p.expr(Op::Add, &[&ys[i], &k[i]])?;
        out[i] = Some(p.assign(&format!("s{i}"), &e)?);
    }
    for (j, input) in inputs.iter().enumerate() {
        let mut sponge = input[..n].to_vec();
        sponge.extend(capacity[n..].iter().copied());
        let want = round0_input(params, &sponge);
        for (i, y) in out.iter().enumerate() {
            if reduce(y.as_ref().expect("assigned").vals[j]) != want[i] {
                bail!("hash_{n} entry vector {j} output {i} mismatch");
            }
        }
    }
    Ok(BuildResult { lines: p.lines })
}
