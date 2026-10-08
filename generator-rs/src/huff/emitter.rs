// Huff emitter backed by a symbolic stack simulator (huff/emitter.ts).
//
// Every stack slot holds a Value (../value.rs) with an exact upper bound and
// one concrete evaluation per test vector. The emitter records gas, maximum
// depth, maximum DUP index and bytecode size, and refuses any DUP or SWAP
// deeper than the fork allows: 16 with the legacy opcodes, 235 from
// Amsterdam where EIP-8024 adds DUPN / SWAPN, emitted as DUPn() / SWAPn()
// macros. Before Shanghai a zero is the ZERO() macro (PUSH1 0x00).
//
// A value that would be DUPed out of reach can instead be shadowed: stored to
// a memory slot when it is produced and loaded from there whenever it is out
// of reach. A permissive pass first records which values need it and a
// second pass with the same schedule shadows exactly those.
//
// Code the schedule reaches by JUMP more than once (the shared body of the
// internal rounds, schedule.rs) is simulated at every call: the first call
// records its lines and opcodes and pays its bytes, every later call replays
// the same schedule for the gas, the stack, the bounds and the concrete
// values without bytes or lines, and must emit the same opcodes segment by
// segment.
//
// Values live in an arena and are compared by index, as the TS compares
// objects by identity.

use std::collections::{HashMap, HashSet};

use super::fork::Fork;
use crate::bail;
use crate::error::Result;
use crate::field::{PRIME, U256, hex, hex_digits, u256};
use crate::value::{Op, Value, apply_op};

pub type Id = usize;

/// Text of a DUP of slot n (1-based from the top): the opcode mnemonic up
/// to 16, the EIP-8024 macro of Eip8024.huff above that.
pub fn dup_text(n: usize) -> String {
    if n <= 16 {
        format!("dup{n}")
    } else {
        format!("DUP{n}()")
    }
}

pub fn swap_text(n: usize) -> String {
    if n <= 16 {
        format!("swap{n}")
    } else {
        format!("SWAP{n}()")
    }
}

pub mod gas {
    pub const PUSH0: u64 = 2;
    pub const PUSH: u64 = 3;
    pub const DUP: u64 = 3;
    pub const SWAP: u64 = 3;
    pub const POP: u64 = 2;
    pub const MOD: u64 = 5;
    pub const MLOAD: u64 = 3;
    pub const MSTORE: u64 = 3;
    pub const JUMP: u64 = 8;
    pub const JUMPDEST: u64 = 1;
    /// plus 3 per word copied
    pub const CODECOPY: u64 = 3;
    pub const CALLDATALOAD: u64 = 3;
}

/// A code table of 32-byte words next to the macro (the round constants of
/// a body call), CODECOPYed to memory at its call site.
#[derive(Debug, Clone)]
pub struct Table {
    pub name: String,
    pub words: Vec<U256>,
}

/// off outside a body; the first call records, the others replay
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BodyMode {
    Off,
    Record,
    Replay,
}

fn op_gas(op: Op) -> u64 {
    match op {
        Op::Add | Op::Shl => 3,
        Op::Mul | Op::Mod => 5,
        Op::Addmod | Op::Mulmod => 8,
    }
}

/// Text, gas and bytes of PUSHing a constant on the fork.
pub fn push_text(c: U256, fork: &Fork) -> String {
    if c.is_zero() {
        return if fork.push0 { "0x0" } else { "ZERO()" }.to_string();
    }
    let digits = hex_digits(c);
    if digits.len().div_ceil(2) == 32 {
        hex(c)
    } else {
        format!("0x{digits}")
    }
}

pub fn push_gas(c: U256, fork: &Fork) -> u64 {
    if c.is_zero() && fork.push0 {
        gas::PUSH0
    } else {
        gas::PUSH
    }
}

pub fn push_bytes(c: U256, fork: &Fork) -> usize {
    if c.is_zero() {
        return if fork.push0 { 1 } else { 2 };
    }
    1 + hex_digits(c).len().div_ceil(2)
}

/// Name of a value a schedule may shadow: compute results in production
/// order, inputs by index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Key {
    Seq(usize),
    In(usize),
}

/// An operand of `compute`: a value to DUP (or push, for a constant not on
/// the stack), a value already at its final position (consumed in place), a
/// fresh constant, a constant loaded from memory at its turn, or a value
/// loaded from memory at its turn with a given bound (a round constant the
/// shared body reads, see `mload_value`).
#[derive(Debug, Clone)]
pub enum Operand {
    Val(Id),
    Inplace(Id),
    Const(U256, String),
    Mload(U256, usize, String),
    Load {
        offset: usize,
        name: String,
        bound: U256,
        vals: Vec<U256>,
    },
}

#[derive(Debug, Clone, Copy)]
struct Slot {
    offset: usize,
    round: i64,
}

pub struct Emitter {
    pub values: Vec<Value>,
    /// index 0 is the bottom of the stack, the top is last
    stack: Vec<Id>,
    pub lines: Vec<String>,
    pub gas: u64,
    pub bytes: usize,
    pub max_depth: usize,
    pub max_dup: usize,
    pub swaps: usize,
    pub pops: usize,
    /// highest memory offset written, exclusive
    pub memory: usize,
    pending: Vec<String>,
    /// whether lines are recorded (off for the builds of the option search)
    text: bool,
    vectors: usize,
    pub fork: Fork,
    pub max_reach: usize,
    /// the one PRIME value, so every copy on the stack shares identity
    pub p: Id,

    // shadow copies: keys of the values that may be shadowed and the keys
    // the schedule shadows
    keys: Vec<Option<Key>>,
    seq: usize,
    shadow: HashSet<Key>,
    /// keys DUPed out of reach, collected when permissive
    pub needed: HashSet<Key>,
    permissive: bool,
    // memory slots: a shadowed value lives in its slot for the round it is
    // produced in and the next one, then the slot is reused
    slots: HashMap<Id, usize>,
    holder: HashMap<usize, Id>,
    /// calldata offsets of the inputs that sit in calldata as the stack
    /// holds them (a part after the first): loaded from there, never stored
    calldata: HashMap<Id, usize>,
    pool: Vec<Slot>,
    round: i64,
    pub slot_base: usize,
    pub stores: usize,
    pub loads: usize,

    // shared body: the recorded lines and opcodes, a segment per body round
    body_mode: BodyMode,
    pub body_lines: Vec<Vec<String>>,
    body_ops: Vec<Vec<String>>,
    replay_ops: Vec<Vec<String>>,
    pub tables: Vec<Table>,
}

impl Emitter {
    pub fn new(
        vectors: usize,
        fork: Fork,
        shadow: HashSet<Key>,
        permissive: bool,
        text: bool,
    ) -> Emitter {
        let mut e = Emitter {
            values: Vec::with_capacity(4096),
            stack: Vec::with_capacity(1100),
            lines: Vec::new(),
            gas: 0,
            bytes: 0,
            max_depth: 0,
            max_dup: 0,
            swaps: 0,
            pops: 0,
            memory: 0,
            pending: Vec::new(),
            text,
            vectors,
            fork,
            max_reach: fork.reach,
            p: 0,
            keys: Vec::with_capacity(4096),
            seq: 0,
            shadow,
            needed: HashSet::new(),
            permissive,
            slots: HashMap::new(),
            holder: HashMap::new(),
            calldata: HashMap::new(),
            pool: Vec::new(),
            round: 0,
            slot_base: 0,
            stores: 0,
            loads: 0,
            body_mode: BodyMode::Off,
            body_lines: Vec::new(),
            body_ops: Vec::new(),
            replay_ops: Vec::new(),
            tables: Vec::new(),
        };
        e.p = e.alloc(Value {
            name: "P".to_string(),
            bound: PRIME,
            vals: vec![PRIME; vectors],
            constant: Some(PRIME),
        });
        e
    }

    pub fn alloc(&mut self, v: Value) -> Id {
        self.values.push(v);
        self.keys.push(None);
        self.values.len() - 1
    }

    pub fn value(&self, id: Id) -> &Value {
        &self.values[id]
    }

    pub fn bound(&self, id: Id) -> U256 {
        self.values[id].bound
    }

    pub fn name(&self, id: Id) -> &str {
        &self.values[id].name
    }

    /// The value k slots below the top, if any.
    pub fn at(&self, k: usize) -> Option<Id> {
        let len = self.stack.len();
        if k < len {
            Some(self.stack[len - 1 - k])
        } else {
            None
        }
    }

    pub fn top(&self, k: usize) -> Result<Id> {
        match self.at(k) {
            Some(v) => Ok(v),
            None => bail!("stack underflow"),
        }
    }

    /// Replaces the stack, the first value on top.
    pub fn set_stack(&mut self, from_top: &[Id]) {
        self.stack = from_top.iter().rev().copied().collect();
    }

    // ---- stack queries -----------------------------------------------------

    /// 1-based position from the top of the nearest copy of v, or 0 if absent
    pub fn find(&self, v: Id) -> usize {
        match self.stack.iter().rev().position(|&x| x == v) {
            Some(i) => i + 1,
            None => 0,
        }
    }

    pub fn find_prime(&self) -> usize {
        for (i, &x) in self.stack.iter().rev().enumerate().take(self.max_reach) {
            if self.values[x].is_prime() {
                return i + 1;
            }
        }
        0
    }

    pub fn depth(&self) -> usize {
        self.stack.len()
    }

    /// true when v sits within DUP reach or has a shadow copy to load
    pub fn reachable(&self, v: Id) -> bool {
        let n = self.find(v);
        (n > 0 && n <= self.max_reach)
            || self.slots.contains_key(&v)
            || self.calldata.contains_key(&v)
    }

    // ---- raw opcodes -------------------------------------------------------

    fn opcode(&mut self, text: impl FnOnce() -> String, gas: u64, bytes: usize) {
        self.gas += gas;
        match self.body_mode {
            BodyMode::Replay => {
                let text = text();
                self.replay_ops.last_mut().expect("segment").push(text);
            }
            BodyMode::Record => {
                let text = text();
                if self.text {
                    self.pending.push(text.clone());
                }
                self.bytes += bytes;
                self.body_ops.last_mut().expect("segment").push(text);
            }
            BodyMode::Off => {
                if self.text {
                    self.pending.push(text());
                }
                self.bytes += bytes;
            }
        }
    }

    /// An opcode outside the arithmetic (labels, jumps, CODECOPY).
    pub fn raw(&mut self, text: &str, gas: u64, bytes: usize) {
        self.opcode(|| text.to_string(), gas, bytes);
    }

    /// A value the stack holds that the arithmetic never sees (a code
    /// offset).
    fn push_opaque(&mut self, name: &str) -> Id {
        let v = self.alloc(Value {
            name: name.to_string(),
            bound: u256(0xffff),
            vals: vec![U256::ZERO; self.vectors],
            constant: None,
        });
        self.pushed(v);
        v
    }

    // The 1024 limit is left to the schedule search (a build over it is
    // rejected, or cut into parts), so the simulation runs through.
    fn pushed(&mut self, v: Id) {
        self.stack.push(v);
        if self.stack.len() > self.max_depth {
            self.max_depth = self.stack.len();
        }
    }

    pub fn dup(&mut self, v: Id) -> Result<Id> {
        let n = self.find(v);
        if n == 0 || n > self.max_reach {
            if let Some(&slot) = self.slots.get(&v) {
                self.load(slot, v)?;
                return Ok(v);
            }
            if let Some(&offset) = self.calldata.get(&v) {
                self.load_calldata(offset, v);
                return Ok(v);
            }
            if n == 0 {
                bail!("{} is not on the stack", self.name(v));
            }
            let key = self.keys[v];
            if let (true, Some(key)) = (self.permissive, key) {
                // charged as the MLOAD it becomes once v is shadowed
                self.needed.insert(key);
                self.opcode(|| dup_text(n), gas::PUSH + gas::MLOAD, 4);
                self.pushed(v);
                return Ok(v);
            }
            bail!("{} is out of reach (dup{n})", self.name(v));
        }
        self.opcode(|| dup_text(n), gas::DUP, if n <= 16 { 1 } else { 2 });
        if n > self.max_dup {
            self.max_dup = n;
        }
        self.pushed(v);
        Ok(v)
    }

    pub fn swap(&mut self, n: usize) -> Result<()> {
        if n < 1 || n > self.max_reach {
            bail!("swap{n} out of range");
        }
        let len = self.stack.len();
        if len <= n {
            bail!("swap below stack bottom");
        }
        self.opcode(|| swap_text(n), gas::SWAP, if n <= 16 { 1 } else { 2 });
        self.swaps += 1;
        self.stack.swap(len - 1, len - 1 - n);
        Ok(())
    }

    pub fn pop(&mut self) -> Result<()> {
        if self.stack.is_empty() {
            bail!("pop on empty stack");
        }
        self.opcode(|| "pop".to_string(), gas::POP, 1);
        self.pops += 1;
        self.stack.pop();
        Ok(())
    }

    pub fn push(&mut self, c: U256, name: Option<&str>) -> Result<Id> {
        let v = if c == PRIME {
            self.p
        } else {
            let name = match name {
                Some(name) => name.to_string(),
                None => format!("0x{}", hex_digits(c)),
            };
            let vals = vec![c; self.vectors];
            self.alloc(Value::new(name, c, vals, Some(c))?)
        };
        if c == PRIME {
            self.opcode(|| "[PRIME]".to_string(), gas::PUSH, 33);
        } else {
            let fork = self.fork;
            self.opcode(
                || push_text(c, &fork),
                push_gas(c, &fork),
                push_bytes(c, &fork),
            );
        }
        self.pushed(v);
        Ok(v)
    }

    /// Store the top of the stack at a memory offset (consumes it).
    pub fn mstore(&mut self, offset: usize) -> Result<()> {
        self.push(u256(offset as u64), None)?;
        self.opcode(|| "mstore".to_string(), gas::MSTORE, 1);
        let len = self.stack.len();
        self.stack.truncate(len.saturating_sub(2));
        if offset + 32 > self.memory {
            self.memory = offset + 32;
        }
        Ok(())
    }

    /// Store a constant at a memory offset (used once for the diag table).
    pub fn mstore_const(&mut self, c: U256, offset: usize) -> Result<()> {
        self.push(c, None)?;
        self.mstore(offset)
    }

    /// Load a constant previously stored with mstore_const.
    pub fn mload(&mut self, c: U256, offset: usize, name: &str) -> Result<Id> {
        self.push(u256(offset as u64), None)?;
        self.stack.pop();
        self.opcode(|| "mload".to_string(), gas::MLOAD, 1);
        let v = self.alloc(Value::new(
            name.to_string(),
            c,
            vec![c; self.vectors],
            Some(c),
        )?);
        self.pushed(v);
        Ok(v)
    }

    /// Load a value stored at a memory offset by code outside the simulation
    /// (a round constant a body call CODECOPYed): the bound is given, so that
    /// the body never depends on the value of one call.
    pub fn mload_value(
        &mut self,
        offset: usize,
        name: &str,
        bound: U256,
        vals: Vec<U256>,
    ) -> Result<Id> {
        self.push(u256(offset as u64), None)?;
        self.stack.pop();
        self.opcode(|| "mload".to_string(), gas::MLOAD, 1);
        let v = self.alloc(Value::new(name.to_string(), bound, vals, None)?);
        self.pushed(v);
        Ok(v)
    }

    /// Put a copy of PRIME on top: dup the nearest copy within reach, else
    /// push.
    pub fn push_prime(&mut self) -> Result<Id> {
        let n = self.find_prime();
        if n > 0 {
            let v = self.stack[self.stack.len() - n];
            return self.dup(v);
        }
        self.push(PRIME, None)
    }

    // ---- control flow ------------------------------------------------------

    /// `name:` (a JUMPDEST)
    pub fn label(&mut self, name: &str) {
        self.opcode(|| format!("{name}:"), gas::JUMPDEST, 1);
    }

    /// the offset of a label (a PUSH2)
    pub fn push_label(&mut self, name: &str) -> Id {
        self.opcode(|| name.to_string(), gas::PUSH, 3);
        self.push_opaque(name)
    }

    /// JUMP to the offset on top
    pub fn jump(&mut self) {
        self.opcode(|| "jump".to_string(), gas::JUMP, 1);
        self.stack.pop();
    }

    /// JUMP to the offset stored at a memory offset: <off> MLOAD JUMP
    pub fn jump_via(&mut self, offset: usize) -> Result<()> {
        self.push(u256(offset as u64), None)?;
        self.stack.pop();
        self.opcode(|| "mload".to_string(), gas::MLOAD, 1);
        self.push_opaque("ret");
        self.jump();
        Ok(())
    }

    /// A code table of the words, appended after the macro (render.rs); its
    /// bytes count once, at its definition.
    pub fn table(&mut self, name: &str, words: Vec<U256>) {
        self.bytes += 32 * words.len();
        self.tables.push(Table {
            name: name.to_string(),
            words,
        });
    }

    /// CODECOPY a table of `words` words to memory at `offset`
    pub fn codecopy(&mut self, name: &str, words: usize, offset: usize) -> Result<()> {
        self.push(u256(32 * words as u64), None)?;
        self.opcode(|| format!("__tablestart({name})"), gas::PUSH, 3);
        self.push_opaque(name);
        self.push(u256(offset as u64), None)?;
        self.opcode(
            || "codecopy".to_string(),
            gas::CODECOPY + 3 * words as u64,
            1,
        );
        let len = self.stack.len();
        self.stack.truncate(len.saturating_sub(3));
        if offset + 32 * words > self.memory {
            self.memory = offset + 32 * words;
        }
        Ok(())
    }

    // ---- shared body -------------------------------------------------------

    /// The first call of a body records, every later one replays: the lines
    /// and opcodes go to the current segment (see `segment`), bytes count
    /// only when recording. The pending opcodes must be flushed.
    pub fn begin_body(&mut self, record: bool) -> Result<()> {
        if !self.pending.is_empty() || self.body_mode != BodyMode::Off {
            bail!("beginBody within a line or a body");
        }
        if record {
            self.body_mode = BodyMode::Record;
            self.body_lines.clear();
            self.body_ops.clear();
        } else {
            self.body_mode = BodyMode::Replay;
            self.replay_ops.clear();
        }
        self.segment();
        Ok(())
    }

    /// A new segment (one per body round, and one for the exit): a replayed
    /// segment must repeat the opcodes of the recorded one.
    pub fn segment(&mut self) {
        self.end_line();
        if self.body_mode == BodyMode::Record {
            self.body_lines.push(Vec::new());
            self.body_ops.push(Vec::new());
        } else {
            self.replay_ops.push(Vec::new());
        }
    }

    /// Ends the body: a replay is checked against the recording, every
    /// segment in full but the last, which a call that leaves the body early
    /// cuts short at its exit.
    pub fn end_body(&mut self) -> Result<()> {
        self.end_line();
        if self.body_mode == BodyMode::Replay {
            let n = self.replay_ops.len();
            for (i, ops) in self.replay_ops.iter().enumerate() {
                let want: &[String] = self.body_ops.get(i).map_or(&[], Vec::as_slice);
                let same = if i == n - 1 {
                    ops.len() <= want.len()
                } else {
                    ops.len() == want.len()
                } && ops.iter().zip(want).all(|(a, b)| a == b);
                if !same {
                    let j = ops
                        .iter()
                        .enumerate()
                        .position(|(k, op)| want.get(k) != Some(op))
                        .unwrap_or(ops.len());
                    fn at(list: &[String], j: usize) -> &str {
                        list.get(j).map_or("end", String::as_str)
                    }
                    bail!(
                        "body segment {i} differs between calls at opcode {j}: {} recorded, {} replayed",
                        at(want, j),
                        at(ops, j)
                    );
                }
            }
        }
        self.body_mode = BodyMode::Off;
        Ok(())
    }

    // ---- shadow copies -----------------------------------------------------

    /// Names a value the schedule may shadow (compute results are keyed by
    /// their production order automatically).
    pub fn key(&mut self, v: Id, key: Key) {
        self.keys[v] = Some(key);
    }

    pub fn shadows(&self, key: Key) -> bool {
        self.shadow.contains(&key)
    }

    /// A new round starts: slots of values produced two rounds ago are free.
    pub fn next_round(&mut self) {
        self.round += 1;
    }

    fn allocate(&mut self, v: Id) -> usize {
        let round = self.round;
        let index = match self.pool.iter().position(|s| s.round <= round - 2) {
            Some(i) => i,
            None => {
                let offset = self.slot_base + 32 * self.pool.len();
                self.pool.push(Slot { offset, round: 0 });
                self.pool.len() - 1
            }
        };
        let slot = &mut self.pool[index];
        slot.round = round;
        let offset = slot.offset;
        self.slots.insert(v, offset);
        self.holder.insert(offset, v);
        if offset + 32 > self.memory {
            self.memory = offset + 32;
        }
        offset
    }

    /// Shadow the top of the stack: DUP1 <off> MSTORE, the value stays on
    /// top.
    pub fn store(&mut self, v: Id) -> Result<usize> {
        if self.top(0)? != v {
            bail!("store expects the value on top");
        }
        let offset = self.allocate(v);
        let fork = self.fork;
        let c = u256(offset as u64);
        self.opcode(|| "dup1".to_string(), gas::DUP, 1);
        self.opcode(
            || push_text(c, &fork),
            push_gas(c, &fork),
            push_bytes(c, &fork),
        );
        self.opcode(|| "mstore".to_string(), gas::MSTORE, 1);
        self.stores += 1;
        Ok(offset)
    }

    /// Declares v stored at a slot by code outside the macro (the entry).
    pub fn declare(&mut self, v: Id) -> usize {
        self.allocate(v)
    }

    /// Declares v the calldata word at `offset`, as it is: dup loads it
    /// from there (<off> CALLDATALOAD, 6 gas, as a slot) without a store.
    pub fn declare_calldata(&mut self, v: Id, offset: usize) {
        self.calldata.insert(v, offset);
    }

    /// Move the top of the stack to a fresh slot (<off> MSTORE, 6 gas): the
    /// value then lives in memory only and dup loads it.
    pub fn spill(&mut self, v: Id) -> Result<()> {
        if self.top(0)? != v {
            bail!("spill expects the value on top");
        }
        let offset = self.allocate(v);
        self.mstore(offset)
    }

    fn load(&mut self, offset: usize, v: Id) -> Result<()> {
        if self.holder.get(&offset) != Some(&v) {
            bail!("shadow slot of {} was reused while live", self.name(v));
        }
        let fork = self.fork;
        let c = u256(offset as u64);
        self.opcode(
            || push_text(c, &fork),
            push_gas(c, &fork),
            push_bytes(c, &fork),
        );
        self.opcode(|| "mload".to_string(), gas::MLOAD, 1);
        self.loads += 1;
        self.pushed(v);
        Ok(())
    }

    fn load_calldata(&mut self, offset: usize, v: Id) {
        let fork = self.fork;
        let c = u256(offset as u64);
        self.opcode(
            || push_text(c, &fork),
            push_gas(c, &fork),
            push_bytes(c, &fork),
        );
        self.opcode(|| "calldataload".to_string(), gas::CALLDATALOAD, 1);
        self.loads += 1;
        self.pushed(v);
    }

    // ---- arithmetic --------------------------------------------------------

    /// Places operands (listed top first) and applies op. In-place operands
    /// must form a suffix of the list and already sit at their final
    /// positions.
    pub fn compute(&mut self, op: Op, operands: &[Operand], name: &str) -> Result<Id> {
        let arity = op.arity();
        if operands.len() != arity {
            bail!("{} takes {arity}", op.text());
        }
        let mut operands: Vec<Operand> = operands.to_vec();
        let mut first_placed = arity;
        while first_placed > 0 && matches!(operands[first_placed - 1], Operand::Inplace(_)) {
            first_placed -= 1;
        }
        // a and b commute for every op but mod: push the deeper one first so
        // the shallower DUP is not pushed one slot further down
        if op != Op::Mod && first_placed >= 2 {
            let depth = |o: &Operand| match o {
                Operand::Val(v) if self.values[*v].constant.is_none() => self.find(*v),
                _ => 0,
            };
            if depth(&operands[0]) > depth(&operands[1]) {
                operands.swap(0, 1);
            }
        }
        for (i, o) in operands.iter().enumerate().skip(first_placed) {
            let Operand::Inplace(v) = o else {
                unreachable!("in-place suffix")
            };
            // slot from the top before the others are placed
            let pos = i - first_placed;
            let found = self.at(pos);
            if found != Some(*v) {
                let found = found.map_or("nothing", |f| self.name(f));
                bail!(
                    "{} expected in place at slot {} for {}, found {found}",
                    self.name(*v),
                    pos + 1,
                    op.text()
                );
            }
        }
        for o in operands[..first_placed].iter().rev() {
            match o {
                Operand::Inplace(_) => bail!("in-place operands must be the deepest ones"),
                Operand::Mload(c, offset, name) => {
                    self.mload(*c, *offset, name)?;
                }
                Operand::Load {
                    offset,
                    name,
                    bound,
                    vals,
                } => {
                    self.mload_value(*offset, name, *bound, vals.clone())?;
                }
                Operand::Const(c, name) => {
                    if *c == PRIME {
                        self.push_prime()?;
                    } else {
                        self.push(*c, Some(name))?;
                    }
                }
                Operand::Val(v) => {
                    let value = &self.values[*v];
                    match value.constant {
                        Some(c) if value.is_prime() || self.find(*v) == 0 => {
                            if value.is_prime() {
                                self.push_prime()?;
                            } else {
                                let name = value.name.clone();
                                self.push(c, Some(&name))?;
                            }
                        }
                        _ => {
                            self.dup(*v)?;
                        }
                    }
                }
            }
        }
        let len = self.stack.len();
        let args: Vec<Id> = self.stack[len - arity..].iter().rev().copied().collect();
        self.stack.truncate(len - arity);
        let result = {
            let refs: Vec<&Value> = args.iter().map(|&a| &self.values[a]).collect();
            apply_op(op, &refs, name.to_string(), self.vectors)?
        };
        self.opcode(|| op.text().to_string(), op_gas(op), 1);
        let result = self.alloc(result);
        self.pushed(result);
        let key = Key::Seq(self.seq);
        self.seq += 1;
        self.keys[result] = Some(key);
        if self.shadow.contains(&key) {
            self.store(result)?;
        }
        Ok(result)
    }

    /// True when a + b can be emitted as a plain ADD.
    pub fn fits_add(&self, a: U256, b: U256) -> bool {
        a.checked_add(b).is_some()
    }

    // ---- output ------------------------------------------------------------

    /// Flush pending opcodes as one line with a stack comment.
    pub fn end_line(&mut self) {
        self.end_line_indent("    ");
    }

    pub fn end_line_indent(&mut self, indent: &str) {
        if !self.text || self.pending.is_empty() {
            return;
        }
        let mut shown: Vec<&str> = self
            .stack
            .iter()
            .rev()
            .take(12)
            .map(|&v| self.values[v].name.as_str())
            .collect();
        if self.stack.len() > 12 {
            shown.push("...");
        }
        let ops = self.pending.join(" ");
        let line = format!("{indent}{ops:<40} // [{}]", shown.join(", "));
        self.pending.clear();
        self.line(line);
    }

    pub fn comment(&mut self, text: &str) {
        self.end_line();
        if self.text && self.body_mode != BodyMode::Replay {
            self.line(if text.is_empty() {
                String::new()
            } else {
                format!("    // {text}")
            });
        }
    }

    /// to the output, or to the body's current segment while recording
    fn line(&mut self, text: String) {
        if self.body_mode == BodyMode::Record {
            self.body_lines.last_mut().expect("segment").push(text);
        } else {
            self.lines.push(text);
        }
    }
}
