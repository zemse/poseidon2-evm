// Huff emitter backed by a symbolic stack simulator.
//
// Every stack slot holds a Value (../shared/value.ts). A Value carries an exact upper
// bound (inclusive, as a BigInt) so the schedule can choose ADD over ADDMOD
// only when the sum provably fits in uint256, plus one concrete evaluation per
// test vector so the emitted stream is checked against the reference before
// any file is written. The emitter also records gas, maximum depth, maximum
// DUP index and bytecode size, and refuses any DUP or SWAP deeper than the
// fork allows (fork.ts): 16 with the legacy opcodes, 235 from Amsterdam where
// EIP-8024 adds DUPN / SWAPN (3 gas, 2 bytes). huffc has no mnemonic for
// those, so they are emitted as DUPn() / SWAPn() macros wrapping __VERBATIM.
// Before Shanghai a zero is the ZERO() macro (PUSH1 0x00) since huffc turns
// every zero literal into PUSH0.
//
// A value that would be DUPed out of reach can instead be shadowed: stored to
// a memory slot when it is produced (DUP1 <off> MSTORE, 9 gas) and loaded
// from there (<off> MLOAD, 6 gas) whenever it is out of reach. Neither
// changes the stack layout, so a permissive pass first records which values
// need it, and when each is loaded for the last time, and a second pass with
// the same schedule shadows exactly those and frees each slot at that load.
//
// Code the schedule reaches by JUMP more than once (the shared body of the
// internal rounds, schedule.ts) is simulated at every call: the first call
// records its lines and opcodes and pays its bytes, every later call replays
// the same schedule for the gas, the stack, the bounds and the concrete
// values without bytes or lines, and must emit the same opcodes segment by
// segment, which is what makes one body valid for every call.

import { PRIME, UINT256_MAX, hex } from "../shared/field.ts";
import { ARITY, Value, applyOp, type Op } from "../shared/value.ts";
import { FORKS, type Fork } from "./fork.ts";

export { Value, type Op };

// Text of a DUP / SWAP of slot n (1-based from the top): the opcode mnemonic
// up to 16, the EIP-8024 macro of Eip8024.huff (render.ts) above that.
export function dupText(n: number): string {
  return n <= 16 ? `dup${n}` : `DUP${n}()`;
}

export function swapText(n: number): string {
  return n <= 16 ? `swap${n}` : `SWAP${n}()`;
}

export const GAS = {
  push0: 2,
  push: 3,
  dup: 3,
  swap: 3,
  pop: 2,
  add: 3,
  mul: 5,
  shl: 3,
  addmod: 8,
  mulmod: 8,
  mod: 5,
  mload: 3,
  mstore: 3,
  jump: 8,
  jumpdest: 1,
  // plus 3 per word copied
  codecopy: 3,
  calldataload: 3,
} as const;

// Memory expansion gas of a frame that touches [0, bytes).
export function memoryGas(bytes: number): number {
  const words = Math.ceil(bytes / 32);
  return 3 * words + Math.floor((words * words) / 512);
}

// A code table of 32-byte words next to the macro (the round constants of a
// body call), CODECOPYed to memory at its call site.
export type Table = { name: string; words: bigint[] };

// Text, gas and bytes of PUSHing a constant on the fork.
export function pushText(c: bigint, fork: Fork): string {
  if (c === 0n) return fork.push0 ? "0x0" : "ZERO()";
  const size = Math.ceil(c.toString(16).length / 2);
  return size === 32 ? hex(c) : "0x" + c.toString(16);
}

export function pushGas(c: bigint, fork: Fork): number {
  return c === 0n && fork.push0 ? GAS.push0 : GAS.push;
}

export function pushBytes(c: bigint, fork: Fork): number {
  if (c === 0n) return fork.push0 ? 1 : 2;
  return 1 + Math.ceil(c.toString(16).length / 2);
}

// Marks an operand the caller expects to already sit at its final position
// (it gets consumed in place). Other operands are duplicated or pushed.
export type Operand = Value | { inplace: Value } | { make: () => void };

export function inplace(v: Value): Operand {
  return { inplace: v };
}

// An operand produced on demand (for example by an MLOAD) at its turn.
export function make(f: () => void): Operand {
  return { make: f };
}

export class Emitter {
  stack: Value[] = []; // index 0 is the top of the stack
  lines: string[] = [];
  gas = 0;
  bytes = 0;
  maxDepth = 0;
  maxDup = 0;
  swaps = 0;
  pops = 0;
  // highest memory offset written, exclusive
  memory = 0;
  private pending: string[] = [];
  private readonly vectors: number;
  readonly fork: Fork;
  readonly maxReach: number;
  // the one PRIME value, so every copy on the stack shares identity
  readonly P: Value;

  // ---- shadow copies -------------------------------------------------------
  // keys of the values that may be shadowed (compute results in production
  // order, inputs named by the schedule) and the keys the schedule shadows
  private keys = new Map<Value, string>();
  private seq = 0;
  readonly shadow: ReadonlySet<string>;
  // keys DUPed out of reach, collected when permissive
  readonly needed = new Set<string>();
  readonly permissive: boolean;
  // dup calls per value so far, and per key the count at its last load
  // (collected when permissive; the real pass frees the slot there)
  private dups = new Map<Value, number>();
  lastLoad: ReadonlyMap<string, number> = new Map();
  // memory slots: a shadowed value lives in its slot until its last load
  // (known from the permissive pass), or for the round it is produced in
  // and the next one when no last load is known, then the slot is reused
  private slots = new Map<Value, number>();
  private holder = new Map<number, Value>();
  // calldata offsets of the inputs that sit in calldata as the stack holds
  // them (a part after the first): loaded from there, never stored
  private calldata = new Map<Value, number>();
  private pool: { offset: number; round: number }[] = [];
  private round = 0;
  slotBase = 0;
  stores = 0;
  loads = 0;

  // ---- shared body ---------------------------------------------------------
  // off outside a body; the first call records, the others replay
  private bodyMode: "off" | "record" | "replay" = "off";
  // the recorded lines and opcodes, a segment per body round
  readonly bodyLines: string[][] = [];
  private bodyOps: string[][] = [];
  private replayOps: string[][] = [];
  readonly tables: Table[] = [];

  constructor(
    vectors: number,
    fork: Fork = FORKS.shanghai,
    shadow: ReadonlySet<string> = new Set(),
    permissive = false,
  ) {
    this.vectors = vectors;
    this.fork = fork;
    this.maxReach = fork.reach;
    this.shadow = shadow;
    this.permissive = permissive;
    this.P = new Value("P", PRIME, new Array(vectors).fill(PRIME), PRIME);
  }

  top(k = 0): Value {
    if (k >= this.stack.length) throw new Error("stack underflow");
    return this.stack[k];
  }

  // ---- stack queries -------------------------------------------------------

  // 1-based position from the top of the nearest copy of v, or 0 if absent
  find(v: Value): number {
    for (let i = 0; i < this.stack.length; i++) {
      if (this.stack[i] === v) return i + 1;
    }
    return 0;
  }

  findPrime(): number {
    for (let i = 0; i < this.stack.length && i < this.maxReach; i++) {
      if (this.stack[i].isPrime) return i + 1;
    }
    return 0;
  }

  get depth(): number {
    return this.stack.length;
  }

  // true when v sits within DUP reach or has a shadow copy to load
  reachable(v: Value): boolean {
    const n = this.find(v);
    return (
      (n > 0 && n <= this.maxReach) || this.slots.has(v) || this.calldata.has(v)
    );
  }

  // ---- raw opcodes ---------------------------------------------------------

  private opcode(text: string, gas: number, bytes: number) {
    this.gas += gas;
    if (this.bodyMode === "replay") {
      this.replayOps[this.replayOps.length - 1].push(text);
      return;
    }
    this.pending.push(text);
    this.bytes += bytes;
    if (this.bodyMode === "record") {
      this.bodyOps[this.bodyOps.length - 1].push(text);
    }
  }

  // An opcode outside the arithmetic (labels, jumps, CODECOPY).
  raw(text: string, gas: number, bytes: number) {
    this.opcode(text, gas, bytes);
  }

  // A value the stack holds that the arithmetic never sees (a code offset).
  private pushOpaque(name: string): Value {
    const v = new Value(name, 0xffffn, new Array(this.vectors).fill(0n));
    this.pushed(v);
    return v;
  }

  // The 1024 limit is left to the schedule search (a build over it is
  // rejected, or cut into parts), so the simulation runs through.
  private pushed(v: Value) {
    this.stack.unshift(v);
    if (this.stack.length > this.maxDepth) this.maxDepth = this.stack.length;
  }

  dup(v: Value): Value {
    const n = this.find(v);
    const count = (this.dups.get(v) ?? 0) + 1;
    this.dups.set(v, count);
    const key = this.keys.get(v);
    if (n === 0 || n > this.maxReach) {
      const slot = this.slots.get(v);
      if (slot !== undefined) {
        this.load(slot, v);
        if (key !== undefined) {
          if (this.permissive) {
            (this.lastLoad as Map<string, number>).set(key, count);
          } else if (this.lastLoad.get(key) === count) {
            this.free(v, slot);
          }
        }
        return v;
      }
      const offset = this.calldata.get(v);
      if (offset !== undefined) {
        this.loadCalldata(offset, v);
        return v;
      }
      if (n === 0) throw new Error(`${v.name} is not on the stack`);
      if (this.permissive && key !== undefined) {
        // charged as the MLOAD it becomes once v is shadowed
        this.needed.add(key);
        (this.lastLoad as Map<string, number>).set(key, count);
        this.opcode(dupText(n), GAS.push + GAS.mload, 4);
        this.pushed(v);
        return v;
      }
      throw new Error(`${v.name} is out of reach (dup${n})`);
    }
    this.opcode(dupText(n), GAS.dup, n <= 16 ? 1 : 2);
    if (n > this.maxDup) this.maxDup = n;
    this.pushed(v);
    return v;
  }

  swap(n: number) {
    if (n < 1 || n > this.maxReach) throw new Error(`swap${n} out of range`);
    if (this.stack.length <= n) throw new Error("swap below stack bottom");
    this.opcode(swapText(n), GAS.swap, n <= 16 ? 1 : 2);
    this.swaps++;
    const tmp = this.stack[0];
    this.stack[0] = this.stack[n];
    this.stack[n] = tmp;
  }

  pop() {
    if (this.stack.length === 0) throw new Error("pop on empty stack");
    this.opcode("pop", GAS.pop, 1);
    this.pops++;
    this.stack.shift();
  }

  push(c: bigint, name?: string): Value {
    if (c < 0n || c > UINT256_MAX) throw new Error("constant out of range");
    const v =
      c === PRIME
        ? this.P
        : new Value(
            name ?? "0x" + c.toString(16),
            c,
            new Array(this.vectors).fill(c),
            c,
          );
    if (c === PRIME) {
      this.opcode("[PRIME]", GAS.push, 33);
    } else {
      this.opcode(
        pushText(c, this.fork),
        pushGas(c, this.fork),
        pushBytes(c, this.fork),
      );
    }
    this.pushed(v);
    return v;
  }

  // Store the top of the stack at a memory offset (consumes it).
  mstore(offset: number) {
    this.push(BigInt(offset));
    this.opcode("mstore", GAS.mstore, 1);
    this.stack.splice(0, 2);
    if (offset + 32 > this.memory) this.memory = offset + 32;
  }

  // Store a constant at a memory offset (used once for the diag table).
  mstoreConst(c: bigint, offset: number) {
    this.push(c);
    this.mstore(offset);
  }

  // Load a constant previously stored with mstoreConst.
  mload(c: bigint, offset: number, name: string): Value {
    this.push(BigInt(offset));
    this.stack.shift();
    this.opcode("mload", GAS.mload, 1);
    const v = new Value(name, c, new Array(this.vectors).fill(c), c);
    this.pushed(v);
    return v;
  }

  // Load a value stored at a memory offset by code outside the simulation
  // (a round constant a body call CODECOPYed): the bound is given, so that
  // the body never depends on the value of one call.
  mloadValue(
    offset: number,
    name: string,
    bound: bigint,
    vals: bigint[],
  ): Value {
    this.push(BigInt(offset));
    this.stack.shift();
    this.opcode("mload", GAS.mload, 1);
    const v = new Value(name, bound, vals);
    this.pushed(v);
    return v;
  }

  // Put a copy of PRIME on top: dup the nearest copy within reach, else push.
  pushPrime(): Value {
    const n = this.findPrime();
    if (n > 0) return this.dup(this.stack[n - 1]);
    return this.push(PRIME);
  }

  // ---- control flow --------------------------------------------------------

  // `name:` (a JUMPDEST)
  label(name: string) {
    this.opcode(`${name}:`, GAS.jumpdest, 1);
  }

  // the offset of a label (a PUSH2)
  pushLabel(name: string): Value {
    this.opcode(name, GAS.push, 3);
    return this.pushOpaque(name);
  }

  // JUMP to the offset on top
  jump() {
    this.opcode("jump", GAS.jump, 1);
    this.stack.shift();
  }

  // JUMP to the offset stored at a memory offset: <off> MLOAD JUMP
  jumpVia(offset: number) {
    this.push(BigInt(offset));
    this.stack.shift();
    this.opcode("mload", GAS.mload, 1);
    this.pushOpaque("ret");
    this.jump();
  }

  // A code table of the words, appended after the macro (render.ts); its
  // bytes count once, at its definition.
  table(name: string, words: bigint[]) {
    this.tables.push({ name, words });
    this.bytes += 32 * words.length;
  }

  // CODECOPY a table of `words` words to memory at `offset`
  codecopy(name: string, words: number, offset: number) {
    this.push(BigInt(32 * words));
    this.opcode(`__tablestart(${name})`, GAS.push, 3);
    this.pushOpaque(name);
    this.push(BigInt(offset));
    this.opcode("codecopy", GAS.codecopy + 3 * words, 1);
    this.stack.splice(0, 3);
    if (offset + 32 * words > this.memory) this.memory = offset + 32 * words;
  }

  // ---- shared body ---------------------------------------------------------

  // The first call of a body records, every later one replays: the lines
  // and opcodes go to the current segment (see segment), bytes count only
  // when recording. The pending opcodes must be flushed.
  beginBody(record: boolean) {
    if (this.pending.length > 0 || this.bodyMode !== "off") {
      throw new Error("beginBody within a line or a body");
    }
    this.bodyMode = record ? "record" : "replay";
    if (record) {
      this.bodyLines.length = 0;
      this.bodyOps.length = 0;
    } else {
      this.replayOps = [];
    }
    this.segment();
  }

  // A new segment (one per body round, and one for the exit): a replayed
  // segment must repeat the opcodes of the recorded one.
  segment() {
    this.endLine();
    if (this.bodyMode === "record") {
      this.bodyLines.push([]);
      this.bodyOps.push([]);
    } else {
      this.replayOps.push([]);
    }
  }

  // Ends the body: a replay is checked against the recording, every segment
  // in full but the last, which a call that leaves the body early cuts
  // short at its exit.
  endBody() {
    this.endLine();
    if (this.bodyMode === "replay") {
      const n = this.replayOps.length;
      for (const [i, ops] of this.replayOps.entries()) {
        const want = this.bodyOps[i] ?? [];
        const length =
          i === n - 1 ? ops.length <= want.length : ops.length === want.length;
        const same = length && ops.every((op, j) => op === want[j]);
        if (!same) {
          const j = ops.findIndex((op, k) => op !== want[k]);
          throw new Error(
            `body segment ${i} differs between calls at opcode ${j}: ` +
              `${want[j] ?? "end"} recorded, ${ops[j] ?? "end"} replayed`,
          );
        }
      }
    }
    this.bodyMode = "off";
  }

  // ---- shadow copies -------------------------------------------------------

  // Names a value the schedule may shadow (compute results are keyed by
  // their production order automatically).
  key(v: Value, key: string) {
    this.keys.set(v, key);
  }

  keyOf(v: Value): string | undefined {
    return this.keys.get(v);
  }

  // A new round starts: slots of values produced two rounds ago are free.
  nextRound() {
    this.round++;
  }

  private allocate(v: Value): number {
    let slot = this.pool.find((s) => s.round <= this.round - 2);
    if (!slot) {
      slot = { offset: this.slotBase + 32 * this.pool.length, round: 0 };
      this.pool.push(slot);
    }
    slot.round = this.round;
    this.slots.set(v, slot.offset);
    this.holder.set(slot.offset, v);
    if (slot.offset + 32 > this.memory) this.memory = slot.offset + 32;
    return slot.offset;
  }

  // The slot of v is free once its last load is done.
  private free(v: Value, offset: number) {
    this.slots.delete(v);
    this.holder.delete(offset);
    this.pool[(offset - this.slotBase) / 32].round = -Infinity;
  }

  // Shadow the top of the stack: DUP1 <off> MSTORE, the value stays on top.
  store(v: Value): number {
    if (this.top(0) !== v) throw new Error("store expects the value on top");
    const offset = this.allocate(v);
    this.opcode("dup1", GAS.dup, 1);
    this.opcode(
      pushText(BigInt(offset), this.fork),
      pushGas(BigInt(offset), this.fork),
      pushBytes(BigInt(offset), this.fork),
    );
    this.opcode("mstore", GAS.mstore, 1);
    this.stores++;
    return offset;
  }

  // Declares v stored at a slot by code outside the macro (the entry).
  declare(v: Value): number {
    return this.allocate(v);
  }

  // Declares v the calldata word at `offset`, as it is: dup loads it from
  // there (<off> CALLDATALOAD, 6 gas, as a slot) without a store.
  declareCalldata(v: Value, offset: number) {
    this.calldata.set(v, offset);
  }

  // Move the top of the stack to a fresh slot (<off> MSTORE, 6 gas): the
  // value then lives in memory only and dup loads it.
  spill(v: Value) {
    if (this.top(0) !== v) throw new Error("spill expects the value on top");
    this.mstore(this.allocate(v));
  }

  slotOf(v: Value): number | undefined {
    return this.slots.get(v);
  }

  private load(offset: number, v: Value) {
    if (this.holder.get(offset) !== v) {
      throw new Error(`shadow slot of ${v.name} was reused while live`);
    }
    this.opcode(
      pushText(BigInt(offset), this.fork),
      pushGas(BigInt(offset), this.fork),
      pushBytes(BigInt(offset), this.fork),
    );
    this.opcode("mload", GAS.mload, 1);
    this.loads++;
    this.pushed(v);
  }

  private loadCalldata(offset: number, v: Value) {
    this.opcode(
      pushText(BigInt(offset), this.fork),
      pushGas(BigInt(offset), this.fork),
      pushBytes(BigInt(offset), this.fork),
    );
    this.opcode("calldataload", GAS.calldataload, 1);
    this.loads++;
    this.pushed(v);
  }

  // ---- arithmetic ----------------------------------------------------------

  // Places operands (listed top first) and applies op. In-place operands must
  // form a suffix of the list and already sit at their final positions.
  compute(op: Op, operands: Operand[], name: string): Value {
    const arity = ARITY[op];
    if (operands.length !== arity) throw new Error(`${op} takes ${arity}`);
    let firstPlaced = arity;
    while (firstPlaced > 0 && "inplace" in operands[firstPlaced - 1]) {
      firstPlaced--;
    }
    // a and b commute for every op but mod: push the deeper one first so the
    // shallower DUP is not pushed one slot further down
    if (op !== "mod" && firstPlaced >= 2) {
      const depth = (o: Operand) =>
        o instanceof Value && o.constant === undefined ? this.find(o) : 0;
      if (depth(operands[0]) > depth(operands[1])) {
        operands = [operands[1], operands[0], ...operands.slice(2)];
      }
    }
    for (let i = firstPlaced; i < arity; i++) {
      const o = operands[i] as { inplace: Value };
      const pos = i - firstPlaced; // slot from the top before the others are placed
      if (this.stack[pos] !== o.inplace) {
        throw new Error(
          `${o.inplace.name} expected in place at slot ${pos + 1} for ${op}, ` +
            `found ${this.stack[pos]?.name ?? "nothing"}`,
        );
      }
    }
    for (let i = firstPlaced - 1; i >= 0; i--) {
      const o = operands[i];
      if ("inplace" in o) {
        throw new Error("in-place operands must be the deepest ones");
      }
      if ("make" in o) {
        const before = this.stack.length;
        o.make();
        if (this.stack.length !== before + 1) {
          throw new Error("make must push exactly one value");
        }
        continue;
      }
      if (o.constant !== undefined && (o.isPrime || this.find(o) === 0)) {
        if (o.isPrime) this.pushPrime();
        else this.push(o.constant, o.name);
      } else {
        this.dup(o);
      }
    }
    const args = this.stack.splice(0, arity);
    const result = this.apply(op, args, name);
    this.pushed(result);
    const key = `#${this.seq++}`;
    this.keys.set(result, key);
    if (this.shadow.has(key)) this.store(result);
    return result;
  }

  private apply(op: Op, args: Value[], name: string): Value {
    const result = applyOp(op, args, name, this.vectors);
    this.opcode(op, GAS[op], 1);
    return result;
  }

  // True when a + b can be emitted as a plain ADD.
  fitsAdd(a: Value, b: Value, cap = UINT256_MAX): boolean {
    return a.bound + b.bound <= cap;
  }

  // ---- output --------------------------------------------------------------

  // Flush pending opcodes as one line with a stack comment.
  endLine(indent = "    ") {
    if (this.pending.length === 0) return;
    const shown = this.stack.slice(0, 12).map((v) => v.name);
    if (this.stack.length > 12) shown.push("...");
    const ops = this.pending.join(" ");
    this.pending = [];
    this.line(`${indent}${ops.padEnd(40)} // [${shown.join(", ")}]`);
  }

  comment(text: string, indent = "    ") {
    this.endLine(indent);
    if (this.bodyMode === "replay") return;
    this.line(text === "" ? "" : `${indent}// ${text}`);
  }

  // to the output, or to the body's current segment while recording
  private line(text: string) {
    if (this.bodyMode === "record") {
      this.bodyLines[this.bodyLines.length - 1].push(text);
    } else {
      this.lines.push(text);
    }
  }
}
