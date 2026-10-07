// Huff emitter backed by a symbolic stack simulator.
//
// Every stack slot holds a Value. A Value carries an exact upper bound
// (inclusive, as a BigInt) so the schedule can choose ADD over ADDMOD only
// when the sum provably fits in uint256, plus one concrete evaluation per test
// vector so the emitted stream is checked against the reference before any
// file is written. The emitter also records gas, maximum depth, maximum DUP
// index and bytecode size, and refuses any DUP or SWAP deeper than 16.

import { PRIME, UINT256_MAX, hex } from "../field.ts";

export class Value {
  private static counter = 0;
  readonly id: number;
  readonly bound: bigint;
  readonly vals: bigint[];
  readonly constant: bigint | undefined;
  name: string;

  constructor(name: string, bound: bigint, vals: bigint[], constant?: bigint) {
    this.id = Value.counter++;
    this.name = name;
    this.bound = bound;
    this.vals = vals;
    this.constant = constant;
    if (bound > UINT256_MAX) throw new Error(`bound overflow for ${name}`);
    for (const v of vals) {
      if (v > bound)
        throw new Error(`concrete value exceeds bound for ${name}`);
    }
  }

  get isPrime(): boolean {
    return this.constant === PRIME;
  }
}

export const GAS = {
  push0: 2,
  push: 3,
  dup: 3,
  swap: 3,
  pop: 2,
  add: 3,
  mul: 5,
  addmod: 8,
  mulmod: 8,
  mod: 5,
} as const;

export type Op = "add" | "mul" | "addmod" | "mulmod" | "mod";

const ARITY: Record<Op, number> = {
  add: 2,
  mul: 2,
  addmod: 3,
  mulmod: 3,
  mod: 2,
};

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

export const MAX_REACH = 16;
export const MAX_DEPTH = 1024;

export class Emitter {
  stack: Value[] = []; // index 0 is the top of the stack
  lines: string[] = [];
  gas = 0;
  bytes = 0;
  maxDepth = 0;
  maxDup = 0;
  swaps = 0;
  pops = 0;
  private pending: string[] = [];
  private readonly vectors: number;
  // the one PRIME value, so every copy on the stack shares identity
  readonly P: Value;

  constructor(vectors: number) {
    this.vectors = vectors;
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
    for (let i = 0; i < this.stack.length && i < MAX_REACH; i++) {
      if (this.stack[i].isPrime) return i + 1;
    }
    return 0;
  }

  get depth(): number {
    return this.stack.length;
  }

  // ---- raw opcodes ---------------------------------------------------------

  private opcode(text: string, gas: number, bytes: number) {
    this.pending.push(text);
    this.gas += gas;
    this.bytes += bytes;
  }

  private pushed(v: Value) {
    this.stack.unshift(v);
    if (this.stack.length > this.maxDepth) this.maxDepth = this.stack.length;
    if (this.stack.length > MAX_DEPTH) throw new Error("stack overflow (1024)");
  }

  dup(v: Value): Value {
    const n = this.find(v);
    if (n === 0) throw new Error(`${v.name} is not on the stack`);
    if (n > MAX_REACH) {
      throw new Error(`${v.name} is out of reach (dup${n})`);
    }
    this.opcode(`dup${n}`, GAS.dup, 1);
    if (n > this.maxDup) this.maxDup = n;
    this.pushed(v);
    return v;
  }

  swap(n: number) {
    if (n < 1 || n > MAX_REACH) throw new Error(`swap${n} out of range`);
    if (this.stack.length <= n) throw new Error("swap below stack bottom");
    this.opcode(`swap${n}`, GAS.swap, 1);
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
    } else if (c === 0n) {
      this.opcode("0x0", GAS.push0, 1);
    } else {
      const size = Math.ceil(c.toString(16).length / 2);
      const text = size === 32 ? hex(c) : "0x" + c.toString(16);
      this.opcode(text, GAS.push, 1 + size);
    }
    this.pushed(v);
    return v;
  }

  // Store a constant at a memory offset (used once for the diag table).
  mstoreConst(c: bigint, offset: number) {
    this.push(c);
    this.push(BigInt(offset));
    this.opcode("mstore", 3, 1);
    this.stack.splice(0, 2);
  }

  // Load a constant previously stored with mstoreConst.
  mload(c: bigint, offset: number, name: string): Value {
    this.push(BigInt(offset));
    this.stack.shift();
    this.opcode("mload", 3, 1);
    const v = new Value(name, c, new Array(this.vectors).fill(c), c);
    this.pushed(v);
    return v;
  }

  // Put a copy of PRIME on top: dup the nearest copy within reach, else push.
  pushPrime(): Value {
    const n = this.findPrime();
    if (n > 0) return this.dup(this.stack[n - 1]);
    return this.push(PRIME);
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
    return result;
  }

  private apply(op: Op, args: Value[], name: string): Value {
    const [a, b, n] = args;
    const each = (f: (i: number) => bigint) =>
      Array.from({ length: this.vectors }, (_, i) => f(i));
    switch (op) {
      case "add": {
        const bound = a.bound + b.bound;
        if (bound > UINT256_MAX) {
          throw new Error(`add overflow: ${a.name} + ${b.name}`);
        }
        this.opcode("add", GAS.add, 1);
        return new Value(
          name,
          bound,
          each((i) => a.vals[i] + b.vals[i]),
        );
      }
      case "mul": {
        const bound = a.bound * b.bound;
        if (bound > UINT256_MAX) {
          throw new Error(`mul overflow: ${a.name} * ${b.name}`);
        }
        this.opcode("mul", GAS.mul, 1);
        return new Value(
          name,
          bound,
          each((i) => a.vals[i] * b.vals[i]),
        );
      }
      case "addmod":
        if (!n.isPrime) throw new Error("addmod modulus must be PRIME");
        this.opcode("addmod", GAS.addmod, 1);
        return new Value(
          name,
          PRIME - 1n,
          each((i) => (a.vals[i] + b.vals[i]) % PRIME),
        );
      case "mulmod":
        if (!n.isPrime) throw new Error("mulmod modulus must be PRIME");
        this.opcode("mulmod", GAS.mulmod, 1);
        return new Value(
          name,
          PRIME - 1n,
          each((i) => (a.vals[i] * b.vals[i]) % PRIME),
        );
      case "mod":
        if (!b.isPrime) throw new Error("mod modulus must be PRIME");
        this.opcode("mod", GAS.mod, 1);
        return new Value(
          name,
          PRIME - 1n,
          each((i) => a.vals[i] % PRIME),
        );
    }
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
    this.lines.push(`${indent}${ops.padEnd(40)} // [${shown.join(", ")}]`);
  }

  comment(text: string, indent = "    ") {
    this.endLine(indent);
    this.lines.push(text === "" ? "" : `${indent}// ${text}`);
  }
}
