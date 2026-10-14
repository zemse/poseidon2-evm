// Straight-line Yul emitter backed by the shared bound tracker.
//
// Every operand is a Value (../shared/value.ts) whose name is the Yul text that
// produces it: a variable, a literal, an mload or a nested expression. expr()
// builds a nested expression and runs applyOp on it, so an ADD or MUL that
// could overflow uint256 throws before any text is written, and every value
// carries its concrete result for each test vector. let(), assign() and
// mstore() are the only calls that emit statements.

import { PRIME, UINT256_MAX, hex } from "../shared/field.ts";
import { Value, applyOp, type Op } from "../shared/value.ts";

export function literal(c: bigint): string {
  if (c < 0n || c > UINT256_MAX) throw new Error("constant out of range");
  return c < 256n ? c.toString() : hex(c);
}

function rename(v: Value, name: string): Value {
  return new Value(name, v.bound, v.vals, v.constant);
}

export class Program {
  lines: string[] = [];
  // every `let` is a stack slot until its block ends: the count per open block
  private frames: number[] = [0];
  readonly vectors: number;
  readonly P: Value;
  private level: number;
  private memory = new Map<string, Value>();

  constructor(vectors: number, level: number) {
    this.vectors = vectors;
    this.level = level;
    this.P = new Value("PRIME", PRIME, new Array(vectors).fill(PRIME), PRIME);
  }

  // ---- text ----------------------------------------------------------------

  line(text: string) {
    this.lines.push("    ".repeat(this.level) + text);
  }

  comment(text: string) {
    this.line(`// ${text}`);
  }

  blank() {
    this.lines.push("");
  }

  block(f: () => void) {
    this.line("{");
    this.level++;
    this.frames.push(0);
    f();
    this.frames.pop();
    this.level--;
    this.line("}");
  }

  // slots currently held by `let`s of the open blocks
  get live(): number {
    return this.frames.reduce((a, b) => a + b, 0);
  }

  // ---- values --------------------------------------------------------------

  constant(c: bigint): Value {
    return new Value(literal(c), c, new Array(this.vectors).fill(c), c);
  }

  // A caller-supplied word (function argument or calldata): any uint256.
  input(name: string, vals: bigint[]): Value {
    return new Value(name, UINT256_MAX, vals);
  }

  // Nested expression; nothing is emitted. A result used more than once must
  // be bound with let() or the text would be evaluated twice.
  expr(op: Op, ...args: Value[]): Value {
    const name = `${op}(${args.map((a) => a.name).join(", ")})`;
    return applyOp(op, args, name, this.vectors);
  }

  let(name: string, v: Value): Value {
    this.frames[this.frames.length - 1]++;
    this.line(`let ${name} := ${v.name}`);
    return rename(v, name);
  }

  assign(name: string, v: Value): Value {
    this.line(`${name} := ${v.name}`);
    return rename(v, name);
  }

  // Store v at the address expression and return the value an mload of the
  // same address yields from now on.
  mstore(addr: string, v: Value): Value {
    this.line(`mstore(${addr}, ${v.name})`);
    const loaded = rename(v, `mload(${addr})`);
    this.memory.set(addr, loaded);
    return loaded;
  }

  mload(addr: string): Value {
    const v = this.memory.get(addr);
    if (!v) throw new Error(`mload of ${addr} before any mstore`);
    return v;
  }
}
