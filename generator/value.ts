// Bound-tracked field values shared by the Huff and Yul generators.
//
// A Value carries an exact upper bound (inclusive, as a BigInt) and one
// concrete evaluation per test vector. applyOp is the single place that
// decides what an EVM arithmetic opcode does to a bound: ADD and MUL are only
// allowed when the result provably fits in uint256, ADDMOD / MULMOD / MOD
// reduce to PRIME - 1. Lazy reduction is therefore proven by the tracker,
// never argued by hand.

import { PRIME, UINT256_MAX } from "./field.ts";

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

export type Op = "add" | "mul" | "addmod" | "mulmod" | "mod";

export const ARITY: Record<Op, number> = {
  add: 2,
  mul: 2,
  addmod: 3,
  mulmod: 3,
  mod: 2,
};

// Result of op on args (first operand first), with the bound of the result
// and its concrete value for each of the `vectors` test inputs.
export function applyOp(
  op: Op,
  args: Value[],
  name: string,
  vectors: number,
): Value {
  const [a, b, n] = args;
  const each = (f: (i: number) => bigint) =>
    Array.from({ length: vectors }, (_, i) => f(i));
  switch (op) {
    case "add": {
      const bound = a.bound + b.bound;
      if (bound > UINT256_MAX) {
        throw new Error(`add overflow: ${a.name} + ${b.name}`);
      }
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
      return new Value(
        name,
        bound,
        each((i) => a.vals[i] * b.vals[i]),
      );
    }
    case "addmod":
      if (!n.isPrime) throw new Error("addmod modulus must be PRIME");
      return new Value(
        name,
        PRIME - 1n,
        each((i) => (a.vals[i] + b.vals[i]) % PRIME),
      );
    case "mulmod":
      if (!n.isPrime) throw new Error("mulmod modulus must be PRIME");
      return new Value(
        name,
        PRIME - 1n,
        each((i) => (a.vals[i] * b.vals[i]) % PRIME),
      );
    case "mod":
      if (!b.isPrime) throw new Error("mod modulus must be PRIME");
      return new Value(
        name,
        PRIME - 1n,
        each((i) => a.vals[i] % PRIME),
      );
  }
}
