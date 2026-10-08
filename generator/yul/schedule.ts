// Poseidon2 permutation as straight-line Yul.
//
// The schedule only decides the order of the field operations and where the
// state lives (Yul locals or the caller's memory array); whether an addition
// is ADD or ADDMOD, and a doubling ADD or MULMOD, is decided per operation
// from the exact bounds the Program tracks. Reductions are forced only where
// they buy laziness later: the M4 temporaries t2 / t3, the internal round sum
// and the column sums of the t = 4k linear layer.
//
// The legacy solc pipeline compiles inline assembly almost literally, with
// or without the optimizer, so the text is shaped for it: results are
// written once per statement as nested expressions, temporaries live in
// blocks that end right after their last use, and in a nested expression
// the deepest local is the outermost operand because solc evaluates
// arguments right to left. Every local is kept within DUP16 / SWAP16 by the
// reach model below, which assumes the literal compile.

import { PRIME, UINT256_MAX } from "../shared/field.ts";
import type { Params } from "../params/params.ts";
import { permutation } from "../shared/reference.ts";
import { Value } from "../shared/value.ts";
import { Program } from "./program.ts";

export type Layout = {
  // elements 0 .. stackElements - 1 live in Yul locals state0, state1, ...;
  // the rest stay in the state array in memory (array mode only)
  stackElements: number;
  // how many of the trailing internal diag constants are kept in a memory
  // table (loaded with MLOAD) instead of PUSH32 literals, to save code size
  diagInMemory: number;
  // M4 with two temporaries (t2, t3) instead of four: t0 and t1 are
  // recomputed (two extra ADDs per M4) so that a block of locals sitting 12
  // deep can still be assigned within SWAP16
  m4Temps: 2 | 4;
  // keep the internal round's x^5 in a `let` that lives through the round
  // instead of writing it back to state0 first; costs one slot of reach
  internalLet: boolean;
};

export type Mode =
  // t = 4 library: the inputs are the function arguments s0 .. s3 and only
  // element 0 is returned, as `result`
  | { kind: "hash" }
  // in-place permutation of the memory array `state`
  | { kind: "array" };

export type BuildResult = {
  lines: string[];
  outputs: Value[];
};

class Builder {
  readonly p: Program;
  readonly t: number;
  readonly params: Params;
  readonly layout: Layout;
  readonly mode: Mode;
  readonly inputs: bigint[][];
  state: Value[] = [];

  constructor(
    params: Params,
    inputs: bigint[][],
    layout: Layout,
    mode: Mode,
    indent: number,
  ) {
    this.params = params;
    this.t = params.t;
    this.layout = layout;
    this.mode = mode;
    this.inputs = inputs;
    this.p = new Program(inputs.length, indent);
    if (mode.kind === "hash" && (params.t !== 4 || layout.stackElements !== 4))
      throw new Error("hash mode is the t = 4 library with all locals");
    if (layout.stackElements > params.t || layout.diagInMemory > params.t)
      throw new Error("layout exceeds t");
  }

  get P(): Value {
    return this.p.P;
  }

  // ---- state placement -----------------------------------------------------

  isLocal(i: number): boolean {
    return i < this.layout.stackElements;
  }

  name(i: number): string {
    return `state${i}`;
  }

  // address of element i in the state array; `mem` aliases `state` once
  // the locals are declared, because the function argument sits under all
  // of them and would be out of reach
  addr(i: number, base = "mem"): string {
    return i === 0 ? base : `add(${base}, 0x${(32 * i).toString(16)})`;
  }

  get inMemory(): number {
    return this.t - this.layout.stackElements;
  }

  set(i: number, v: Value): Value {
    this.state[i] = this.isLocal(i)
      ? this.p.assign(this.name(i), v)
      : this.p.mstore(this.addr(i), v);
    return this.state[i];
  }

  // Locals are stack slots in declaration order: state0 is the deepest,
  // then the `mem` pointer that loads of memory elements go through.
  // Anything else (temporaries, expressions) is within easy reach.
  rank(v: Value): number {
    const m = /^state(\d+)$/.exec(v.name);
    if (m && this.isLocal(Number(m[1]))) return Number(m[1]);
    if (v.name.startsWith("mload(mem") || v.name.startsWith("mload(add(mem"))
      return this.layout.stackElements;
    return Infinity;
  }

  // Whether v can be DUPed with `intermediates` values pushed above the
  // live lets. Locals sit under every later let (PRIME, the diag table
  // pointer, temporaries); a memory element also pushes its offset before
  // `mem` is read.
  reachable(v: Value, intermediates: number): boolean {
    const i = this.rank(v);
    if (i === Infinity) return true;
    const offset = i === this.layout.stackElements ? 1 : 0;
    const above = this.p.live - 1 - i;
    return above + intermediates + offset + 1 <= 16;
  }

  // ---- arithmetic ----------------------------------------------------------

  fits(a: Value, b: Value): boolean {
    return a.bound + b.bound <= UINT256_MAX;
  }

  // a + b, lazily unless the bound says otherwise or a reduction is asked for
  add(a: Value, b: Value, reduce = false): Value {
    if (reduce || !this.fits(a, b)) return this.p.expr("addmod", a, b, this.P);
    return this.p.expr("add", a, b);
  }

  // d * s for the internal diagonal: 1 and 2 are the fixed t <= 3 diagonals
  scaled(s: Value, i: number): Value {
    const d = this.params.internalDiagMinusOne[i];
    if (d === 1n) return s;
    if (d === 2n && this.fits(s, s)) {
      return this.p.expr("shl", this.p.constant(1n), s);
    }
    return this.p.expr("mulmod", this.diag(i), s, this.P);
  }

  diag(i: number): Value {
    const d = this.params.internalDiagMinusOne[i];
    if (i < this.t - this.layout.diagInMemory) return this.p.constant(d);
    return this.p.mload(this.tableAddr(i));
  }

  tableAddr(i: number): string {
    const k = i - (this.t - this.layout.diagInMemory);
    return k === 0 ? "table" : `add(table, 0x${(32 * k).toString(16)})`;
  }

  // Sum of values into the variable `name`, reducing only when a partial
  // sum would overflow or the total would exceed cap. Shallow values go
  // innermost and the deepest local outermost, and the nesting is cut into
  // further statements whenever an operand would otherwise be read with too
  // many intermediates on the stack to reach it.
  chainSum(values: Value[], name: string, cap = UINT256_MAX): Value {
    const p = this.p;
    const order = values.slice().sort((a, b) => this.rank(b) - this.rank(a));
    // operand j of the current statement, innermost first, and whether the
    // step that adds it reduces
    let window: { v: Value; reduce: boolean }[] = [];
    let acc: Value | undefined;
    let bound = 0n;
    let variable: Value | undefined;
    const flush = () => {
      let e = acc!;
      for (const { v, reduce } of window) {
        e = reduce ? p.expr("addmod", e, v, this.P) : p.expr("add", e, v);
      }
      variable = variable ? p.assign(name, e) : p.let(name, e);
      acc = variable;
      window = [];
    };
    // intermediates on the stack when operand j of a window of n is read:
    // the operands outside it, plus PRIME for each reducing step from j out.
    // The first value of the chain is innermost of all and read last.
    const fits = (w: { v: Value; reduce: boolean }[]) => {
      const reach = (v: Value, outer: { reduce: boolean }[], own: number) =>
        this.reachable(
          v,
          outer.length - own + outer.filter((o) => o.reduce).length,
        );
      return (
        (acc === variable || reach(acc!, w, 0)) &&
        w.every(({ v }, j) => reach(v, w.slice(j), 1))
      );
    };
    for (let j = 0; j < order.length; j++) {
      const v = order[j];
      if (acc === undefined) {
        acc = v;
        bound = v.bound;
        continue;
      }
      const last = j === order.length - 1;
      const lazy = bound + v.bound;
      const reduce = lazy > UINT256_MAX || (last && lazy > cap);
      bound = reduce ? PRIME - 1n : lazy;
      const step = { v, reduce };
      if (!fits([...window, step])) {
        flush();
        if (!fits([step])) throw new Error(`${v.name} is out of reach`);
      }
      window.push(step);
    }
    if (window.length > 0 || variable === undefined) flush();
    if (variable!.bound > cap) throw new Error("chain sum exceeds cap");
    return variable!;
  }

  // (s_i + c)^5 written back to element i; y and x2 are popped with the block
  sbox(i: number, c: bigint) {
    const p = this.p;
    p.block(() => {
      const y = p.let("y", this.add(this.state[i], p.constant(c)));
      const x2 = p.let("x2", p.expr("mulmod", y, y, this.P));
      this.set(
        i,
        p.expr("mulmod", p.expr("mulmod", x2, x2, this.P), y, this.P),
      );
    });
  }

  // ---- linear layers -------------------------------------------------------

  // Poseidon2 M4 on the four elements idx, in place.
  //   t0 = v0 + v1, t1 = v2 + v3, t2 = 2 v1 + t1, t3 = 2 v3 + t0
  //   t4 = 4 t1 + t3, t5 = 4 t0 + t2, t6 = t3 + t5, t7 = t2 + t4
  //   out = [t6, t5, t7, t4]
  // t2 and t3 are reduced so that t4 .. t7 and the next round's constant
  // addition stay lazy. With `clean` every output is reduced. Outputs not in
  // `needed` are skipped (or kept as temporaries when another output uses
  // them). With two temporaries the doublings are shifts evaluated before
  // the other operand so a deep element is read with one intermediate on
  // the stack; with four, add(v, v) compiles a little cheaper.
  m4(idx: number[], clean: boolean, needed = [true, true, true, true]) {
    const p = this.p;
    const v = idx.map((i) => this.state[i]);
    const one = p.constant(1n);
    const four = p.constant(4n);
    p.block(() => {
      // t0 and t1 as locals, or recomputed where they are used
      const t0 = () => p.expr("add", v[1], v[0]);
      const t1 = () => p.expr("add", v[3], v[2]);
      let T0 = t0;
      let T1 = t1;
      if (this.layout.m4Temps === 4) {
        const l0 = p.let("t0", t0());
        const l1 = p.let("t1", t1());
        T0 = () => l0;
        T1 = () => l1;
      }
      const two = (x: Value, t: () => Value) =>
        this.layout.m4Temps === 4
          ? p.expr("addmod", p.expr("add", x, x), t(), this.P)
          : p.expr("addmod", t(), p.expr("shl", one, x), this.P);
      const t2 = p.let("t2", two(v[1], T1));
      const t3 = p.let("t3", two(v[3], T0));
      // the deep operands of the recomputed sums go innermost so they are
      // read before the modulus and the other summand are on the stack
      const quad = (t: () => Value) =>
        this.layout.m4Temps === 4
          ? p.expr("mulmod", t(), four, this.P)
          : p.expr("mulmod", four, t(), this.P);
      let t4: Value | undefined;
      let t5: Value | undefined;
      if (needed[3] || needed[2]) {
        const e =
          this.layout.m4Temps === 4
            ? this.add(quad(T1), t3, clean)
            : this.add(t3, quad(T1), clean);
        t4 = needed[3] ? this.set(idx[3], e) : p.let("t4", e);
      }
      if (needed[1] || needed[0]) {
        const e =
          this.layout.m4Temps === 4
            ? this.add(quad(T0), t2, clean)
            : this.add(t2, quad(T0), clean);
        t5 = needed[1] ? this.set(idx[1], e) : p.let("t5", e);
      }
      if (needed[0]) this.set(idx[0], this.add(t3, t5!, clean));
      if (needed[2]) this.set(idx[2], this.add(t2, t4!, clean));
    });
  }

  externalMatrix(clean: boolean, needed?: boolean[]) {
    const p = this.p;
    const t = this.t;
    if (t === 2 || t === 3) {
      // circ(2, 1[, 1]): out_i = s_i + sum
      p.block(() => {
        const sum = this.chainSum(this.state, "sum");
        for (let i = 0; i < t; i++) {
          this.set(i, this.add(sum, this.state[i], clean));
        }
      });
      return;
    }
    if (t === 4) {
      this.m4([0, 1, 2, 3], clean, needed);
      return;
    }
    // y = M4 per block, z_i = sum over blocks of y_{b,i},
    // out_{b,i} = y_{b,i} + z_i; z_i is reduced far enough for the last
    // addition to stay lazy
    const k = t / 4;
    for (let b = 0; b < k; b++) {
      this.m4(
        [0, 1, 2, 3].map((i) => 4 * b + i),
        false,
      );
    }
    for (let i = 0; i < 4; i++) {
      p.block(() => {
        const column = Array.from(
          { length: k },
          (_, b) => this.state[4 * b + i],
        );
        const widest = column.reduce((m, y) => (y.bound > m ? y.bound : m), 0n);
        const cap = clean ? UINT256_MAX : UINT256_MAX - widest;
        const z = this.chainSum(column, "z", cap);
        for (let b = 0; b < k; b++) {
          this.set(4 * b + i, this.add(z, this.state[4 * b + i], clean));
        }
      });
    }
  }

  // ---- rounds --------------------------------------------------------------

  externalRound(round: number, clean: boolean, needed?: boolean[]) {
    const rc = this.params.roundConstants[round];
    for (let i = 0; i < this.t; i++) this.sbox(i, rc[i]);
    this.externalMatrix(clean, needed);
  }

  // s0 = (s0 + c)^5, then s_i = d_i s_i + sum with the sum reduced so that
  // every output stays within 2p. Without internalLet x^5 goes through
  // state0 so that the S-box temporaries are popped before the sum is built
  // (one slot of reach for the deepest locals).
  internalRound(round: number) {
    const p = this.p;
    const t = this.t;
    const c = this.params.roundConstants[round][0];
    const outputs = (x5: Value) => {
      const old = [x5, ...this.state.slice(1)];
      const sum = this.chainSum(old, "sum", PRIME - 1n);
      for (let i = 0; i < t; i++) {
        this.set(i, this.add(sum, this.scaled(old[i], i)));
      }
    };
    if (!this.layout.internalLet) {
      this.sbox(0, c);
      p.block(() => outputs(this.state[0]));
      return;
    }
    p.block(() => {
      const y = p.let("y", this.add(this.state[0], p.constant(c)));
      const x2 = p.let("x2", p.expr("mulmod", y, y, this.P));
      const x5 = p.let(
        "x5",
        p.expr("mulmod", p.expr("mulmod", x2, x2, this.P), y, this.P),
      );
      outputs(x5);
    });
  }

  // ---- whole permutation ---------------------------------------------------

  build(): BuildResult {
    const p = this.p;
    const t = this.t;
    const { roundsF, roundsP } = this.params;
    const rfHalf = roundsF / 2;
    const pEnd = rfHalf + roundsP;
    const total = roundsF + roundsP;

    // PRIME is declared after the state locals so that the locals, which
    // are read with temporaries on top, are the deeper slots
    p.comment("inputs reduced mod PRIME");
    const prime = p.constant(PRIME);
    const raw = (i: number) =>
      p.input(
        this.mode.kind === "hash" ? `s${i}` : `mload(${this.addr(i, "state")})`,
        this.inputs.map((input) => input[i]),
      );
    for (let i = 0; i < this.layout.stackElements; i++) {
      this.state[i] = p.let(this.name(i), p.expr("mod", raw(i), prime));
    }
    if (this.inMemory > 0) p.let("mem", p.input("state", []));
    p.let("PRIME", prime);
    for (let i = this.layout.stackElements; i < t; i++) {
      this.state[i] = p.mstore(this.addr(i), p.expr("mod", raw(i), this.P));
    }
    p.blank();

    p.comment("initial linear layer");
    this.externalMatrix(false);
    p.blank();

    for (let r = 0; r < rfHalf; r++) {
      p.comment(`round ${r} (external)`);
      this.externalRound(r, r === rfHalf - 1);
      p.blank();
    }

    const internal = () => {
      for (let r = rfHalf; r < pEnd; r++) {
        p.comment(`round ${r} (internal)`);
        this.internalRound(r);
        p.blank();
      }
    };
    if (this.layout.diagInMemory > 0) {
      p.block(() => {
        p.comment(
          "diag constants that would not fit the code size as PUSH32, in free memory",
        );
        p.let("table", p.input("mload(0x40)", []));
        for (let i = t - this.layout.diagInMemory; i < t; i++) {
          p.mstore(
            this.tableAddr(i),
            p.constant(this.params.internalDiagMinusOne[i]),
          );
        }
        p.blank();
        internal();
      });
    } else {
      internal();
    }

    const needed =
      this.mode.kind === "hash" ? [true, false, false, false] : undefined;
    for (let r = pEnd; r < total; r++) {
      p.comment(`round ${r} (external)`);
      const last = r === total - 1;
      this.externalRound(r, last, last ? needed : undefined);
      if (!last) p.blank();
    }

    p.blank();
    if (this.mode.kind === "hash") {
      p.assign("result", this.state[0]);
    } else {
      for (let i = 0; i < this.layout.stackElements; i++) {
        const base = this.inMemory > 0 ? "mem" : "state";
        p.line(`mstore(${this.addr(i, base)}, ${this.state[i].name})`);
      }
    }

    // outputs must be clean and match the reference permutation
    const checked = this.mode.kind === "hash" ? 1 : t;
    for (let i = 0; i < checked; i++) {
      if (this.state[i].bound >= PRIME)
        throw new Error(`output ${i} is not clean`);
    }
    this.inputs.forEach((input, k) => {
      const want = permutation(this.params, input);
      for (let i = 0; i < checked; i++) {
        if (this.state[i].vals[k] !== want[i]) {
          throw new Error(`vector ${k} output ${i} mismatch`);
        }
      }
    });

    return { lines: p.lines, outputs: this.state };
  }
}

export function buildPermutation(
  params: Params,
  inputs: bigint[][],
  layout: Layout,
  mode: Mode,
  indent: number,
): BuildResult {
  return new Builder(params, inputs, layout, mode, indent).build();
}
