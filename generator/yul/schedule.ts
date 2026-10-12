// Poseidon2 permutation as straight-line Yul.
//
// The schedule only decides the order of the field operations and where the
// state lives (Yul locals or the caller's memory array); whether an addition
// is ADD or ADDMOD, and a doubling ADD or MULMOD, is decided per operation
// from the exact bounds the Program tracks. Reductions are forced only where
// they buy laziness later: the M4 temporaries t2 / t3, the internal round sum
// (or, for t = 2, the internal round's state1) and the column sums of the
// t = 4k linear layer.
//
// The legacy solc pipeline compiles inline assembly almost literally, with
// or without the optimizer, so the text is shaped for it: results are
// written once per statement as nested expressions, temporaries live in
// blocks that end right after their last use, and in a nested expression
// the deepest local is the outermost operand because solc evaluates
// arguments right to left. Every local is kept within DUP16 / SWAP16 by the
// reach model below, which assumes the literal compile.

import { add, mod, PRIME, UINT256_MAX } from "../shared/field.ts";
import type { Params } from "../round-constants/round-constants.ts";
import { matmulExternal, permutation } from "../shared/reference.ts";
import { Value } from "../shared/value.ts";
import { Program } from "./program.ts";

export type Layout = {
  // elements 0 .. stackElements - 1 live in Yul locals state0, state1, ...;
  // the rest stay in the state array in memory (array mode only)
  stackElements: number;
  // how many of the trailing internal diag constants are kept in a memory
  // table (loaded with MLOAD) instead of PUSH32 literals, to save code size
  diagInMemory: number;
  // how many of the last diag constants in memory are kept at 0x40 and 0x60
  // instead of the table (PUSH1 and MLOAD, 6 gas against 12 with the ADD to
  // the table pointer); the free memory pointer and the zero slot are
  // restored after the internal rounds
  diagFixed: number;
  // how many of the leading internal diag constants are locals declared for
  // the internal rounds (DUP, 3 gas like PUSH32 but 1 byte): solc's constant
  // optimizer turns a PUSH32 used more than once into a CODECOPY and MLOAD
  // (about 25 gas more per use) when it runs with few runs (200)
  diagLets: number;
  // how many of the following diag constants are kept in the scratch space
  // (mload(0) and mload(0x20), 5 and 6 gas, no table pointer)
  diagScratch: number;
  // M4 with two temporaries (t2, t3) instead of four: t0 and t1 are
  // recomputed (two extra ADDs per M4) so that a block of locals sitting 12
  // deep can still be assigned within SWAP16
  m4Temps: 2 | 4;
  // keep the internal round's x^5 in a `let` that lives through the round
  // instead of writing it back to state0 first; costs one slot of reach
  internalLet: boolean;
  // declare PRIME before the state locals (the deepest slot) and reduce the
  // inputs with it: PRIME is then one PUSH32 instead of one per input, which
  // the constant optimizer would copy from code with few runs, and t = 3
  // and t = 4 compile to fewer stack moves
  primeFirst: boolean;
  // internal rounds: keep the sum lazy and reduce every output but state0
  // with addmod, instead of reducing the sum and letting the outputs grow
  // until a doubling needs mulmod (t = 2, where that is one reduction per
  // round either way and the doubling stays a shift)
  internalReduceOutputs: boolean;
  // t = 3 internal rounds: the sum as (x5 + s1) + s2 and s1 reduced once the
  // next round's x5 + s1 would overflow (the Huff periodic policy), so that
  // s2 may grow to 5p and the sum takes one addmod instead of up to two
  periodicInternal: boolean;
  // how many of the last locals take the raw input words, reduced where the
  // initial linear layer first adds or doubles them (ADDMOD / MULMOD),
  // instead of a MOD with a PRIME literal each: with few runs solc copies a
  // PUSH32 that occurs more than once from code
  rawInputs: number;
};

export type Mode =
  // t = 4 library: the inputs are the function arguments s0 .. s3 and only
  // element 0 is returned, as `result`
  | { kind: "hash" }
  // the t = 4 library from round 0's S-boxes on (poseidon2_rest): the
  // arguments state0 .. state3 are the initial linear layer plus round 0's
  // constants, any uint256, folded per arity by buildHashEntry
  | { kind: "hashRest" }
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
  diagLocals: Value[] = [];

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
    if (
      mode.kind !== "array" &&
      (params.t !== 4 || layout.stackElements !== 4)
    )
      throw new Error("hash mode is the t = 4 library with all locals");
    if (
      layout.stackElements > params.t ||
      layout.diagScratch > 2 ||
      layout.diagFixed > 2 ||
      layout.diagFixed > layout.diagInMemory ||
      layout.diagLets + layout.diagScratch + layout.diagInMemory > params.t
    )
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

  // Locals are stack slots in declaration order: state0 is the deepest
  // (after PRIME with primeFirst), then the `mem` pointer that loads of
  // memory elements go through. Anything else (temporaries, expressions) is
  // within easy reach.
  rank(v: Value): number {
    const shift = this.layout.primeFirst ? 1 : 0;
    if (v.name === "PRIME" && this.layout.primeFirst) return 0;
    const m = /^state(\d+)$/.exec(v.name);
    if (m && this.isLocal(Number(m[1]))) return Number(m[1]) + shift;
    if (v.name.startsWith("mload(mem") || v.name.startsWith("mload(add(mem"))
      return this.memRank;
    return Infinity;
  }

  get memRank(): number {
    return this.layout.stackElements + (this.layout.primeFirst ? 1 : 0);
  }

  // Whether v can be DUPed with `intermediates` values pushed above the
  // live lets. Locals sit under every later let (PRIME, the diag table
  // pointer, temporaries); a memory element also pushes its offset before
  // `mem` is read.
  reachable(v: Value, intermediates: number): boolean {
    const i = this.rank(v);
    if (i === Infinity) return true;
    const offset = i === this.memRank ? 1 : 0;
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
    if (i < this.layout.diagLets) return this.diagLocals[i];
    if (i < this.layout.diagLets + this.layout.diagScratch)
      return this.p.mload(this.scratchAddr(i));
    if (i < this.t - this.layout.diagInMemory) return this.p.constant(d);
    if (i >= this.t - this.layout.diagFixed)
      return this.p.mload(this.fixedAddr(i));
    return this.p.mload(this.tableAddr(i));
  }

  scratchAddr(i: number): string {
    return i === this.layout.diagLets ? "0" : "0x20";
  }

  fixedAddr(i: number): string {
    return i === this.t - this.layout.diagFixed ? "0x40" : "0x60";
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
  sbox(i: number, c?: bigint) {
    const p = this.p;
    p.block(() => {
      const y =
        c === undefined
          ? this.state[i]
          : p.let("y", this.add(this.state[i], p.constant(c)));
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
      const t0 = () => sum2(p, v[1], v[0]);
      const t1 = () => sum2(p, v[3], v[2]);
      let T0 = t0;
      let T1 = t1;
      if (this.layout.m4Temps === 4) {
        const l0 = p.let("t0", t0());
        const l1 = p.let("t1", t1());
        T0 = () => l0;
        T1 = () => l1;
      }
      const two = (x: Value, t: () => Value) => {
        // a raw input word is doubled with MULMOD
        const raw = !this.fits(x, x);
        if (this.layout.m4Temps === 4) {
          const xx = raw
            ? p.expr("mulmod", x, p.constant(2n), this.P)
            : p.expr("add", x, x);
          return p.expr("addmod", xx, t(), this.P);
        }
        const tt = t();
        const sh = raw
          ? p.expr("mulmod", p.constant(2n), x, this.P)
          : p.expr("shl", one, x);
        return p.expr("addmod", tt, sh, this.P);
      };
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
    // hashRest takes round 0's constants already added
    const folded = this.mode.kind === "hashRest" && round === 0;
    for (let i = 0; i < this.t; i++) {
      this.sbox(i, folded ? undefined : rc[i]);
    }
    this.externalMatrix(clean, needed);
  }

  // t = 3: sum = (x5 + s1 + s2) mod p with x5 + s1 lazy, so that s2 may grow
  // to 5p; s1 + sum stays lazy while the next round's x5 + s1 fits.
  periodicOutputs(old: Value[]) {
    const p = this.p;
    const sum = p.let(
      "sum",
      p.expr("addmod", p.expr("add", old[0], old[1]), old[2], this.P),
    );
    for (let i = 0; i < 3; i++) {
      const reduce =
        i === 1 && sum.bound + old[i].bound + (PRIME - 1n) > UINT256_MAX;
      this.set(i, this.add(sum, this.scaled(old[i], i), reduce));
    }
  }

  // s0 = (s0 + c)^5, then s_i = d_i s_i + sum with the sum reduced so that
  // every output stays within 2p, or with internalReduceOutputs the sum lazy
  // as far as the next round's s0 + c fits and every other output reduced.
  // Without internalLet x^5 goes through state0 so that the S-box
  // temporaries are popped before the sum is built (one slot of reach for
  // the deepest locals).
  internalRound(round: number) {
    const p = this.p;
    const t = this.t;
    const c = this.params.roundConstants[round][0];
    const lazy = this.layout.internalReduceOutputs;
    const outputs = (x5: Value) => {
      const old = [x5, ...this.state.slice(1)];
      if (
        this.layout.periodicInternal &&
        t === 3 &&
        !lazy &&
        this.fits(x5, old[1])
      ) {
        this.periodicOutputs(old);
        return;
      }
      const cap = lazy ? UINT256_MAX - x5.bound - (PRIME - 1n) : PRIME - 1n;
      const sum = this.chainSum(old, "sum", cap);
      for (let i = 0; i < t; i++) {
        this.set(i, this.add(sum, this.scaled(old[i], i), lazy && i > 0));
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

  // Inputs reduced mod PRIME and the initial linear layer. PRIME is declared
  // after the state locals (unless primeFirst) so that the locals, which are
  // read with temporaries on top, are the deeper slots.
  entry() {
    const p = this.p;
    const t = this.t;
    const { rawInputs, stackElements } = this.layout;
    if (rawInputs >= stackElements) {
      p.comment(
        "inputs reduced mod PRIME by the first addmod or mulmod of the initial linear layer",
      );
    } else if (rawInputs > 0) {
      p.comment(
        `inputs reduced mod PRIME (the last ${rawInputs} by the first addmod or mulmod of the initial linear layer)`,
      );
    } else {
      p.comment("inputs reduced mod PRIME");
    }
    const prime = this.layout.primeFirst
      ? p.let("PRIME", p.constant(PRIME))
      : p.constant(PRIME);
    const raw = (i: number) =>
      p.input(
        this.mode.kind === "hash" ? `s${i}` : `mload(${this.addr(i, "state")})`,
        this.inputs.map((input) => input[i]),
      );
    for (let i = 0; i < stackElements; i++) {
      const e =
        i + rawInputs >= stackElements ? raw(i) : p.expr("mod", raw(i), prime);
      this.state[i] = p.let(this.name(i), e);
    }
    if (this.inMemory > 0) p.let("mem", p.input("state", []));
    if (!this.layout.primeFirst) p.let("PRIME", prime);
    for (let i = this.layout.stackElements; i < t; i++) {
      this.state[i] = p.mstore(this.addr(i), p.expr("mod", raw(i), this.P));
    }
    p.blank();

    p.comment("initial linear layer");
    this.externalMatrix(false);
    p.blank();
  }

  build(): BuildResult {
    const p = this.p;
    const t = this.t;
    const { roundsF, roundsP } = this.params;
    const rfHalf = roundsF / 2;
    const pEnd = rfHalf + roundsP;
    const total = roundsF + roundsP;

    if (this.mode.kind === "hashRest") {
      p.let("PRIME", p.constant(PRIME));
      const folded = this.inputs.map((input) =>
        round0Input(this.params, input),
      );
      for (let i = 0; i < t; i++) {
        this.state[i] = p.input(this.name(i), folded.map((y) => y[i]));
      }
      p.blank();
    } else {
      this.entry();
    }

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
    const { diagLets, diagScratch, diagInMemory, diagFixed } = this.layout;
    if (diagLets + diagScratch + diagInMemory > 0) {
      p.block(() => {
        const d = this.params.internalDiagMinusOne;
        if (diagLets > 0) {
          p.comment(
            "diag constants as locals: solc copies a PUSH32 used more than once from code with few optimizer runs",
          );
          for (let i = 0; i < diagLets; i++) {
            this.diagLocals[i] = p.let(`diag${i}`, p.constant(d[i]));
          }
        }
        if (diagScratch > 0) {
          p.comment("diag constants in the scratch space");
          for (let i = diagLets; i < diagLets + diagScratch; i++) {
            p.mstore(this.scratchAddr(i), p.constant(d[i]));
          }
        }
        if (diagInMemory > 0) {
          p.comment(
            "diag constants that would not fit the code size as PUSH32, in free memory",
          );
          p.let("table", p.input("mload(0x40)", []));
          for (let i = t - diagInMemory; i < t - diagFixed; i++) {
            p.mstore(this.tableAddr(i), p.constant(d[i]));
          }
        }
        if (diagFixed > 0) {
          p.comment(
            "diag constants in the free memory pointer and the zero slot, restored after the internal rounds",
          );
          for (let i = t - diagFixed; i < t; i++) {
            p.mstore(this.fixedAddr(i), p.constant(d[i]));
          }
        }
        p.blank();
        internal();
        if (diagFixed > 0) p.line("mstore(0x40, table)");
        if (diagFixed > 1) p.line("mstore(0x60, 0)");
      });
    } else {
      internal();
    }

    const needed =
      this.mode.kind !== "array" ? [true, false, false, false] : undefined;
    for (let r = pEnd; r < total; r++) {
      p.comment(`round ${r} (external)`);
      const last = r === total - 1;
      this.externalRound(r, last, last ? needed : undefined);
      if (!last) p.blank();
    }

    p.blank();
    if (this.mode.kind !== "array") {
      p.assign("result", this.state[0]);
    } else {
      for (let i = 0; i < this.layout.stackElements; i++) {
        const base = this.inMemory > 0 ? "mem" : "state";
        p.line(`mstore(${this.addr(i, base)}, ${this.state[i].name})`);
      }
    }

    // outputs must be clean and match the reference permutation
    const checked = this.mode.kind !== "array" ? 1 : t;
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

// a + b, with ADDMOD when a raw input word could overflow it
function sum2(p: Program, a: Value, b: Value): Value {
  return a.bound + b.bound <= UINT256_MAX
    ? p.expr("add", a, b)
    : p.expr("addmod", a, b, p.P);
}

// The state after the initial linear layer and round 0's constants, mod p.
function round0Input(params: Params, input: bigint[]): bigint[] {
  const s = input.map(mod);
  matmulExternal(s);
  return s.map((x, i) => add(x, params.roundConstants[0][i]));
}

// hash_n's entry into poseidon2_rest (t = 4): the initial linear layer and
// round 0's constants on [x, y, z, 0 .., n << 64] folded into four linear
// forms over the reduced inputs, assigned to s0 .. s3. The test inputs
// supply x, y, z.
export function buildHashEntry(
  params: Params,
  inputs: bigint[][],
  n: number,
  indent: number,
): BuildResult {
  const p = new Program(inputs.length, indent);
  p.let("PRIME", p.constant(PRIME));
  const arg = (i: number) =>
    p.expr(
      "mod",
      p.input(["x", "y", "z"][i], inputs.map((input) => input[i])),
      p.P,
    );
  // the constant part of each form
  const capacity = [0n, 0n, 0n, BigInt(n) << 64n];
  const k = round0Input(params, capacity).map((c) => p.constant(c));
  const [one, two, four, five] = [1n, 2n, 4n, 5n].map((v) => p.constant(v));
  let ys: Value[];
  if (n === 1) {
    // [5a, 4a, a, a]
    const a = p.let("a", arg(0));
    ys = [p.expr("mulmod", a, five, p.P), p.expr("shl", two, a), a, a];
  } else if (n === 2) {
    // with t0 = a + b: [5 t0 + 2b, 4 t0 + 2b, t0 + 2b, t0]
    const b = p.let("b", arg(1));
    const t0 = p.let("t0", p.expr("add", b, arg(0)));
    const b2 = p.let("b2", p.expr("shl", one, b));
    ys = [
      p.expr("add", p.expr("mulmod", t0, five, p.P), b2),
      p.expr("add", p.expr("mulmod", t0, four, p.P), b2),
      p.expr("add", t0, b2),
      t0,
    ];
  } else if (n === 3) {
    // with t0 = a + b, u = 2b + c, v = 4c + t0:
    // [5 t0 + u, 4 t0 + u, v + u, v]
    const b = p.let("b", arg(1));
    const c = p.let("c", arg(2));
    const t0 = p.let("t0", p.expr("add", b, arg(0)));
    const u = p.let("u", p.expr("add", p.expr("shl", one, b), c));
    const v = p.let("v", p.expr("add", p.expr("mulmod", c, four, p.P), t0));
    ys = [
      p.expr("add", p.expr("mulmod", t0, five, p.P), u),
      p.expr("add", p.expr("mulmod", t0, four, p.P), u),
      p.expr("addmod", v, u, p.P),
      v,
    ];
  } else {
    throw new Error(`hash_${n} has no entry`);
  }
  // hash_1 in order, the others y3 first
  const order = n === 1 ? [0, 1, 2, 3] : [3, 2, 1, 0];
  const out: Value[] = [];
  for (const i of order) {
    out[i] = p.assign(`s${i}`, p.expr("add", ys[i], k[i]));
  }
  inputs.forEach((input, j) => {
    const want = round0Input(params, [
      ...input.slice(0, n),
      ...capacity.slice(n),
    ]);
    for (let i = 0; i < 4; i++) {
      if (mod(out[i].vals[j]) !== want[i]) {
        throw new Error(`hash_${n} entry vector ${j} output ${i} mismatch`);
      }
    }
  });
  return { lines: p.lines, outputs: out };
}
