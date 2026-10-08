// Stack schedule for the Poseidon2 permutation.
//
// The schedule follows the hand-written t = 4 Huff: results are produced on
// top of the stack, operands are DUPed rather than SWAPed, PRIME copies and
// other operands are pushed early so later results land in place on top of
// them, and dead values are left behind as garbage. Every ADD / MUL is backed
// by the emitter's bound check; the schedule only chooses when to reduce, it
// never asserts safety by itself.
//
// For larger t the options below trade a few gas for stack reach and depth:
// dead slots can be reclaimed with SWAPn POP (5 gas), the M4 operand order
// can favour deep inputs, and the internal sum can reduce with MOD instead
// of pre-placed ADDMOD operands. The reach itself comes from the fork
// (fork.ts): 16 with the legacy opcodes, 235 with EIP-8024 from Amsterdam.
//
// A build covers a range of steps (step 0 is the initial linear layer, step
// r + 1 is round r) so that a permutation too large for the fork's code size
// can be cut into parts: every part takes the state from calldata, and a part
// that does not end the permutation leaves it in memory at [0, 32t) for the
// STATICCALL to the next one (render.ts). With the shadow option, values the
// reach cannot DUP are kept as memory copies (emitter.ts), which is what lets
// t >= 16 run with the legacy opcodes.

import { Emitter, Value, inplace, make, type Operand } from "./emitter.ts";
import { PRIME, UINT256_MAX } from "../field.ts";
import type { Params } from "../params.ts";
import { permutationSteps } from "../reference.ts";
import { FORKS, type Fork } from "./fork.ts";

export type BuildOptions = {
  // keep the internal diag constants in memory instead of PUSH32 (t >= 4)
  diagInMemory: boolean;
  // reclaim the old state slot after each element's S-box
  gcExternal: boolean;
  // reclaim the M4 temporaries t0, t1, t2 (and t3 when it does not disturb
  // the in-place layout)
  gcM4: boolean;
  // reclaim old state slots in internal rounds as each element is replaced
  gcInternal: boolean;
  // reduce the internal sum with [PRIME] swap1 mod instead of pre-placing
  // ADDMOD operands under the chain (keeps deep DUPs within reach)
  chainSwapMod: boolean;
  // t = 4k external layer as out_b = M4(s_b + S) with S = sum of blocks,
  // instead of per-block M4 followed by cross-block sums (better reach)
  externalD: boolean;
  // leave a PRIME copy under the outputs of an external layer when another
  // external round follows, so its elements DUP it instead of pushing it
  primeUnderExternal: boolean;
  // with gcInternal, leave the garbage of the first gcInternalFrom internal
  // rounds in place (no SWAPn POP) as far as the depth allows
  gcInternalFrom: number;
  // with diagInMemory, keep the last diagPush32 diag constants as PUSH32
  // (3 gas instead of 6 per use) as far as the code size allows
  diagPush32: number;
  // shadow the values the reach cannot DUP in memory and hand the outputs
  // over in memory instead of on the stack (garbage out of reach stays)
  shadow: boolean;
};

export const DEFAULT_OPTIONS: BuildOptions = {
  diagInMemory: false,
  gcExternal: false,
  gcM4: false,
  gcInternal: false,
  chainSwapMod: false,
  externalD: false,
  primeUnderExternal: true,
  gcInternalFrom: 0,
  diagPush32: 0,
  shadow: false,
};

// Steps [from, to) of the permutation (see permutationSteps in reference.ts).
export type Range = { from: number; to: number };

export function stepCount(params: Params): number {
  return 1 + params.roundsF + params.roundsP;
}

// The enabled options, numbers with their value: "gcInternal, diagPush32=6"
export function describeOptions(opts: BuildOptions): string {
  const enabled = Object.entries(opts)
    .filter(([, v]) => v)
    .map(([k, v]) => (typeof v === "number" ? `${k}=${v}` : k));
  return enabled.length ? enabled.join(", ") : "none";
}

export type BuildResult = {
  emitter: Emitter;
  outputs: Value[];
  lines: string[];
  gas: number;
  bytes: number;
  maxDepth: number;
  maxDup: number;
  swaps: number;
  pops: number;
  range: Range;
  // the state ends in memory at [0, 32t) (a part that hands over, or shadow)
  stateInMemory: boolean;
  // memory slot of each input the entry must shadow, by index
  inputSlots: (number | undefined)[];
  // code bytes at the end of each step of the range
  stepBytes: number[];
  memory: number;
};

export const DIAG_MEMORY_BASE = 0;

class Builder {
  readonly e: Emitter;
  readonly t: number;
  readonly params: Params;
  readonly opts: BuildOptions;
  readonly range: Range;
  // the state leaves on the stack in order (default) or in memory at
  // [0, 32t): always with shadow, and for any part that hands over
  readonly stateInMemory: boolean;
  readonly diagBase: number;
  readonly inputSlots: (number | undefined)[] = [];
  readonly stepBytes: number[] = [];
  state: Value[];
  // dead values left near the top of the state by the previous round,
  // collected at the start of the next internal round when gcInternal is on
  dead: Value[] = [];

  constructor(
    params: Params,
    inputs: bigint[][],
    opts: BuildOptions,
    fork: Fork,
    range: Range,
    shadow: ReadonlySet<string>,
    permissive: boolean,
  ) {
    this.params = params;
    this.t = params.t;
    this.opts = opts;
    this.range = range;
    this.stateInMemory = opts.shadow || range.to < stepCount(params);
    this.e = new Emitter(inputs.length, fork, shadow, permissive);
    // the hand-off region [0, 32t) comes first, then the diag table and the
    // shadow slots
    this.diagBase = this.stateInMemory ? 32 * this.t : DIAG_MEMORY_BASE;
    this.e.slotBase =
      this.diagBase +
      (opts.diagInMemory ? 32 * (this.t - opts.diagPush32) : 0);
    // takes: [s0, s1, ..., s(t-1), PRIME]
    this.state = [];
    for (let i = 0; i < this.t; i++) {
      const vals = inputs.map((inp) => inp[i]);
      const v = new Value(`s${i}`, PRIME - 1n, vals);
      this.e.key(v, `in:${i}`);
      if (shadow.has(`in:${i}`)) this.inputSlots[i] = this.e.declare(v);
      this.state.push(v);
    }
    this.e.stack = [...this.state, this.e.P];
    this.e.maxDepth = this.e.stack.length;
  }

  get P(): Value {
    return this.e.P;
  }

  constant(c: bigint, name?: string): Value {
    return new Value(name ?? "0x" + c.toString(16), c, [], c);
  }

  // true when diag constant i is loaded from memory rather than pushed
  diagStored(i: number): boolean {
    return this.opts.diagInMemory && i < this.t - this.opts.diagPush32;
  }

  diag(i: number): Operand {
    const d = this.params.internalDiagMinusOne[i];
    if (!this.diagStored(i)) return this.constant(d, `d${i}`);
    return make(() => this.e.mload(d, this.diagBase + 32 * i, `d${i}`));
  }

  // Indices of values sorted by stack depth, deepest first, so that each
  // DUP happens before the shallower ones push it further down.
  byDepth(values: Value[]): number[] {
    const e = this.e;
    return values
      .map((v, i) => ({ i, d: e.find(v) }))
      .sort((a, b) => b.d - a.d)
      .map((x) => x.i);
  }

  // Reclaim the slot of a dead value: the top moves into its place. With
  // shadow, garbage the reach cannot swap is left behind.
  gc(v: Value) {
    const pos = this.e.find(v);
    if (this.opts.shadow && (pos < 2 || pos > this.e.maxReach + 1)) return;
    this.gcAt(pos);
  }

  gcAt(pos: number) {
    const e = this.e;
    if (pos < 2) throw new Error(`cannot gc slot ${pos}`);
    e.swap(pos - 1);
    e.pop();
  }

  // ---- building blocks -----------------------------------------------------

  // Computes a via makeA (which must leave it on top) then a + b, either as
  // a plain ADD with b DUPed on top, or as ADDMOD with b and PRIME placed
  // under a beforehand so the result lands in place.
  addTo(makeA: () => Value, b: Value, name: string, reduce: boolean): Value {
    const e = this.e;
    if (reduce) {
      e.pushPrime();
      e.dup(b);
      const a = makeA();
      return e.compute(
        "addmod",
        [inplace(a), inplace(b), inplace(this.P)],
        name,
      );
    }
    const a = makeA();
    return e.compute("add", [b, inplace(a)], name);
  }

  // a + b from two existing values
  pairAdd(a: Value, b: Value, name: string, reduce: boolean): Value {
    const e = this.e;
    if (reduce || !e.fitsAdd(a, b)) {
      return e.compute("addmod", [a, b, this.P], name);
    }
    return e.compute("add", [a, b], name);
  }

  // Sum of values as a chain, reducing only when a partial sum would
  // overflow or when the final sum would exceed cap. The chain runs from the
  // last value to the first so the deepest DUPs happen before the chain grows.
  chainSum(values: Value[], name: string, cap = UINT256_MAX): Value {
    const e = this.e;
    const n = values.length;
    if (n < 2) throw new Error("chainSum needs two values");
    // plan both directions, keep the one with fewer reductions; on a tie
    // start from the last value so the deepest DUPs happen first
    const plan = (order: Value[]) => {
      const reduce: boolean[] = [];
      let bound = order[0].bound;
      for (let j = 1; j < n; j++) {
        const last = j === n - 1;
        const lazy = bound + order[j].bound;
        const r = lazy > UINT256_MAX || (last && lazy > cap);
        reduce.push(r);
        bound = r ? PRIME - 1n : lazy;
      }
      return reduce;
    };
    const reversed = values.slice().reverse();
    const count = (r: boolean[]) => r.filter(Boolean).length;
    const planFwd = plan(values);
    const planRev = plan(reversed);
    const [order, reduce] =
      count(planFwd) < count(planRev) ? [values, planFwd] : [reversed, planRev];
    if (this.opts.chainSwapMod) {
      // reduce the accumulator with MOD right before an ADD would overflow,
      // and once more at the end if the cap demands it; no garbage, no
      // pre-placed operands, so deep DUPs stay within reach
      let acc = e.dup(order[0]);
      for (let j = 1; j < n; j++) {
        if (acc.bound + order[j].bound > UINT256_MAX) acc = this.modTop(acc);
        acc = e.compute("add", [order[j], inplace(acc)], name);
      }
      if (acc.bound > cap) acc = this.modTop(acc);
      return acc;
    }
    // [value, PRIME] for every reduced step, last step deepest
    for (let j = n - 1; j >= 2; j--) {
      if (reduce[j - 1]) {
        e.pushPrime();
        e.dup(order[j]);
      }
    }
    let acc: Value;
    if (reduce[0]) {
      acc = e.compute("addmod", [order[0], order[1], this.P], name);
    } else {
      acc = e.compute("add", [order[0], order[1]], name);
    }
    for (let j = 2; j < n; j++) {
      if (reduce[j - 1]) {
        acc = e.compute(
          "addmod",
          [inplace(acc), inplace(order[j]), inplace(this.P)],
          name,
        );
      } else {
        acc = e.compute("add", [order[j], inplace(acc)], name);
      }
    }
    return acc;
  }

  // v % PRIME for v on top: [PRIME] swap1 mod
  modTop(v: Value): Value {
    const e = this.e;
    if (e.top(0) !== v) throw new Error("modTop expects the value on top");
    e.pushPrime();
    e.swap(1);
    return e.compute("mod", [inplace(v), inplace(this.P)], v.name);
  }

  // x^5 for y sitting on top with a PRIME copy right under it, which the
  // last MULMOD consumes together with y itself.
  sbox(y: Value, name: string): Value {
    const e = this.e;
    if (e.top(0) !== y || e.top(1) !== this.P) {
      throw new Error("sbox expects [y, P] on top");
    }
    e.pushPrime();
    const x2 = e.compute("mulmod", [y, y, this.P], "x2");
    const x4 = e.compute("mulmod", [x2, inplace(x2), inplace(this.P)], "x4");
    return e.compute(
      "mulmod",
      [inplace(x4), inplace(y), inplace(this.P)],
      name,
    );
  }

  // Keeps a PRIME copy near the top so later copies stay within reach.
  floatPrime() {
    const n = this.e.findPrime();
    if (n === 0 || n > this.e.maxReach / 2) this.e.pushPrime();
  }

  // ---- external rounds ------------------------------------------------------

  // s_i + c_i then x^5 for every element, last element first so the results
  // end up in state order.
  addConstantsAndSbox(round: number) {
    const e = this.e;
    const t = this.t;
    if (this.opts.gcExternal) {
      for (const v of this.dead) {
        const pos = e.find(v);
        if (pos >= 2 && pos <= e.maxReach + 1) this.gc(v);
      }
      this.dead = [];
    }
    this.floatPrime();
    e.endLine();
    const out: Value[] = new Array(t);
    // with shadow the results replace the old slots in place, so the shallow
    // elements go first and every slot stays within the reach of the swap
    const order = this.byDepth(this.state);
    if (this.opts.shadow && this.opts.gcExternal) order.reverse();
    for (const i of order) {
      const s = this.state[i];
      const c = this.constant(this.params.roundConstants[round][i], "c");
      e.pushPrime();
      let y: Value;
      if (e.fitsAdd(s, c)) {
        y = e.compute("add", [c, s], `s${i}+c`);
      } else {
        y = e.compute("addmod", [c, s, this.P], `s${i}+c`);
      }
      out[i] = this.sbox(y, `s${i}'`);
      if (this.opts.gcExternal) this.gc(s);
      e.endLine();
    }
    if (this.opts.gcExternal) {
      // PRIME copies would otherwise sit above the state and cost reach in
      // the linear layer
      while (e.top(0) === this.P) e.pop();
      e.endLine();
    }
    this.state = out;
  }

  // Poseidon2 M4 on four values.
  //   t0 = v0 + v1, t1 = v2 + v3, t2 = 2 v1 + t1, t3 = 2 v3 + t0
  //   t4 = 4 t1 + t3, t5 = 4 t0 + t2, t6 = t3 + t5, t7 = t2 + t4
  //   out = [t6, t5, t7, t4]
  // t2 and t3 are reduced so that t4..t7 can be lazy with headroom left for
  // the next round's constant addition. With `deep` the doublings are taken
  // first so the deepest inputs are DUPed before temporaries pile up.
  m4(
    v: Value[],
    names: string[],
    clean: boolean,
    hooks: {
      beforeOutputs?: () => void;
      beforeLast?: () => void;
      // keep [o0, o1, o2, o3] in order (final round): garbage is collected
      // in multiples of four so the rotation returns to the original order
      keepOrder?: boolean;
      // dead values below the temporaries that may be collected as well
      extraGarbage?: Value[];
      // collect garbage regardless of the gcM4 option
      forceGc?: boolean;
      // a PRIME copy was placed under the inputs and must stay there
      primeBelow?: boolean;
    } = {},
  ): Value[] {
    const e = this.e;
    const four = this.constant(4n);
    // the standard order DUPs v3 again under four temporaries
    const deep = Math.max(...v.map((x) => e.find(x))) + 4 > e.maxReach;
    let t0: Value;
    let t1: Value;
    let t2: Value;
    let t3: Value;
    const temps: Value[] = [];
    if (deep) {
      const d3 = e.compute("add", [v[3], v[3]], "2s3");
      e.endLine();
      const d1 = e.compute("add", [v[1], v[1]], "2s1");
      e.endLine();
      t1 = e.compute("add", [v[2], v[3]], "t1");
      e.endLine();
      t0 = e.compute("add", [v[0], v[1]], "t0");
      e.endLine();
      t3 = e.compute("addmod", [d3, t0, this.P], "t3");
      e.endLine();
      t2 = e.compute("addmod", [d1, t1, this.P], "t2");
      e.endLine();
      temps.push(d3, d1);
    } else {
      t1 = e.compute("add", [v[2], v[3]], "t1");
      e.endLine();
      t0 = e.compute("add", [v[0], v[1]], "t0");
      e.endLine();
      t3 = this.addTo(
        () => e.compute("add", [v[3], v[3]], "2s3"),
        t0,
        "t3",
        true,
      );
      e.endLine();
      t2 = this.addTo(
        () => e.compute("add", [v[1], v[1]], "2s1"),
        t1,
        "t2",
        true,
      );
      e.endLine();
    }
    if (hooks.beforeOutputs) hooks.beforeOutputs();
    const t4 = this.addTo(
      () => e.compute("mulmod", [t1, four, this.P], "4t1"),
      t3,
      names[3],
      clean || !e.fitsAdd(t3, this.P),
    );
    e.endLine();
    const t7 = this.pairAdd(t2, t4, names[2], clean);
    e.endLine();
    const t5 = this.addTo(
      () => e.compute("mulmod", [t0, four, this.P], "4t0"),
      t2,
      names[1],
      clean || !e.fitsAdd(t2, this.P),
    );
    e.endLine();
    const gc = (this.opts.gcM4 || hooks.forceGc) && !hooks.beforeOutputs;
    const extra = [...temps, ...(hooks.extraGarbage ?? [])];
    if (gc && !hooks.keepOrder) {
      // three live outputs on top, order does not matter here
      for (const g of [t2, t0, t1, ...extra]) this.gc(g);
      e.endLine();
    }
    if (hooks.beforeLast) hooks.beforeLast();
    const t6 = this.pairAdd(t3, t5, names[0], clean);
    e.endLine();
    if (gc && hooks.keepOrder) {
      // always take the slot right under the four outputs: a uniform
      // rotation, applied a multiple of four times, restores their order
      const dead = new Set([t2, t3, t0, t1, ...extra]);
      let run = 0;
      while (run < e.depth - 4 && dead.has(e.top(4 + run))) run++;
      const count = run - (run % 4);
      for (let i = 0; i < count; i++) this.gcAt(5);
      e.endLine();
    } else if (gc && !hooks.beforeLast) {
      this.gc(t3);
      e.endLine();
    } else if (gc) {
      this.dead.push(t3);
    }
    return [t6, t5, t7, t4];
  }

  // primeUnder leaves a PRIME copy right under the outputs: required for the
  // returned layout [s0', ..., s(t-1)', PRIME] at t <= 4, and used before
  // another external round so its elements find PRIME within reach.
  externalMatrix(clean: boolean, beforeLast?: () => void, primeUnder = false) {
    const e = this.e;
    const t = this.t;
    const names = Array.from({ length: t }, (_, i) => `s${i}'`);
    const beforeOutputs =
      (clean && t <= 4) ||
      (primeUnder && !clean && this.opts.primeUnderExternal)
        ? () => e.pushPrime()
        : undefined;
    if (t === 2 || t === 3) {
      // circ(2, 1[, 1]): out_i = s_i + sum
      const sum = this.chainSum(this.state, "sum");
      e.endLine();
      const out: Value[] = new Array(t);
      if (beforeOutputs) beforeOutputs();
      for (let i = t - 1; i >= 0; i--) {
        if (i === 0 && beforeLast) beforeLast();
        out[i] = this.pairAdd(this.state[i], sum, names[i], clean);
        e.endLine();
      }
      this.state = out;
      return;
    }
    if (t === 4) {
      this.state = this.m4(this.state, names, clean, {
        beforeOutputs,
        beforeLast,
      });
      return;
    }
    const k = t / 4;
    if (this.opts.externalD) {
      // out_b = M4(s_b + S) with S_i = sum over blocks of s_{b,i}; S is
      // reduced so that the block inputs stay within 2p
      const S: Value[] = new Array(4);
      for (let i = 3; i >= 0; i--) {
        const column = Array.from(
          { length: k },
          (_, b) => this.state[4 * b + i],
        );
        S[i] = this.chainSum(column, `S${i}`, PRIME - 1n);
        e.endLine();
      }
      const out: Value[] = new Array(t);
      for (let b = k - 1; b >= 0; b--) {
        const u: Value[] = new Array(4);
        if (b === 0 && beforeOutputs) beforeOutputs();
        const block = this.state.slice(4 * b, 4 * b + 4);
        for (const i of this.byDepth(block)) {
          u[i] = this.pairAdd(block[i], S[i], `u${4 * b + i}`, false);
          e.endLine();
        }
        const res = this.m4(u, names.slice(4 * b, 4 * b + 4), clean, {
          keepOrder: clean,
          extraGarbage: u,
          forceGc: true,
          beforeLast: b === 0 ? beforeLast : undefined,
          primeBelow: b === 0 && beforeOutputs !== undefined,
        });
        for (let i = 0; i < 4; i++) out[4 * b + i] = res[i];
      }
      this.state = out;
      return;
    }
    // y = M4 per block, z_i = sum over blocks of y_{b,i},
    // out_{b,i} = y_{b,i} + z_i
    const y: Value[] = new Array(t);
    for (let b = k - 1; b >= 0; b--) {
      const block = this.state.slice(4 * b, 4 * b + 4);
      const yNames = [0, 1, 2, 3].map((i) => `y${4 * b + i}`);
      const res = this.m4(block, yNames, false, {
        keepOrder: clean,
        forceGc: clean,
      });
      for (let i = 0; i < 4; i++) y[4 * b + i] = res[i];
    }
    const z: Value[] = new Array(4);
    for (let i = 3; i >= 0; i--) {
      const column = Array.from({ length: k }, (_, b) => y[4 * b + i]);
      // leave room so that y + z stays lazy
      z[i] = this.chainSum(column, `z${i}`, UINT256_MAX - 3n * PRIME);
      e.endLine();
    }
    const out: Value[] = new Array(t);
    if (beforeOutputs) beforeOutputs();
    if (clean && !this.stateInMemory) {
      // final round: outputs replace their y in ascending order so they end
      // up on top in state order once the z values are popped
      for (let j = 0; j < t; j++) {
        out[j] = this.pairAdd(y[j], z[j % 4], names[j], true);
        this.gc(y[j]);
        e.endLine();
      }
      for (let i = 0; i < 4; i++) e.pop();
      e.endLine();
    } else {
      for (let j = t - 1; j >= 0; j--) {
        if (j === 0 && beforeLast) beforeLast();
        out[j] = this.pairAdd(y[j], z[j % 4], names[j], clean);
        if (this.opts.gcExternal && j > 0) this.gc(y[j]);
        e.endLine();
      }
    }
    this.state = out;
  }

  // Writes the state to [0, 32t) for the next part or the caller. DUP and
  // MSTORE leave the stack as it was, so every element is fetched from the
  // same layout (shadowed ones with MLOAD).
  storeState() {
    const e = this.e;
    e.comment("State to memory");
    for (let i = 0; i < this.t; i++) {
      e.dup(this.state[i]);
      e.mstore(32 * i);
      e.endLine();
    }
  }

  // ---- internal rounds ------------------------------------------------------

  // Expects s0 on top with a PRIME copy under it (placed by the previous
  // round) so that s0 + c lands in place for the S-box.
  internalRound(round: number, nextInternal: boolean) {
    const e = this.e;
    const t = this.t;
    const s0 = this.state[0];
    if (e.top(0) !== s0 || e.top(1) !== this.P) {
      throw new Error("internal round expects [s0, P] on top");
    }
    const c = this.constant(this.params.roundConstants[round][0], "c");
    if (!e.fitsAdd(s0, c)) throw new Error("s0 + c does not fit");
    const y = e.compute("add", [c, inplace(s0)], "s0+c");
    const x5 = this.sbox(y, "s0^5");
    e.endLine();
    const collect =
      this.opts.gcInternal &&
      round - this.params.roundsF / 2 >= this.opts.gcInternalFrom;
    if (collect) {
      // the previous round's garbage sits above the state; x5 may move
      for (const v of this.dead) {
        const pos = e.find(v);
        if (pos >= 2 && pos <= e.maxReach + 1) this.gc(v);
      }
      e.endLine();
    }
    this.dead = [];

    const old = [x5, ...this.state.slice(1)];
    const sum = this.chainSum(old, "sum", PRIME - 1n);
    e.endLine();

    const out: Value[] = new Array(t);
    // deepest element first, s0 last so it lands on the pre-placed PRIME;
    // shallowest first when the results replace the old slots in place with
    // shadow, so the swap of every slot stays within reach
    const others = this.byDepth(old).filter((i) => i !== 0);
    if (this.opts.shadow && collect) others.reverse();
    const order = [...others, 0];
    for (const [n, i] of order.entries()) {
      const s = old[i];
      const d = this.params.internalDiagMinusOne[i];
      if (n === Math.min(1, t - 2)) {
        // PRIME copy that ends up under the new state, within reach of the
        // next round; placed one element late so the deepest DUP fits
        e.pushPrime();
        if (collect) {
          // the previous round's copy is the only other PRIME left above
          // the state and would pile up round after round
          for (let pos = 2; pos <= e.maxReach + 1 && pos <= e.depth; pos++) {
            if (e.top(pos - 1) === this.P) {
              this.gcAt(pos);
              break;
            }
          }
        }
      }
      if (i === 0 && nextInternal) {
        // PRIME copy under the next round's s0 + c
        e.pushPrime();
      }
      if (d === 1n) {
        out[i] = this.pairAdd(s, sum, `s${i}'`, false);
      } else if (d === 2n) {
        if (e.fitsAdd(s, s)) {
          out[i] = this.addTo(
            () => e.compute("add", [s, s], `2s${i}`),
            sum,
            `s${i}'`,
            sum.bound + 2n * s.bound > UINT256_MAX,
          );
        } else {
          out[i] = this.addTo(
            () => e.compute("mulmod", [s, this.constant(2n), this.P], `2s${i}`),
            sum,
            `s${i}'`,
            !e.fitsAdd(sum, this.P),
          );
        }
      } else {
        out[i] = this.addTo(
          () => e.compute("mulmod", [s, this.diag(i), this.P], `m${i}`),
          sum,
          `s${i}'`,
          !e.fitsAdd(sum, this.P),
        );
      }
      if (collect && i > 0) this.gc(s);
      e.endLine();
    }
    this.dead.push(sum, x5);
    this.state = out;
  }

  // ---- whole permutation ----------------------------------------------------

  build(): Value[] {
    const e = this.e;
    const { roundsF, roundsP } = this.params;
    const rfHalf = roundsF / 2;
    const pEnd = rfHalf + roundsP;
    const total = roundsF + roundsP;
    const { from, to } = this.range;
    const hasInternal = from <= pEnd && to > rfHalf + 1;

    if (hasInternal && this.diagStored(0)) {
      e.comment(
        "Internal diag constants, loaded with MLOAD in the internal rounds",
      );
      for (let i = 0; this.diagStored(i); i++) {
        e.mstoreConst(
          this.params.internalDiagMinusOne[i],
          this.diagBase + 32 * i,
        );
        e.endLine();
      }
      e.comment("");
    }

    if (from === 0) {
      e.nextRound();
      e.comment("Initial linear layer");
      this.externalMatrix(false, undefined, true);
      e.comment("");
      this.stepBytes.push(e.bytes);
    }

    for (let r = Math.max(from - 1, 0); r + 1 < to; r++) {
      e.nextRound();
      // round r + 1 belongs to this part too
      const next = r + 2 < to;
      if (r < rfHalf) {
        e.comment(`Round ${r} (external)`);
        this.addConstantsAndSbox(r);
        const last = r === rfHalf - 1;
        this.externalMatrix(
          false,
          last && next ? () => e.pushPrime() : undefined,
          !last,
        );
      } else if (r < pEnd) {
        e.comment(`Round ${r} (internal)`);
        if (from === r + 1) {
          // the entry leaves [s0, ..., PRIME]: place the PRIME copy the
          // round expects under s0
          e.pushPrime();
          e.swap(1);
        }
        this.internalRound(r, r < pEnd - 1 && next);
      } else {
        e.comment(`Round ${r} (external)`);
        this.addConstantsAndSbox(r);
        this.externalMatrix(r === total - 1, undefined, true);
      }
      e.comment("");
      this.stepBytes.push(e.bytes);
    }

    if (this.stateInMemory) this.storeState();
    e.endLine();
    return this.state;
  }
}

// Builds steps [range.from, range.to) and checks the emitted stream against
// the reference on every input. With shadow a permissive pass first finds
// the values DUPed out of reach, then the real pass shadows them.
export function buildPermutation(
  params: Params,
  inputs: bigint[][],
  opts: BuildOptions = DEFAULT_OPTIONS,
  fork: Fork = FORKS.shanghai,
  range: Range = { from: 0, to: stepCount(params) },
): BuildResult {
  let shadow: ReadonlySet<string> = new Set();
  if (opts.shadow) {
    const probe = new Builder(params, inputs, opts, fork, range, shadow, true);
    probe.build();
    shadow = probe.e.needed;
  }
  const b = new Builder(params, inputs, opts, fork, range, shadow, false);
  const outputs = b.build();
  const e = b.e;
  const final = range.to === stepCount(params);

  if (!b.stateInMemory) {
    // the outputs must sit on top in state order and be clean
    for (let i = 0; i < params.t; i++) {
      if (e.stack[i] !== outputs[i]) {
        throw new Error(`output ${i} is not at slot ${i + 1}`);
      }
      if (outputs[i].bound >= PRIME) {
        throw new Error(`output ${i} is not clean`);
      }
    }
    if (params.t <= 4 && e.stack[params.t] !== e.P) {
      throw new Error("PRIME expected under outputs");
    }
  } else if (final) {
    for (let i = 0; i < params.t; i++) {
      if (outputs[i].bound >= PRIME) {
        throw new Error(`output ${i} is not clean`);
      }
    }
  }

  // concrete check of the emitted stream against the reference permutation
  // (a part that hands over leaves lazy values, the next entry reduces them)
  inputs.forEach((input, k) => {
    const want = permutationSteps(params, input, range.from, range.to);
    for (let i = 0; i < params.t; i++) {
      const got = final ? outputs[i].vals[k] : outputs[i].vals[k] % PRIME;
      if (got !== want[i]) {
        throw new Error(`vector ${k} output ${i} mismatch`);
      }
    }
  });

  return {
    emitter: e,
    outputs,
    lines: e.lines,
    gas: e.gas,
    bytes: e.bytes,
    maxDepth: e.maxDepth,
    maxDup: e.maxDup,
    swaps: e.swaps,
    pops: e.pops,
    range,
    stateInMemory: b.stateInMemory,
    inputSlots: b.inputSlots,
    stepBytes: b.stepBytes,
    memory: e.memory,
  };
}

// Largest n in [0, hi] accepted by ok, which must be monotone (true up to
// some n, false after) and true for 0.
export function largest(hi: number, ok: (n: number) => boolean): number {
  let lo = 0;
  while (lo < hi) {
    const mid = Math.ceil((lo + hi) / 2);
    if (ok(mid)) lo = mid;
    else hi = mid - 1;
  }
  return lo;
}

export type Best = { result: BuildResult; opts: BuildOptions };

// Tries the option combinations that make sense for t and returns the
// cheapest build of the range that stays within reach, depth and code size,
// or undefined when the schedules that build are too large or too deep (the
// caller may then split the permutation). The shadow option is only tried
// when no schedule keeps the whole state within reach, so the widths that
// fit the reach keep their stack-only output. With DUPN / SWAPN each
// combination also defers gcInternal as long as the depth allows and keeps
// as many diag constants PUSH32 as the code size allows (the depth grows
// with gcInternalFrom and the size with diagPush32, so a binary search finds
// each limit). Throws when nothing builds at all.
export function buildBest(
  params: Params,
  inputs: bigint[][],
  maxBytes: number,
  fork: Fork = FORKS.shanghai,
  range: Range = { from: 0, to: stepCount(params) },
): Best | undefined {
  const bools = [false, true];
  const candidates = (shadow: boolean): BuildOptions[] => {
    const list: BuildOptions[] = [];
    for (const diagInMemory of params.t >= 4 ? bools : [false]) {
      for (const gcExternal of bools) {
        for (const gcM4 of params.t >= 4 ? bools : [false]) {
          for (const gcInternal of bools) {
            for (const chainSwapMod of bools) {
              for (const externalD of params.t >= 8 ? bools : [false]) {
                for (const primeUnderExternal of bools) {
                  list.push({
                    diagInMemory,
                    gcExternal,
                    gcM4,
                    gcInternal,
                    chainSwapMod,
                    externalD,
                    primeUnderExternal,
                    gcInternalFrom: 0,
                    diagPush32: 0,
                    shadow,
                  });
                }
              }
            }
          }
        }
      }
    }
    return list;
  };
  const attempt = (opts: BuildOptions): BuildResult | undefined => {
    try {
      return buildPermutation(params, inputs, opts, fork, range);
    } catch {
      return undefined;
    }
  };
  let best: Best | undefined;
  let built = 0;
  const failures: string[] = [];
  const search = (list: BuildOptions[]) => {
    for (let opts of list) {
      try {
        let result = buildPermutation(params, inputs, opts, fork, range);
        built++;
        if (fork.reach > 16 && result.maxDepth <= 1000) {
          if (opts.gcInternal) {
            const gcInternalFrom = largest(params.roundsP, (n) => {
              const r = attempt({ ...opts, gcInternalFrom: n });
              return r !== undefined && r.maxDepth <= 1000;
            });
            opts = { ...opts, gcInternalFrom };
            result = buildPermutation(params, inputs, opts, fork, range);
          }
          if (opts.diagInMemory && result.bytes <= maxBytes) {
            const diagPush32 = largest(params.t, (n) => {
              const r = attempt({ ...opts, diagPush32: n });
              return r !== undefined && r.bytes <= maxBytes;
            });
            opts = { ...opts, diagPush32 };
            result = buildPermutation(params, inputs, opts, fork, range);
          }
        }
        if (result.maxDepth > 1000) {
          failures.push(`${JSON.stringify(opts)}: depth ${result.maxDepth}`);
          continue;
        }
        if (result.bytes > maxBytes) {
          failures.push(`${JSON.stringify(opts)}: ${result.bytes} bytes`);
          continue;
        }
        if (!best || result.gas < best.result.gas) best = { result, opts };
      } catch (err) {
        failures.push(`${JSON.stringify(opts)}: ${(err as Error).message}`);
      }
    }
  };
  search(candidates(false));
  if (built === 0) search(candidates(true));
  if (built === 0) {
    const reasons = new Map<string, number>();
    for (const f of failures) {
      const reason = f.slice(f.indexOf("}: ") + 3);
      reasons.set(reason, (reasons.get(reason) ?? 0) + 1);
    }
    const summary = [...reasons].map(([r, n]) => `${n}x ${r}`).join("\n  ");
    throw new Error(
      `no schedule works for t = ${params.t} on ${fork.name} ` +
        `(${failures.length} option combinations tried):\n  ${summary}`,
    );
  }
  return best;
}
