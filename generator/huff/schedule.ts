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
//
// The consuming internal rounds rotate the stack layout by one slot per
// round, so after `period` rounds (the elements the stack holds) the layout
// is back where it started and the bounds are a fixed point after the first
// round. With sharedBody the steady internal rounds (all but the first and
// the last of the range) are therefore emitted once as a body of one period
// that every call reaches by JUMP with its return label in memory and its
// round constants CODECOPYed from a code table to a memory scratch; a last
// call of fewer rounds leaves the body at a mid exit. The body's diag
// constants are PUSH32 as it exists once, which is what the code size
// otherwise forces into memory or into a split. With consumeGroup the round
// consumes the elements in sub-chains of that many slots, each rotating on
// its own (one SWAP more per chain), so the period is the chains' lcm and
// the body shorter, which is what lets a part hold its rounds within the
// legacy code size.

import {
  Emitter,
  Value,
  inplace,
  make,
  memoryGas,
  type Operand,
  type Table,
} from "./emitter.ts";
import { PRIME, UINT256_MAX } from "../shared/field.ts";
import type { Params } from "../round-constants/round-constants.ts";
import { permutationSteps, spongeState } from "../shared/reference.ts";
import { FORKS, type Fork } from "./fork.ts";
import {
  BLOCKS,
  HASH_FORMS,
  INTERNAL3,
  INTERNAL3_PERIODIC,
  INTERNAL4,
  LINEAR_FINAL4,
  ROUND4_FIRST,
  TEMPLATES,
  type Template,
  type TemplateKind,
} from "./templates.ts";

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
  // internal rounds: keep the sum lazy and reduce every output but s0 with
  // ADDMOD, instead of reducing the sum and letting the outputs grow until
  // a doubling needs MULMOD (t <= 3, where the diag is 1 / 2 and nothing
  // else reduces the elements)
  internalReduceOutputs: boolean;
  // internal rounds: leave a PRIME copy under the new state only when the
  // nearest copy would leave the reach, instead of every round; t = 2
  // with internalMul3 omits backing copies when false
  floatPrimeInternal: boolean;
  // internal rounds consume the old state in place: the sum chain DUPs
  // every element in advance and each element is then SWAPped to the top
  // for its MULMOD, so no garbage is left and nothing is popped (t = 12
  // within DUP16, where the state would otherwise need SWAPn POP)
  internalConsume: boolean;
  // with internalConsume, stack the PRIME copies of a round under m0 at
  // once (DUPs and one SWAP) so that each swapped element lands on its own,
  // instead of DUPing one and SWAPping it under every element
  primeStack: boolean;
  // with gcInternal, leave the garbage of the first gcInternalFrom internal
  // rounds in place (no SWAPn POP) as far as the depth allows
  gcInternalFrom: number;
  // with gcM4, leave the M4 temporaries of the first gcM4From external
  // layers in place as far as the depth allows
  gcM4From: number;
  // with diagInMemory, keep the last diagPush32 diag constants as PUSH32
  // (3 gas instead of 6 per use) as far as the code size allows
  diagPush32: number;
  // shadow the values the reach cannot DUP in memory and hand the outputs
  // over in memory instead of on the stack (garbage out of reach stays)
  shadow: boolean;
  // with internalConsume, run the steady internal rounds through one body
  // of a period reached by JUMP (see above)
  sharedBody: boolean;
  // with sharedBody, keep the first bodyInline steady rounds inline as far
  // as the code size allows
  bodyInline: number;
  // with internalConsume, consume the elements of a round that leads to
  // another in sub-chains of consumeGroup slots (the last takes the rest),
  // each rotating on its own, for a shorter body (0: one chain)
  consumeGroup: number;
  // with internalConsume, the elements the stack holds when the reach
  // cannot hold them all (0: reach - 4); each one more takes a slot of the
  // sum chain's PRIME copies and saves its loads and store
  consumeSlots: number;
  // external rounds (t <= 4) and, with externalD, the M4 of every block as
  // the stack programs of templates.ts, from restricted searches: the
  // lanes are S-boxed in place and the linear layer consumes its operands,
  // so a round leaves at most one dead value and a block none
  externalTemplate: boolean;
  // t = 4 internal rounds as the stack program of templates.ts
  // (INTERNAL4): one dead value a round instead of five, for three SWAPs;
  // t = 3 uses periodic bound-checked reductions, with INTERNAL3 fallbacks
  internalTemplate: boolean;
  // t = 2 internal rounds: s1' = (3 s1 mod P) + s0^5 and
  // s0' = 2 s0^5 + s1 lazy, instead of a shared lazy sum
  // (one op less per round, after the first generic bridge)
  internalMul3: boolean;
  // store PRIME in memory once and load it (PUSH, MLOAD) where no copy is
  // within reach instead of PUSH32 (3 gas more, 30 bytes less)
  primeInMemory: boolean;
  // with externalD and shadow (t >= 8), the external rounds as a stream of
  // blocks: the S-box outputs go to memory slots, but those of the last
  // blocks of a layer, which the next layer takes first; the column sums
  // load them, and each block's M4 runs straight into the next round's
  // S-boxes
  externalStream: boolean;
};

export const DEFAULT_OPTIONS: BuildOptions = {
  diagInMemory: false,
  gcExternal: false,
  gcM4: false,
  gcInternal: false,
  chainSwapMod: false,
  externalD: false,
  primeUnderExternal: true,
  internalReduceOutputs: false,
  floatPrimeInternal: false,
  internalConsume: false,
  primeStack: false,
  gcInternalFrom: 0,
  gcM4From: 0,
  diagPush32: 0,
  shadow: false,
  sharedBody: false,
  bodyInline: 0,
  consumeGroup: 0,
  consumeSlots: 0,
  externalTemplate: false,
  internalTemplate: false,
  internalMul3: false,
  primeInMemory: false,
  externalStream: false,
};

// Steps [from, to) of the permutation (see permutationSteps in reference.ts).
export type Range = { from: number; to: number };

// What a build takes and what its caller reads: the bound of every input
// (clean, PRIME - 1, by default), whether the inputs sit in calldata at
// [0, 32t) as the stack holds them (a part after the first, whose entry
// loads them as they are: a shadowed input is then loaded from there instead
// of a memory slot the entry fills) and the outputs the caller uses (all by
// default). The t = 4 hash entry starts its rounds from the lazy values of
// its round 0 and reads s0' alone, so its last linear layer computes only
// that row (finalRoundRow0).
export type Boundary = {
  bounds?: bigint[];
  calldata?: boolean;
  live?: number[];
  // the inputs as [s0, PRIME, s1, ...] rather than over the PRIME copy
  primeSecond?: boolean;
  // with primeSecond, a PRIME copy this many dead values below them
  primeBelow?: number;
};

// A part hands its state over below 2p: an internal round leaves m_i + sum
// with both reduced, and any output above the bound is reduced before it is
// stored. The next part takes the words as they are, within that bound.
export const HANDOVER_BOUND = 2n * PRIME - 1n;
export const HANDOVER_BOUND_TEXT = "2p";

// the boundary of part `from` of a split: lazy inputs from calldata
export function partBoundary(t: number, from: number): Boundary {
  if (from === 0) return {};
  return { bounds: new Array(t).fill(HANDOVER_BOUND), calldata: true };
}

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
  // the round constants of the shared body's calls
  tables: Table[];
};

export const DIAG_MEMORY_BASE = 0;

// blocks a streamed external layer keeps on the stack
const STREAM_KEEP = 2;

// The internal rounds of the range but its first and last, whose code
// differs (the entry's PRIME copy, the final round's layout): the ones the
// shared body may run, from round `first`.
export function steadyRounds(
  params: Params,
  range: Range,
): { first: number; steady: number } {
  const rfHalf = params.roundsF / 2;
  const first = Math.max(range.from - 1, rfHalf) + 1;
  const last = Math.min(range.to - 2, rfHalf + params.roundsP - 1) - 1;
  return { first, steady: Math.max(last - first + 1, 0) };
}

// elements the consuming round holds on the stack: consumeSlots, or as
// many as leave 4 slots of the reach ([output, sum, m0] and a PRIME copy)
export function heldSlots(
  t: number,
  reach: number,
  consumeSlots: number,
): number {
  if (consumeSlots > 0) return Math.min(consumeSlots, t - 1);
  return Math.min(t - 1, reach - 4);
}

// elements the consuming round holds on the stack: the rounds the layout
// takes to rotate back, the length of the shared body; in sub-chains of
// `group` slots each rotates on its own, so the lcm of their lengths
export function bodyPeriod(
  params: Params,
  fork: Fork,
  consumeSlots: number,
  group = 0,
): number {
  const slots = heldSlots(params.t, fork.reach, consumeSlots);
  if (group === 0 || group >= slots) return slots;
  const rem = slots % group;
  return rem === 0 ? group : lcm(group, rem);
}

function lcm(a: number, b: number): number {
  const gcd = (x: number, y: number): number => (y === 0 ? x : gcd(y, x % y));
  return (a / gcd(a, b)) * b;
}

// The sub-chain lengths worth trying, by the period they give, shortest
// first: the one with the fewest chains per period (the chains cost a SWAP
// each, the calls of a shorter body their overhead)
export function groupCandidates(
  params: Params,
  fork: Fork,
  consumeSlots: number,
): number[] {
  const slots = bodyPeriod(params, fork, consumeSlots);
  const byPeriod = new Map<number, number>();
  for (let group = 1; group < slots; group++) {
    const period = bodyPeriod(params, fork, consumeSlots, group);
    if (period >= slots) continue;
    const prev = byPeriod.get(period);
    if (
      prev === undefined ||
      Math.ceil(slots / group) < Math.ceil(slots / prev)
    ) {
      byPeriod.set(period, group);
    }
  }
  return [...byPeriod].sort((a, b) => a[0] - b[0]).map(([, group]) => group);
}

class Builder {
  readonly e: Emitter;
  readonly t: number;
  readonly params: Params;
  readonly opts: BuildOptions;
  readonly range: Range;
  readonly vectors: number;
  // the state leaves on the stack in order (default) or in memory at
  // [0, 32t): always with shadow, and for any part that hands over
  readonly stateInMemory: boolean;
  readonly diagBase: number;
  // the shared body's scratch: the round constants of a call, then the
  // return offsets of its mid exit and of its end
  readonly rcBase: number;
  readonly period: number;
  readonly inputSlots: (number | undefined)[] = [];
  readonly stepBytes: number[] = [];
  state: Value[];
  // dead values left near the top of the state by the previous round,
  // collected at the start of the next internal round when gcInternal is on
  dead: Value[] = [];
  // the outputs the caller reads, in state order (all when undefined)
  readonly live: number[] | undefined;
  // external layers built so far
  layers = 0;
  // what the S-boxes of a template add in place of the round constants (the
  // hash entry's round 0, hashRound0)
  laneConstants: bigint[] | undefined;
  // the state holds the S-box outputs of the current round (externalStream)
  sboxed = false;
  // the outputs are already at [0, 32t) (streamLinear)
  stored = false;

  constructor(
    params: Params,
    inputs: bigint[][],
    opts: BuildOptions,
    fork: Fork,
    range: Range,
    shadow: ReadonlySet<string>,
    permissive: boolean,
    boundary: Boundary = {},
  ) {
    this.params = params;
    this.t = params.t;
    this.opts = opts;
    this.range = range;
    this.live = boundary.live;
    this.vectors = inputs.length;
    this.stateInMemory = opts.shadow || range.to < stepCount(params);
    this.e = new Emitter(inputs.length, fork, shadow, permissive);
    // the hand-off region [0, 32t) comes first, then the diag table, the
    // body scratch and the shadow slots
    this.diagBase = this.stateInMemory ? 32 * this.t : DIAG_MEMORY_BASE;
    this.rcBase =
      this.diagBase + (opts.diagInMemory ? 32 * (this.t - opts.diagPush32) : 0);
    this.period = bodyPeriod(
      params,
      fork,
      opts.consumeSlots,
      opts.consumeGroup,
    );
    this.e.slotBase =
      this.rcBase + (opts.sharedBody ? 32 * (this.period + 2) : 0);
    if (opts.primeInMemory) this.e.slotBase += 32;
    // takes: [s0, s1, ..., s(t-1), PRIME]
    this.state = [];
    for (let i = 0; i < this.t; i++) {
      const vals = inputs.map((inp) => inp[i]);
      const v = new Value(`s${i}`, boundary.bounds?.[i] ?? PRIME - 1n, vals);
      this.e.key(v, `in:${i}`);
      if (shadow.has(`in:${i}`)) {
        if (boundary.calldata) this.e.declareCalldata(v, 32 * i);
        else this.inputSlots[i] = this.e.declare(v);
      }
      this.state.push(v);
    }
    if (boundary.primeSecond) {
      this.e.stack = [this.state[0], this.e.P, ...this.state.slice(1)];
      if (boundary.primeBelow !== undefined) {
        for (let k = 0; k < boundary.primeBelow; k++) {
          const zeros = inputs.map(() => 0n);
          this.e.stack.push(new Value(`g${k}`, 0n, zeros));
        }
        this.e.stack.push(this.e.P);
      }
    } else {
      this.e.stack = [...this.state, this.e.P];
    }
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

  // Sum of values with every operand DUPed in advance, deepest value first
  // (its DUP happens before the copies pile up; values in memory are
  // loaded last), so the chain runs in place and leaves nothing behind. A
  // reduction (where a partial sum would overflow or the final one exceed
  // cap) is an ADDMOD with a PRIME copy placed under its operand while the
  // reach of the later DUPs allows (every copy pushes them one deeper;
  // loads from memory have no reach), the first steps first, else an
  // ADDMOD with a copy DUPed on top and swapped under the accumulator
  // (3 gas more, no slot).
  chainSumInPlace(values: Value[], name: string, cap: bigint): Value {
    const e = this.e;
    const n = values.length;
    if (n < 2) throw new Error("chainSumInPlace needs two values");
    const order = this.byDepth(values)
      .reverse()
      .map((i) => values[i]);
    // per step: "addmod" (PRIME under the operand), "addmodTop" (PRIME
    // swapped under the accumulator) or "add"
    const steps: ("add" | "addmod" | "addmodTop")[] = [];
    let bound = order[0].bound;
    for (let j = 1; j < n; j++) {
      const lazy = bound + order[j].bound;
      const last = j === n - 1;
      if (lazy <= UINT256_MAX && !(last && lazy > cap)) {
        steps.push("add");
        bound = lazy;
      } else {
        steps.push("addmodTop");
        bound = PRIME - 1n;
      }
    }
    // the slots each DUPed operand has left: order[i] is DUPed after the
    // n - 1 - i operands below it and the copies placed under them
    const room: (number | undefined)[] = order.map((v, i) => {
      const at = e.find(v);
      const index = at + (n - 1 - i);
      return at > 0 && index <= e.maxReach ? e.maxReach - index : undefined;
    });
    for (let j = 1; j < n; j++) {
      if (
        steps[j - 1] === "addmodTop" &&
        room.slice(0, j).every((r) => r === undefined || r > 0)
      ) {
        steps[j - 1] = "addmod";
        for (let i = 0; i < j; i++) {
          if (room[i] !== undefined) room[i]!--;
        }
      }
    }
    for (let j = n - 1; j >= 1; j--) {
      if (steps[j - 1] === "addmod") e.pushPrime();
      e.dup(order[j]);
    }
    e.dup(order[0]);
    let acc = order[0];
    for (let j = 1; j < n; j++) {
      if (steps[j - 1] === "add") {
        acc = e.compute("add", [inplace(acc), inplace(order[j])], name);
      } else if (steps[j - 1] === "addmod") {
        acc = e.compute(
          "addmod",
          [inplace(acc), inplace(order[j]), inplace(this.P)],
          name,
        );
      } else {
        e.pushPrime();
        e.swap(2);
        acc = e.compute(
          "addmod",
          [inplace(order[j]), inplace(acc), inplace(this.P)],
          name,
        );
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

  // x^5 for y on top without a PRIME copy under it: the copies are DUPed
  // and SWAPped under the operands instead, same gas as sbox with its copy
  // pre-placed.
  sboxNoPrime(y: Value, name: string): Value {
    const e = this.e;
    if (e.top(0) !== y) throw new Error("sboxNoPrime expects y on top");
    e.pushPrime();
    const x2 = e.compute("mulmod", [y, y, inplace(this.P)], "x2");
    e.pushPrime();
    e.swap(1);
    const x4 = e.compute("mulmod", [x2, inplace(x2), inplace(this.P)], "x4");
    e.pushPrime();
    e.swap(2);
    return e.compute(
      "mulmod",
      [inplace(y), inplace(x4), inplace(this.P)],
      name,
    );
  }

  // Keeps a PRIME copy near the top so later copies stay within reach.
  floatPrime() {
    const n = this.e.findPrime();
    if (n === 0 || n > this.e.maxReach / 2) this.e.pushPrime();
  }

  // ---- external rounds from templates -----------------------------------------

  // The template of a list whose layout the stack holds for `inputs` (the
  // s<i> of the layout), or undefined.
  template(list: Template[], inputs: Value[]): Template | undefined {
    const e = this.e;
    return list.find((tpl) =>
      tpl.init.every((name, k) => {
        if (k >= e.depth) return false;
        const v = e.top(k);
        return name === "P" ? v.isPrime : v === inputs[Number(name.slice(1))];
      }),
    );
  }

  // Replays the stack program of a template (templates.ts) on `inputs`;
  // `round` names the round constants of its lanes. Returns the values its
  // moves name s<i>', as names[i], which end in the template's final layout.
  runTemplate(
    list: Template[],
    inputs: Value[],
    names: string[],
    round?: number,
  ): Value[] {
    const e = this.e;
    const tpl = this.template(list, inputs);
    if (!tpl) throw new Error("no template fits the layout");
    const out: Value[] = new Array(names.length);
    for (const move of tpl.ops.split(" ")) {
      let m: RegExpExecArray | null;
      if ((m = /^dup(\d+)$/.exec(move))) {
        e.dup(e.top(Number(m[1]) - 1));
      } else if ((m = /^swap(\d+)$/.exec(move))) {
        e.swap(Number(m[1]));
      } else if (move === "P") {
        e.pushPrime();
      } else if ((m = /^d(\d+)$/.exec(move))) {
        const i = Number(m[1]);
        const d = this.params.internalDiagMinusOne[i];
        if (this.diagStored(i)) e.mload(d, this.diagBase + 32 * i, `d${i}`);
        else e.push(d, `d${i}`);
      } else if (move === "4") {
        e.push(4n);
      } else if (move === "pop") {
        e.pop();
      } else if ((m = /^(add|addmod|mulmod)=(.+)$/.exec(move))) {
        const op = m[1] as "add" | "addmod" | "mulmod";
        const operands = [inplace(e.top(0)), inplace(e.top(1))];
        if (op !== "add") operands.push(inplace(this.P));
        const index = /^s(\d+)'$/.exec(m[2]);
        const v = e.compute(
          op,
          operands,
          index ? names[Number(index[1])] : m[2],
        );
        if (index) out[Number(index[1])] = v;
        e.endLine();
      } else if ((m = /^sbox(\d+)(n?)$/.exec(move))) {
        if (round === undefined) throw new Error("sbox needs a round");
        this.templateLane(inputs, Number(m[1]), round, m[2] === "");
        e.endLine();
      } else {
        throw new Error(`unknown template move ${move}`);
      }
    }
    e.endLine();
    for (let i = 0; i < names.length; i++) {
      if (!out[i]) throw new Error(`template leaves s${i}' unnamed`);
    }
    return out;
  }

  // An external round of t <= 4 from its template. Unmatched t = 4
  // layouts use separate S-boxes and a linear template or generic M4.
  externalTemplate(kind: TemplateKind, round?: number) {
    const names = Array.from({ length: this.t }, (_, i) => `s${i}'`);
    if (this.t === 4) {
      const full = TEMPLATES[4][kind];
      if (this.template(full, this.state)) {
        this.state = this.runTemplate(full, this.state, names, round);
        return;
      }
      if (round !== undefined) this.addConstantsAndSbox(round);
      const linear =
        kind === "final"
          ? LINEAR_FINAL4
          : BLOCKS[kind === "exit" ? "exit" : "block"];
      if (this.template(linear, this.state)) {
        this.state = this.runTemplate(linear, this.state, names);
      } else {
        this.externalMatrix(
          kind === "final",
          kind === "exit" ? () => this.e.pushPrime() : undefined,
          kind !== "exit",
        );
      }
      return;
    }
    const list = TEMPLATES[this.t]?.[kind] ?? [];
    this.state = this.runTemplate(list, this.state, names, round);
  }

  // s_i + c then x^5 for lane i on top, consumed in place; with primeUnder
  // the PRIME copy under it is consumed as well. A lazy input that does not
  // fit the ADD takes an ADDMOD with that copy (or a swapped-in one) and
  // the S-box without it, leaving the same stack.
  templateLane(inputs: Value[], i: number, round: number, primeUnder: boolean) {
    const e = this.e;
    const s = inputs[i];
    if (e.top(0) !== s) throw new Error(`template expects s${i} on top`);
    if (primeUnder && e.top(1) !== this.P) {
      throw new Error(`template expects PRIME under s${i}`);
    }
    const c = this.constant(
      this.laneConstants?.[i] ?? this.params.roundConstants[round][i],
      "c",
    );
    let y: Value;
    if (e.fitsAdd(s, c)) {
      y = e.compute("add", [c, inplace(s)], `s${i}+c`);
    } else {
      if (!primeUnder) {
        e.pushPrime();
        e.swap(1);
      }
      y = e.compute("addmod", [c, inplace(s), inplace(this.P)], `s${i}+c`);
      primeUnder = false;
    }
    return primeUnder ? this.sbox(y, `x${i}`) : this.sboxNoPrime(y, `x${i}`);
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
    let order = this.byDepth(this.state);
    if (this.opts.shadow && this.opts.gcExternal) order.reverse();
    const memory = order.filter((i) => e.find(this.state[i]) === 0);
    if (memory.length) {
      // elements the consuming rounds keep in memory (the first indices):
      // loaded last, highest index first, so that the blocks come out in
      // order with block 0 on top
      order = [
        ...order.filter((i) => i !== 0 && !memory.includes(i)),
        ...memory.sort((a, b) => b - a),
        0,
      ];
    }
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
    const gcM4 = this.opts.gcM4 && this.layers > this.opts.gcM4From;
    const gc = (gcM4 || hooks.forceGc) && !hooks.beforeOutputs;
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
    this.layers++;
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
        if (this.opts.externalTemplate) {
          // the block's inputs on top in order, consumed by its template
          for (let i = 3; i >= 0; i--) {
            u[i] = this.pairAdd(block[i], S[i], `u${4 * b + i}`, false);
            e.endLine();
          }
          const kind = clean
            ? "final"
            : b === 0 && beforeLast
              ? "exit"
              : "block";
          const res = this.runTemplate(
            BLOCKS[kind],
            u,
            names.slice(4 * b, 4 * b + 4),
          );
          for (let i = 0; i < 4; i++) out[4 * b + i] = res[i];
          continue;
        }
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

  // ---- streamed external rounds (externalStream) ---------------------------

  get stream(): boolean {
    return this.opts.externalStream && this.opts.externalD && this.t >= 8;
  }

  // The blocks a streamed layer leaves on the stack.
  get streamKeep(): number {
    return Math.min(STREAM_KEEP, this.t / 4);
  }

  // s + c and the S-box of a lane over a PRIME copy: an input on top gets
  // the copy swapped under it, any other is DUPed over one (its slot is
  // left dead); a lazy input that does not fit the ADD takes an ADDMOD
  // with a second copy.
  streamLane(s: Value, c: bigint, name: string): Value {
    const e = this.e;
    const k = this.constant(c, "c");
    const fits = e.fitsAdd(s, k);
    const onTop = e.top(0) === s;
    e.pushPrime();
    if (!fits) e.pushPrime();
    if (onTop) e.swap(fits ? 1 : 2);
    else e.dup(s);
    const y = fits
      ? e.compute("add", [k, inplace(s)], "y")
      : e.compute("addmod", [k, inplace(s), inplace(this.P)], "y");
    return this.sbox(y, name);
  }

  // The S-boxes of a round from the state wherever it is (after an
  // internal round or at the entry of a part): every output goes to a
  // memory slot but those of the kept blocks, the last ones.
  streamSbox(round: number) {
    const e = this.e;
    const t = this.t;
    const k = t / 4;
    const keep = this.streamKeep;
    e.pushPrime();
    e.endLine();
    const out: Value[] = new Array(t);
    for (let i = 0; i < t; i++) {
      const c = this.params.roundConstants[round][i];
      out[i] = this.streamLane(this.state[i], c, `x${i}`);
      if (Math.floor(i / 4) < k - keep) e.spill(out[i]);
      e.endLine();
    }
    this.state = out;
    this.sboxed = true;
  }

  // The linear layer of a round from its S-box outputs (or the inputs,
  // before round 0): the column sums S (reduced), then block by block,
  // those whose inputs sit on the stack first, u = x + S and the M4 of the
  // block (templates.ts). With `next` the M4 runs straight into the S-boxes
  // of that round, stored to memory slots but those of the last blocks;
  // without, it is the last round's, reduced, and its outputs go straight
  // to their words of [0, 32t) for the caller.
  streamLinear(next?: number) {
    const e = this.e;
    const t = this.t;
    const k = t / 4;
    const keep = this.streamKeep;
    this.layers++;
    const x = this.state;
    e.pushPrime();
    e.endLine();
    const S: Value[] = new Array(4);
    for (let i = 3; i >= 0; i--) {
      const column = Array.from({ length: k }, (_, b) => x[4 * b + i]);
      S[i] = this.chainSumInPlace(column, `S${i}`, PRIME - 1n);
      e.endLine();
    }
    const onStack = (b: number) =>
      [0, 1, 2, 3].every((i) => e.find(x[4 * b + i]) > 0);
    const blocks = Array.from({ length: k }, (_, b) => k - 1 - b);
    const order = [
      ...blocks.filter((b) => onStack(b)),
      ...blocks.filter((b) => !onStack(b)),
    ];
    const kind = next === undefined ? "final" : "block";
    const out: Value[] = new Array(t);
    order.forEach((b, n) => {
      const u: Value[] = new Array(4);
      for (let i = 3; i >= 0; i--) {
        u[i] = this.pairAdd(x[4 * b + i], S[i], `u${4 * b + i}`, false);
        e.endLine();
      }
      const names = [0, 1, 2, 3].map((i) => `s${4 * b + i}'`);
      const o = this.runTemplate(BLOCKS[kind], u, names);
      for (let i = 0; i < 4; i++) {
        const j = 4 * b + i;
        if (e.top(0) !== o[i]) e.swap(e.find(o[i]) - 1);
        if (next !== undefined) {
          const c = this.params.roundConstants[next][j];
          out[j] = this.streamLane(o[i], c, `x${j}`);
          if (n + keep < k) e.spill(out[j]);
        } else {
          out[j] = o[i];
          e.mstore(32 * j);
        }
        e.endLine();
      }
    });
    this.state = out;
    this.sboxed = next !== undefined;
    this.stored = next === undefined;
  }

  // Last round when the caller reads s0' alone (t = 4): row 0 of M4 on the
  // S-box outputs, s0' = 5 x0 + 7 x1 + x2 + 3 x3, taken straight from the
  // S-boxes instead of the M4 temporaries. A PRIME copy for the final MOD
  // goes down first; each lane, last first, is S-boxed on top of its
  // coefficient and a PRIME copy, MULMODed by the coefficient in place and
  // ADDed to the row so far, which stays under 4p.
  finalRoundRow0(round: number) {
    const e = this.e;
    if (this.t !== 4) throw new Error("finalRoundRow0 is t = 4 only");
    const row = [5n, 7n, 1n, 3n];
    e.pushPrime();
    let acc: Value | undefined;
    for (let i = 3; i >= 0; i--) {
      const s = this.state[i];
      const k = row[i];
      let coeff: Value | undefined;
      if (k !== 1n) {
        e.pushPrime();
        coeff = e.push(k);
      }
      const c = this.constant(this.params.roundConstants[round][i], "c");
      e.pushPrime();
      let y: Value;
      if (e.fitsAdd(s, c)) {
        y = e.compute("add", [c, s], `s${i}+c`);
      } else {
        y = e.compute("addmod", [c, s, this.P], `s${i}+c`);
      }
      let term = this.sbox(y, `s${i}'`);
      if (coeff) {
        term = e.compute(
          "mulmod",
          [inplace(term), inplace(coeff), inplace(this.P)],
          `${k}s${i}'`,
        );
      }
      acc = acc
        ? e.compute("add", [inplace(term), inplace(acc)], "row0")
        : term;
      e.endLine();
    }
    const out = e.compute("mod", [inplace(acc!), inplace(this.P)], "s0'");
    e.endLine();
    this.state = [out];
  }

  // Round 0 of the hash entry for n inputs, from the PRIME copy SETUP
  // leaves. The other lanes are the sponge constants (zeros, then the
  // capacity n << 64), so the initial linear layer and the constant addition
  // fold into y_i = p_i + K_i, p_i = sum_j M4[i][j] in_j and K_i = M4[i][3]
  // (n << 64) + c_i. The forms program of HASH_FORMS loads the inputs and
  // leaves p_i over the PRIME copy SETUP pushed, then ROUND4 adds K_i in the
  // S-boxes, leaving [s0', PRIME, s1', s2', s3', 3 dead values, PRIME] for
  // the rounds after.
  hashRound0(n: number, words: bigint[][]) {
    const e = this.e;
    if (this.t !== 4) throw new Error("hashRound0 is t = 4 only");
    const program = HASH_FORMS[n];
    if (!program) throw new Error(`hash arity ${n}`);
    // the words as CALLDATALOAD leaves them, not reduced
    const raw = Array.from({ length: n }, (_, i) => {
      const v = new Value(
        `r${i}`,
        UINT256_MAX,
        words.map((w) => w[i]),
      );
      e.declareCalldata(v, 4 + 32 * i);
      return v;
    });
    e.stack = [this.P];
    e.maxDepth = 1;
    const forms = new Map<string, Value>();
    for (const move of program.split(" ")) {
      let m: RegExpExecArray | null;
      if ((m = /^dup(\d+)$/.exec(move))) {
        e.dup(e.top(Number(m[1]) - 1));
      } else if ((m = /^swap(\d+)$/.exec(move))) {
        e.swap(Number(m[1]));
      } else if (move === "P") {
        e.pushPrime();
      } else if (move === "4") {
        e.push(4n);
      } else if ((m = /^r(\d+)$/.exec(move))) {
        e.calldataLoad(raw[Number(m[1])]);
      } else if ((m = /^(add|addmod|mulmod|mod)=(.+)$/.exec(move))) {
        const op = m[1] as "add" | "addmod" | "mulmod" | "mod";
        const operands = [inplace(e.top(0)), inplace(e.top(1))];
        if (op === "addmod" || op === "mulmod") operands.push(inplace(this.P));
        forms.set(m[2], e.compute(op, operands, m[2]));
        e.endLine();
      } else {
        throw new Error(`unknown forms move ${move}`);
      }
    }
    e.endLine();
    const form = (name: string) => {
      const v = forms.get(name);
      if (!v) throw new Error(`hash_${n} round 0 leaves no ${name}`);
      return v;
    };
    const p2 = form("p2");
    const inputs = [form("p0"), form("p1"), p2, forms.get("p3") ?? p2];
    // M4[i][3], the capacity's column
    const column = [3n, 1n, 7n, 6n];
    const iv = BigInt(n) << 64n;
    this.laneConstants = column.map(
      (c, i) => (c * iv + this.params.roundConstants[0][i]) % PRIME,
    );
    const names = Array.from({ length: 4 }, (_, i) => `s${i}'`);
    this.state = this.runTemplate(ROUND4_FIRST, inputs, names, 0);
    this.laneConstants = undefined;
  }

  // Writes the state to [0, 32t) for the next part or the caller. DUP and
  // MSTORE leave the stack as it was, so every element is fetched from the
  // same layout (shadowed ones with MLOAD). A hand-over reduces an element
  // above the bound the next part takes.
  storeState(handsOver: boolean) {
    const e = this.e;
    e.comment("State to memory");
    for (let i = 0; i < this.t; i++) {
      e.dup(this.state[i]);
      if (handsOver && this.state[i].bound > HANDOVER_BOUND) {
        this.state[i] = this.modTop(this.state[i]);
      }
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
    if (this.opts.internalTemplate && t === 4) {
      // x + s1 + s3 is a lazy ADD in the program
      const lazy = this.state[1].bound + this.state[3].bound + (PRIME - 1n);
      if (lazy <= UINT256_MAX && this.template(INTERNAL4, this.state)) {
        const names = Array.from({ length: t }, (_, i) => `s${i}'`);
        this.state = this.runTemplate(INTERNAL4, this.state, names, round);
        this.dead = [];
        return;
      }
    }
    if (this.opts.internalTemplate && t === 3) {
      const b1 = this.state[1].bound;
      const b2 = this.state[2].bound;
      const p1 = PRIME - 1n;
      if (b1 <= 4n * p1 && b2 <= 5n * p1) {
        const final =
          !nextInternal ||
          round === this.params.roundsF / 2 + this.params.roundsP - 1;
        const kind =
          b1 > 3n * p1
            ? "reset"
            : b2 > 2n * p1
              ? "high"
              : final
                ? "final"
                : "low";
        const list = INTERNAL3_PERIODIC[kind];
        if (this.template(list, this.state)) {
          const names = Array.from({ length: t }, (_, i) => `s${i}'`);
          this.state = this.runTemplate(list, this.state, names, round);
          this.dead = [];
          return;
        }
      }
      // the lazy ADDs: x + s1 + 2 s2 and 2 x + s1 + s2 (+ c in the next
      // round) from reduced inputs, x + s2 and s2 + sum from lazy ones
      const steady =
        PRIME - 1n + b1 + 2n * b2 <= UINT256_MAX &&
        3n * (PRIME - 1n) + b1 + b2 <= UINT256_MAX;
      const lazy = PRIME - 1n + b2 <= UINT256_MAX;
      const list = steady
        ? INTERNAL3.slice(0, 1)
        : lazy
          ? INTERNAL3.slice(1)
          : undefined;
      if (list && this.template(list, this.state)) {
        const names = Array.from({ length: t }, (_, i) => `s${i}'`);
        this.state = this.runTemplate(list, this.state, names, round);
        this.dead = [];
        return;
      }
    }
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

    const s1 = this.state[1];
    if (
      this.opts.internalMul3 &&
      t === 2 &&
      !collect &&
      3n * (PRIME - 1n) + s1.bound <= UINT256_MAX
    ) {
      // s1' = (3 s1 mod P) + s0^5 lazy on the PRIME copy for the next round,
      // s0' = 2 s0^5 + s1 lazy on its own copy: no sum to share
      if (this.opts.floatPrimeInternal) this.floatPrime();
      e.pushPrime();
      const m = e.compute(
        "mulmod",
        [this.constant(3n), s1, inplace(this.P)],
        "3s1",
      );
      const out1 = e.compute("add", [x5, inplace(m)], "s1'");
      e.endLine();
      if (nextInternal) e.pushPrime();
      const d = e.compute("add", [x5, x5], "2s0^5");
      const out0 = e.compute("add", [s1, inplace(d)], "s0'");
      e.endLine();
      this.dead.push(x5);
      this.state = [out0, out1];
      return;
    }

    const old = [x5, ...this.state.slice(1)];
    // the sum is reduced, or with internalReduceOutputs lazy as far as the
    // next round's s0 + c still fits
    const lazy = this.opts.internalReduceOutputs;
    const cap = lazy ? UINT256_MAX - x5.bound - (PRIME - 1n) : PRIME - 1n;
    const sum = this.chainSum(old, "sum", cap);
    e.endLine();

    // the round program after the last internal round adds its round
    // constants with an ADD only to an output that fits, otherwise an ADDMOD
    // and an S-box without its PRIME copy (14 gas) instead of reducing here
    // (8)
    const nextC =
      this.opts.externalTemplate &&
      t <= 3 &&
      nextInternal &&
      round === this.params.roundsF / 2 + this.params.roundsP - 1
        ? this.params.roundConstants[round + 1]
        : undefined;
    const tight = (bound: bigint, i: number) =>
      nextC !== undefined && i > 0 && bound + nextC[i] > UINT256_MAX;

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
        // next round; placed one element late so the deepest DUP fits. When
        // the outputs replace the old slots in place the previous round's
        // copy already sits under the new state, and with floatPrimeInternal
        // the copies come from deeper until the nearest leaves the reach
        if (!collect || e.findPrime() === 0) {
          if (this.opts.floatPrimeInternal) this.floatPrime();
          else if (!(t === 2 && this.opts.internalMul3 && !collect))
            e.pushPrime();
        }
      }
      if (i === 0 && nextInternal) {
        // PRIME copy under the next round's s0 + c
        e.pushPrime();
      }
      const reduce = lazy && i > 0;
      if (d === 1n) {
        out[i] = this.pairAdd(
          s,
          sum,
          `s${i}'`,
          reduce || tight(s.bound + sum.bound, i),
        );
      } else if (d === 2n) {
        if (e.fitsAdd(s, s)) {
          const wideSum = sum.bound + 2n * s.bound;
          out[i] = this.addTo(
            () => e.compute("add", [s, s], `2s${i}`),
            sum,
            `s${i}'`,
            reduce || wideSum > UINT256_MAX || tight(wideSum, i),
          );
        } else {
          out[i] = this.addTo(
            () => e.compute("mulmod", [s, this.constant(2n), this.P], `2s${i}`),
            sum,
            `s${i}'`,
            reduce ||
              !e.fitsAdd(sum, this.P) ||
              tight(sum.bound + (PRIME - 1n), i),
          );
        }
      } else {
        out[i] = this.addTo(
          () => e.compute("mulmod", [s, this.diag(i), this.P], `m${i}`),
          sum,
          `s${i}'`,
          reduce ||
            !e.fitsAdd(sum, this.P) ||
            tight(sum.bound + (PRIME - 1n), i),
        );
      }
      if (collect && i > 0) this.gc(s);
      e.endLine();
    }
    this.dead.push(sum, x5);
    this.state = out;
  }

  // The chains in which the consuming round takes the elements of `old` the
  // stack holds but s0, as index lists. m0 takes the slot of a chain's
  // first element, the output of each element takes the slot of the next
  // one and the last output the first slot when m0 is swapped back on top
  // (one SWAP per chain, the last one's in place of the swap that brings
  // m0 to the sum), so the chains decide the next layout: for the rounds
  // in between slot order from the slot under the sum, as one chain (the
  // layout rotates by one slot) or in sub-chains of consumeGroup slots
  // (each rotates on its own), and for the last internal round chains that
  // leave every element in the slots of its block of the external layer
  // (block 0 on top, as externalD needs; the elements in memory are the
  // first indices and come out on top). Each slot is an edge from the block
  // of its range to the block of the element it holds, so those chains are
  // Eulerian circuits of the blocks (in- and out-degree are the block
  // size), one per connected component, found by Hierholzer's algorithm
  // from the lowest slot left.
  consumeChains(old: Value[], mem: number, nextInternal: boolean): number[][] {
    const e = this.e;
    const t = this.t;
    const slots = t - 1 - mem;
    // slot s holds index s - 2 + mem in the block order
    const at = new Map<number, number>();
    for (let i = 1; i < t; i++) {
      const s = e.find(old[i]);
      if (s >= 3 && s <= slots + 2) at.set(s, i);
    }
    if (at.get(3) === undefined) throw new Error("no element under the sum");
    const order = [...at.keys()].sort((a, b) => a - b);
    const chains: number[][] = [];
    if (nextInternal) {
      const group = this.opts.consumeGroup || order.length;
      for (let k = 0; k < order.length; k += group) {
        chains.push(order.slice(k, k + group).map((s) => at.get(s)!));
      }
      return chains;
    }
    const block = (i: number) => i >> 2;
    const out = new Map<number, number[]>();
    for (const s of order) {
      const b = block(s - 2 + mem);
      out.set(b, [...(out.get(b) ?? []), s]);
    }
    const used = new Set<number>();
    for (const first of order) {
      if (used.has(first)) continue;
      const circuit: number[] = [];
      const stack = [{ node: block(first - 2 + mem), via: 0 }];
      while (stack.length) {
        const top = stack[stack.length - 1];
        const s = out.get(top.node)?.pop();
        if (s !== undefined) stack.push({ node: block(at.get(s)!), via: s });
        else circuit.push(stack.pop()!.via);
      }
      circuit.pop();
      circuit.reverse();
      const start = circuit.indexOf(first);
      const chain = [...circuit.slice(start), ...circuit.slice(0, start)];
      for (const s of chain) used.add(s);
      chains.push(chain.map((s) => at.get(s)!));
    }
    if (used.size !== slots) throw new Error("the blocks have no circuit");
    return chains;
  }

  // Internal round that consumes the old state in place. Expects [s0, P] on
  // top, the other elements right under them and a PRIME copy under the
  // state (installed by the first round, from the slot below). The sum
  // chain lands on a PRIME copy so that s0^5, swapped on top of it, is
  // consumed by its MULMOD, whose result takes the slot right under the
  // sum. Every other element is swapped to the top (the previous output
  // takes its slot), gets a PRIME copy swapped under it and is consumed by
  // its MULMOD; the last ADD consumes the sum and m0 together.
  //
  // The stack holds reach - 4 such elements ([output, sum, m0] and the
  // PRIME copy below take the rest of the reach), or consumeSlots, one or
  // two more at the price of the sum chain's PRIME copies; beyond that the
  // first indices live in memory (block 0 and whole blocks, so that the
  // external layer after finds its blocks in place), loaded for the chain
  // and their MULMOD and stored again, and s0^5 joins the chain from memory
  // as well.
  // The first round gets them all on the stack: the ones the region does
  // not hold are loaded from where they sit (shadowed when out of reach),
  // each following an element whose output moves to memory so that
  // [output, sum, m0] stays on top, and the round ends by installing the
  // PRIME copy under the region.
  //
  // In the shared body the round constant is MLOADed from slot `rc` of the
  // scratch, with the bound of any field element so that the body never
  // depends on the constant of one call.
  internalRoundConsume(round: number, nextInternal: boolean, rc?: number) {
    const e = this.e;
    const t = this.t;
    const s0 = this.state[0];
    if (e.top(0) !== s0 || e.top(1) !== this.P) {
      throw new Error("internal round expects [s0, P] on top");
    }
    const slots = heldSlots(t, e.maxReach, this.opts.consumeSlots);
    const mem = t - 1 - slots;
    const c0 = this.params.roundConstants[round][0];
    let c: Operand;
    if (rc === undefined) {
      c = this.constant(c0, "c");
      if (!e.fitsAdd(s0, c)) throw new Error("s0 + c does not fit");
    } else {
      if (s0.bound + (PRIME - 1n) > UINT256_MAX) {
        throw new Error("s0 + c does not fit");
      }
      const offset = this.rcBase + 32 * rc;
      const vals = new Array(this.vectors).fill(c0);
      c = make(() => e.mloadValue(offset, "c", PRIME - 1n, vals));
    }
    const y = e.compute("add", [c, inplace(s0)], "s0+c");
    const x5 = this.sbox(y, "s0^5");
    e.endLine();
    // the external round before leaves an M4 temporary among the state;
    // its slot takes s0^5, which is swapped back on top
    for (const v of this.dead) this.gc(v);
    this.dead = [];
    if (e.top(0) !== x5) e.swap(e.find(x5) - 1);
    if (mem === 0 && e.stack[t] !== this.P) {
      // the PRIME copy the rounds DUP from, in place of the slot under the
      // state
      e.pushPrime();
      e.swap(t + 1);
      e.pop();
    }
    e.endLine();

    const old = [x5, ...this.state.slice(1)];
    if (mem > 0) e.spill(x5);
    e.pushPrime();
    const sum = this.chainSumInPlace(old, "sum", PRIME - 1n);
    e.endLine();
    // [sum, P, s0^5, ...]: s0^5 on top of the PRIME copy, m0 lands on the sum
    if (mem > 0) {
      e.swap(1);
      e.dup(x5);
    } else {
      e.swap(2);
    }
    const m0 = e.compute(
      "mulmod",
      [this.diag(0), inplace(x5), inplace(this.P)],
      "m0",
    );
    e.endLine();

    const out: Value[] = new Array(t);
    // m_i + sum on top; the output of an index in memory goes there
    const finish = (i: number, s: Value) => {
      const m = e.compute(
        "mulmod",
        [this.diag(i), inplace(s), inplace(this.P)],
        `m${i}`,
      );
      out[i] = e.compute("add", [sum, inplace(m)], `s${i}'`);
      if (i <= mem) e.spill(out[i]);
      e.endLine();
    };
    // an element not held by the region: loaded under a PRIME copy
    const load = (i: number) => {
      e.pushPrime();
      e.dup(old[i]);
      finish(i, old[i]);
    };
    const loads: number[] = [];
    for (let i = 1; i < t; i++) {
      const s = e.find(old[i]);
      if (s < 3 || s > slots + 2) loads.push(i);
    }
    const toStack = loads.filter((i) => i > mem);
    const chains = this.consumeChains(old, mem, nextInternal);
    const order = chains.flat();
    // m0 back on top, the chain's last output into the slot of its first
    // element (the sum is then right under m0 after the last chain)
    const close = () => e.swap(e.find(m0) - 1);
    if (this.opts.primeStack) {
      // the elements in memory first, then the PRIME copies of the first
      // `stacked` swapped elements under m0: [m0, P, ..., P, sum, ...]. The
      // k-th element sits under the copies left over its turn, so its swap
      // must still reach it; the elements after the stacked ones get their
      // copy swapped under them.
      for (const j of loads) if (j <= mem) load(j);
      const depths = order.map((i) => e.find(old[i]));
      const fits = (n: number) =>
        depths.slice(0, n).every((d, k) => d + n - k - 1 <= e.maxReach);
      let stacked = order.length;
      while (stacked > 0 && !fits(stacked)) stacked--;
      if (stacked > 0) {
        for (let k = 0; k < stacked; k++) e.pushPrime();
        e.swap(stacked);
        e.endLine();
      }
      let k = 0;
      for (const chain of chains) {
        for (const i of chain) {
          const s = old[i];
          e.swap(e.find(s) - 1);
          if (k >= stacked) {
            e.pushPrime();
            e.swap(1);
          }
          finish(i, s);
          if (i <= mem) {
            // the output went to memory: one that comes back to the stack
            // takes its place on top, with its own PRIME copy
            const j = toStack.shift();
            if (j === undefined) throw new Error("no element to load on top");
            load(j);
          }
          k++;
        }
        close();
      }
    } else {
      let k = 0;
      for (const chain of chains) {
        for (const i of chain) {
          const s = old[i];
          e.swap(e.find(s) - 1);
          e.pushPrime();
          e.swap(1);
          finish(i, s);
          if (i <= mem) {
            // the output went to memory: one that comes back to the stack
            // takes its place on top
            const j = toStack.shift();
            if (j === undefined) throw new Error("no element to load on top");
            load(j);
          }
          if (k === 0) for (const j of loads) if (j <= mem) load(j);
          k++;
        }
        close();
      }
    }
    if (toStack.length) throw new Error("elements left to load on top");
    out[0] = e.compute("add", [inplace(e.top(0)), inplace(e.top(1))], "s0'");
    if (mem > 0 && e.stack[slots + 1] !== this.P) {
      // the PRIME copy the rounds DUP from, in place of the slot under the
      // region
      e.pushPrime();
      e.swap(slots + 2);
      e.pop();
    }
    if (nextInternal) {
      // PRIME copy under the next round's s0 + c
      e.pushPrime();
      e.swap(1);
    }
    e.endLine();
    this.state = out;
  }

  // The steady internal rounds of the range that run through the shared
  // body, as the rounds of each call: full calls of a period, then the
  // remainder as a last call that leaves at the mid exit. Undefined when the
  // body would run once at most.
  bodyCalls(): number[][] | undefined {
    const { first, steady } = steadyRounds(this.params, this.range);
    if (this.opts.bodyInline > steady) {
      throw new Error("bodyInline exceeds the steady rounds");
    }
    const start = first + this.opts.bodyInline;
    const rest = steady - this.opts.bodyInline;
    const full = Math.floor(rest / this.period);
    if (full === 0) return undefined;
    const calls: number[][] = [];
    for (let c = 0; c < full; c++) {
      const r = start + c * this.period;
      calls.push(Array.from({ length: this.period }, (_, k) => r + k));
    }
    const rem = rest % this.period;
    if (rem > 0) {
      const r = start + full * this.period;
      calls.push(Array.from({ length: rem }, (_, k) => r + k));
    }
    return calls;
  }

  // Emits the calls of the shared body. A call CODECOPYs its round
  // constants from its code table to the scratch, stores its return label
  // and JUMPs to the body, which the last call falls into instead; the
  // body's text goes out there. The emitter simulates the body at every
  // call, recording it at the first (emitter.ts). A remainder call stores
  // its return label at the mid exit's slot, which the full calls had set
  // to the label right after the exit.
  emitBodyCalls(calls: number[][]) {
    const e = this.e;
    const period = this.period;
    const retMid = this.rcBase + 32 * period;
    const retEnd = retMid + 32;
    const rem = calls[calls.length - 1].length % period;
    e.comment("Shared body of the steady internal rounds (see the calls)");
    if (rem > 0) {
      e.pushLabel("body_mid");
      e.mstore(retMid);
      e.endLine();
    }
    for (const [c, rounds] of calls.entries()) {
      const n = rounds.length;
      const lastCall = c === calls.length - 1;
      e.comment(
        `Rounds ${rounds[0]} to ${rounds[n - 1]} (internal): body call ${c}`,
      );
      const name = `RC${c}`;
      e.table(
        name,
        rounds.map((r) => this.params.roundConstants[r][0]),
      );
      e.codecopy(name, n, this.rcBase);
      e.pushLabel(`ret${c}`);
      e.mstore(n < period ? retMid : retEnd);
      if (!lastCall) {
        e.pushLabel("body");
        e.jump();
      }
      e.endLine();

      e.beginBody(c === 0);
      e.label("body");
      e.endLine();
      for (const [k, r] of rounds.entries()) {
        if (k > 0) e.segment();
        if (k === rem && k > 0) {
          // the mid exit: a remainder call returns, a full one goes on
          e.jumpVia(retMid);
          e.endLine();
          e.label("body_mid");
          e.endLine();
        }
        e.nextRound();
        e.comment(`Round ${r} (internal)`);
        this.internalRoundConsume(r, true, k);
        e.comment("");
        this.stepBytes.push(e.bytes);
      }
      e.segment();
      e.jumpVia(n < period ? retMid : retEnd);
      e.endLine();
      e.endBody();
      if (lastCall) {
        e.comment(
          "Shared body, entered by the calls above (the last falls in)",
        );
        for (const lines of e.bodyLines) e.lines.push(...lines);
      }
      e.label(`ret${c}`);
      e.endLine();
    }
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

    if (this.opts.primeInMemory) {
      // the slot below the shadow slots
      const offset = e.slotBase - 32;
      e.comment("PRIME in memory, loaded where no copy is within reach");
      e.pushPrime();
      e.mstore(offset);
      e.endLine();
      e.comment("");
      e.primeSlot = offset;
    }

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
      if (this.opts.externalTemplate && this.t <= 4)
        this.externalTemplate("entry");
      else if (this.stream && to > 1) this.streamLinear(0);
      else this.externalMatrix(false, undefined, true);
      e.comment("");
      this.stepBytes.push(e.bytes);
    }

    let body: number[][] | undefined;
    if (this.opts.sharedBody) {
      if (!this.opts.internalConsume) {
        throw new Error("sharedBody needs internalConsume");
      }
      body = this.bodyCalls();
      if (!body) throw new Error("the body would run once at most");
    }

    for (let r = Math.max(from - 1, 0); r + 1 < to; r++) {
      if (body && r === body[0][0]) {
        this.emitBodyCalls(body);
        r += body.flat().length - 1;
        continue;
      }
      e.nextRound();
      // round r + 1 belongs to this part too
      const next = r + 2 < to;
      if (r < rfHalf) {
        e.comment(`Round ${r} (external)`);
        const last = r === rfHalf - 1;
        if (this.opts.externalTemplate && this.t <= 4) {
          this.externalTemplate(last && next ? "exit" : "round", r);
        } else if (this.stream) {
          if (!this.sboxed) this.streamSbox(r);
          if (!last && next) {
            this.streamLinear(r + 1);
          } else {
            this.sboxed = false;
            this.externalMatrix(
              false,
              last && next ? () => e.pushPrime() : undefined,
              !last,
            );
          }
        } else {
          this.addConstantsAndSbox(r);
          this.externalMatrix(
            false,
            last && next ? () => e.pushPrime() : undefined,
            !last,
          );
        }
      } else if (r < pEnd) {
        e.comment(`Round ${r} (internal)`);
        if (from === r + 1) {
          // the entry leaves [s0, ..., PRIME]: place the PRIME copy the
          // round expects under s0
          e.pushPrime();
          e.swap(1);
        }
        // the round programs of t <= 3 expect the PRIME copy under s0 as
        // well
        const primeUnder =
          (r < pEnd - 1 || (this.opts.externalTemplate && this.t <= 3)) && next;
        if (this.opts.internalConsume) {
          this.internalRoundConsume(r, r < pEnd - 1 && next);
        } else {
          this.internalRound(r, primeUnder);
        }
      } else if (r === total - 1 && this.live) {
        e.comment(`Round ${r} (external, s0' only)`);
        if (this.live.length !== 1 || this.live[0] !== 0) {
          throw new Error("only s0' can be the live output");
        }
        this.finalRoundRow0(r);
      } else {
        e.comment(`Round ${r} (external)`);
        if (this.opts.externalTemplate && this.t <= 4) {
          this.externalTemplate(r === total - 1 ? "final" : "round", r);
        } else if (this.stream) {
          if (!this.sboxed) this.streamSbox(r);
          if (r < total - 1 && next) {
            this.streamLinear(r + 1);
          } else if (r === total - 1 && this.stateInMemory) {
            this.streamLinear();
          } else {
            this.sboxed = false;
            this.externalMatrix(r === total - 1, undefined, true);
          }
        } else {
          this.addConstantsAndSbox(r);
          this.externalMatrix(r === total - 1, undefined, true);
        }
      }
      e.comment("");
      this.stepBytes.push(e.bytes);
    }

    if (this.stateInMemory && !this.stored) {
      this.storeState(to < stepCount(this.params));
    }
    e.endLine();
    return this.state;
  }
}

// The dead values hash round 0 leaves between its outputs and the PRIME copy
// under them, which the rounds after copy from
export const HASH_DEAD = 3;

// The round 0 the hash entry runs for n inputs (Builder.hashRound0) with its
// gas, bytes, stack depth and lazy outputs, checked against the reference
// before anything is written.
export type Prologue = {
  n: number;
  lines: string[];
  gas: number;
  bytes: number;
  // stack depth at the end: the rounds after run on top of it
  depth: number;
  // [s0', s1', s2', s3'] after round 0, lazy
  outputs: Value[];
};

export function buildHashPrologue(
  params: Params,
  inputs: bigint[][],
  fork: Fork,
): Prologue {
  const n = inputs[0].length;
  const states = inputs.map((input) => spongeState(params, input));
  const b = new Builder(
    params,
    states,
    DEFAULT_OPTIONS,
    fork,
    { from: 0, to: 2 },
    new Set(),
    false,
  );
  b.hashRound0(n, inputs);
  const e = b.e;
  states.forEach((state, k) => {
    const want = permutationSteps(params, state, 0, 2);
    for (let i = 0; i < params.t; i++) {
      if (b.state[i].vals[k] % PRIME !== want[i]) {
        throw new Error(`hash_${n} round 0: vector ${k} output ${i} mismatch`);
      }
    }
  });
  const layout: (Value | undefined)[] = [b.state[0], b.P, ...b.state.slice(1)];
  layout.push(...new Array(HASH_DEAD).fill(undefined), b.P);
  if (layout.some((v, i) => v && e.top(i) !== v)) {
    throw new Error(
      `hash_${n} round 0: outputs are not [s0', PRIME, s1', s2', s3', 3 dead, PRIME]`,
    );
  }
  return {
    n,
    lines: e.lines,
    gas: e.gas,
    bytes: e.bytes,
    depth: e.depth,
    outputs: b.state,
  };
}

// The rounds after round 0 shared by the hash entry's arities, built from
// the lazy values every prologue leaves (their bounds joined, their vectors
// concatenated) and reading s0' alone.
export function buildHashRounds(
  params: Params,
  prologues: Prologue[],
  maxBytes: number,
  fork: Fork,
): Best {
  const t = params.t;
  const inputs: bigint[][] = [];
  const bounds: bigint[] = new Array(t).fill(0n);
  for (const p of prologues) {
    for (let i = 0; i < t; i++) {
      if (p.outputs[i].bound > bounds[i]) bounds[i] = p.outputs[i].bound;
    }
    for (let k = 0; k < p.outputs[0].vals.length; k++) {
      inputs.push(p.outputs.map((v) => v.vals[k]));
    }
  }
  const best = buildBest(
    params,
    inputs,
    maxBytes,
    fork,
    { from: 2, to: stepCount(params) },
    { bounds, live: [0], primeSecond: true, primeBelow: HASH_DEAD },
  );
  if (!best) throw new Error(`the hash rounds do not fit on ${fork.name}`);
  return best;
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
  boundary: Boundary = {},
): BuildResult {
  let shadow: ReadonlySet<string> = new Set();
  let lastLoad: ReadonlyMap<string, number> = new Map();
  if (opts.shadow) {
    const probe = new Builder(
      params,
      inputs,
      opts,
      fork,
      range,
      shadow,
      true,
      boundary,
    );
    probe.build();
    shadow = probe.e.needed;
    lastLoad = probe.e.lastLoad;
  }
  const b = new Builder(
    params,
    inputs,
    opts,
    fork,
    range,
    shadow,
    false,
    boundary,
  );
  b.e.lastLoad = lastLoad;
  const outputs = b.build();
  const e = b.e;
  const final = range.to === stepCount(params);
  // the state indices the outputs hold
  const live = boundary.live ?? outputs.map((_, i) => i);

  if (!b.stateInMemory) {
    // the outputs must sit on top in state order and be clean
    for (let i = 0; i < live.length; i++) {
      if (e.stack[i] !== outputs[i]) {
        throw new Error(`output ${live[i]} is not at slot ${i + 1}`);
      }
      if (outputs[i].bound >= PRIME) {
        throw new Error(`output ${live[i]} is not clean`);
      }
    }
    if (!boundary.live && params.t <= 4 && e.stack[params.t] !== e.P) {
      throw new Error("PRIME expected under outputs");
    }
  } else if (final) {
    for (let i = 0; i < live.length; i++) {
      if (outputs[i].bound >= PRIME) {
        throw new Error(`output ${live[i]} is not clean`);
      }
    }
  } else {
    for (let i = 0; i < live.length; i++) {
      if (outputs[i].bound > HANDOVER_BOUND) {
        throw new Error(`output ${live[i]} is above the hand-over bound`);
      }
    }
  }

  // concrete check of the emitted stream against the reference permutation
  // (a part that hands over leaves lazy values, the next entry reduces them;
  // the inputs may be lazy as well)
  inputs.forEach((input, k) => {
    const clean = input.map((x) => x % PRIME);
    const want = permutationSteps(params, clean, range.from, range.to);
    for (let i = 0; i < live.length; i++) {
      const got = final ? outputs[i].vals[k] : outputs[i].vals[k] % PRIME;
      if (got !== want[live[i]]) {
        throw new Error(`vector ${k} output ${live[i]} mismatch`);
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
    tables: e.tables,
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
// cheapest build of the range (code and memory expansion) that stays within
// reach, depth and code size, or undefined when the schedules that build are
// too large or too deep (the caller may then split the permutation). The
// shadow option is only tried when no schedule keeps the whole state within
// reach, so the widths that fit the reach keep their stack-only output. With
// DUPN / SWAPN each combination also defers gcInternal as long as the depth
// allows, keeps as many diag constants PUSH32 as the code size allows and
// then as many steady rounds inline (the depth grows with gcInternalFrom and
// the size with diagPush32 and bodyInline, so a binary search finds each
// limit); a body over the code size first takes the sub-chains of the
// longest period that fits. Throws when nothing builds at all.
export function buildBest(
  params: Params,
  inputs: bigint[][],
  maxBytes: number,
  fork: Fork = FORKS.shanghai,
  range: Range = { from: 0, to: stepCount(params) },
  boundary: Boundary = {},
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
                  for (const internalReduceOutputs of params.t <= 3
                    ? bools
                    : [false]) {
                    for (const floatPrimeInternal of bools) {
                      // the consuming round neither collects garbage nor
                      // floats PRIME copies
                      const consume =
                        params.t >= 8 && !gcInternal && !floatPrimeInternal;
                      for (const internalConsume of consume ? bools : [false]) {
                        for (const primeStack of internalConsume
                          ? bools
                          : [false]) {
                          for (const sharedBody of internalConsume
                            ? bools
                            : [false]) {
                            // the templates replace the external rounds (t <= 4)
                            // or the M4 of every block (with externalD), so the
                            // options those would collect or pre-place are moot
                            const templated =
                              params.t <= 4
                                ? !gcExternal && !gcM4 && !primeUnderExternal
                                : externalD && !gcM4;
                            for (const externalTemplate of templated
                              ? bools
                              : [false]) {
                              for (const internalTemplate of (params.t === 3 ||
                                params.t === 4) &&
                              !gcInternal
                                ? bools
                                : [false]) {
                                for (const internalMul3 of params.t === 2 &&
                                internalReduceOutputs
                                  ? bools
                                  : [false]) {
                                  // with shadow the external rounds of the
                                  // templated blocks stream, which collects
                                  // no garbage
                                  const externalStream =
                                    shadow && externalD && externalTemplate;
                                  if (externalStream && gcExternal) continue;
                                  list.push({
                                    diagInMemory,
                                    gcExternal,
                                    gcM4,
                                    gcInternal,
                                    chainSwapMod,
                                    externalD,
                                    primeUnderExternal,
                                    internalReduceOutputs,
                                    floatPrimeInternal,
                                    internalConsume,
                                    primeStack,
                                    gcInternalFrom: 0,
                                    gcM4From: 0,
                                    diagPush32: 0,
                                    shadow,
                                    sharedBody,
                                    bodyInline: 0,
                                    consumeGroup: 0,
                                    consumeSlots: 0,
                                    externalTemplate,
                                    internalTemplate,
                                    internalMul3,
                                    primeInMemory: false,
                                    externalStream,
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
    // with shadow, a consuming schedule whose elements the reach cannot
    // hold all also with one and two more on the stack
    const extra = [fork.reach - 3, fork.reach - 2].filter((n) => n < params.t);
    return list.flatMap((opts) =>
      shadow && opts.primeStack && opts.sharedBody
        ? [opts, ...extra.map((consumeSlots) => ({ ...opts, consumeSlots }))]
        : [opts],
    );
  };
  const attempt = (opts: BuildOptions): BuildResult | undefined => {
    try {
      return buildPermutation(params, inputs, opts, fork, range, boundary);
    } catch {
      return undefined;
    }
  };
  // the code and the memory it expands (the state region at least)
  const cost = (result: BuildResult) =>
    result.gas + memoryGas(Math.max(result.memory, 32 * params.t));
  let best: Best | undefined;
  let built = 0;
  const failures: string[] = [];
  // the option searches after a first build: deeper garbage, sub-chains,
  // diag constants as PUSH32 and inline rounds as the code size allows;
  // the options and the build, or why it fails
  const finish = (
    opts: BuildOptions,
    result: BuildResult,
  ): { opts: BuildOptions; result: BuildResult } | string => {
    const build = () =>
      buildPermutation(params, inputs, opts, fork, range, boundary);
    try {
      if (result.maxDepth <= 1000) {
        if (opts.gcInternal && fork.reach > 16) {
          const gcInternalFrom = largest(params.roundsP, (n) => {
            const r = attempt({ ...opts, gcInternalFrom: n });
            return r !== undefined && r.maxDepth <= 1000;
          });
          opts = { ...opts, gcInternalFrom };
          result = build();
        }
        if (opts.gcM4 && fork.reach > 16) {
          const gcM4From = largest(params.roundsF + 1, (n) => {
            const r = attempt({ ...opts, gcM4From: n });
            return r !== undefined && r.maxDepth <= 1000;
          });
          opts = { ...opts, gcM4From };
          result = build();
        }
        if (opts.sharedBody && result.bytes > maxBytes) {
          // a body too large for the code size: sub-chains shorten it,
          // the longest period that fits (the shorter, the more chains
          // and calls)
          const groups = groupCandidates(params, fork, opts.consumeSlots);
          const fits = (n: number) => {
            const r = attempt({ ...opts, consumeGroup: groups[n] });
            return r !== undefined && r.bytes <= maxBytes;
          };
          if (groups.length > 0 && fits(0)) {
            const consumeGroup = groups[largest(groups.length - 1, fits)];
            opts = { ...opts, consumeGroup };
            result = build();
          }
        }
        if (opts.diagInMemory && result.bytes <= maxBytes) {
          const diagPush32 = largest(params.t, (n) => {
            const r = attempt({ ...opts, diagPush32: n });
            return r !== undefined && r.bytes <= maxBytes;
          });
          opts = { ...opts, diagPush32 };
          result = build();
        }
        if (opts.sharedBody && result.bytes <= maxBytes) {
          const { steady } = steadyRounds(params, range);
          const fits = (n: number) => {
            const r = attempt({ ...opts, bodyInline: n });
            return r !== undefined && r.bytes <= maxBytes;
          };
          const base = opts.bodyInline;
          let bodyInline = base + largest(steady - base, (n) => fits(base + n));
          // a remainder call and the mid exit cost more than the 3 gas
          // per round the body charges, so the largest count that leaves
          // none when one fits
          const period = bodyPeriod(
            params,
            fork,
            opts.consumeSlots,
            opts.consumeGroup,
          );
          const extra = (period - ((steady - bodyInline) % period)) % period;
          if (bodyInline >= extra && fits(bodyInline - extra)) {
            bodyInline -= extra;
          }
          opts = { ...opts, bodyInline };
          result = build();
        }
      }
    } catch (err) {
      return `${JSON.stringify(opts)}: ${(err as Error).message}`;
    }
    if (result.maxDepth > 1000) {
      return `${JSON.stringify(opts)}: depth ${result.maxDepth}`;
    }
    if (result.bytes > maxBytes) {
      return `${JSON.stringify(opts)}: ${result.bytes} bytes`;
    }
    return { opts, result };
  };
  const search = (list: BuildOptions[]) => {
    for (let opts of list) {
      let result: BuildResult;
      try {
        const build = () =>
          buildPermutation(params, inputs, opts, fork, range, boundary);
        if (opts.sharedBody) {
          // the round after a part's entry still loads from the entry's
          // shadow slots (a memory layout of its own), so the body starts
          // at the first count of inline rounds that builds
          let r = attempt(opts);
          while (r === undefined && opts.bodyInline < 2) {
            opts = { ...opts, bodyInline: opts.bodyInline + 1 };
            r = attempt(opts);
          }
          result = r ?? build();
        } else {
          result = build();
        }
      } catch (err) {
        failures.push(`${JSON.stringify(opts)}: ${(err as Error).message}`);
        continue;
      }
      built++;
      let chosen = finish(opts, result);
      // where the code size binds (a shorter body, diag constants in
      // memory, or no fit at all), PRIME from memory frees 30 bytes per
      // PUSH32 for 3 gas
      const binding =
        typeof chosen === "string"
          ? chosen.endsWith(" bytes")
          : (chosen.opts.sharedBody && chosen.opts.consumeGroup > 0) ||
            (chosen.opts.diagInMemory && chosen.opts.diagPush32 < params.t);
      if (binding) {
        const pim = { ...opts, primeInMemory: true };
        const r = attempt(pim);
        if (r !== undefined) {
          const alt = finish(pim, r);
          if (
            typeof alt !== "string" &&
            (typeof chosen === "string" ||
              cost(alt.result) < cost(chosen.result))
          ) {
            chosen = alt;
          }
        }
      }
      if (typeof chosen === "string") {
        failures.push(chosen);
        continue;
      }
      if (!best || cost(chosen.result) < cost(best.result)) best = chosen;
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
