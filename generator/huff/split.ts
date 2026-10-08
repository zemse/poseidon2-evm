// Cuts a permutation that does not fit the fork's code size into parts at
// step boundaries (the initial linear layer, then one step per round). Every
// hop costs the same whatever the cut (the hand-over in the caller, a cold
// STATICCALL and the entry of the callee), so the fewest parts cost the least
// gas unless a part only fits through the dearest schedules: a greedy pass
// finds that number by extending each part as far as the size allows (with
// the shared body of the internal rounds, at its shortest period, where
// that holds more), then the cuts are moved to balance the bytes so every
// part keeps the same slack, and fewer parts are kept while they build and
// cost less. Each part is built like a whole permutation (option search,
// bound tracker, reference check of its own steps); a part after the first
// takes its inputs as the part before leaves them, lazy below the hand-over
// bound (partBoundary), so its entry neither reduces nor stores them.

import type { Params } from "../round-constants/round-constants.ts";
import type { Fork } from "./fork.ts";
import { overhead, type Overhead } from "./render.ts";
import {
  buildBest,
  buildPermutation,
  groupCandidates,
  largest,
  partBoundary,
  stepCount,
  DEFAULT_OPTIONS,
  type Best,
  type BuildOptions,
  type Range,
} from "./schedule.ts";

export type Part = Best & { overhead: Overhead };

// the initcode is CONSTRUCTOR (at most 29 bytes), the runtime and the
// address word
const CONSTRUCTOR_BYTES = 29;

export function splitPermutation(
  params: Params,
  inputs: bigint[][],
  fork: Fork,
): Part[] {
  const t = params.t;
  const steps = stepCount(params);
  // entry and tail at their largest (every input shadowed, PUSH2 offsets)
  const allSlots = new Array(t).fill(0xffff);
  // a part after the first takes its inputs lazy from calldata (no
  // reduction, no slots)
  const budget = ({ from, to }: Range) =>
    fork.codeSize -
    overhead(fork, t, from === 0 ? allSlots : [], true, to < steps, from > 0)
      .bytes;
  const boundary = (range: Range) => partBoundary(t, range.from);

  // options for the size probes: the cheapest schedule of a short range,
  // which also decides whether the state needs shadowing
  const probe = buildBest(params, inputs, Infinity, fork, {
    from: 0,
    to: Math.min(steps, 6),
  });
  if (!probe) throw new Error("the first steps do not build");
  const probeOpts: BuildOptions = {
    ...DEFAULT_OPTIONS,
    shadow: probe.opts.shadow,
    diagInMemory: probe.opts.diagInMemory,
  };
  // the shared body of the steady internal rounds lets a part hold far
  // more of them: the probe also tries that schedule (as the option search
  // will), with the steady rounds it needs inline, as one chain and in the
  // sub-chains of the shortest period
  const bodyOpts: BuildOptions = {
    ...probeOpts,
    internalConsume: true,
    primeStack: true,
    sharedBody: true,
  };
  const groups = [0, ...groupCandidates(params, fork).slice(0, 1)];
  const fits = (opts: BuildOptions, range: Range): boolean => {
    try {
      const r = buildPermutation(
        params,
        inputs,
        opts,
        fork,
        range,
        boundary(range),
      );
      return r.maxDepth <= 1000 && r.bytes <= budget(range);
    } catch {
      return false;
    }
  };
  const builds = (range: Range): boolean =>
    fits(probeOpts, range) ||
    (t >= 8 &&
      groups.some((consumeGroup) =>
        [0, 1, 2].some((bodyInline) =>
          fits({ ...bodyOpts, bodyInline, consumeGroup }, range),
        ),
      ));

  // fewest parts: extend each as far as it fits
  const greedy: Range[] = [];
  const stepBytes: number[] = [];
  for (let from = 0; from < steps;) {
    const len = largest(steps - from, (n) =>
      n === 0 ? true : builds({ from, to: from + n }),
    );
    if (len === 0) {
      throw new Error(
        `step ${from} alone exceeds the code size on ${fork.name}`,
      );
    }
    const range = { from, to: from + len };
    const r = buildPermutation(
      params,
      inputs,
      probeOpts,
      fork,
      range,
      boundary(range),
    );
    let prev = 0;
    for (const b of r.stepBytes) {
      stepBytes.push(b - prev);
      prev = b;
    }
    greedy.push(range);
    from += len;
  }

  // cuts that balance the bytes of the steps over `count` parts
  const balance = (count: number, weights: number[]): Range[] => {
    const total = weights.reduce((a, b) => a + b, 0);
    const ranges: Range[] = [];
    let from = 0;
    let sum = 0;
    for (let step = 0; step < steps; step++) {
      sum += weights[step];
      const j = ranges.length + 1;
      if (j < count && sum >= (j * total) / count) {
        ranges.push({ from, to: step + 1 });
        from = step + 1;
      }
    }
    ranges.push({ from, to: steps });
    return ranges;
  };

  // the bytes of each step as built parts had them
  const measured = (parts: Part[]): number[] => {
    const weights: number[] = [];
    for (const part of parts) {
      let prev = 0;
      for (const b of part.result.stepBytes) {
        weights.push(b - prev);
        prev = b;
      }
    }
    return weights;
  };

  const build = (ranges: Range[]): Part[] | undefined => {
    const parts: Part[] = [];
    for (const range of ranges) {
      const best = buildBest(
        params,
        inputs,
        budget(range),
        fork,
        range,
        boundary(range),
      );
      if (!best) return undefined;
      const { result } = best;
      const o = overhead(
        fork,
        t,
        result.inputSlots,
        result.stateInMemory,
        range.to < steps,
        range.from > 0,
      );
      const runtime = result.bytes + o.bytes;
      if (runtime > fork.codeSize) {
        throw new Error(`part ${range.from}..${range.to}: ${runtime} bytes`);
      }
      if (CONSTRUCTOR_BYTES + runtime + 32 > fork.initcodeSize) {
        throw new Error(`part ${range.from}..${range.to}: initcode too large`);
      }
      parts.push({ ...best, overhead: o });
    }
    return parts;
  };
  const gas = (parts: Part[]) =>
    parts.reduce(
      (sum, p) => sum + p.overhead.entryGas + p.result.gas + p.overhead.tailGas,
      0,
    );
  const cheaper = (a: Part[] | undefined, b: Part[] | undefined) =>
    a && b ? (gas(b) < gas(a) ? b : a) : (a ?? b);

  let parts = cheaper(build(balance(greedy.length, stepBytes)), build(greedy));
  if (!parts) throw new Error(`no split fits on ${fork.name}`);
  // the option search per part may find smaller code than the probe: try
  // fewer parts while they fit and cost less (a part may only fit through
  // the dearest schedules), cut by the probe bytes and by the bytes the
  // parts actually had
  for (let count = greedy.length - 1; count >= 1; count--) {
    const fewer = cheaper(
      build(balance(count, stepBytes)),
      build(balance(count, measured(parts))),
    );
    if (!fewer || gas(fewer) >= gas(parts)) break;
    parts = fewer;
  }
  return parts;
}
