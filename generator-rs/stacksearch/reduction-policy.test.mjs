import assert from "node:assert/strict";
import test from "node:test";
import { generateParams } from "../../generator/round-constants/round-constants.ts";
import { PRIME } from "../../generator/shared/field.ts";
import { FORKS } from "../../generator/huff/fork.ts";
import {
  buildBest,
  buildPermutation,
  DEFAULT_OPTIONS,
  stepCount,
} from "../../generator/huff/schedule.ts";

function internalCounts(lines) {
  return lines
    .join("\n")
    .split(/\/\/ Round \d+ \(/)
    .filter((s) => s.startsWith("internal)"))
    .map((s) => {
      const counts = {};
      for (const line of s.split("\n").slice(1)) {
        for (const op of line.split("//")[0].trim().split(/\s+/)) {
          counts[op] = (counts[op] ?? 0) + 1;
        }
      }
      return counts;
    });
}

for (const name of ["osaka", "amsterdam"]) {
  test(`t2 lazy MULMOD policy and external re-entry on ${name}`, () => {
    const params = generateParams(2);
    for (const rc of params.roundConstants) rc[0] = PRIME - 1n;
    for (const [b, floatPrimeInternal] of [
      [1n, false],
      [1n, true],
      [2n, false],
      [2n, true],
      [3n, false],
      [3n, true],
    ]) {
      const bounds = [3n * PRIME - 1n, b * PRIME - 1n];
      const inputs = [[0n, 0n], [1n, bounds[1]], bounds];
      // buildPermutation checks every output against permutationSteps.
      const result = buildPermutation(
        params,
        inputs,
        {
          ...DEFAULT_OPTIONS,
          internalMul3: true,
          floatPrimeInternal,
          internalReduceOutputs: true,
          externalTemplate: true,
        },
        FORKS[name],
        { from: 5, to: stepCount(params) },
        { bounds },
      );
      const rounds = internalCounts(result.lines);
      assert.equal(rounds.length, 56);
      assert.equal(rounds[0].addmod ?? 0, b === 3n ? 2 : 0);
      for (const round of rounds.slice(1)) {
        assert.equal(round.mul ?? 0, 0);
        assert.equal(round.addmod ?? 0, 0);
        assert.equal(round.mulmod, 4);
        assert.equal(round.add, 4);
      }
      assert.ok(result.outputs.every((v) => v.bound < PRIME));
    }
  });

  test(`t2 omitted backing and tight-budget compact selection on ${name}`, () => {
    const params = generateParams(2);
    const inputs = [
      [0n, 0n],
      [1n, PRIME - 1n],
      [PRIME - 1n, PRIME - 1n],
    ];
    const fork = FORKS[name];
    const compactBytes = name === "osaka" ? 3867 : 3956;
    const compactGas = name === "osaka" ? 5904 : 5865;
    const plainBytes = name === "osaka" ? 7373 : 3963;
    for (const tight of [false, true]) {
      const best = buildBest(
        params,
        inputs,
        tight ? compactBytes : fork.codeSize - 51,
        fork,
      );
      assert.ok(best);
      assert.equal(best.opts.internalMul3, true);
      assert.equal(best.opts.floatPrimeInternal, tight);
      assert.equal(best.result.bytes, tight ? compactBytes : plainBytes);
      assert.equal(best.result.gas, tight ? compactGas : 5862);
      assert.ok(best.result.maxDup <= fork.reach);
      assert.ok(best.result.maxDepth <= 1000);
    }
  });

  test(`t3 periodic reductions and external re-entry on ${name}`, () => {
    const params = generateParams(3);
    for (const rc of params.roundConstants) rc[0] = PRIME - 1n;
    const p1 = PRIME - 1n;
    const result = buildPermutation(
      params,
      [
        [0n, 0n, 0n],
        [p1, p1, p1],
        [1n, p1, 0n],
      ],
      { ...DEFAULT_OPTIONS, externalTemplate: true, internalTemplate: true },
      FORKS[name],
    );
    const rounds = internalCounts(result.lines);
    assert.equal(rounds.length, 56);
    const mods = rounds.map((s) => s.addmod ?? 0);
    assert.deepEqual(mods.slice(0, 5), [3, 1, 2, 1, 3]);
    assert.equal(mods[55], 2);
    assert.equal(mods.filter((n) => n === 1).length, 27);
    assert.equal(mods.filter((n) => n === 2).length, 15);
    assert.equal(mods.filter((n) => n === 3).length, 14);
    assert.equal(
      rounds.reduce((n, s) => n + s.add, 0),
      293,
    );
    assert.equal(
      rounds.reduce((n, s) => n + s.addmod, 0),
      99,
    );
    assert.ok(rounds.every((s) => s.mulmod === 3));
    assert.ok(result.outputs.every((v) => v.bound < PRIME));
  });
}
