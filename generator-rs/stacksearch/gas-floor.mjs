// Osaka t = 2, 3, 4 opcode accounting and the fixed-mix stack-slot relaxation.
// Run with Node's native TypeScript support: node gas-floor.mjs [2 3 4].
// This reads generator output; compiled revm verification is a separate gate.

import assert from "node:assert/strict";
import { pathToFileURL } from "node:url";

const arithmetic = {
  add: [3, 1],
  mul: [5, 1],
  addmod: [8, 2],
  mulmod: [8, 2],
};

export function account(counts) {
  let arithmeticGas = 0;
  let consumedSlots = 0;
  for (const [op, count] of Object.entries(counts)) {
    assert(Number.isSafeInteger(count) && count >= 0, `invalid count: ${op}`);
    if (["push", "dup", "swap"].includes(op)) continue;
    assert(Object.hasOwn(arithmetic, op), `unsupported opcode: ${op}`);
    arithmeticGas += arithmetic[op][0] * count;
    consumedSlots += arithmetic[op][1] * count;
  }
  const supply = (counts.push ?? 0) + (counts.dup ?? 0);
  const swaps = 3 * (counts.swap ?? 0);
  const floor = arithmeticGas + 3 * consumedSlots;
  const gas = arithmeticGas + 3 * supply + swaps;
  return {
    arithmeticGas,
    consumedSlots,
    floor,
    gas,
    gap: gas - floor,
    swaps,
    surplusSupply: 3 * (supply - consumedSlots),
  };
}

function opcode(token) {
  if (token === "[PRIME]") return "push";
  if (/^0x[0-9a-f]+$/i.test(token)) {
    assert(BigInt(token) !== 0n, "PUSH0 is outside the three-gas supply model");
    return "push";
  }
  const stack = /^(dup|swap)([1-9]|1[0-6])$/.exec(token);
  if (stack) return stack[1];
  assert(Object.hasOwn(arithmetic, token), `unsupported opcode: ${token}`);
  return token;
}

export function trace(lines) {
  const segments = [];
  let current;
  for (const line of lines) {
    const text = line.trim();
    const heading =
      /^\/\/ (Initial linear layer|Round \d+ \((external|internal)\))$/.exec(
        text,
      );
    if (heading) {
      current = {
        name: heading[1],
        group: heading[2] ?? "initial",
        counts: {},
      };
      segments.push(current);
      continue;
    }
    const code = text.split("//", 1)[0].trim();
    if (!code) continue;
    assert(current, `opcode outside a round: ${code}`);
    for (const token of code.split(/\s+/)) {
      const op = opcode(token);
      current.counts[op] = (current.counts[op] ?? 0) + 1;
    }
  }
  return segments.map((segment) => ({
    ...segment,
    ...account(segment.counts),
  }));
}

function sumCounts(segments) {
  const counts = {};
  for (const segment of segments) {
    for (const [op, count] of Object.entries(segment.counts)) {
      counts[op] = (counts[op] ?? 0) + count;
    }
  }
  return counts;
}

async function main() {
  const widths = process.argv.slice(2).map(Number);
  if (widths.length === 0) widths.push(2, 3, 4);
  assert(
    widths.every((t) => [2, 3, 4].includes(t)),
    "supported widths: 2, 3, 4",
  );
  const { assertKnown } =
    await import("../../generator/round-constants/assert-known.ts");
  const { generateParams } =
    await import("../../generator/round-constants/round-constants.ts");
  const { testInputs } = await import("../../generator/shared/vectors.ts");
  const { FORKS } = await import("../../generator/huff/fork.ts");
  const { buildBest, describeOptions } =
    await import("../../generator/huff/schedule.ts");
  const { entryBytes, overhead, memoryGas } =
    await import("../../generator/huff/render.ts");
  assertKnown();
  const fork = FORKS.osaka;
  const rows = [];
  for (const t of widths) {
    const params = generateParams(t);
    const best = buildBest(
      params,
      testInputs(t),
      fork.codeSize - entryBytes(fork, t),
      fork,
    );
    assert(best, `no Osaka schedule for t=${t}`);
    const built = best.result;
    const segments = trace(built.lines);
    assert.equal(segments.length, 1 + params.roundsF + params.roundsP);
    const counts = sumCounts(segments);
    const core = account(counts);
    assert.equal(core.gas, built.gas);
    assert.equal(
      segments.reduce((sum, segment) => sum + segment.gas, 0),
      built.gas,
    );
    const o = overhead(fork, t, built.inputSlots, built.stateInMemory, false);
    const wrapper =
      o.entryGas + o.tailGas + memoryGas(Math.max(built.memory, 32 * t));
    const expected = {
      initial: 1,
      external: params.roundsF,
      internal: params.roundsP,
    };
    const groups = Object.entries(expected).map(([name, count]) => {
      const selected = segments.filter((segment) => segment.group === name);
      assert.equal(selected.length, count, `${name} segment count`);
      return { name, count, ...account(sumCounts(selected)) };
    });
    rows.push({
      t,
      options: describeOptions(best.opts),
      counts,
      core,
      wrapper,
      call: core.gas + wrapper,
      sameWrapperFloor: core.floor + wrapper,
      groups,
      segments,
    });
  }
  console.log(JSON.stringify(rows, null, 2));
}

if (
  process.argv[1] &&
  pathToFileURL(process.argv[1]).href === import.meta.url
) {
  await main();
}
