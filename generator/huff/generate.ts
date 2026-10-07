// Generates the Poseidon2 BN254 Huff permutation for a state width t.
//
//   node generator/huff/generate.ts [t ...]      (default: 4)
//
// Parameters are derived like the HorizenLabs sage script (../params.ts),
// the stack schedule is simulated and checked against the BigInt reference
// permutation before anything is written (schedule.ts). t = 4 goes to
// src/bn254/huff/Permutation.huff, other widths get their own directory with
// an entry contract and a Foundry test.

import { mkdirSync, writeFileSync } from "fs";
import { generateParams } from "../params.ts";
import { permutation } from "../reference.ts";
import { testInputs } from "../vectors.ts";
import { buildBest } from "./schedule.ts";
import {
  renderEntry,
  renderForgeTest,
  renderPermutation,
  type Vector,
} from "./render.ts";

const CODE_SIZE_LIMIT = 24576;
// entry contract (calldata loads, stores, return) plus Utils.huff constants
const ENTRY_OVERHEAD = 12 * 12 + 64;

function generate(t: number) {
  const params = generateParams(t);
  const inputs = testInputs(t);
  const { result, opts } = buildBest(
    params,
    inputs,
    CODE_SIZE_LIMIT - ENTRY_OVERHEAD,
  );
  const enabled = Object.entries(opts)
    .filter(([, v]) => v)
    .map(([k]) => k)
    .join(", ");
  console.log(
    `t=${t} Rf=${params.roundsF} Rp=${params.roundsP}: ${result.gas} gas, ` +
      `${result.bytes} bytes, depth ${result.maxDepth}, dup ${result.maxDup}, ` +
      `${result.swaps} swaps, ${result.pops} pops, options: ${enabled || "none"}`,
  );

  if (t === 4) {
    const path = "src/bn254/huff/Permutation.huff";
    writeFileSync(
      path,
      renderPermutation(params, result, opts, "./Utils.huff"),
    );
    console.log(`  wrote ${path}`);
    return;
  }
  const dir = `src/bn254/huff/t${t}`;
  mkdirSync(dir, { recursive: true });
  writeFileSync(
    `${dir}/Permutation.huff`,
    renderPermutation(params, result, opts, "../Utils.huff"),
  );
  writeFileSync(`${dir}/Poseidon2.huff`, renderEntry(params));
  const vectors: Vector[] = inputs.map((input) => ({
    input,
    output: permutation(params, input),
  }));
  writeFileSync(`test/Poseidon2T${t}.t.sol`, renderForgeTest(params, vectors));
  console.log(
    `  wrote ${dir}/Permutation.huff, ${dir}/Poseidon2.huff, test/Poseidon2T${t}.t.sol`,
  );
}

const widths = process.argv.slice(2).map(Number);
for (const t of widths.length ? widths : [4]) {
  if (!Number.isInteger(t) || t < 2) throw new Error(`invalid t: ${t}`);
  generate(t);
}
