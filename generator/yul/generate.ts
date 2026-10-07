// Generates the Poseidon2 BN254 Yul libraries for a state width t.
//
//   node generator/yul/generate.ts [t ...]      (default: 4)
//
// Parameters are derived like the HorizenLabs sage script (../params.ts),
// the straight-line Yul is simulated with exact bounds and checked against
// the BigInt reference permutation before anything is written (schedule.ts).
// t = 4 keeps the hash_1 / hash_2 / hash_3 / poseidon2_core library in
// src/bn254/yul/LibPoseidon2Yul.sol, other widths get an in-place
// permute(uint256[t] memory) library in src/bn254/yul/t<t>/ and a Foundry
// test.

import { mkdirSync, writeFileSync } from "fs";
import { generateParams } from "../params.ts";
import { permutation } from "../reference.ts";
import { testInputs } from "../vectors.ts";
import { buildPermutation, type Layout } from "./schedule.ts";
import {
  libraryName,
  renderArrayLibrary,
  renderForgeTest,
  renderHashLibrary,
  type Vector,
} from "./render.ts";

// Per-width placement, tuned against solc 0.8.30 (legacy pipeline, no
// via-IR): locals up to the DUP16 / SWAP16 reach, diag constants moved to
// memory only as far as the 24,576 byte code size of a contract using the
// library requires. From t = 16 the permutation alone exceeds that size, so
// those widths are generated for experiments only (their tests need
// FOUNDRY_CODE_SIZE_LIMIT raised and have no Huff permutation to fuzz
// against).
function layoutFor(t: number): Layout {
  if (t <= 4) {
    return { stackElements: t, diagInMemory: 0, m4Temps: 4, ssa: true };
  }
  if (t === 8) {
    return { stackElements: 8, diagInMemory: 2, m4Temps: 4, ssa: false };
  }
  if (t === 12) {
    return { stackElements: 12, diagInMemory: 10, m4Temps: 2, ssa: false };
  }
  return { stackElements: 11, diagInMemory: t, m4Temps: 2, ssa: false };
}

function generate(t: number) {
  const params = generateParams(t);
  const inputs = testInputs(t);
  const layout = layoutFor(t);

  if (t === 4) {
    const result = buildPermutation(
      params,
      inputs,
      layout,
      { kind: "hash" },
      3,
    );
    const path = "src/bn254/yul/LibPoseidon2Yul.sol";
    writeFileSync(path, renderHashLibrary(result));
    console.log(`t=4 Rf=${params.roundsF} Rp=${params.roundsP}: wrote ${path}`);
    return;
  }

  const result = buildPermutation(params, inputs, layout, { kind: "array" }, 3);
  const dir = `src/bn254/yul/t${t}`;
  mkdirSync(dir, { recursive: true });
  const lib = `${dir}/${libraryName(t)}.sol`;
  writeFileSync(lib, renderArrayLibrary(params, layout, result));
  const vectors: Vector[] = inputs.map((input) => ({
    input,
    output: permutation(params, input),
  }));
  const test = `test/Poseidon2YulT${t}.t.sol`;
  writeFileSync(test, renderForgeTest(params, vectors, t <= 12));
  console.log(
    `t=${t} Rf=${params.roundsF} Rp=${params.roundsP}: ${layout.stackElements} locals, ` +
      `${layout.diagInMemory} diag constants in memory, wrote ${lib}, ${test}`,
  );
  if (t > 12) {
    console.log(
      `  t=${t} exceeds the 24,576 byte code size limit; run its test with FOUNDRY_CODE_SIZE_LIMIT=100000`,
    );
  }
}

const widths = process.argv.slice(2).map(Number);
for (const t of widths.length ? widths : [4]) {
  if (!Number.isInteger(t) || t < 2) throw new Error(`invalid t: ${t}`);
  generate(t);
}
