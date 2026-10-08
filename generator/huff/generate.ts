// Generates the Poseidon2 BN254 Huff permutation for a state width t.
//
//   node generator/huff/generate.ts [--amsterdam] [t ...]      (default: 4)
//
// Parameters are derived like the HorizenLabs sage script (../params.ts),
// the stack schedule is simulated and checked against the BigInt reference
// permutation before anything is written (schedule.ts). t = 4 goes to
// src/bn254/huff/Permutation.huff, other widths get their own directory with
// an entry contract and a Foundry test. With --amsterdam the schedule may use
// the EIP-8024 DUPN / SWAPN opcodes (stack reach 235, code size 65,536) and
// the output goes to src/bn254/huff/amsterdam/t<t>/ and test/amsterdam/.

import { mkdirSync, writeFileSync } from "fs";
import { generateParams } from "../params.ts";
import { permutation } from "../reference.ts";
import { testInputs } from "../vectors.ts";
import type { Target } from "./emitter.ts";
import { buildBest, describeOptions } from "./schedule.ts";
import {
  entryBytes,
  renderEip8024,
  renderEntry,
  renderForgeTest,
  renderPermutation,
  type Vector,
} from "./render.ts";

// EIP-170, raised by EIP-7954 on Amsterdam
const CODE_SIZE_LIMIT: Record<Target, number> = {
  legacy: 24576,
  amsterdam: 65536,
};
// entry contract (calldata loads, stores, return) plus Utils.huff constants
const ENTRY_OVERHEAD = 12 * 12 + 64;

function generate(t: number, target: Target) {
  const params = generateParams(t);
  const inputs = testInputs(t);
  const overhead = target === "legacy" ? ENTRY_OVERHEAD : entryBytes(t);
  const { result, opts } = buildBest(
    params,
    inputs,
    CODE_SIZE_LIMIT[target] - overhead,
    target,
  );
  console.log(
    `t=${t} Rf=${params.roundsF} Rp=${params.roundsP}: ${result.gas} gas, ` +
      `${result.bytes} bytes, depth ${result.maxDepth}, dup ${result.maxDup}, ` +
      `${result.swaps} swaps, ${result.pops} pops, options: ${describeOptions(opts)}`,
  );

  if (t === 4 && target === "legacy") {
    const path = "src/bn254/huff/Permutation.huff";
    writeFileSync(
      path,
      renderPermutation(params, result, opts, "./Utils.huff"),
    );
    console.log(`  wrote ${path}`);
    return;
  }
  const dir =
    target === "legacy"
      ? `src/bn254/huff/t${t}`
      : `src/bn254/huff/amsterdam/t${t}`;
  const utilsPath = target === "legacy" ? "../Utils.huff" : "../../Utils.huff";
  mkdirSync(dir, { recursive: true });
  if (target === "amsterdam") {
    writeFileSync("src/bn254/huff/amsterdam/Eip8024.huff", renderEip8024());
  }
  writeFileSync(
    `${dir}/Permutation.huff`,
    renderPermutation(params, result, opts, utilsPath, target),
  );
  writeFileSync(`${dir}/Poseidon2.huff`, renderEntry(params));
  const vectors: Vector[] = inputs.map((input) => ({
    input,
    output: permutation(params, input),
  }));
  const testDir = target === "legacy" ? "test" : "test/amsterdam";
  mkdirSync(testDir, { recursive: true });
  const testPath = `${testDir}/Poseidon2T${t}.t.sol`;
  writeFileSync(testPath, renderForgeTest(params, vectors, target));
  console.log(
    `  wrote ${dir}/Permutation.huff, ${dir}/Poseidon2.huff, ${testPath} ` +
      `(${result.bytes + entryBytes(t)} runtime bytes)`,
  );
}

const args = process.argv.slice(2);
const target: Target = args.includes("--amsterdam") ? "amsterdam" : "legacy";
const widths = args.filter((a) => a !== "--amsterdam").map(Number);
for (const t of widths.length ? widths : [4]) {
  if (!Number.isInteger(t) || t < 2) throw new Error(`invalid t: ${t}`);
  generate(t, target);
}
