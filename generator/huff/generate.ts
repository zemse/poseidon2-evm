// Generates the Poseidon2 BN254 Huff permutation for a state width t.
//
//   node generator/huff/generate.ts [--hardfork <name>] [t ...]   (default: 4)
//
// Parameters are derived like the HorizenLabs sage script (../round-constants/round-constants.ts),
// the stack schedule is simulated and checked against the BigInt reference
// permutation before anything is written (schedule.ts). The hardfork
// (fork.ts, default amsterdam) decides the opcodes the schedule may use and
// the code size. Every width gets src/bn254/huff/t<t>/Permutation.huff,
// and every width but t = 4 (whose hash entry t4/Poseidon2.huff is
// hand-written) an entry contract and a Foundry test; a fork other than the
// default gets src/bn254/huff/<fork>/t<t>/ and test/<fork>/. A permutation
// over the fork's code size is split into parts (split.ts), Part0.huff being
// the contract to call.

import { existsSync, mkdirSync, rmSync, writeFileSync } from "fs";
import { assertKnown } from "../round-constants/assert-known.ts";
import { generateParams } from "../round-constants/round-constants.ts";
import { permutation } from "../shared/reference.ts";
import { testInputs } from "../shared/vectors.ts";
import { DEFAULT_HARDFORK, fork as forkOf, type Fork } from "./fork.ts";
import {
  buildBest,
  describeOptions,
  type BuildOptions,
  type BuildResult,
} from "./schedule.ts";
import { splitPermutation } from "./split.ts";
import {
  entryBytes,
  huffDir,
  memoryGas,
  renderDeployParts,
  renderEip8024,
  renderEntry,
  renderForgeTest,
  renderPart,
  renderPermutation,
  renderZero,
  testDir,
  type Vector,
} from "./render.ts";

// entry contract (calldata loads, stores, return) plus Utils.huff constants
const ENTRY_OVERHEAD = 12 * 12 + 64;

function describe(result: BuildResult, opts: BuildOptions): string {
  const e = result.emitter;
  const shadow =
    e.stores + e.loads > 0 ? `, ${e.stores} shadowed, ${e.loads} loads` : "";
  return (
    `${result.gas} gas, ${result.bytes} bytes, depth ${result.maxDepth}, ` +
    `dup ${result.maxDup}, ${result.swaps} swaps, ${result.pops} pops${shadow}, ` +
    `options: ${describeOptions(opts)}`
  );
}

function generate(t: number, fork: Fork) {
  const params = generateParams(t);
  const inputs = testInputs(t);
  const legacy = fork.name === DEFAULT_HARDFORK;
  const overhead = legacy && t === 4 ? ENTRY_OVERHEAD : entryBytes(fork, t);
  const dir = `${huffDir(fork)}/t${t}`;
  const utilsPath = legacy ? "../Utils.huff" : "../../Utils.huff";
  const vectors: Vector[] = inputs.map((input) => ({
    input,
    output: permutation(params, input),
  }));
  const tests = testDir(fork);
  const testPath = `${tests}/Poseidon2T${t}.t.sol`;
  const label = `t=${t} Rf=${params.roundsF} Rp=${params.roundsP} on ${fork.name}`;

  const best = buildBest(params, inputs, fork.codeSize - overhead, fork);
  if (best) {
    const { result, opts } = best;
    console.log(`${label}: ${describe(result, opts)}`);
    if (t === 4 && legacy) {
      // t4/Poseidon2.huff is the hand-written hash_1 / hash_2 / hash_3 entry
      const path = `${dir}/Permutation.huff`;
      writeForkFiles(fork);
      writeFileSync(
        path,
        renderPermutation(params, result, opts, utilsPath, fork),
      );
      console.log(`  wrote ${path}`);
      return;
    }
    mkdirSync(dir, { recursive: true });
    writeForkFiles(fork);
    if (existsSync(`${dir}/DeployParts.sol`)) rmSync(`${dir}/DeployParts.sol`);
    writeFileSync(
      `${dir}/Permutation.huff`,
      renderPermutation(params, result, opts, utilsPath, fork),
    );
    writeFileSync(`${dir}/Poseidon2.huff`, renderEntry(params, fork, result));
    mkdirSync(tests, { recursive: true });
    writeFileSync(testPath, renderForgeTest(params, vectors, fork));
    const bytes =
      result.bytes +
      entryBytes(fork, t, result.inputSlots, result.stateInMemory);
    console.log(
      `  wrote ${dir}/Permutation.huff, ${dir}/Poseidon2.huff, ${testPath} ` +
        `(${bytes} runtime bytes)`,
    );
    return;
  }

  // over the code size: split at step boundaries
  const parts = splitPermutation(params, inputs, fork);
  console.log(`${label}: ${parts.length} parts (code size ${fork.codeSize})`);
  mkdirSync(dir, { recursive: true });
  writeForkFiles(fork);
  let total = 0;
  parts.forEach(({ result, opts, overhead: o }, i) => {
    const { from, to } = result.range;
    const bytes = result.bytes + o.bytes;
    const memory = memoryGas(Math.max(result.memory, 32 * t + 32));
    const gas = o.entryGas + result.gas + o.tailGas + memory;
    total += gas;
    console.log(
      `  part ${i}: steps ${from}..${to - 1}, ${bytes} bytes, ${gas} gas ` +
        `(entry ${o.entryGas}, tail ${o.tailGas}, memory ${memory}): ` +
        describe(result, opts),
    );
    writeFileSync(
      `${dir}/Part${i}.huff`,
      renderPart(params, result, opts, utilsPath, fork, i, parts.length),
    );
  });
  writeFileSync(`${dir}/DeployParts.sol`, renderDeployParts());
  // parts of an earlier, longer split
  for (let i = parts.length; existsSync(`${dir}/Part${i}.huff`); i++) {
    rmSync(`${dir}/Part${i}.huff`);
  }
  mkdirSync(tests, { recursive: true });
  writeFileSync(testPath, renderForgeTest(params, vectors, fork, parts.length));
  console.log(
    `  ${total} gas per call with ${parts.length - 1} cold hops ` +
      `(${fork.coldAccount} each; warm ${fork.warmAccount}), ` +
      `wrote ${dir}/Part0..${parts.length - 1}.huff, ${testPath}`,
  );
}

// the opcode macros a fork needs next to its width directories
function writeForkFiles(fork: Fork) {
  if (fork.reach > 16) {
    writeFileSync(`${huffDir(fork)}/Eip8024.huff`, renderEip8024(fork.reach));
  }
  if (!fork.push0) writeFileSync(`${huffDir(fork)}/Zero.huff`, renderZero());
}

const args = process.argv.slice(2);
let fork = forkOf(DEFAULT_HARDFORK);
const widths: number[] = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === "--hardfork") {
    fork = forkOf(args[++i] ?? "");
  } else {
    widths.push(Number(args[i]));
  }
}
// the parameter derivation must reproduce the known t = 3 / t = 4 values
assertKnown();
for (const t of widths.length ? widths : [4]) {
  if (!Number.isInteger(t) || t < 2) throw new Error(`invalid t: ${t}`);
  generate(t, fork);
}
