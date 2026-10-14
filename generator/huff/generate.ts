// Generates the Poseidon2 BN254 Huff permutation for a state width t.
//
//   node generator/huff/generate.ts [--hardfork <name>] [t ...]   (default: 4)
//
// Parameters are derived like the HorizenLabs sage script (../round-constants/round-constants.ts),
// the stack schedule is simulated and checked against the BigInt reference
// permutation before anything is written (schedule.ts). The hardfork
// (fork.ts, default amsterdam) decides the opcodes the schedule may use and
// the code size. Every width gets src/bn254/huff/t<t>/Permutation.huff,
// and every width but t = 4 an entry contract and a Foundry test; t = 4 gets
// the hash_1 / hash_2 / hash_3 entry t4/Poseidon2.huff instead (its own
// round 0 per arity and the rounds after it shared, tested by
// test/Poseidon2.t.sol); a fork other than the default gets
// src/bn254/huff/<fork>/t<t>/ and test/<fork>/ (t = 4 a generated test of
// the hash entry against the reference sponge). A permutation over the
// fork's code size is split into parts (split.ts), Part0.huff being the
// contract to call.

import { existsSync, mkdirSync, rmSync, writeFileSync } from "fs";
import { assertKnown } from "../round-constants/assert-known.ts";
import { generateParams } from "../round-constants/round-constants.ts";
import { permutation } from "../shared/reference.ts";
import { testInputs } from "../shared/vectors.ts";
import { DEFAULT_HARDFORK, fork as forkOf, type Fork } from "./fork.ts";
import {
  buildBest,
  buildHashPrologue,
  buildHashRounds,
  describeOptions,
  type BuildOptions,
  type BuildResult,
} from "./schedule.ts";
import { splitPermutation, type Part } from "./split.ts";
import {
  entryBytes,
  hashEntry,
  huffDir,
  memoryGas,
  overhead,
  renderDeployParts,
  renderEip8024,
  renderEntry,
  renderForgeTest,
  renderHashEntry,
  renderHashTest,
  renderPart,
  renderPermutation,
  renderZero,
  testDir,
  type Vector,
} from "./render.ts";

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

// gas of a call to an unsplit permutation's entry
function entryGas(fork: Fork, t: number, result: BuildResult): number {
  const o = overhead(
    fork,
    t,
    result.inputSlots,
    result.stateInMemory,
    false,
    false,
    result.memory,
  );
  const memory = memoryGas(Math.max(result.memory, 32 * t));
  return o.entryGas + result.gas + o.tailGas + memory;
}

// gas of a call to a part, with a cold hop to the next one
function partGas(part: Part, t: number): number {
  const { result, overhead: o } = part;
  const memory = memoryGas(Math.max(result.memory, 32 * t));
  return o.entryGas + result.gas + o.tailGas + memory;
}

function generate(t: number, fork: Fork) {
  const params = generateParams(t);
  const inputs = testInputs(t);
  const legacy = fork.name === DEFAULT_HARDFORK;
  const entryOverhead = entryBytes(fork, t);
  const dir = `${huffDir(fork)}/t${t}`;
  const utilsPath = legacy ? "../Utils.huff" : "../../Utils.huff";
  const vectors: Vector[] = inputs.map((input) => ({
    input,
    output: permutation(params, input),
  }));
  const tests = testDir(fork);
  const testPath = `${tests}/Poseidon2T${t}.t.sol`;
  const label = `t=${t} Rf=${params.roundsF} Rp=${params.roundsP} on ${fork.name}`;

  let best = buildBest(params, inputs, fork.codeSize - entryOverhead, fork);
  // the budget leaves room for the entry without shadow slots; with its own
  // slots it may not fit
  if (
    best &&
    best.result.bytes +
      entryBytes(
        fork,
        t,
        best.result.inputSlots,
        best.result.stateInMemory,
        best.result.memory,
      ) >
      fork.codeSize
  ) {
    best = undefined;
  }
  // a whole permutation that fits only through the sub-chains of a shorter
  // body pays for the size (the chains, the calls, diag constants in
  // memory), which a split may beat
  let parts: Part[] | undefined;
  if (best && best.opts.consumeGroup > 0) {
    parts = splitPermutation(params, inputs, fork);
    const single = entryGas(fork, t, best.result);
    const split = parts.reduce((sum, p) => sum + partGas(p, t), 0);
    if (split < single) {
      console.log(`${label}: ${describe(best.result, best.opts)}`);
      console.log(
        `  ${single} gas per call as one contract: the split below costs less`,
      );
      best = undefined;
    } else {
      parts = undefined;
    }
  }
  if (best) {
    const { result, opts } = best;
    console.log(`${label}: ${describe(result, opts)}`);
    if (t === 4) {
      // t4/Poseidon2.huff is the hash_1 / hash_2 / hash_3 entry: round 0
      // per arity, then the rounds after it shared, returning s0' alone
      mkdirSync(dir, { recursive: true });
      writeForkFiles(fork);
      writeFileSync(
        `${dir}/Permutation.huff`,
        renderPermutation(params, result, opts, utilsPath, fork),
      );
      const prologues = [1, 2, 3].map((n) =>
        buildHashPrologue(
          params,
          inputs.map((input) => input.slice(0, n)),
          fork,
        ),
      );
      const budget = fork.codeSize - hashEntry(fork, prologues).bytes;
      const rounds = buildHashRounds(params, prologues, budget, fork);
      const entry = hashEntry(fork, prologues, rounds.result);
      console.log(`  hash rounds: ${describe(rounds.result, rounds.opts)}`);
      writeFileSync(
        `${dir}/Poseidon2.huff`,
        renderHashEntry(params, fork, rounds, prologues, utilsPath),
      );
      // the default fork's test is the hand-written test/Poseidon2.t.sol
      let wrote = `${dir}/Permutation.huff, ${dir}/Poseidon2.huff`;
      if (!legacy) {
        mkdirSync(tests, { recursive: true });
        writeFileSync(testPath, renderHashTest(params, inputs, fork));
        wrote += `, ${testPath}`;
      }
      const gas = entry.gas.map((g, i) => `hash_${i + 1} ${g}`).join(", ");
      console.log(
        `  wrote ${wrote} (${gas} gas, ${entry.bytes} runtime bytes)`,
      );
      return;
    }
    mkdirSync(dir, { recursive: true });
    writeForkFiles(fork);
    // the parts of an earlier split
    if (existsSync(`${dir}/DeployParts.sol`)) rmSync(`${dir}/DeployParts.sol`);
    for (let i = 0; existsSync(`${dir}/Part${i}.huff`); i++) {
      rmSync(`${dir}/Part${i}.huff`);
    }
    writeFileSync(
      `${dir}/Permutation.huff`,
      renderPermutation(params, result, opts, utilsPath, fork),
    );
    writeFileSync(`${dir}/Poseidon2.huff`, renderEntry(params, fork, result));
    mkdirSync(tests, { recursive: true });
    writeFileSync(testPath, renderForgeTest(params, vectors, fork));
    const bytes =
      result.bytes +
      entryBytes(
        fork,
        t,
        result.inputSlots,
        result.stateInMemory,
        result.memory,
      );
    console.log(
      `  wrote ${dir}/Permutation.huff, ${dir}/Poseidon2.huff, ${testPath} ` +
        `(${bytes} runtime bytes)`,
    );
    return;
  }

  // over the code size: split at step boundaries
  parts ??= splitPermutation(params, inputs, fork);
  console.log(`${label}: ${parts.length} parts (code size ${fork.codeSize})`);
  mkdirSync(dir, { recursive: true });
  writeForkFiles(fork);
  let total = 0;
  parts.forEach((part, i) => {
    const { result, opts, overhead: o } = part;
    const { from, to } = result.range;
    const bytes = result.bytes + o.bytes;
    const memory = memoryGas(Math.max(result.memory, 32 * t));
    const gas = partGas(part, t);
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
