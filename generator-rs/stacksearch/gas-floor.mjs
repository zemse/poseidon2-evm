// Osaka t = 2, 3, 4 opcode accounting and the fixed-mix stack-slot relaxation.
// Run with node gas-floor.mjs [2 3 4] (needs cargo).
// This reads the Rust generator output; compiled revm verification is a
// separate gate.

import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

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
      /^\/\/ (Initial linear layer|Round \d+ \((external|internal)(?:, streamed internal outputs)?\))$/.exec(
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

// This is execution accounting, not a stack-slot floor. Terminal stores
// consume outputs, so the arithmetic-only relaxation uses `permutation`.
export function entryCost(built) {
  if (built.entryKind === "permutation" || built.entryKind === undefined) {
    const core = account(sumCounts(trace(built.lines))).gas;
    assert.equal(core, built.gas);
    return {
      kind: "permutation",
      core,
      wrapper: built.wrapper,
      call: core + built.wrapper,
    };
  }
  assert.equal(built.entryKind, "t2-terminal", "unsupported entry kind");
  assert.equal(built.t, 2);
  assert(
    ["paris", "shanghai", "cancun", "prague", "osaka", "amsterdam"].includes(
      built.hardfork,
    ),
  );
  const push0 = built.hardfork !== "paris";
  const reach = built.hardfork === "amsterdam" ? 235 : 16;
  const tokens = built.lines.flatMap((line) =>
    line.split("//", 1)[0].trim().split(/\s+/).filter(Boolean),
  );
  let core = 0;
  let bytes = 0;
  let depth = 3; // the unchanged wrapper supplies [s0, s1, PRIME]
  let memory = 0;
  const stores = [];
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    if (token === "msize") {
      assert.equal(
        tokens[++i],
        "mstore",
        "MSIZE must be consumed by the next store",
      );
      assert(depth >= 1, "store stack underflow");
      assert(depth < 1024, "MSIZE stack overflow");
      assert(memory < 64, "only two sequential output stores are supported");
      stores.push(memory);
      memory += 32;
      depth -= 1; // MSIZE pushes one word; MSTORE consumes it and the value
      core += 2 + 3;
      bytes += 2;
    } else if (Object.hasOwn(arithmetic, token)) {
      const [gas, consumed] = arithmetic[token];
      assert(depth >= consumed + 1, "arithmetic stack underflow");
      depth -= consumed;
      core += gas;
      bytes += 1;
    } else if (token === "[PRIME]" || /^0x[0-9a-f]{1,64}$/i.test(token)) {
      const zero = token !== "[PRIME]" && BigInt(token) === 0n;
      core += zero && push0 ? 2 : 3;
      bytes +=
        token === "[PRIME]"
          ? 33
          : zero && push0
            ? 1
            : 1 + Math.max(1, Math.ceil(BigInt(token).toString(16).length / 2));
      depth += 1;
    } else {
      const ordinary = /^(dup|swap)([1-9]|1[0-6])$/.exec(token);
      const extended = token === "dupn" || token === "swapn";
      assert(ordinary || extended, `unsupported entry opcode: ${token}`);
      const op = ordinary ? ordinary[1] : token.slice(0, -1);
      const n = ordinary ? Number(ordinary[2]) : Number(tokens[++i]);
      assert(
        Number.isInteger(n) && n >= (extended ? 17 : 1) && n <= reach,
        "invalid stack reach",
      );
      assert(depth >= n + (op === "swap" ? 1 : 0), "stack operation underflow");
      if (op === "dup") depth += 1;
      core += 3;
      bytes += extended ? 2 : 1;
    }
    assert(depth <= 1024, "stack overflow");
  }
  assert.deepEqual(stores, [0, 32], "terminal outputs must occupy [0, 64)");
  const entryGas = 3 + 2 * (3 + 3 + 3 + 5) - (push0 ? 1 : 0);
  const tailGas = 2 + (push0 ? 2 : 3); // MSIZE, zero, RETURN; no second store pass
  const words = memory / 32;
  const memoryGas = 3 * words + Math.floor((words * words) / 512);
  const wrapper = entryGas + tailGas + memoryGas;
  const runtimeBytes = bytes + (push0 ? 42 : 43) + (push0 ? 3 : 4);
  assert.equal(core, built.gas, "entry core gas");
  assert.equal(entryGas, built.entryGas, "calldata wrapper gas");
  assert.equal(tailGas, built.tailGas, "return wrapper gas");
  assert.equal(memoryGas, built.memoryGas, "memory expansion gas");
  assert.equal(wrapper, built.wrapper, "entry wrapper gas");
  assert.equal(runtimeBytes, built.runtimeBytes, "entry runtime bytes");
  return {
    kind: built.entryKind,
    core,
    stores,
    memory,
    entryGas,
    tailGas,
    memoryGas,
    wrapper,
    runtimeBytes,
    call: core + wrapper,
  };
}

async function main() {
  const widths = process.argv.slice(2).map(Number);
  if (widths.length === 0) widths.push(2, 3, 4);
  assert(
    widths.every((t) => [2, 3, 4].includes(t)),
    "supported widths: 2, 3, 4",
  );
  // the schedules `poseidon2-gen huff --hardfork osaka` selects
  const manifest = fileURLToPath(new URL("../Cargo.toml", import.meta.url));
  const schedules = JSON.parse(
    execFileSync(
      "cargo",
      [
        "run",
        "--release",
        "--offline",
        "--locked",
        "--quiet",
        "--manifest-path",
        manifest,
        "--",
        "schedule",
        "--hardfork",
        "osaka",
        ...widths.map(String),
      ],
      {
        encoding: "utf8",
        maxBuffer: 1 << 28,
        stdio: ["ignore", "pipe", "inherit"],
      },
    ),
  );
  const rows = [];
  for (const built of schedules) {
    const { t } = built;
    const permutation = built.permutation ?? built;
    const entry = entryCost(built);
    const segments = trace(permutation.lines);
    assert.equal(segments.length, 1 + built.roundsF + built.roundsP);
    const counts = sumCounts(segments);
    const core = account(counts);
    assert.equal(core.gas, permutation.gas);
    assert.equal(
      segments.reduce((sum, segment) => sum + segment.gas, 0),
      permutation.gas,
    );
    const wrapper = permutation.wrapper;
    const expected = {
      initial: 1,
      external: built.roundsF,
      internal: built.roundsP,
    };
    const groups = Object.entries(expected).map(([name, count]) => {
      const selected = segments.filter((segment) => segment.group === name);
      assert.equal(selected.length, count, `${name} segment count`);
      return { name, count, ...account(sumCounts(selected)) };
    });
    rows.push({
      t,
      options: built.options,
      counts,
      coreScope: "public permutation with its own wrapper",
      core,
      wrapper,
      permutationCall: core.gas + wrapper,
      entry,
      call: entry.call,
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
