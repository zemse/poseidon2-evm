// Native integration: run serially, with the same resource limits as cargo.
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import test from "node:test";
import { fileURLToPath } from "node:url";
import { entryCost, trace } from "./gas-floor.mjs";

const manifest = fileURLToPath(new URL("../Cargo.toml", import.meta.url));
const root = fileURLToPath(new URL("../../", import.meta.url));
function run(...args) {
  return execFileSync(
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
      ...args,
    ],
    {
      cwd: root,
      encoding: "utf8",
      maxBuffer: 1 << 28,
      stdio: ["ignore", "pipe", "inherit"],
    },
  );
}

test("selected entry accounting matches compiled small-state execution on three forks", () => {
  for (const hardfork of ["amsterdam", "osaka", "paris"]) {
    const schedules = JSON.parse(
      run("schedule", "--hardfork", hardfork, "2", "3"),
    );
    const execution = run("verify", "--hardfork", hardfork, "2", "3", "4", "8");
    const paris = hardfork === "paris";
    assert.deepEqual(
      schedules.map((built) => built.t),
      [2, 3],
    );
    for (const built of schedules) {
      const { t } = built;
      const entry = entryCost(built);
      assert.equal(built.entryKind, `t${t}-terminal`);
      assert.equal(
        built.permutation.gas + built.permutation.wrapper,
        entry.call + (t === 2 ? 3 : 6),
      );
      assert(
        !built.permutation.lines.some((line) =>
          /\b(msize|mstore|mload|codecopy)\b/.test(line),
        ),
      );
      if (t === 3 || hardfork === "osaka") {
        const segments = trace(built.permutation.lines);
        assert.equal(segments.length, 65);
        assert.equal(
          segments.reduce((sum, segment) => sum + segment.gas, 0),
          built.permutation.gas,
        );
        assert.equal(
          segments.filter((segment) => segment.group === "external").length,
          8,
        );
        assert.equal(
          segments.filter((segment) => segment.group === "internal").length,
          56,
        );
      }
      assert.deepEqual(entry.stores, t === 2 ? [0, 32] : [0, 32, 64]);
      assert.equal(entry.memory, 32 * t);
      assert.equal(entry.entryGas, (t === 2 ? 30 : 44) + (paris ? 1 : 0));
      assert.equal(entry.tailGas, paris ? 5 : 4);
      assert.equal(entry.memoryGas, 3 * t);
      const raw = new RegExp(
        `^t=${t} on ${hardfork}: verified (\\d+) calls, (\\d+) runtime bytes, call gas (\\d+) \\(model (\\d+), ([+-]\\d+)\\)$`,
        "m",
      ).exec(execution);
      assert(raw, execution);
      assert(Number(raw[1]) > 0);
      assert.equal(Number(raw[2]), entry.runtimeBytes);
      assert.equal(Number(raw[3]), entry.call);
      assert.equal(Number(raw[4]), entry.call);
      assert.equal(Number(raw[5]), 0);
      assert.equal(entry.call, (t === 2 ? 5909 : 7644) + (paris ? 2 : 0));
      const runtimeBytes =
        t === 2 ? (hardfork === "amsterdam" ? 4011 : 7421) : 6713;
      assert.equal(entry.runtimeBytes, runtimeBytes + (paris ? 2 : 0));
    }
    const t8 = hardfork === "amsterdam" ? 23568 : paris ? 24278 : 24217;
    assert.match(
      execution,
      new RegExp(
        `^t=8 on ${hardfork}: verified \\d+ calls, \\d+ runtime bytes, call gas ${t8} \\(model ${t8}, \\+0\\)$`,
        "m",
      ),
    );
    for (const [i, gas] of (paris
      ? [11884, 11891, 11964]
      : [11883, 11890, 11963]
    ).entries()) {
      assert(execution.includes(`hash_${i + 1} ${gas} (model ${gas}, +0)`));
    }
    const permutation = paris ? 12085 : 12083;
    assert(
      execution.includes(
        `permutation entry ${permutation} (model ${permutation}, +0)`,
      ),
    );
    console.log(execution.trim());
  }
});

test("gas-floor keeps canonical floors separate from selected entry costs", () => {
  const script = fileURLToPath(new URL("./gas-floor.mjs", import.meta.url));
  const rows = JSON.parse(
    execFileSync(process.execPath, [script, "2", "3", "4"], {
      cwd: root,
      encoding: "utf8",
    }),
  );
  assert.deepEqual(
    rows.map((row) => row.call),
    [5909, 7644, 12083],
  );
  assert.equal(rows[0].permutationCall, 5912);
  assert.equal(rows[1].permutationCall, 7650);
  assert.equal(rows[1].core.gas, 7578);
  for (const row of rows) {
    assert.equal(row.permutationCall, row.core.gas + row.wrapper);
    assert.equal(row.sameWrapperFloor, row.core.floor + row.wrapper);
    assert.equal(row.entry.call, row.call);
  }
});
