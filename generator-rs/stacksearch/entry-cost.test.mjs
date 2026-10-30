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
    const [built] = JSON.parse(run("schedule", "--hardfork", hardfork, "2"));
    const entry = entryCost(built);
    assert.equal(built.entryKind, "t2-terminal");
    assert.equal(
      built.permutation.gas + built.permutation.wrapper,
      entry.call + 3,
    );
    assert(
      !built.permutation.lines.some((line) =>
        /\b(msize|mstore|mload)\b/.test(line),
      ),
    );
    if (hardfork === "osaka") {
      assert.equal(
        trace(built.permutation.lines).reduce(
          (sum, segment) => sum + segment.gas,
          0,
        ),
        built.permutation.gas,
      );
    }
    const execution = run("verify", "--hardfork", hardfork, "2", "3", "4", "8");
    const raw =
      /^t=2 on \w+: verified (\d+) calls, (\d+) runtime bytes, call gas (\d+) \(model (\d+), ([+-]\d+)\)$/m.exec(
        execution,
      );
    assert(raw, execution);
    assert(Number(raw[1]) > 0);
    assert.equal(Number(raw[2]), entry.runtimeBytes);
    assert.equal(Number(raw[3]), entry.call);
    assert.equal(Number(raw[4]), entry.call);
    assert.equal(Number(raw[5]), 0);
    const paris = hardfork === "paris";
    assert.equal(entry.call, paris ? 5911 : 5909);
    const expected = [
      [3, paris ? 7652 : 7650],
      [8, hardfork === "amsterdam" ? 23760 : paris ? 24278 : 24217],
    ];
    for (const [t, gas] of expected) {
      assert.match(
        execution,
        new RegExp(
          `^t=${t} on ${hardfork}: verified \\d+ calls, \\d+ runtime bytes, call gas ${gas} \\(model ${gas}, \\+0\\)$`,
          "m",
        ),
      );
    }
    for (const [i, gas] of (paris
      ? [11890, 11897, 11970]
      : [11889, 11896, 11969]
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
    [5909, 7650, 12083],
  );
  assert.equal(rows[0].permutationCall, 5912);
  for (const row of rows) {
    assert.equal(row.permutationCall, row.core.gas + row.wrapper);
    assert.equal(row.sameWrapperFloor, row.core.floor + row.wrapper);
    assert.equal(row.entry.call, row.call);
  }
});
