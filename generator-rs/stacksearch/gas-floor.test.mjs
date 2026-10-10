import assert from "node:assert/strict";
import test from "node:test";
import { account, trace } from "./gas-floor.mjs";

test("baseline opcode counts reproduce core gas and scoped floors", () => {
  const cases = [
    [
      {
        dup: 822,
        add: 208,
        swap: 19,
        push: 128,
        mulmod: 217,
        addmod: 59,
        mul: 55,
      },
      6014,
      5552,
    ],
    [
      { dup: 975, add: 345, swap: 148, push: 147, mulmod: 240, addmod: 116 },
      7693,
      7054,
    ],
    [
      { dup: 1339, add: 492, addmod: 78, swap: 204, push: 404, mulmod: 506 },
      11989,
      11128,
    ],
  ];
  for (const [counts, gas, floor] of cases) {
    const result = account(counts);
    assert.equal(result.gas, gas);
    assert.equal(result.floor, floor);
    assert.equal(result.gap, result.swaps + result.surplusSupply);
  }
});

test("trace follows round headings and ignores stack comments", () => {
  const segments = trace([
    "    // Initial linear layer",
    "    dup2 add // [s0', s1, P]",
    "",
    "    // Round 0 (external)",
    "    [PRIME] dup16 0x04 mulmod // [x0, P]",
    "    // Round 4 (internal)",
    "    swap1 dup1 add",
  ]);
  assert.deepEqual(
    segments.map((s) => s.group),
    ["initial", "external", "internal"],
  );
  assert.deepEqual(
    segments.map((s) => s.gas),
    [6, 17, 9],
  );
  assert.deepEqual(segments[1].counts, { push: 2, dup: 1, mulmod: 1 });
});

test("unsupported arithmetic cannot silently enter the floor model", () => {
  assert.throws(() => account({ mod: 1 }), /unsupported opcode/);
  assert.throws(() => account({ pop: 1 }), /unsupported opcode/);
  assert.throws(() => account({ add: -1 }), /invalid count/);
  assert.throws(() => account({ add: 1.5 }), /invalid count/);
});

test("trace rejects cheaper zero supply and non-Osaka stack operations", () => {
  for (const instruction of ["0x0", "0x00"]) {
    assert.throws(
      () => trace(["// Initial linear layer", instruction]),
      /PUSH0/,
    );
  }
  for (const instruction of ["dup17", "DUP17()", "mload", "sub"]) {
    assert.throws(
      () => trace(["// Initial linear layer", instruction]),
      /unsupported opcode/,
    );
  }
});

test("trace rejects opcodes not attributed to a segment", () => {
  assert.throws(() => trace(["dup1"]), /outside a round/);
});
