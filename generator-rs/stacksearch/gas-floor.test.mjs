import assert from "node:assert/strict";
import test from "node:test";
import { account, entryCost, trace } from "./gas-floor.mjs";

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

test("streamed external re-entry retains its own segment and opcode costs", () => {
  const segments = trace([
    "// Round 59 (internal)",
    "dup1 add",
    "// Round 60 (external, streamed internal outputs)",
    "dup2 dup1 mulmod",
  ]);
  assert.equal(segments.length, 2);
  assert.deepEqual(
    segments.map((s) => s.group),
    ["internal", "external"],
  );
  assert.deepEqual(
    segments.map((s) => s.gas),
    [6, 14],
  );
  assert.deepEqual(segments[1].counts, { dup: 2, mulmod: 1 });
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

// Short accounting fixtures, not permutation correctness oracles.
function terminal(hardfork = "osaka", t = 2) {
  const paris = hardfork === "paris";
  return {
    t,
    hardfork,
    entryKind: `t${t}-terminal`,
    gas: t === 2 ? 50 : 78,
    entryGas: (t === 2 ? 30 : 44) + (paris ? 1 : 0),
    tailGas: paris ? 5 : 4,
    memoryGas: t === 2 ? 6 : 9,
    wrapper: (t === 2 ? 40 : 57) + (paris ? 2 : 0),
    runtimeBytes: (t === 2 ? 91 : 104) + (paris ? 2 : 0),
    lines: [
      t === 2
        ? "[PRIME] swap1 dup1 dup4 add dup3 dup2 dup6 addmod msize mstore addmod msize mstore"
        : "dup1 dup4 dup4 add add [PRIME] dup1 dup3 dup6 addmod msize mstore dup1 dup3 dup7 addmod msize mstore swap2 addmod msize mstore",
    ],
  };
}

test("terminal accounting charges every output store and expansion exactly once", () => {
  for (const t of [2, 3]) {
    for (const name of ["amsterdam", "osaka", "paris"]) {
      const built = terminal(name, t);
      const entry = entryCost(built);
      assert.equal(
        entry.call,
        (t === 2 ? 90 : 135) + (name === "paris" ? 2 : 0),
      );
      assert.equal(entry.memoryGas, 3 * t);
      assert.equal(entry.memory, 32 * t);
      assert.deepEqual(entry.stores, t === 2 ? [0, 32] : [0, 32, 64]);
      assert.throws(
        () => trace(["// Initial linear layer", ...built.lines]),
        /unsupported opcode/,
      );
    }
  }
});

test("both terminal adapters reject unmodeled memory, wrong metadata and unsafe stacks", () => {
  for (const t of [2, 3]) {
    for (const hardfork of ["amsterdam", "osaka", "paris"]) {
      for (const instruction of [
        "mload",
        "mstore",
        "codecopy",
        "calldatacopy",
        "return",
        "jump",
        "dupn 236",
        "swapn 236",
        "dup17",
        "dupn",
        "dupn 0",
        "swapn 16",
      ]) {
        const built = terminal(hardfork, t);
        built.lines.unshift(instruction);
        assert.throws(() => entryCost(built));
      }
      for (const key of [
        "gas",
        "entryGas",
        "tailGas",
        "memoryGas",
        "wrapper",
        "runtimeBytes",
      ]) {
        const built = terminal(hardfork, t);
        built[key] += 1;
        assert.throws(() => entryCost(built));
      }
      for (const lines of [
        ["addmod addmod"],
        ["msize dup1 mstore"],
        ["msize mstore"],
        ["msize mstore ".repeat(t + 1)],
        ["dup1 ".repeat(1024 - (t + 1)) + "msize mstore"],
        ["dup1 ".repeat(1025 - (t + 1))],
        ["dup16"],
        ["swap16"],
      ])
        assert.throws(() => entryCost({ ...terminal(hardfork, t), lines }));
      for (const entryKind of [
        "unknown",
        `t${5 - t}-terminal`,
        "t4-terminal",
      ]) {
        assert.throws(() => entryCost({ ...terminal(hardfork, t), entryKind }));
      }
      for (const width of [0, 1, 4, 8, 2.5, "3"]) {
        assert.throws(() => entryCost({ ...terminal(hardfork, t), t: width }));
      }
      assert.throws(() =>
        entryCost({ ...terminal(hardfork, t), hardfork: "unknown" }),
      );
    }
  }
});
