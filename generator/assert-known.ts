// Known values from sources independent of params.ts and reference.ts. Both
// generators run every assertion here before building any width, so a change
// to the parameter derivation or the reference permutation that breaks t = 3
// or t = 4 stops the generation: constants.ts (Barretenberg t = 4), the
// Barretenberg t = 4 KAT, the sponge vectors in test/Poseidon2.t.sol, the
// HorizenLabs t = 3 instance and the Poseidon2 paper round-number table.

import { hex } from "./field.ts";
import { calcRoundNumbers, generateParams } from "./params.ts";
import { hashSponge, permutation } from "./reference.ts";
import { internal_matrix_diagonal, round_constant } from "../constants.ts";

function assert(name: string, ok: boolean) {
  if (!ok) throw new Error(`${name} does not match the known value`);
}

// Poseidon2 paper, table for 254-bit primes with alpha = 5
export function assertKnownRounds() {
  const paperRounds: Record<number, [number, number]> = {
    2: [8, 56],
    3: [8, 56],
    4: [8, 56],
    8: [8, 57],
    12: [8, 57],
    16: [8, 57],
    20: [8, 57],
    24: [8, 57],
  };
  for (const [t, [rf, rp]] of Object.entries(paperRounds)) {
    const r = calcRoundNumbers(Number(t), 5);
    assert(
      `t=${t} rounds (${r.roundsF}, ${r.roundsP})`,
      r.roundsF === rf && r.roundsP === rp,
    );
  }
}

// HorizenLabs t = 3 instance
export function assertKnownT3() {
  const p = generateParams(3);
  assert(
    "t=3 internal diag [1, 1, 2]",
    p.internalDiagMinusOne.join() === "1,1,2",
  );
  assert(
    "t=3 round constant [0][0] vs HorizenLabs RC3",
    hex(p.roundConstants[0][0]) ===
      "0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816",
  );
  assert(
    "t=3 round constant [63][2] vs HorizenLabs RC3",
    hex(p.roundConstants[63][2]) ===
      "0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6",
  );
  assert(
    "t=3 HorizenLabs KAT",
    permutation(p, [0n, 1n, 2n]).map(hex).join() ===
      [
        "0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033",
        "0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570",
        "0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8",
      ].join(),
  );
}

// Barretenberg t = 4: constants.ts, the KAT and the sponge vectors
export function assertKnownT4() {
  const p = generateParams(4);
  assert(
    "t=4 round constants vs constants.ts",
    p.roundConstants.length === round_constant.length &&
      p.roundConstants.every((rc, r) =>
        rc.every((c, i) => hex(c) === round_constant[r][i]),
      ),
  );
  assert(
    "t=4 internal diag vs constants.ts",
    p.internalDiagMinusOne.every(
      (d, i) => hex(d) === internal_matrix_diagonal[i],
    ),
  );
  assert(
    "t=4 Barretenberg KAT",
    permutation(p, [0n, 1n, 2n, 3n]).map(hex).join() ===
      [
        "0x01bd538c2ee014ed5141b29e9ae240bf8db3fe5b9a38629a9647cf8d76c01737",
        "0x239b62e7db98aa3a2a8f6a0d2fa1709e7a35959aa6c7034814d9daa90cbac662",
        "0x04cbb44c61d928ed06808456bf758cbf0c18d1e15a7b6dbc8245fa7515d5e3cb",
        "0x2e11c5cff2a22c64d01304b778d78f6998eff1ab73163a35603f54794c30847a",
      ].join(),
  );
  assert(
    "t=4 hash_1(0)",
    hex(hashSponge(p, [0n])) ===
      "0x2710144414c3a5f2354f4c08d52ed655b9fe253b4bf12cb9ad3de693d9b1db11",
  );
  assert(
    "t=4 hash_2(0, 0)",
    hex(hashSponge(p, [0n, 0n])) ===
      "0x0b63a53787021a4a962a452c2921b3663aff1ffd8d5510540f8e659e782956f1",
  );
  assert(
    "t=4 hash_3(x, y, z)",
    hex(
      hashSponge(p, [
        0x300ced31bf248a1a2d4ea02b5e9f302a9e34df3c2109d5f1046ee9f59de6f6f1n,
        0x2e6eb409ed7f41949cdb1925ac3ec68132b2443d873589a8afde4c027c3c0b68n,
        0x2f08443953fc54fb351e41a46da99bbec1d290dae2907d2baf5174ed28eee9ean,
      ]),
    ) === "0x27e4cf07e4bf24219f6a2da9be19cea601313a95f8a1360cf8f15d474826bf49",
  );
}

export function assertKnown() {
  assertKnownRounds();
  assertKnownT3();
  assertKnownT4();
}
