// Known values from sources independent of params.ts and reference.ts. Both
// generators run every assertion here before building any width, so a change
// to the parameter derivation or the reference permutation that no longer
// reproduces them stops the generation. Every value outside this repository is
// pinned to a commit permalink: the Poseidon2 paper round-number table, the
// HorizenLabs t = 3 instance, Barretenberg t = 4 (constants.ts, its KAT and
// the sponge vectors in test/Poseidon2.t.sol), TACEO KATs for t = 2, 4, 8, 12,
// 16 and gnark-crypto constants for t = 8, 12, 16. Nothing pins t = 20, 24 or
// 28 beyond the paper's round numbers for 20 and 24.

import { PRIME, hex, mod } from "./field.ts";
import { calcRoundNumbers, generateParams } from "./params.ts";
import { hashSponge, permutation } from "./reference.ts";
import { internal_matrix_diagonal, round_constant } from "../constants.ts";

const HORIZEN =
  "https://github.com/HorizenLabs/poseidon2/blob/bb476b9ca38198cf5092487283c8b8c5d4317c4e/plain_implementations/src/poseidon2";
const BARRETENBERG =
  "https://github.com/AztecProtocol/aztec-packages/blob/8c7eb07b84eda9bcb3951fbacaa3529f6a726ae6/barretenberg/cpp/src/barretenberg/crypto/poseidon2/poseidon2_params.hpp";
const TACEO_CO_SNARKS =
  "https://github.com/TaceoLabs/co-snarks/blob/f6c5a16dff0c5978496f3c2511115c9b8654e7d0/mpc-core/src/gadgets/poseidon2/poseidon2_permutation.rs";
const TACEO_NOIR =
  "https://github.com/TaceoLabs/noir-poseidon/blob/ecb23c8476baba7ab7a16800ca25dd60e4832895/poseidon2/src/bn254/permutation.nr";
const GNARK =
  "https://github.com/Consensys-Incorporated/gnark-crypto/blob/a3a3ae54638a1201fa818d7d722ee57b1e1631f2/ecc/bn254/fr/poseidon2/poseidon2_constants.go";

function assert(name: string, ok: boolean, source: string) {
  if (!ok) {
    throw new Error(`${name} does not match the known value (${source})`);
  }
}

// permutation of [0, 1, ..., t - 1], or of the given inputs reduced mod PRIME
function kat(t: number, inputs?: bigint[]): string[] {
  const state = inputs ?? Array.from({ length: t }, (_, i) => BigInt(i));
  return permutation(
    generateParams(t),
    state.map((x) => mod(x, PRIME)),
  ).map(hex);
}

// Poseidon2 paper (https://eprint.iacr.org/2023/323), table for 254-bit
// primes with alpha = 5
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
      "https://eprint.iacr.org/2023/323",
    );
  }
}

// HorizenLabs t = 3 instance
export function assertKnownT3() {
  const p = generateParams(3);
  assert(
    "t=3 internal diag [1, 1, 2]",
    p.internalDiagMinusOne.join() === "1,1,2",
    `${HORIZEN}/poseidon2_instance_bn256.rs#L11-L15`,
  );
  assert(
    "t=3 round constant [0][0]",
    hex(p.roundConstants[0][0]) ===
      "0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816",
    `${HORIZEN}/poseidon2_instance_bn256.rs#L33`,
  );
  assert(
    "t=3 round constant [63][2]",
    hex(p.roundConstants[63][2]) ===
      "0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6",
    `${HORIZEN}/poseidon2_instance_bn256.rs#L287`,
  );
  assert(
    "t=3 HorizenLabs KAT",
    kat(3).join() ===
      [
        "0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033",
        "0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570",
        "0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8",
      ].join(),
    `${HORIZEN}/poseidon2.rs#L493-L502`,
  );
}

// Barretenberg t = 4: constants.ts, the KAT and the sponge vectors
export function assertKnownT4() {
  const p = generateParams(4);
  assert(
    "t=4 round constants",
    p.roundConstants.length === round_constant.length &&
      p.roundConstants.every((rc, r) =>
        rc.every((c, i) => hex(c) === round_constant[r][i]),
      ),
    `constants.ts, from ${BARRETENBERG}`,
  );
  assert(
    "t=4 internal diag",
    p.internalDiagMinusOne.every(
      (d, i) => hex(d) === internal_matrix_diagonal[i],
    ),
    `constants.ts, from ${BARRETENBERG}`,
  );
  assert(
    "t=4 Barretenberg KAT",
    kat(4).join() ===
      [
        "0x01bd538c2ee014ed5141b29e9ae240bf8db3fe5b9a38629a9647cf8d76c01737",
        "0x239b62e7db98aa3a2a8f6a0d2fa1709e7a35959aa6c7034814d9daa90cbac662",
        "0x04cbb44c61d928ed06808456bf758cbf0c18d1e15a7b6dbc8245fa7515d5e3cb",
        "0x2e11c5cff2a22c64d01304b778d78f6998eff1ab73163a35603f54794c30847a",
      ].join(),
    `${BARRETENBERG}#L447-L458`,
  );
  assert(
    "t=4 hash_1(0)",
    hex(hashSponge(p, [0n])) ===
      "0x2710144414c3a5f2354f4c08d52ed655b9fe253b4bf12cb9ad3de693d9b1db11",
    "test/Poseidon2.t.sol",
  );
  assert(
    "t=4 hash_2(0, 0)",
    hex(hashSponge(p, [0n, 0n])) ===
      "0x0b63a53787021a4a962a452c2921b3663aff1ffd8d5510540f8e659e782956f1",
    "test/Poseidon2.t.sol",
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
    "test/Poseidon2.t.sol",
  );
}

// TACEO KATs: co-snarks for t = 2, 4 (an input above PRIME) and 8,
// noir-poseidon for t = 12 and 16
export function assertKnownTaceo() {
  assert(
    "t=2 TACEO KAT",
    kat(2).join() ===
      [
        "0x1d01e56f49579cec72319e145f06f6177f6c5253206e78c2689781452a31878b",
        "0x0d189ec589c41b8cffa88cfc523618a055abe8192c70f75aa72fc514560f6c61",
      ].join(),
    `${TACEO_CO_SNARKS}#L334-L348`,
  );
  const x =
    0x9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789n;
  assert(
    "t=4 TACEO KAT 2",
    kat(4, [x, x, x, x]).join() ===
      [
        "0x2bf1eaf87f7d27e8dc4056e9af975985bccc89077a21891d6c7b6ccce0631f95",
        "0x0c01fa1b8d0748becafbe452c0cb0231c38224ea824554c9362518eebdd5701f",
        "0x018555a8eb50cf07f64b019ebaf3af3c925c93e631f3ecd455db07bbb52bbdd3",
        "0x0cbea457c91c22c6c31fd89afd2541efc2edf31736b9f721e823b2165c90fd41",
      ].join(),
    `${TACEO_CO_SNARKS}#L410-L451`,
  );
  assert(
    "t=8 TACEO KAT",
    kat(8).join() ===
      [
        "0x1d1a50bcde871247856df135d56a4ca61af575f1140ed9b1503c77528cf345df",
        "0x2d3943cf476ed49fd8a636660d8a76c83b55f07d06bc082005ad7eb1a21791c5",
        "0x2fcda2dd846fadfde8104b1d05175dcf3cf8bd698ed8ea3ad2fbcf9c06e00310",
        "0x28811ac7e0829171f9d3d81f1c0ff8f34b360d407a16b331a1cb6b5d992de094",
        "0x2c07c1817cfccb67c1297935514885c07abad5a0e15477f6c076c0b0fb1ad6f3",
        "0x1b6114397199bc44e37437dd3ba1754dff007d3315bfcdcdc14ec27d02452f52",
        "0x1431250baf36fb61a07618caee4dd2f500da339a05c553e8f529a3349e617aa2",
        "0x0b19bfa00c8f1d505074130e7f8b49a8624b1905e280ceca5ba11099b081b265",
      ].join(),
    `${TACEO_CO_SNARKS}#L454-L500`,
  );
  assert(
    "t=12 TACEO KAT",
    kat(12).join() ===
      [
        "0x3014e0ec17029f7e4f5cfe8c7c54fc3df6a5f7539f6aa304b2f3c747a9105618",
        "0x2f90753e7aaf46c158cd12346da7dd37c3136353ec51525cabbaaf2b2350f9b2",
        "0x2e28bdc8b2c68b09da0cb653ee7e54eca909cf2ae010784554aa3e165b1a105f",
        "0x1d6a97ef87dbd3476a848af45beebe6b5d79cb047b37212e3e5839f1e80b397a",
        "0x24e23df24b19b75f44218a08d107709d35561bc1b982cfc317d54568cd496519",
        "0x185a08e623b85e797844191a1f184f7b8fc486253919eb20f1186a8331757018",
        "0x069ed78df853a105c8949dae5b4e81cbe370e8f6e25735a688aa8ff3df9659eb",
        "0x284395d79b64123211a4a59b81a90f9cfa8d8314dccde4cef22ec1e31431efd3",
        "0x0f24be5a8c95e3504ead0da9e792b77d7056f94461d69b04b33ea5d239f8e444",
        "0x022469ccfef0ce5a237518c38dec31fc2804e633b3b365c23a9f703ca31ef393",
        "0x1fcdcee218d5a0101bd233d572f184964854d445ca08d2bd6df6ceba5651e322",
        "0x0905469a776b7d5a3f18841edb90fa0d8c6de479c2789c042dafefb367ad1a2b",
      ].join(),
    `${TACEO_NOIR}#L741-L757`,
  );
  assert(
    "t=16 TACEO KAT",
    kat(16).join() ===
      [
        "0x0fc2e6b758f493969e1d860f9a44ee3bdffdf796f382aa4ffb16fa4e9bcc333f",
        "0x0c118155a0dfeca3f91faf14a350511228ac33743be91249c6e0b3a635a50de4",
        "0x1a02b3a6571f22bb6392322d3f9f5de145b4f00bdf483072ce6188c30ba0f83d",
        "0x26631df6b2522ecde57413cd680ed590ded356e1c680f865f45be8eb960d1e06",
        "0x250ac4dfed40dc37bac9abe46f7bff3a80481d52a157ac80a1e5d39a5ed60e18",
        "0x17160980d8e7d9cb31addaf294cf047768bffd9fe433e8903b4ed262ee913f5b",
        "0x1d708a9f0995c2e0cd2f55e5dc795126f7191a0eb934ac8172bf54e520361ff6",
        "0x20721a18915e96e37e12c9697427f34d6a366787ea94ea65565c36813a0d77a3",
        "0x08671a9e58105eed9ac673249dcf22f08f098e3c6eb28f9eaa55d67d755972d0",
        "0x01e879484303c6d057128fbcc3a4222c779a62d3666df65d4e0b64c8031d7cc4",
        "0x239e2ce87955ebe19aaad000b38725b729f51175ab7d688f15d997edf0e3b7fc",
        "0x06be612f42b3ebdbade3fe199338c9118eb6b5fb760bda96e45443f130a8b2de",
        "0x11b2c04b4eb9e4844e5ddbb19b56059a815ed5d69405ba51786961235d5f073c",
        "0x006da33e2d57616c0ffc855b48d225a1237c3d80fc7e6b6e73b74e162b85c8a8",
        "0x0ef50c2615882523c6c73a69b4371332a066b2dc4b9630f186db47e3bfca88c8",
        "0x0e2ceb1f8fde5f80be1f41bd239fabdc2f6133a6a98920a55c42891c3a925152",
      ].join(),
    `${TACEO_NOIR}#L1062-L1082`,
  );
}

// gnark-crypto constants: the first and last internal diag entry, the first
// round constant, the first constant of the first partial round and the last
// round constant, with the line of each in the gnark-crypto table
export function assertKnownGnark() {
  const known: Record<number, [string, number][]> = {
    8: [
      ["0x05bffb5e301d8c468c35e24eb2165b6b71725fb7ac9a48efe5ce041bdb05676d", 424],
      ["0x2dd221096053de389fae88e7caa5c43ab55e22aeb758ee130d1246c1dff47b53", 431],
      ["0x0dad22d08a6b8d81d4a5ffc34b9677a7c5254c85e953551f9eba9a0a97590c10", 435],
      ["0x0da23df12d0bf47bb92f15ee189386c20f552d0bc66ae492b92d69556b2fe75a", 475],
      ["0x28bfc4dc9594e9add687744b79f4feb979e2143d742d4e4d1d5bb64bb799a02a", 1082],
    ],
    12: [
      ["0x20bb1e98f40bfe80b8e2f2c885ea13a2ea1f146ff61218c31075ad79dd8f4ffa", 1090],
      ["0x08b593b39852f7ad095a03a3eee546c388e02896d460454c6f1887c8d1c82e37", 1101],
      ["0x0f43621f15c4af9c4e52180b3ab6fbc9cf57863dc34e6190232841eb8b085634", 1105],
      ["0x2fcd24c963827617cdce5a14014ea5af93e46190242697ea182ff72b0479d09e", 1161],
      ["0x11ea79fb35b1a82c8bb6a9e1a17cc058975d8953279f362fc4c64944ea6c0b3d", 2012],
    ],
    16: [
      ["0x269aaf7c0e0ae1a709c1b7cd137c366a3ef21c0ca7d9fb2b33b5a1ae235768e4", 2020],
      ["0x1ba0b493c987b9c1424ede9239ba100dc005e717aa71ca6d6a605561e379bdce", 2035],
      ["0x11a8c50ae2baf9f5e8b3c672c7326f002cdec557448fdfa263f0adfbaaceacff", 2039],
      ["0x0f1139934f4fb0ff2f4bd0b7d28544a1c8938de92dcf965e1a1781c86aa8e6c2", 2111],
      ["0x115107e62902f6facbd8a1caa2a2f67a15301e5c034cb99c764f6402ca331781", 3206],
    ],
  };
  for (const [width, values] of Object.entries(known)) {
    const t = Number(width);
    const p = generateParams(t);
    const rc = p.roundConstants;
    const actual: [string, bigint][] = [
      ["diag[0]", p.internalDiagMinusOne[0]],
      [`diag[${t - 1}]`, p.internalDiagMinusOne[t - 1]],
      ["rc[0][0]", rc[0][0]],
      [`rc[${p.roundsF / 2}][0]`, rc[p.roundsF / 2][0]],
      ["last rc", rc[rc.length - 1][t - 1]],
    ];
    actual.forEach(([name, value], i) =>
      assert(
        `t=${t} ${name}`,
        hex(value) === values[i][0],
        `${GNARK}#L${values[i][1]}`,
      ),
    );
  }
}

export function assertKnown() {
  assertKnownRounds();
  assertKnownT3();
  assertKnownT4();
  assertKnownTaceo();
  assertKnownGnark();
}
