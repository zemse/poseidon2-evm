// Writes formal-verification/Poseidon2/Spec/Vectors.lean from the external test vectors.
import fs from "node:fs";
const outFile = process.argv[2];
const h = (n) => "0x" + BigInt(n).toString(16).padStart(64, "0");
const list = (xs) => "[" + xs.map(h).join(",\n    ") + "]";
const NOIR_P = "https://github.com/TaceoLabs/noir-poseidon/blob/ecb23c8476baba7ab7a16800ca25dd60e4832895/poseidon2/src/bn254/permutation.nr";
const noir = JSON.parse(fs.readFileSync("noir_vectors.json", "utf8"));

const commit = process.argv[3];
function wide() {
  let w = `/-! ## t = 20, 24, 28: NOT external

The outputs of the repository's own Rust reference permutation (\`generator-rs/src/reference.rs\`
at commit ${commit}) on the input [0, 1, .., t - 1], with the constants of \`Constants/T<t>.lean\`.
This shows only that the Lean definition and that reference agree; neither is independent of
the generated constants. -/

`;
  for (const line of fs.readFileSync("repo_kat.jsonl", "utf8").trim().split("\n")) {
    const k = JSON.parse(line);
    if (k.t < 20) continue;
    w += `theorem repo_t${k.t} :
    permutationWords T${k.t}.params (List.range ${k.t}) =
    ${list(k.out)} := by
  decide +kernel

`;
  }
  return w;
}
let s = `import Poseidon2.Spec.Sponge
import Poseidon2.Spec.Constants.T2
import Poseidon2.Spec.Constants.T3
import Poseidon2.Spec.Constants.T4
import Poseidon2.Spec.Constants.T8
import Poseidon2.Spec.Constants.T12
import Poseidon2.Spec.Constants.T16
import Poseidon2.Spec.Constants.T20
import Poseidon2.Spec.Constants.T24
import Poseidon2.Spec.Constants.T28

/-!
# Known-answer tests

Test vectors published by other implementations, checked against the spec by kernel
evaluation (\`decide +kernel\`; no \`native_decide\`). Inputs are 256-bit words read modulo
\`P\` (\`permutationWords\`, \`hashWords\`), outputs are canonical. Each theorem cites its source.
There are no external vectors for t = 20, 24, 28; the last section only checks agreement
with this repository's own reference implementation for those widths.

Generated from the cited files by a transcription script; do not edit by hand.
-/

namespace Poseidon2.Spec.Vectors

open Constants

/-! ## Permutation: TaceoLabs noir-poseidon, every vector of its tests for t = 2 .. 16 -/

`;
const idx = {};
for (const v of noir) {
  idx[v.t] = (idx[v.t] || 0) + 1;
  s += `/-- ${NOIR_P}#L${v.line} -/
theorem noir_t${v.t}_${idx[v.t]} :
    permutationWords T${v.t}.params
    ${list(v.input)} =
    ${list(v.output)} := by
  decide +kernel

`;
}

const x9a = "0x9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789";
s += `/-! ## Permutation: other sources -/

/-- HorizenLabs reference implementation, the BN254 t = 3 instance:
https://github.com/HorizenLabs/poseidon2/blob/bb476b9ca38198cf5092487283c8b8c5d4317c4e/plain_implementations/src/poseidon2/poseidon2.rs#L492-L504 -/
theorem horizen_t3 :
    permutationWords T3.params [0, 1, 2] =
    ${list(["0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033", "0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570", "0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8"])} := by
  decide +kernel

/-- Barretenberg \`TEST_VECTOR_INPUT\` / \`TEST_VECTOR_OUTPUT\`:
https://github.com/AztecProtocol/aztec-packages/blob/8c7eb07b84eda9bcb3951fbacaa3529f6a726ae6/barretenberg/cpp/src/barretenberg/crypto/poseidon2/poseidon2_params.hpp#L447-L458 -/
theorem barretenberg_t4 :
    permutationWords T4.params [0, 1, 2, 3] =
    ${list(["0x01bd538c2ee014ed5141b29e9ae240bf8db3fe5b9a38629a9647cf8d76c01737", "0x239b62e7db98aa3a2a8f6a0d2fa1709e7a35959aa6c7034814d9daa90cbac662", "0x04cbb44c61d928ed06808456bf758cbf0c18d1e15a7b6dbc8245fa7515d5e3cb", "0x2e11c5cff2a22c64d01304b778d78f6998eff1ab73163a35603f54794c30847a"])} := by
  decide +kernel

/-- TaceoLabs co-snarks \`posedon2_bn254_t4_kat2\`, every input word above \`P\`:
https://github.com/TaceoLabs/co-snarks/blob/be49d09364089e3d81670d9574da0c286beb400b/mpc-core/src/gadgets/poseidon2/poseidon2_permutation.rs#L409-L451 -/
theorem taceo_t4_above_p :
    permutationWords T4.params ${list([x9a, x9a, x9a, x9a])} =
    ${list(["0x2bf1eaf87f7d27e8dc4056e9af975985bccc89077a21891d6c7b6ccce0631f95", "0x0c01fa1b8d0748becafbe452c0cb0231c38224ea824554c9362518eebdd5701f", "0x018555a8eb50cf07f64b019ebaf3af3c925c93e631f3ecd455db07bbb52bbdd3", "0x0cbea457c91c22c6c31fd89afd2541efc2edf31736b9f721e823b2165c90fd41"])} := by
  decide +kernel

/-! ## Hash (t = 4 sponge) -/

/-- noir-lang/poseidon \`test_poseidon2_1\`:
https://github.com/noir-lang/poseidon/blob/e105cdd5c79c222860d53c5dfdb8fa8012b291c0/src/tests.nr#L72-L78 -/
theorem noir_hash_1 :
    hashWords T4.params [1000] =
    0x16433a80e26a23547e25d61dd95fd5793d1ca2dcd78ae64cd146d3b99a35fa7c := by
  decide +kernel

/-- noir-lang/poseidon \`test_poseidon2_2\`:
https://github.com/noir-lang/poseidon/blob/e105cdd5c79c222860d53c5dfdb8fa8012b291c0/src/tests.nr#L80-L86 -/
theorem noir_hash_2 :
    hashWords T4.params [1000, 2000] =
    0x118d5a5ecb25dafe99eb45cb196604a23d0b7c0cbd0c2be29e0787e59b7a1d8a := by
  decide +kernel

/-- noir-lang/poseidon \`test_poseidon2_3\`:
https://github.com/noir-lang/poseidon/blob/e105cdd5c79c222860d53c5dfdb8fa8012b291c0/src/tests.nr#L88-L94 -/
theorem noir_hash_3 :
    hashWords T4.params [1000, 2000, 3000] =
    0x0f1badcd0d52ced816fb6e6826fdf66ada038135d53cbb993f320ca6529223cd := by
  decide +kernel

/-- noir-lang/noir \`poseidon2_simplification\`, \`Poseidon2::hash([0], 1)\`:
https://github.com/noir-lang/noir/blob/5f17b1ef1872d49bbe0556e546358e9b93ef82c4/test_programs/compile_success_empty/poseidon2_simplification/src/main.nr -/
theorem noir_hash_1_zero :
    hashWords T4.params [0] =
    0x2710144414c3a5f2354f4c08d52ed655b9fe253b4bf12cb9ad3de693d9b1db11 := by
  decide +kernel

/-- Barretenberg \`HashConsistencyCheck\`: four inputs (two permutations), every word above \`P\`.
Checks the general \`sponge\`, of which \`hash\` is the one-permutation case:
https://github.com/AztecProtocol/aztec-packages/blob/8c7eb07b84eda9bcb3951fbacaa3529f6a726ae6/barretenberg/cpp/src/barretenberg/crypto/poseidon2/poseidon2.test.cpp#L32-L45 -/
theorem barretenberg_sponge_4 :
    (sponge T4.params (${list([x9a, x9a, x9a, x9a])}.map (fun w => (w : F)))).val =
    0x2f43a0f83b51a6f5fc839dea0ecec74947637802a579fa9841930a25a0bcec11 := by
  decide +kernel

${wide()}end Poseidon2.Spec.Vectors
`;
fs.writeFileSync(outFile, s);
console.log("ok", noir.length + 8, "theorems");
