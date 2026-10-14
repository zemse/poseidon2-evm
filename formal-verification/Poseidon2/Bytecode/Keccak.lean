import Ethereum.SpongeHash.Keccak256
import Poseidon2.Bytecode.All

/-!
# The recorded keccak256 of each artifact

Each exported artifact records the keccak256 of its code (`Artifact.keccak`, written by
`poseidon2-gen lean-export`), which `scripts/check-deployed.sh` compares with the code of a
deployment. The `#guard` below recomputes it from `Artifact.code`, the bytes the theorems are
about, with EVMLean's pure Lean Keccak-256 (`Ethereum.KEC`), and fails the build if one differs.

This is an evaluation by Lean's interpreter at build time, not a kernel proof: `decide +kernel`
on `KEC` of 1,088 bytes (nine blocks) took 129 s and 36.7 GB, and the artifacts hold 0.7 MB.
-/

namespace Poseidon2.Bytecode

/-- 32 bytes as a big-endian number. -/
def beNat (b : ByteArray) : Nat :=
  b.data.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- The keccak256 of the artifact's code. -/
def Artifact.codeKeccak (a : Artifact) : Nat :=
  beNat (Ethereum.KEC a.code)

/-- The artifacts whose recorded keccak256 is not that of their code. -/
def keccakMismatches : List String :=
  (all.filter fun a => a.codeKeccak != a.keccak).map (·.name)

#guard keccakMismatches == []

end Poseidon2.Bytecode
