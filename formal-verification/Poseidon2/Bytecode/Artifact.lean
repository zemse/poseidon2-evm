/-!
# Exported runtime bytecode

The files next to this one are written by `poseidon2-gen lean-export` (generator-rs): one per
artifact, the runtime code as 32-byte big-endian words (the last one zero padded) with its
byte count and keccak256. Words keep the literals small for the kernel; `bytes` splits them.
The keccak256 is the `codehash` of an account holding the code, to compare with
`eth_getCodeHash` / `keccak256(eth_getCode)` of a deployment; the kernel does not recompute it.
-/

namespace Poseidon2.Bytecode

/-- How the contract is called; see `Spec/Interface.lean`. -/
inductive Kind where
  /-- `huffPerm` -/
  | huffPerm
  /-- `huffHash` -/
  | huffHash
  /-- part `i` of `n` of a split Huff permutation (Osaka); no artifact at this commit -/
  | huffPart (i n : Nat)
  /-- `yulHash` -/
  | yulHash
  /-- `yulPerm` -/
  | yulPerm
  /-- `hashV2`: the deployed v2 Huff t = 4 contract -/
  | hashV2
  deriving DecidableEq, Repr

/-- One exported runtime bytecode. -/
structure Artifact where
  name : String
  /-- state width -/
  t : Nat
  kind : Kind
  /-- byte count -/
  size : Nat
  keccak : Nat
  words : List Nat

/-- A word as 32 big-endian bytes. -/
def wordBytes (w : Nat) : List Nat :=
  [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8,
    7, 6, 5, 4, 3, 2, 1, 0].map fun i => (w >>> (8 * i)) % 256

/-- Words as bytes. -/
def wordsBytes : List Nat → List Nat
  | [] => []
  | w :: ws => wordBytes w ++ wordsBytes ws

/-- The code bytes. -/
def Artifact.bytes (a : Artifact) : List Nat :=
  (wordsBytes a.words).take a.size

/-- The code as EVMLean reads it. -/
def Artifact.code (a : Artifact) : ByteArray :=
  ⟨(a.bytes.map UInt8.ofNat).toArray⟩

end Poseidon2.Bytecode
