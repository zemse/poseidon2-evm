import Poseidon2.Spec.Sponge
import Poseidon2.Spec.Constants.T4

/-!
# Contract interfaces: calldata in, returndata out

What each kind of contract returns for a call with calldata `cd` (a list of bytes) and call
value `v`, stated with `permutationWords` and `hashWords`. These are the right-hand sides of the
bytecode theorems. They describe the deployed behaviour for every calldata, including calldata
outside the ABI the contracts document, as read from the sources at this commit:

* `huffPerm` (`src/bn254/huff/t<t>/Poseidon2.huff`, every width but 4): `t` words read with
  `CALLDATALOAD` at `0, 32, .., 32·(t-1)` (zero past the end of the calldata), each modulo `P`;
  the `t` output words returned. No selector, any calldata size, any call value.
* `huffHash` (`src/bn254/huff/t4/Poseidon2.huff`, `IPoseidon2`): the 4-byte selector is not
  read; the arity comes from the calldata size alone: 1 below `0x44` bytes (including empty
  calldata), 2 at exactly `0x44`, 3 above. The words are read at `4, 0x24, 0x44`; one word,
  `hashWords`, is returned. Any call value.
* `yulHash` (`Poseidon2Yul_BN254`, `src/bn254/yul/Poseidon2Yul.sol`, a non-payable fallback):
  reverts with empty data on a non-zero call value; otherwise always reads the three words at
  `4, 0x24, 0x44` and puts `((cds - 4) >> 5) << 64` in the capacity element, computed on
  256-bit words (so `cds < 4` wraps), and returns element 0 of the permutation. On ABI calldata
  (`cds = 4 + 32·n`, `n = 1, 2, 3`) this is `hashWords` of the `n` words (`hash_entries_abi`
  checks both t = 4 entries against `hashWords` on four such calldatas; `yulCapacity_abi`).
* `hashV2`: the deployed v2 Huff t = 4 contract of `deployed-artifacts/bn254-huff/v2`, built
  from older sources: as `yulHash` but without the call value check, for calldata of at least 4
  bytes; below 4 bytes one fixed word that is not a Poseidon2 output (`hashV2Short`).
* `yulPerm` (the `Poseidon2YulT<t>` contracts of `test/Poseidon2YulT<t>.t.sol`, the Foundry
  wrappers that call `LibPoseidon2YulT<t>.permute` on a `uint256[t] memory` and return it):
  a Solidity external function `permute(uint256[t])`. Reverts with empty data when the calldata
  is shorter than 4 bytes, the selector is not `permute(uint256[t])`, the call value is not
  zero, or fewer than `32·t` bytes follow the selector; otherwise returns the `t` output words
  of the `t` words at `4, 0x24, ..`. The libraries are `internal`, so they only exist as bytes
  inside a contract; these wrappers are the contracts the repository already compiles and tests.

No artifact at this commit is split: every Osaka build fits one contract (at most 24,370 bytes).
Should one be split (`Part0`, .., exported with `Kind.huffPart`), its parts have no interface
here and no theorem.

Every input is a 256-bit word read modulo `P`, so `w` and `w + P` (and `w + 2P`, .., below `2^256`)
give the same output; a caller who needs distinct inputs to stay distinct must pass words below
`P`. `Abi.lean` relates the t = 4 hash entries to `hashWords` on all ABI calldata.
-/

namespace Poseidon2.Spec.Interface

/-- The 256-bit big-endian word at byte offset `off`, zero past the end (`CALLDATALOAD`). -/
def calldataWord (cd : List UInt8) (off : Nat) : Nat :=
  ((List.range 32).map fun i => (cd.getD (off + i) 0).toNat).foldl (fun acc b => acc * 256 + b) 0

/-- `n` consecutive words from byte offset `off`. -/
def calldataWords (cd : List UInt8) (off n : Nat) : List Nat :=
  (List.range n).map fun i => calldataWord cd (off + 32 * i)

/-- A word as 32 big-endian bytes (the word is taken modulo `2^256`). -/
def wordBytes (w : Nat) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat (w / 256 ^ (31 - i) % 256)

/-- Words as returndata. -/
def encodeWords (ws : List Nat) : List UInt8 :=
  ws.flatMap wordBytes

/-- How a call ends: returned data, or a revert with its data. -/
inductive Outcome where
  | ret (out : List UInt8)
  | revert (out : List UInt8)
  deriving DecidableEq, Repr

/-- The Huff permutation entry of width `c.t`. -/
def huffPerm (c : Params) (cd : List UInt8) : Outcome :=
  .ret (encodeWords (permutationWords c (calldataWords cd 0 c.t)))

/-- The arity the Huff t = 4 hash entry takes from the calldata size. -/
def huffArity (cds : Nat) : Nat :=
  if cds < 0x44 then 1 else if cds = 0x44 then 2 else 3

/-- The Huff t = 4 hash entry (`hash_1` / `hash_2` / `hash_3`, selector ignored). -/
def huffHash (c : Params) (cd : List UInt8) : Outcome :=
  .ret (encodeWords [hashWords c (calldataWords cd 4 (huffArity cd.length))])

/-- The capacity word `Poseidon2Yul_BN254` computes: `shl(64, shr(5, sub(calldatasize(), 4)))`
on 256-bit words. -/
def yulCapacity (cds : Nat) : Nat :=
  (cds + 2 ^ 256 - 4) % 2 ^ 256 / 32 * 2 ^ 64 % 2 ^ 256

/-- `Poseidon2Yul_BN254`: call value `v`. -/
def yulHash (c : Params) (cd : List UInt8) (v : Nat) : Outcome :=
  if v ≠ 0 then .revert [] else
  let ws := calldataWords cd 4 3 ++ [yulCapacity cd.length]
  .ret (encodeWords [(permutationWords c ws).headD 0])

/-- What the deployed v2 Huff t = 4 contract returns for calldata of 0 to 3 bytes, whatever the
bytes: it adds the capacity word, which wrapped below zero, to another word without reducing it
first. Not a Poseidon2 output (`yulHash` returns the permutation's for the same calldata). This
is the deployed bytecode's observed behaviour, taken from the checker's run of it and the same
as anvil returns; the theorems prove the bytecode returns it. -/
def hashV2Short : Nat := 0x0fcc8f62b28d181b60d780425f6a28111c2de73ab52e084c8c15975a470682d5

/-- The deployed v2 Huff t = 4 contract (`deployed-artifacts/bn254-huff/v2`, older than the
source at this commit): on calldata of at least 4 bytes `yulHash` without the call value check,
below 4 bytes `hashV2Short`. -/
def hashV2 (c : Params) (cd : List UInt8) : Outcome :=
  if cd.length < 4 then .ret (encodeWords [hashV2Short]) else
  let ws := calldataWords cd 4 3 ++ [yulCapacity cd.length]
  .ret (encodeWords [(permutationWords c ws).headD 0])

/-- The `Poseidon2YulT<t>` wrapper with function selector `sel` (`permute(uint256[t])`). -/
def yulPerm (c : Params) (sel : Nat) (cd : List UInt8) (v : Nat) : Outcome :=
  if cd.length < 4 then .revert []
  else if calldataWord cd 0 / 2 ^ 224 ≠ sel then .revert []
  else if v ≠ 0 then .revert []
  else if cd.length - 4 < 32 * c.t then .revert []
  else .ret (encodeWords (permutationWords c (calldataWords cd 4 c.t)))

/-- `bytes4(keccak256("permute(uint256[t])"))` for the Yul widths (solc's `methodIdentifiers`,
equal to `cast sig`). -/
def permuteSelector : Nat → Nat
  | 2 => 0x81be1a25
  | 3 => 0xa7982175
  | 8 => 0x6e85443c
  | 12 => 0x496f3b22
  | _ => 0

/-! On ABI calldata the entries are the documented functions. -/

theorem huffArity_abi (n : Nat) (h1 : 1 ≤ n) (h3 : n ≤ 3) : huffArity (4 + 32 * n) = n := by
  unfold huffArity; split_ifs <;> omega

theorem yulCapacity_abi (n : Nat) (h : n ≤ 3) : yulCapacity (4 + 32 * n) = n * 2 ^ 64 := by
  match n, h with
  | 0, _ | 1, _ | 2, _ | 3, _ => decide +kernel

theorem calldataWord_nil (off : Nat) : calldataWord [] off = 0 := by
  simp [calldataWord]

example : huffArity 0 = 1 ∧ huffArity 0x43 = 1 ∧ huffArity 0x44 = 2 ∧ huffArity 0x45 = 3 := by
  decide

/-- `cds = 3` wraps: `(3 - 4) mod 2^256 >> 5 << 64` keeps the low 192 bits of `2^251 - 1`. -/
example : yulCapacity 3 = (2 ^ 251 - 1) * 2 ^ 64 % 2 ^ 256 := by decide +kernel

/-- Agreement of the two t = 4 hash interfaces with `hashWords` on ABI calldata for `hash_1`,
`hash_2`, `hash_3` (inputs of the noir-lang/poseidon tests, selector bytes arbitrary), and on
an input above `P`. -/
theorem hash_entries_abi :
    let sel : List UInt8 := [0xde, 0xad, 0xbe, 0xef]
    let c := Constants.T4.params
    (List.all [[1000], [1000, 2000], [1000, 2000, 3000], [P + 5, 2 ^ 256 - 1]] fun ws =>
      huffHash c (sel ++ encodeWords ws) == .ret (encodeWords [hashWords c ws]) &&
      yulHash c (sel ++ encodeWords ws) 0 == .ret (encodeWords [hashWords c ws])) = true := by
  decide +kernel

end Poseidon2.Spec.Interface
