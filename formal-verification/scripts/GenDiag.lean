-- Writes DiagCheck.lean: for each width, every value of the diagonal draws 0 .. k (each value
-- with the LFSR state after it), in chunks of 96, and the theorems that check them.
-- Run from formal-verification/ after `lake build`:
--   lake env lean scripts/GenDiag.lean > Poseidon2/Spec/DiagCheck.lean
-- `#eval` only computes the certificate; the kernel checks it when DiagCheck.lean builds.
import Poseidon2.Spec.GrainCheck
import Poseidon2.Spec.Diagonal
open Poseidon2.Spec Poseidon2.Spec.Grain Poseidon2.Spec.GrainCheck Poseidon2.Spec.Constants

def valsAfter (n : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | m + 1, s => match bits n 0 s with
    | some (v, s') => (v, s') :: valsAfter n m s'
    | none => []

def hex (v : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 v)

partial def chunks (k : Nat) : List (Nat × Nat) → List (List (Nat × Nat))
  | [] => []
  | l => l.take k :: chunks k (l.drop k)

def header : String := "import Poseidon2.Spec.GrainCheck
import Poseidon2.Spec.Diagonal

/-!
# The internal diagonals are Grain LFSR draws

For every width `t ≥ 4`, `diagM1` of `Constants/T<t>.lean` is `r - 1` for the row `r` of `t`
values the HorizenLabs script draws (`F(grain_random_bits(254))`, read modulo `P`) as draw
number `k` after the round constants (`Grain.diagonal`), checked by kernel evaluation:
k = 4, 30, 6, 6, 42, 2, 34 for t = 4, 8, 12, 16, 20, 24, 28. The round-constant certificates
of `GrainCheck` are reused; the lists below hold every value of draws `0 .. k` with the LFSR
state after it (`Grain.valChain`), computed outside the kernel and checked by it, so they also
give the rows of the draws before `k` (`Grain.drawRow_of_vals`), which `MinpolyCheck` shows
fail the script's `check_minpoly_condition` while draw `k` passes it.

For t = 4 .. 16 the diagonals also match the external tables; for t = 20, 24, 28 this is
their only derivation. Written by `scripts/GenDiag.lean`.
-/

namespace Poseidon2.Spec.DiagCheck

open Constants GrainCheck
"

def gen (t rf rp k : Nat) (ss : List Nat) : IO Unit := do
  let s0 := ss.getLast!
  let ds := valsAfter 254 ((k + 1) * t) s0
  let cs := chunks 96 ds
  let p := IO.println
  p s!"/-! ### t = {t}: draws 0 .. {k}, {ds.length} values -/\n"
  p s!"/-- The LFSR state after the round constants for t = {t} (the last of `statesT{t}`). -/"
  p s!"def diagStartT{t} : Nat := {hex s0}\n"
  let mut start := s0
  let mut i := 0
  for c in cs do
    p s!"/-- Values {96 * i} .. {96 * i + c.length - 1} of the draws for t = {t}, each with the state after it. -/"
    p s!"def diagValsT{t}_{i} : List (Nat × Nat) :=\n  [{", ".intercalate (c.map fun (v, s) => s!"({hex v}, {hex s})")}]\n"
    p s!"theorem vals_t{t}_{i} : Grain.valChain 254 {hex start} diagValsT{t}_{i} = true := by\n  decide +kernel\n"
    start := c.getLast!.2
    i := i + 1
  let n := cs.length
  let names := (List.range n).map fun j => s!"diagValsT{t}_{j}"
  p s!"/-- The values of draws 0 .. {k} for t = {t}. -/\ndef diagValsT{t} : List (Nat × Nat) :=\n  {names.foldr (fun x acc => if acc == "" then x else s!"{x} ++ ({acc})") ""}\n"
  let rec proof (j : Nat) (fuel : Nat) : String :=
    match fuel with
    | 0 => ""
    | f + 1 =>
      if j + 1 = n then s!"vals_t{t}_{j}"
      else s!"(Grain.valChain_append_of _ _ _ _ _ vals_t{t}_{j} (by decide +kernel)\n    {proof (j + 1) f})"
  p s!"theorem vals_t{t} : Grain.valChain 254 diagStartT{t} diagValsT{t} = true :=\n  {proof 0 (n + 1)}\n"
  p s!"/-- Draw `j ≤ {k}` for t = {t}. -/"
  p s!"theorem drawRow_t{t} (j : Nat) (hj : j ≤ {k}) : Grain.drawRow {t} {rf} {rp} j =\n    some (((diagValsT{t}.drop (j * {t})).take {t}).map fun vs => vs.1 % P) :=\n  Grain.drawRow_of_vals {t} {rf} {rp} j _ statesT{t} diagValsT{t} (by decide +kernel) chain_t{t} vals_t{t}\n    (by rw [show diagValsT{t}.length = {ds.length} by decide +kernel]; omega)\n"
  p s!"theorem diagonal_t{t} : Grain.diagonal {t} {rf} {rp} {k} = some T{t}.params.diagM1 := by\n  rw [Grain.diagonal, drawRow_t{t} {k} le_rfl]\n  decide +kernel\n"

#eval do
  IO.println header
  gen 4 8 56 4 statesT4
  gen 8 8 57 30 statesT8
  gen 12 8 57 6 statesT12
  gen 16 8 57 6 statesT16
  gen 20 8 57 42 statesT20
  gen 24 8 57 2 statesT24
  gen 28 8 59 34 statesT28
  IO.println "end Poseidon2.Spec.DiagCheck"
