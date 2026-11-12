import Poseidon2.Spec.Minpoly
import Poseidon2.Spec.Constants.T2

/-!
# The fixed internal matrix for t = 2 against the script's check

The script does not draw `M_I` for t = 2: it fixes `[[2, 1], [1, 3]]` (`diagM1 = [1, 2]`)
and runs no `check_minpoly_condition` on it. This file states what that check would say:
the matrix passes it.
Certificates written by `scripts/minpoly.mjs`, checked by kernel evaluation.
-/

namespace Poseidon2.Spec.MinpolyCheck.T2

open Minpoly

/-- `r` of the fixed matrix (`diagM1 + 1`). -/
def row : List Nat := [2, 3]

theorem row_eq : Constants.T2.params.diagM1.map (· + 1) = row := by decide +kernel

/-- The characteristic polynomial of the matrix, without its leading `1`. -/
def fl : List Nat := [0x5, 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffffc]

theorem mat : matOk 2 row fl = true := by decide +kernel

/-- The bits of `P` after its leading one, most significant first (1 part). -/
def bits0 : List Bool := [true, false, false, false, false, false, true, true, false, false, true, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, true, false, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]

def bits : List Bool := bits0

/-- `x ^ e mod f` after each part of the square-and-multiply. -/
def sq1 : List Nat := [0x5, 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000]

theorem run0 : sqRun fl bits0 (xL 2) = sq1 := by decide +kernel

theorem run : sqRun fl bits (xL 2) = sq1 :=
  run0

/-- `x ^ (P ^ d) mod f`, d = 1 .. 1. -/
def hs : List (List Nat) := [sq1]

theorem frob : frobOk fl bits hs :=
  ⟨by decide +kernel, by decide +kernel, _, _, rfl, run,
    rfl⟩

/-- Bezout identities `u · f + w · (x ^ (P ^ d) - x) = 1`, d = 1 .. 1. -/
def bez : List (List Nat × List Nat) :=
  [([0x135b52945a13d9aa49b9b57c33cd568ba9ae5ce9ca4a2d06e7f3fbd4c6666666], [0x1, 0x9ada94a2d09ecd524dcdabe19e6ab45d4d72e74e525168373f9fdea63333333])]

theorem bezout : bezOk fl hs bez = true := by decide +kernel

/-- The maximal proper divisors of 2. -/
def ms : List Nat := [1]

def W1_1 : List Nat := [0x3e8, 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffeee]

theorem pw1_0 : powsNe fl sq1 4 sq1 (mulXs fl 0 (xL 2)) W1_1 = true := by
  decide +kernel

theorem pw1 : powsNe fl sq1 4 sq1 (xL 2) W1_1 = true :=
  pw1_0

theorem degs : degOk fl hs ms :=
  ⟨by decide +kernel, by
    intro m hm
    simp only [ms, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl
    · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, _, pw1⟩⟩

theorem pass : MinpolyCondition 2 (partialMatrix 2 row) :=
  minpolyCondition_of_cert 2 _ fl bits hs bez ms (by decide +kernel) mat frob bezout degs

end Poseidon2.Spec.MinpolyCheck.T2
