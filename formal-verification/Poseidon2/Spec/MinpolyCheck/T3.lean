import Poseidon2.Spec.Minpoly
import Poseidon2.Spec.Constants.T3

/-!
# The fixed internal matrix for t = 3 against the script's check

The script does not draw `M_I` for t = 3: it fixes `[[2, 1, 1], [1, 2, 1], [1, 1, 3]]` (`diagM1 = [1, 1, 2]`)
and runs no `check_minpoly_condition` on it. This file states what that check would say:
the matrix fails it: its characteristic polynomial has the root 1 (eigenvector
`(1, -1, 0)`). The check is a sufficient condition against arbitrarily long subspace trails,
not a necessary one.
Certificates written by `scripts/minpoly.mjs`, checked by kernel evaluation.
-/

namespace Poseidon2.Spec.MinpolyCheck.T3

open Minpoly

/-- `r` of the fixed matrix (`diagM1 + 1`). -/
def row : List Nat := [2, 2, 3]

theorem row_eq : Constants.T3.params.diagM1.map (· + 1) = row := by decide +kernel

/-- The monic product `g · h` without its leading `1`. -/
def fOf (g h : List Nat) : List Nat := (mulL (g ++ [1]) (h ++ [1])).take 3

/-- The matrix: `f = g · h`, `g` of degree 2. -/
def g0 : List Nat := [0x7, 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffffb]

def h0 : List Nat := [0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000]

theorem fail0 : ¬MinpolyCondition 3 (partialMatrix 3 row) :=
  not_minpolyCondition 3 _ (fOf g0 h0) g0 h0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Poseidon2.Spec.MinpolyCheck.T3
