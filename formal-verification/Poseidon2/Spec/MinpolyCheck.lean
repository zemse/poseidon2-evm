import Poseidon2.Spec.MinpolyCheck.T2
import Poseidon2.Spec.MinpolyCheck.T3
import Poseidon2.Spec.MinpolyCheck.T4
import Poseidon2.Spec.MinpolyCheck.T8
import Poseidon2.Spec.MinpolyCheck.T12
import Poseidon2.Spec.MinpolyCheck.T16
import Poseidon2.Spec.MinpolyCheck.T20
import Poseidon2.Spec.MinpolyCheck.T24
import Poseidon2.Spec.MinpolyCheck.T28

/-!
# The internal diagonals are the script's selection

For every width `t ≥ 4`, the HorizenLabs script keeps the first Grain draw whose matrix
`circ(0, 1, .., 1) + diag(r)` passes `check_minpoly_condition` (`Minpoly.MinpolyCondition`:
for `i = 1 .. 2t` the minimal polynomial of `M ^ i` over `GF(P)` is irreducible of degree
`t`). `selected_t<t>` states that draw `k` (4, 30, 6, 6, 42, 2, 34) is that first passing draw
(`Minpoly.FirstPass`) and that `diagM1` of `Constants/T<t>.lean` is its `r - 1`. So, given the
round numbers, the spec's constants for every `t ≥ 4` are what the script outputs.

For t = 2 and 3 the script fixes `M_I` and checks nothing: the t = 2 matrix passes the same
check (`fixed_t2`), the t = 3 matrix fails it (`fixed_t3`, the eigenvalue 1).
-/

namespace Poseidon2.Spec.MinpolyCheck

open Minpoly Constants

theorem selected_t4 : FirstPass 4 8 56 4 ∧ Grain.diagonal 4 8 56 4 = some T4.params.diagM1 :=
  ⟨T4.firstPass, DiagCheck.diagonal_t4⟩

theorem selected_t8 : FirstPass 8 8 57 30 ∧ Grain.diagonal 8 8 57 30 = some T8.params.diagM1 :=
  ⟨T8.firstPass, DiagCheck.diagonal_t8⟩

theorem selected_t12 : FirstPass 12 8 57 6 ∧ Grain.diagonal 12 8 57 6 = some T12.params.diagM1 :=
  ⟨T12.firstPass, DiagCheck.diagonal_t12⟩

theorem selected_t16 : FirstPass 16 8 57 6 ∧ Grain.diagonal 16 8 57 6 = some T16.params.diagM1 :=
  ⟨T16.firstPass, DiagCheck.diagonal_t16⟩

theorem selected_t20 : FirstPass 20 8 57 42 ∧ Grain.diagonal 20 8 57 42 = some T20.params.diagM1 :=
  ⟨T20.firstPass, DiagCheck.diagonal_t20⟩

theorem selected_t24 : FirstPass 24 8 57 2 ∧ Grain.diagonal 24 8 57 2 = some T24.params.diagM1 :=
  ⟨T24.firstPass, DiagCheck.diagonal_t24⟩

theorem selected_t28 : FirstPass 28 8 59 34 ∧ Grain.diagonal 28 8 59 34 = some T28.params.diagM1 :=
  ⟨T28.firstPass, DiagCheck.diagonal_t28⟩

theorem fixed_t2 : MinpolyCondition 2 (partialMatrix 2 (T2.params.diagM1.map (· + 1))) := by
  rw [T2.row_eq]; exact T2.pass

theorem fixed_t3 : ¬MinpolyCondition 3 (partialMatrix 3 (T3.params.diagM1.map (· + 1))) := by
  rw [T3.row_eq]; exact T3.fail0

end Poseidon2.Spec.MinpolyCheck
