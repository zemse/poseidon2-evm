import Poseidon2.Checker.Check

/-!
# Checking the spec side in segments

For a permutation case, `resultOk` runs `permG linOps` over the atom table the bytecode built.
For wide states that run is too large for one kernel declaration, so it is checked in segments
of rounds, as `Segments.lean` does for the bytecode run: `roundsRun` runs the rounds of
`rounds c` one at a time, `permG_eq_roundsRun` shows that this is `permG`, `rounds_seg` splits a
run of rounds at any point, and `resultOk_perm` reduces the case to a run of rounds and a
comparison of the returned forms.
-/

namespace Poseidon2.Checker

open Poseidon2.Spec

/-- One round of the permutation. -/
inductive Round where
  | full (rc : List Nat)
  | part (rc : Nat)

/-- The rounds of the permutation after the first `M_E`, in order. -/
def rounds (c : Params) : List Round :=
  (c.rcExternal.take (c.roundsF / 2)).map .full ++ c.rcInternal.map .part ++
    (c.rcExternal.drop (c.roundsF / 2)).map .full

section

variable {α σ : Type} (A : Ops α σ) (d : List Nat)

/-- One round, as `fullRounds` and `partialRounds` run it. -/
def round : Round → List α → σ → List α × σ
  | .full rc, xs, st =>
    let r := sboxAll A (List.zipWith A.addC xs rc) st
    (external A r.1, r.2)
  | .part _, [], st => ([], st)
  | .part rc, x :: xs, st =>
    let r := A.sbox (A.addC x rc) st
    (internal A d (r.1 :: xs), r.2)

/-- The rounds of a list, one after the other. -/
def roundsRun : List Round → List α → σ → List α × σ
  | [], xs, st => (xs, st)
  | r :: rs, xs, st =>
    let p := round A d r xs st
    roundsRun rs p.1 p.2

theorem roundsRun_append : ∀ (l₁ l₂ : List Round) (xs : List α) (st : σ),
    roundsRun A d (l₁ ++ l₂) xs st =
      roundsRun A d l₂ (roundsRun A d l₁ xs st).1 (roundsRun A d l₁ xs st).2
  | [], _, _, _ => rfl
  | r :: l₁, l₂, xs, st => by
    simp only [List.cons_append, roundsRun]
    exact roundsRun_append l₁ l₂ _ _

theorem fullRounds_eq : ∀ (rcs : List (List Nat)) (xs : List α) (st : σ),
    fullRounds A rcs xs st = roundsRun A d (rcs.map .full) xs st
  | [], _, _ => rfl
  | rc :: rcs, xs, st => by
    simp only [fullRounds, List.map_cons, roundsRun, round]
    exact fullRounds_eq rcs _ _

theorem roundsRun_part_nil : ∀ (rcs : List Nat) (st : σ),
    roundsRun A d (rcs.map .part) [] st = ([], st)
  | [], _ => rfl
  | _ :: rcs, st => by
    simp only [List.map_cons, roundsRun, round]
    exact roundsRun_part_nil rcs st

theorem partialRounds_eq : ∀ (rcs : List Nat) (xs : List α) (st : σ),
    partialRounds A d rcs xs st = roundsRun A d (rcs.map .part) xs st
  | [], _, _ => rfl
  | _ :: rcs, [], st => by
    simp only [partialRounds, List.map_cons, roundsRun, round]
    exact (roundsRun_part_nil A d rcs st).symm
  | rc :: rcs, x :: xs, st => by
    simp only [partialRounds, List.map_cons, roundsRun, round]
    exact partialRounds_eq rcs _ _

theorem permG_eq_roundsRun (c : Params) (xs : List α) (st : σ) :
    permG A c xs st = roundsRun A c.diagM1 (rounds c) (external A xs) st := by
  simp only [permG, rounds, roundsRun_append, fullRounds_eq A c.diagM1,
    partialRounds_eq A c.diagM1]

/-- A run of rounds splits after its first `n`: the basis of checking it in segments. -/
theorem rounds_seg (l : List Round) (n : Nat) (xs : List α) (st : σ) (ys : List α) (st' : σ)
    (h : roundsRun A d (l.take n) xs st = (ys, st')) :
    roundsRun A d l xs st = roundsRun A d (l.drop n) ys st' := by
  conv_lhs => rw [← List.take_append_drop n l, roundsRun_append, h]

end

/-- A permutation case that returned `ws` over the table `tb` passes if the spec's rounds, run on
the input forms over `tb`, end in forms `ys` that the returned words match. -/
theorem resultOk_perm {fs : Facts} {c : Params} {ins : List Term} {ws : List SV} {tb : Tab}
    {ys : List Lin} {st : Tab} {g : Nat}
    (h : roundsRun linOps c.diagM1 (rounds c) (external linOps (inputForms fs ins tb).1)
      (inputForms fs ins tb).2 = (ys, st))
    (ho : outputsMatch ws ys = true) :
    resultOk fs (.perm c ins) (.ret ws tb g) = true := by
  simp only [resultOk, specForms]
  rw [permG_eq_roundsRun, h]
  exact ho

/-- `resultOk_perm` with the gas of the run. -/
theorem resultOkGas_perm {fs : Facts} {c : Params} {ins : List Term} {ws : List SV} {tb : Tab}
    {ys : List Lin} {st : Tab} {g : Nat}
    (h : roundsRun linOps c.diagM1 (rounds c) (external linOps (inputForms fs ins tb).1)
      (inputForms fs ins tb).2 = (ys, st))
    (ho : outputsMatch ws ys = true) :
    resultOkGas fs (.perm c ins) g (.ret ws tb g) = true := by
  simp only [resultOkGas, beq_self_eq_true, Bool.true_and]
  exact resultOk_perm h ho

end Poseidon2.Checker
