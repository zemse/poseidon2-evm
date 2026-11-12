import Poseidon2.Checker.SymExec

/-!
# Checking a run in segments

A long run is checked as segments of `runN` between literal checker states, so the kernel
never holds the whole run (memory) or a deep chain of unevaluated states (stack). A segment
boundary names the instructions still to run by the `pc` of the first one (`Code.at`), not by
the list itself, because comparing two long lists is a deep recursion in the kernel.
`seg_run` shows that this loses nothing: every instruction list a run reaches is a suffix of
the decoded code (`runN_suffix`), the decoded `pc`s strictly increase (`Code.ofBytes_wf`), and
such a suffix is determined by its first `pc` (`suffix_eq_at`).
-/

namespace Poseidon2.Checker

/-- The `pc` of the next instruction, `none` at the end of the code. -/
def pcOf : List (Nat × Ins) → Option Nat
  | [] => none
  | (pc, _) :: _ => some pc

/-- The instructions from `pc` on (`none`: none left). -/
def Code.at (code : Code) : Option Nat → List (Nat × Ins)
  | none => []
  | some pc => code.ins.dropWhile (·.1 < pc)

/-- Where a segment stopped: the next `pc` and the state, or `none` if the run ended. -/
def Out.pcSt : Out → Option (Option Nat × St)
  | .next is s => some (pcOf is, s)
  | .done _ => none

/-- Decoded code whose jump destinations are suffixes of its instructions and whose `pc`s
strictly increase. -/
structure Code.WF (code : Code) : Prop where
  dests : ∀ d ∈ code.dests, d.2 <:+ code.ins
  sorted : code.ins.Pairwise (fun a b => a.1 < b.1)

theorem findDest_mem (t : Nat) :
    ∀ (ds : List (Nat × List (Nat × Ins))) (is : List (Nat × Ins)),
      findDest t ds = some is → ∃ d ∈ ds, d.2 = is
  | [], _, h => by simp [findDest] at h
  | (p, l) :: ds, is, h => by
    simp only [findDest] at h
    split at h
    · exact ⟨(p, l), by simp, by simpa using h⟩
    · obtain ⟨d, hd, e⟩ := findDest_mem t ds is h
      exact ⟨d, by simp [hd], e⟩

theorem step1_suffix (fs : Facts) (code : Code) (hwf : code.WF) (is is' : List (Nat × Ins))
    (s s' : St) (hs : is <:+ code.ins) (h : step1 fs code is s = .next is' s') :
    is' <:+ code.ins := by
  match is, h with
  | (pc, i) :: rest, h =>
    simp only [step1] at h
    split at h
    · cases h
      exact List.IsSuffix.trans (List.suffix_cons _ _) hs
    · split at h
      · rename_i hl
        cases h
        obtain ⟨d, hd, e⟩ := findDest_mem _ code.dests _ hl
        exact e ▸ hwf.dests d hd
      · cases h
    · cases h

theorem runN_suffix (fs : Facts) (code : Code) (hwf : code.WF) :
    ∀ (k : Nat) (is is' : List (Nat × Ins)) (s s' : St), is <:+ code.ins →
      runN fs code k is s = .next is' s' → is' <:+ code.ins
  | 0, is, is', s, s', hs, h => by
    simp only [runN, Out.next.injEq] at h
    exact h.1 ▸ hs
  | k + 1, is, is', s, s', hs, h => by
    simp only [runN] at h
    split at h
    · rename_i is₁ s₁ h₁
      exact runN_suffix fs code hwf k is₁ is' s₁ s'
        (step1_suffix fs code hwf is is₁ s s₁ hs h₁) h
    · cases h

theorem dropWhile_append_of_all {α : Type} (p : α → Bool) :
    ∀ (pre l : List α), (∀ a ∈ pre, p a = true) → (pre ++ l).dropWhile p = l.dropWhile p
  | [], _, _ => rfl
  | a :: pre, l, h => by
    simp only [List.cons_append, List.dropWhile, h a (by simp)]
    exact dropWhile_append_of_all p pre l fun x hx => h x (by simp [hx])

/-- In a list of strictly increasing `pc`s, a suffix is the list from its first `pc` on. -/
theorem suffix_eq_at (code : Code) (hwf : code.WF) (l : List (Nat × Ins))
    (hl : l <:+ code.ins) : l = code.at (pcOf l) := by
  obtain ⟨pre, hpre⟩ := hl
  have hsort := hwf.sorted
  rw [← hpre] at hsort
  match l, hsort, hpre with
  | [], _, _ => rfl
  | (pc, i) :: rest, hsort, hpre =>
    simp only [Code.at, pcOf, ← hpre]
    rw [dropWhile_append_of_all]
    · simp
    · intro a ha
      have := List.pairwise_append.mp hsort
      simpa using this.2.2 a ha (pc, i) (by simp)

/-- One segment: a `runN` from the instructions at `p` that stops at `p'` with state `s'`
lets the run continue from there. -/
theorem seg_run (fs : Facts) (code : Code) (hwf : code.WF) (k f : Nat) (p p' : Option Nat)
    (s s' : St) (h : (runN fs code k (code.at p) s).pcSt = some (p', s')) :
    run fs code (k + f) (code.at p) s = run fs code f (code.at p') s' := by
  cases hr : runN fs code k (code.at p) s with
  | done r => simp [hr, Out.pcSt] at h
  | next is' s₁ =>
    simp only [hr, Out.pcSt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hp, rfl⟩ := h
    have hsuf : code.at p <:+ code.ins := by
      cases p with
      | none => exact List.nil_suffix
      | some pc => exact List.dropWhile_suffix _
    have := suffix_eq_at code hwf is' (runN_suffix fs code hwf k _ _ _ _ hsuf hr)
    rw [run_add fs code k f _ _ _ _ hr, this, hp]

end Poseidon2.Checker

namespace Poseidon2.Checker

theorem destSuffixes_suffix (dj : List Nat) :
    ∀ (l : List (Nat × Ins)), ∀ d ∈ destSuffixes dj l, d.2 <:+ l
  | [], d, hd => by simp [destSuffixes] at hd
  | (pc, i) :: rest, d, hd => by
    have ih := destSuffixes_suffix dj rest
    have tail : ∀ d ∈ destSuffixes dj rest, d.2 <:+ (pc, i) :: rest :=
      fun d hd => (ih d hd).trans (List.suffix_cons _ _)
    simp only [destSuffixes] at hd
    split at hd
    · split at hd
      · simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact List.suffix_refl _
        · exact tail d hd
      · exact tail d hd
    · exact tail d hd

/-- Every decoded `pc` is at least the start. -/
theorem decode_ge : ∀ (f pc : Nat) (bs : List Nat), ∀ x ∈ decode f pc bs, pc ≤ x.1
  | 0, _, _, x, hx => by simp [decode] at hx
  | _ + 1, _, [], x, hx => by simp [decode] at hx
  | f + 1, pc, b :: bs, x, hx => by
    have hn := decodeOne_len b bs
    rcases hd : decodeOne b bs with ⟨i, n, rest⟩
    simp only [decode, hd, List.mem_cons] at hx
    rw [hd] at hn
    rcases hx with rfl | hx
    · exact le_refl _
    · cases rest with
      | none => simp at hx
      | some r =>
        have := decode_ge f _ _ x hx
        simp only at hn
        omega

/-- Decoded `pc`s strictly increase. -/
theorem decode_sorted : ∀ (f pc : Nat) (bs : List Nat),
    (decode f pc bs).Pairwise (fun a b => a.1 < b.1)
  | 0, _, _ => by simp [decode]
  | _ + 1, _, [] => by simp [decode]
  | f + 1, pc, b :: bs => by
    have hn := decodeOne_len b bs
    rcases hd : decodeOne b bs with ⟨i, n, rest⟩
    rw [hd] at hn
    simp only [decode, hd]
    cases rest with
    | none => simp
    | some r =>
      refine List.Pairwise.cons (fun x hx => ?_) (decode_sorted f _ _)
      have := decode_ge f _ _ x hx
      simp only at hn ⊢
      omega

theorem Code.ofBytes_wf (bs : List Nat) : (Code.ofBytes bs).WF where
  dests := destSuffixes_suffix _ _
  sorted := decode_sorted _ _ _

end Poseidon2.Checker

namespace Poseidon2.Checker

theorem Code.at_zero (code : Code) : code.at (some 0) = code.ins := by
  simp [Code.at, dropWhile_false]

end Poseidon2.Checker
