import Poseidon2.Checker.Forms
import Poseidon2.Spec.Sponge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Spec bridge: the symbolic run of the spec evaluates to the spec

The checker compares returned forms with `permG linOps` (and `hashG linOps`) run on input
atoms. This file proves that such a run, evaluated under any atom valuation `ρ` that agrees
with the atom table it ends with, is `permG (ringOps F)` run on the evaluated inputs:
`permG_bridge`, `hashG_bridge`. Together with a simulation of the bytecode (not proven yet),
this is what turns "the forms match" into "the contract returns the permutation".

The proof is generic: `permG` (and every function it is built from) commutes with any map
`h` that is a homomorphism of the `Ops` records, where the S-box may need a property `Good`
of the state that holds of later states and so of earlier ones (`OpsHom`).
-/

namespace Poseidon2.Checker

open Poseidon2.Spec

/-! ## Generic: `permG` commutes with a homomorphism of `Ops` -/

section Generic

variable {α σ β τ : Type} (A : Ops α σ) (B : Ops β τ) (h : α → β) (Good : σ → Prop)
  (k : σ → τ)

/-- `h` maps the operations of `A` to those of `B`; the S-box only where the state after it is
`Good`, and `Good` of the state after an S-box implies `Good` before it. -/
structure OpsHom : Prop where
  zero : h A.zero = B.zero
  add : ∀ a b, h (A.add a b) = B.add (h a) (h b)
  addC : ∀ a c, h (A.addC a c) = B.addC (h a) c
  mulC : ∀ a c, h (A.mulC a c) = B.mulC (h a) c
  sbox : ∀ a st, Good (A.sbox a st).2 → h (A.sbox a st).1 = (B.sbox (h a) (k st)).1
  sboxState : ∀ a st, k (A.sbox a st).2 = (B.sbox (h a) (k st)).2
  back : ∀ a st, Good (A.sbox a st).2 → Good st

variable {A B h Good k}

theorem m4_hom (H : OpsHom A B h Good k) (a b c d : α) :
    (m4 A a b c d).map h = m4 B (h a) (h b) (h c) (h d) := by
  simp [m4, H.add, H.mulC]

theorem m4Blocks_hom (H : OpsHom A B h Good k) :
    ∀ xs : List α, (m4Blocks A xs).map h = m4Blocks B (xs.map h)
  | a :: b :: c :: d :: r => by
    simp only [m4Blocks, List.map_append, List.map_cons, m4_hom H, m4Blocks_hom H r]
  | [] => by simp [m4Blocks]
  | [_] => by simp [m4Blocks]
  | [_, _] => by simp [m4Blocks]
  | [_, _, _] => by simp [m4Blocks]

theorem sum_hom (H : OpsHom A B h Good k) : ∀ xs : List α, h (sum A xs) = sum B (xs.map h)
  | [] => by simp [sum, H.zero]
  | x :: xs => by simp [sum, H.add, sum_hom H xs]

theorem colSums_hom (H : OpsHom A B h Good k) :
    ∀ xs : List α, (fun s => (h s.1, h s.2.1, h s.2.2.1, h s.2.2.2)) (colSums A xs) =
      colSums B (xs.map h)
  | a :: b :: c :: d :: r => by
    have := colSums_hom H r
    simp only [colSums, List.map_cons, H.add] at this ⊢
    rw [← this]
  | [] => by simp [colSums, H.zero]
  | [_] => by simp [colSums, H.zero]
  | [_, _] => by simp [colSums, H.zero]
  | [_, _, _] => by simp [colSums, H.zero]

theorem addColSums_hom (H : OpsHom A B h Good k) (s : α × α × α × α) :
    ∀ xs : List α, (addColSums A s xs).map h =
      addColSums B (h s.1, h s.2.1, h s.2.2.1, h s.2.2.2) (xs.map h)
  | a :: b :: c :: d :: r => by
    simp [addColSums, H.add, addColSums_hom H s r]
  | [] => by simp [addColSums]
  | [_] => by simp [addColSums]
  | [_, _] => by simp [addColSums]
  | [_, _, _] => by simp [addColSums]

theorem external_hom (H : OpsHom A B h Good k) (xs : List α) :
    (external A xs).map h = external B (xs.map h) := by
  match xs with
  | [a, b] => simp [external, sum, H.add, H.zero]
  | [a, b, c] => simp [external, sum, H.add, H.zero]
  | [a, b, c, d] => simp [external, m4_hom H]
  | [] => simp [external, m4Blocks, addColSums]
  | [a] => simp [external, m4Blocks, addColSums]
  | a :: b :: c :: d :: e :: r =>
    have hm := m4Blocks_hom H (a :: b :: c :: d :: e :: r)
    have hc := colSums_hom H (m4Blocks A (a :: b :: c :: d :: e :: r))
    simp only [external]
    rw [addColSums_hom H, hm]
    congr 1
    rw [← hm]
    simpa using hc

theorem zipWith_hom (H : OpsHom A B h Good k) (s : α) :
    ∀ (xs : List α) (d : List Nat),
      (List.zipWith (fun x di => A.add (A.mulC x di) s) xs d).map h =
        List.zipWith (fun x di => B.add (B.mulC x di) (h s)) (xs.map h) d
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, di :: d => by simp [H.add, H.mulC, zipWith_hom H s xs d]

theorem internal_hom (H : OpsHom A B h Good k) (d : List Nat) (xs : List α) :
    (internal A d xs).map h = internal B d (xs.map h) := by
  simp only [internal, zipWith_hom H, sum_hom H]

theorem zipWith_addC_hom (H : OpsHom A B h Good k) :
    ∀ (xs : List α) (rc : List Nat),
      (List.zipWith A.addC xs rc).map h = List.zipWith B.addC (xs.map h) rc
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, c :: rc => by simp [H.addC, zipWith_addC_hom H xs rc]

/-- What the stateful functions satisfy: the results map, the start state is `Good`, and the
states correspond. -/
def Commutes (r : List α × σ) (r' : List β × τ) (st : σ) : Prop :=
  r.1.map h = r'.1 ∧ Good st ∧ k r.2 = r'.2

theorem sboxAll_hom (H : OpsHom A B h Good k) :
    ∀ (xs : List α) (st : σ), Good (sboxAll A xs st).2 →
      Commutes (h := h) (Good := Good) (k := k) (sboxAll A xs st) (sboxAll B (xs.map h) (k st)) st
  | [], st, hg => by simpa [Commutes, sboxAll] using hg
  | x :: xs, st, hg => by
    simp only [sboxAll] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := sboxAll_hom H xs _ hg
    refine ⟨?_, H.back x st h2, ?_⟩
    · simp only [List.map_cons, H.sbox x st h2, h1, H.sboxState, sboxAll]
    · simp only [h3, H.sboxState, sboxAll, List.map_cons]

theorem fullRounds_hom (H : OpsHom A B h Good k) :
    ∀ (rcs : List (List Nat)) (xs : List α) (st : σ), Good (fullRounds A rcs xs st).2 →
      Commutes (h := h) (Good := Good) (k := k) (fullRounds A rcs xs st) (fullRounds B rcs (xs.map h) (k st)) st
  | [], xs, st, hg => by simpa [Commutes, fullRounds] using hg
  | rc :: rcs, xs, st, hg => by
    simp only [fullRounds] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := fullRounds_hom H rcs _ _ hg
    obtain ⟨s1, s2, s3⟩ := sboxAll_hom H _ st h2
    rw [zipWith_addC_hom H] at s1 s3
    refine ⟨?_, s2, ?_⟩
    · rw [h1, external_hom H, s1, s3]
    · rw [h3, external_hom H, s1, s3]

theorem partialRounds_hom (H : OpsHom A B h Good k) (d : List Nat) :
    ∀ (rcs : List Nat) (xs : List α) (st : σ), Good (partialRounds A d rcs xs st).2 →
      Commutes (h := h) (Good := Good) (k := k) (partialRounds A d rcs xs st) (partialRounds B d rcs (xs.map h) (k st)) st
  | [], xs, st, hg => by simpa [Commutes, partialRounds] using hg
  | _ :: _, [], st, hg => by simpa [Commutes, partialRounds] using hg
  | rc :: rcs, x :: xs, st, hg => by
    simp only [partialRounds] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := partialRounds_hom H d rcs _ _ hg
    have e1 := H.sbox (A.addC x rc) st h2
    have e2 := H.sboxState (A.addC x rc) st
    rw [H.addC] at e1 e2
    refine ⟨?_, H.back _ st h2, ?_⟩
    · rw [h1, internal_hom H, List.map_cons, e1, e2]; simp [partialRounds]
    · rw [h3, internal_hom H, List.map_cons, e1, e2]; simp [partialRounds]

theorem permG_hom (H : OpsHom A B h Good k) (c : Params) (xs : List α) (st : σ)
    (hg : Good (permG A c xs st).2) :
    Commutes (h := h) (Good := Good) (k := k) (permG A c xs st) (permG B c (xs.map h) (k st)) st := by
  simp only [permG] at hg ⊢
  obtain ⟨h1, h2, h3⟩ := fullRounds_hom H _ _ _ hg
  obtain ⟨p1, p2, p3⟩ := partialRounds_hom H _ _ _ _ h2
  obtain ⟨f1, f2, f3⟩ := fullRounds_hom H _ _ _ p2
  rw [external_hom H] at f1 f3
  refine ⟨?_, f2, ?_⟩
  · rw [h1, p1, p3, f1, f3]
  · rw [h3, p1, p3, f1, f3]

end Generic

end Poseidon2.Checker

namespace Poseidon2.Checker

open Poseidon2.Spec

/-! ## Linear forms evaluate homomorphically -/

/-- The value of a term list under an atom valuation. -/
def termsEval (ρ : Nat → F) : List (Nat × Nat) → F
  | [] => 0
  | (i, a) :: r => (a : F) * ρ i + termsEval ρ r

/-- The value of a form. -/
def Lin.eval (ρ : Nat → F) (l : Lin) : F := (l.c : F) + termsEval ρ l.ts

theorem termsEval_append (ρ : Nat → F) :
    ∀ xs ys : List (Nat × Nat), termsEval ρ (xs ++ ys) = termsEval ρ xs + termsEval ρ ys
  | [], ys => by simp [termsEval]
  | (i, a) :: xs, ys => by simp [termsEval, termsEval_append ρ xs ys, add_assoc]

theorem merge_eval (ρ : Nat → F) :
    ∀ (f : Nat) (xs ys : List (Nat × Nat)),
      termsEval ρ (merge f xs ys) = termsEval ρ xs + termsEval ρ ys
  | 0, xs, ys => termsEval_append ρ xs ys
  | _ + 1, [], ys => by simp [merge, termsEval]
  | _ + 1, (i, a) :: xs, [] => by simp [merge, termsEval]
  | f + 1, (i, a) :: xs, (j, b) :: ys => by
    simp only [merge]
    split
    · simp only [termsEval, merge_eval ρ f xs ((j, b) :: ys)]; ring
    · split
      · simp only [termsEval, merge_eval ρ f ((i, a) :: xs) ys]; ring
      · have hij : i = j := by omega
        subst hij
        have hc : ((((a + b) % P : Nat)) : F) = (a : F) + (b : F) := by
          rw [ZMod.natCast_mod]; push_cast; ring
        split
        · rename_i h0
          have : (a : F) + (b : F) = 0 := by rw [← hc, h0]; simp
          simp only [termsEval, merge_eval ρ f xs ys]
          linear_combination (-ρ i) * this
        · simp only [termsEval, merge_eval ρ f xs ys, hc]; ring

theorem Lin.eval_add (ρ : Nat → F) (a b : Lin) : (a.add b).eval ρ = a.eval ρ + b.eval ρ := by
  simp only [Lin.add, Lin.eval, merge_eval]
  rw [ZMod.natCast_mod]; push_cast; ring

theorem Lin.eval_const (ρ : Nat → F) (c : Nat) : (Lin.const c).eval ρ = (c : F) := by
  simp [Lin.const, Lin.eval, termsEval, ZMod.natCast_mod]

theorem termsEval_scale (ρ : Nat → F) (k : Nat) :
    ∀ ts : List (Nat × Nat),
      termsEval ρ (ts.map fun (i, v) => (i, v * k % P)) = (k : F) * termsEval ρ ts
  | [] => by simp [termsEval]
  | (i, a) :: r => by
    simp only [List.map_cons, termsEval, termsEval_scale ρ k r, ZMod.natCast_mod]
    push_cast; ring

theorem Lin.eval_scale (ρ : Nat → F) (a : Lin) (k : Nat) :
    (a.scale k).eval ρ = (k : F) * a.eval ρ := by
  by_cases h0 : k % P = 0
  · have : (k : F) = 0 := by rw [← ZMod.natCast_mod, h0]; simp
    simp [Lin.scale, h0, Lin.eval, termsEval, this]
  · have e : (a.scale k) = ⟨a.c * (k % P) % P, a.ts.map fun (i, v) => (i, v * (k % P) % P)⟩ := by
      simp [Lin.scale, h0]
    rw [e]
    simp only [Lin.eval, termsEval_scale, ZMod.natCast_mod, Nat.cast_mul]
    ring

theorem pow5_cast (x : Nat) : ((pow5 x : Nat) : F) = (x : F) ^ 5 := by
  simp only [pow5, ZMod.natCast_mod, Nat.cast_mul]
  ring

end Poseidon2.Checker

namespace Poseidon2.Checker

open Poseidon2.Spec

/-! ## Structural equality is equality -/

theorem Term.beq_eq : ∀ a b : Term, a.beq b = true → a = b
  | .const x, .const y, h => by simp [Term.beq] at h; rw [h]
  | .cdl x, .cdl y, h => by simp [Term.beq] at h; rw [h]
  | .cds, .cds, _ => rfl
  | .cv, .cv, _ => rfl
  | .un o a, .un o' a', h => by
    simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Term.beq_eq a a' h.2]
  | .bin o a b, .bin o' a' b', h => by
    simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Term.beq_eq a a' h.1.2, Term.beq_eq b b' h.2]
  | .const _, .cdl _, h | .const _, .cds, h | .const _, .cv, h | .const _, .un _ _, h
  | .const _, .bin _ _ _, h | .cdl _, .const _, h | .cdl _, .cds, h | .cdl _, .cv, h
  | .cdl _, .un _ _, h | .cdl _, .bin _ _ _, h | .cds, .const _, h | .cds, .cdl _, h
  | .cds, .cv, h | .cds, .un _ _, h | .cds, .bin _ _ _, h | .cv, .const _, h | .cv, .cdl _, h
  | .cv, .cds, h | .cv, .un _ _, h | .cv, .bin _ _ _, h | .un _ _, .const _, h
  | .un _ _, .cdl _, h | .un _ _, .cds, h | .un _ _, .cv, h | .un _ _, .bin _ _ _, h
  | .bin _ _ _, .const _, h | .bin _ _ _, .cdl _, h | .bin _ _ _, .cds, h
  | .bin _ _ _, .cv, h | .bin _ _ _, .un _ _, h => by simp [Term.beq] at h

theorem termsBeq_eq : ∀ a b : List (Nat × Nat), termsBeq a b = true → a = b
  | [], [], _ => rfl
  | (i, x) :: r, (j, y) :: s, h => by
    simp only [termsBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, h.1.2, termsBeq_eq r s h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [termsBeq] at h

theorem Lin.beq_eq (a b : Lin) (h : a.beq b = true) : a = b := by
  simp only [Lin.beq, Bool.and_eq_true, beq_iff_eq] at h
  cases a; cases b
  simp only at h
  rw [h.1, termsBeq_eq _ _ h.2]

theorem Def.beq_eq : ∀ a b : Def, a.beq b = true → a = b
  | .word a, .word b, h => by rw [Term.beq_eq a b h]
  | .pow5 a, .pow5 b, h => by rw [Lin.beq_eq a b h]
  | .word _, .pow5 _, h | .pow5 _, .word _, h => by simp [Def.beq] at h

/-! ## The atom table -/

/-- What an atom stands for, in the field. -/
def Def.val (e : Env) (ρ : Nat → F) : Def → F
  | .word t => (t.eval e : F)
  | .pow5 l => l.eval ρ ^ 5

/-- `ρ` gives every atom of the table its value. -/
def Tab.Valid (e : Env) (ρ : Nat → F) (tb : Tab) : Prop :=
  ∀ p ∈ tb.defs, ρ p.1 = p.2.val e ρ

theorem lookupDef_mem (d : Def) :
    ∀ (ds : List (Nat × Def)) (i : Nat), lookupDef d ds = some i → (i, d) ∈ ds
  | [], _, h => by simp [lookupDef] at h
  | (j, d') :: r, i, h => by
    simp only [lookupDef] at h
    split at h
    · rename_i hb
      cases h
      rw [Def.beq_eq d d' hb]
      simp
    · exact List.mem_cons_of_mem _ (lookupDef_mem d r i h)

/-- `Tab.atom` returns an atom standing for `d`, and keeps every earlier atom. -/
theorem Tab.atom_spec (e : Env) (ρ : Nat → F) (tb : Tab) (d : Def)
    (hv : Tab.Valid e ρ (tb.atom d).2) :
    (tb.atom d).1.eval ρ = d.val e ρ ∧ Tab.Valid e ρ tb := by
  unfold Tab.atom at hv ⊢
  split
  · rename_i i hl
    simp only [hl] at hv
    refine ⟨?_, hv⟩
    simp [Lin.eval, termsEval, hv _ (lookupDef_mem d _ i hl)]
  · rename_i hl
    simp only [hl] at hv
    refine ⟨?_, fun p hp => hv p (List.mem_cons_of_mem _ hp)⟩
    simp [Lin.eval, termsEval, hv (tb.next, d) (by simp)]

/-- `linOps` maps to the field operations under `Lin.eval ρ`, for any `ρ` valid on the table
the run ends with. -/
theorem linOps_hom (e : Env) (ρ : Nat → F) :
    OpsHom linOps (ringOps F) (Lin.eval ρ) (Tab.Valid e ρ) (fun _ => ()) where
  zero := by simp [linOps, ringOps, Lin.eval, termsEval]
  add a b := Lin.eval_add ρ a b
  addC a c := by simp [linOps, ringOps, Lin.eval_add, Lin.eval_const]
  mulC a c := by simp [linOps, ringOps, Lin.eval_scale]
  sbox a st hv := by
    simp only [linOps, ringOps] at hv ⊢
    unfold Tab.sbox at hv ⊢
    split
    · rename_i c hc
      have : a.eval ρ = (c : F) := by
        cases a; simp only [Lin.asConst] at hc; split at hc <;> simp_all [Lin.eval, termsEval]
      rw [Lin.eval_const, pow5_cast, this]
    · rename_i hc
      simp only [hc] at hv
      exact (Tab.atom_spec e ρ st _ hv).1
  sboxState _ _ := rfl
  back a st hv := by
    simp only [linOps] at hv
    unfold Tab.sbox at hv
    split at hv
    · exact hv
    · exact (Tab.atom_spec e ρ st _ hv).2

/-- **The spec bridge**: the symbolic spec run, evaluated under a valuation valid on the table
it ends with, is the permutation of the evaluated inputs. -/
theorem permG_bridge (e : Env) (ρ : Nat → F) (c : Params) (xs : List Lin) (tb : Tab)
    (hv : Tab.Valid e ρ (permG linOps c xs tb).2) :
    (permG linOps c xs tb).1.map (Lin.eval ρ) = permutation c (xs.map (Lin.eval ρ)) :=
  (permG_hom (linOps_hom e ρ) c xs tb hv).1

theorem spongeStateG_hom (ρ : Nat → F) (t : Nat) (xs : List Lin) :
    (spongeStateG linOps t xs).map (Lin.eval ρ) = spongeStateG (ringOps F) t (xs.map (Lin.eval ρ)) := by
  have H := linOps_hom (⟨[], 0⟩ : Env) ρ
  simp only [spongeStateG, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    List.length_map, H.addC, H.zero]

/-- The spec bridge for the hash: the symbolic `hashG` evaluates to `hash`. -/
theorem hashG_bridge (e : Env) (ρ : Nat → F) (c : Params) (xs : List Lin) (tb : Tab)
    (hv : Tab.Valid e ρ (hashG linOps c xs tb).2) :
    (hashG linOps c xs tb).1.eval ρ = Spec.hash c (xs.map (Lin.eval ρ)) := by
  have hp := (permG_hom (linOps_hom e ρ) c (spongeStateG linOps c.t xs) tb hv).1
  rw [spongeStateG_hom] at hp
  show _ = (hashG (ringOps F) c (xs.map (Lin.eval ρ)) ()).1
  simp only [hashG]
  rw [← hp]
  cases (permG linOps c (spongeStateG linOps c.t xs) tb).1 with
  | nil => exact (linOps_hom e ρ).zero
  | cons a r => rfl

end Poseidon2.Checker
