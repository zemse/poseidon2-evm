import Poseidon2.Checker.FieldSound
import Poseidon2.Checker.Check

/-!
# A valuation of the atom table

The soundness lemmas hold for any valuation `ρ` valid on the atom table (`Tab.Valid`, every atom
gets its value: a word atom the value of its term, a `pow5 l` atom the fifth power of `l` under
`ρ`). This file builds one. It exists when every `pow5` atom is a form over older atoms
(`Tab.WF`): `defsVal` values the atoms from the oldest on, and `Tab.WF.valid` proves it valid.

The table has that shape at the end of every run the checker accepts: every form the checker
holds (on the stack, in memory) names only atoms the table already has (`St.Inv`), each step
keeps this (`step_inv`, `ctl_inv'`, `runN_inv'`), and so does the spec's symbolic run on top
of it (`OpsInv`, `permG_inv`, `hashG_inv` for `linOps`).
-/

namespace Poseidon2.Checker

open Poseidon2.Spec

/-! ## Forms over older atoms -/

/-- Every atom of `l` is below `n`. -/
def Lin.Below (n : Nat) (l : Lin) : Prop := ∀ p ∈ l.ts, p.1 < n

/-- Every form in `v` names atoms below `n`. -/
def SV.Below (n : Nat) : SV → Prop
  | .word _ => True
  | .lin l _ => l.Below n
  | .pw _ l _ => l.Below n

/-- A `pow5` atom is a form over atoms below `n`. -/
def Def.Below (n : Nat) : Def → Prop
  | .word _ => True
  | .pow5 l => l.Below n

/-- Atoms newest first, indices decreasing, each atom defined over the older ones. -/
def DefsOk : List (Nat × Def) → Prop
  | [] => True
  | (i, d) :: r => (∀ p ∈ r, p.1 < i) ∧ d.Below i ∧ DefsOk r

/-- The table's indices are below its counter and every atom is defined over older ones. -/
structure Tab.WF (tb : Tab) : Prop where
  lt : ∀ p ∈ tb.defs, p.1 < tb.next
  ok : DefsOk tb.defs

theorem Lin.Below.mono {n m : Nat} {l : Lin} (h : l.Below n) (hm : n ≤ m) : l.Below m :=
  fun p hp => lt_of_lt_of_le (h p hp) hm

theorem SV.Below.mono {n m : Nat} {v : SV} (h : v.Below n) (hm : n ≤ m) : v.Below m := by
  cases v with
  | word _ => trivial
  | lin l _ => exact Lin.Below.mono (n := n) h hm
  | pw _ l _ => exact Lin.Below.mono (n := n) h hm

theorem SV.below_word (n : Nat) (w : Word) : (SV.word w).Below n := trivial

theorem SV.below_const (n v : Nat) : (SV.const v).Below n := trivial

theorem Lin.below_const (n c : Nat) : (Lin.const c).Below n := by
  intro p hp; simp [Lin.const] at hp

theorem merge_below (n : Nat) :
    ∀ (f : Nat) (xs ys : List (Nat × Nat)), (∀ p ∈ xs, p.1 < n) →
      (∀ p ∈ ys, p.1 < n) →
      ∀ p ∈ merge f xs ys, p.1 < n
  | 0, xs, ys, hx, hy, p, hp => by
    simp only [merge, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hx p hp
    · exact hy p hp
  | _ + 1, [], ys, _, hy, p, hp => by simp only [merge] at hp; exact hy p hp
  | _ + 1, (i, a) :: xs, [], hx, _, p, hp => by simp only [merge] at hp; exact hx p hp
  | f + 1, (i, a) :: xs, (j, b) :: ys, hx, hy, p, hp => by
    have hx' : ∀ q ∈ xs, q.1 < n := fun q hq => hx q (List.mem_cons_of_mem _ hq)
    have hy' : ∀ q ∈ ys, q.1 < n := fun q hq => hy q (List.mem_cons_of_mem _ hq)
    have hi : i < n := hx (i, a) List.mem_cons_self
    have hj : j < n := hy (j, b) List.mem_cons_self
    simp only [merge] at hp
    split at hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hi
      · exact merge_below n f xs _ hx' hy p hp
    · split at hp
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact hj
        · exact merge_below n f _ ys hx hy' p hp
      · split at hp
        · exact merge_below n f xs ys hx' hy' p hp
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact hi
          · exact merge_below n f xs ys hx' hy' p hp

theorem Lin.below_add {n : Nat} {a b : Lin} (ha : a.Below n) (hb : b.Below n) :
    (a.add b).Below n :=
  merge_below n _ _ _ ha hb

theorem Lin.below_scale {n : Nat} {a : Lin} (ha : a.Below n) (k : Nat) : (a.scale k).Below n := by
  intro p hp
  unfold Lin.scale at hp
  dsimp only at hp
  split at hp
  · simp at hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ha q hq

/-! ## The table operations keep the shape -/

/-- `tb'` is a well-formed table at least as far as `tb`. -/
def Tab.Grows (tb tb' : Tab) : Prop := tb'.WF ∧ tb.next ≤ tb'.next

theorem Tab.Grows.refl {tb : Tab} (h : tb.WF) : tb.Grows tb := ⟨h, le_refl _⟩

theorem Tab.Grows.trans {a b c : Tab} (h1 : a.Grows b) (h2 : b.Grows c) : a.Grows c :=
  ⟨h2.1, le_trans h1.2 h2.2⟩

theorem Def.Below.mono {n m : Nat} {d : Def} (h : d.Below n) (hm : n ≤ m) : d.Below m := by
  cases d with
  | word _ => trivial
  | pow5 l => exact Lin.Below.mono (n := n) h hm

theorem Tab.atom_wf (tb : Tab) (d : Def) (hw : tb.WF) (hd : d.Below tb.next) :
    tb.Grows (tb.atom d).2 ∧ (tb.atom d).1.Below (tb.atom d).2.next := by
  unfold Tab.atom
  split
  · rename_i i hl
    refine ⟨Tab.Grows.refl hw, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact hw.lt _ (lookupDef_mem d _ i hl)
  · refine ⟨⟨⟨?_, ?_⟩, Nat.le_succ _⟩, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hw.lt p hp)
    · exact ⟨hw.lt, hd, hw.ok⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact Nat.lt_succ_self _

theorem Tab.sbox_wf (tb : Tab) (l : Lin) (hw : tb.WF) (hl : l.Below tb.next) :
    tb.Grows (tb.sbox l).2 ∧ (tb.sbox l).1.Below (tb.sbox l).2.next := by
  unfold Tab.sbox
  split
  · exact ⟨Tab.Grows.refl hw, Lin.below_const _ _⟩
  · exact Tab.atom_wf tb _ hw hl

/-! ## The valuation -/

/-- Values the atoms from the oldest on: each atom gets its value under the atoms before it. -/
def defsVal (e : Env) : List (Nat × Def) → Nat → F
  | [] => fun _ => 0
  | (i, d) :: r => fun j => if j = i then d.val e (defsVal e r) else defsVal e r j

theorem termsEval_congr (ρ ρ' : Nat → F) :
    ∀ ts : List (Nat × Nat), (∀ p ∈ ts, ρ p.1 = ρ' p.1) →
      termsEval ρ ts = termsEval ρ' ts
  | [], _ => rfl
  | (i, a) :: r, h => by
    simp only [termsEval]
    rw [h (i, a) List.mem_cons_self,
      termsEval_congr ρ ρ' r fun p hp => h p (List.mem_cons_of_mem _ hp)]

theorem Def.val_congr (e : Env) (ρ ρ' : Nat → F) (n : Nat) (d : Def) (hd : d.Below n)
    (h : ∀ j, j < n → ρ j = ρ' j) : d.val e ρ = d.val e ρ' := by
  cases d with
  | word _ => rfl
  | pow5 l =>
    simp only [Def.val, Lin.eval]
    rw [termsEval_congr ρ ρ' l.ts fun p hp => h p.1 (hd p hp)]

theorem DefsOk.below : ∀ (ds : List (Nat × Def)), DefsOk ds → ∀ p ∈ ds, p.2.Below p.1
  | [], _, _, hp => by simp at hp
  | (i, d) :: r, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.2.1
    · exact DefsOk.below r h.2.2 p hp

theorem defsVal_valid (e : Env) :
    ∀ ds : List (Nat × Def), DefsOk ds →
      ∀ p ∈ ds, defsVal e ds p.1 = p.2.val e (defsVal e ds)
  | [], _, _, hp => by simp at hp
  | (i, d) :: r, h, p, hp => by
    have agree : ∀ j, j < i → defsVal e r j = defsVal e ((i, d) :: r) j := fun j hj => by
      simp only [defsVal]; rw [if_neg (by omega)]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [defsVal, if_pos]
      exact Def.val_congr e _ _ _ _ h.2.1 agree
    · have hpi := h.1 p hp
      rw [← agree _ hpi, defsVal_valid e r h.2.2 p hp]
      exact Def.val_congr e _ _ _ _ (DefsOk.below r h.2.2 p hp) fun j hj => agree j (by omega)

/-- **A valuation exists** for a well-formed table. -/
theorem Tab.WF.valid {tb : Tab} (h : tb.WF) (e : Env) : Tab.Valid e (defsVal e tb.defs) tb :=
  fun p hp => defsVal_valid e tb.defs h.ok p hp

/-! ## The spec's symbolic run keeps the shape

Generic: an `Ops` record whose operations keep a property `V` of values (relative to the
threaded state), whose S-box keeps a property `Q` of the state, and whose S-box keeps `V` of
earlier values. -/

section Generic

variable {α σ : Type} {A : Ops α σ} {Q : σ → Prop} {V : σ → α → Prop}

structure OpsInv (A : Ops α σ) (Q : σ → Prop) (V : σ → α → Prop) : Prop where
  zero : ∀ st, V st A.zero
  add : ∀ st a b, V st a → V st b → V st (A.add a b)
  addC : ∀ st a c, V st a → V st (A.addC a c)
  mulC : ∀ st a c, V st a → V st (A.mulC a c)
  sbox : ∀ st a, Q st → V st a → Q (A.sbox a st).2 ∧ V (A.sbox a st).2 (A.sbox a st).1
  mono : ∀ st a b, Q st → V st a → V st b → V (A.sbox a st).2 b

/-- Every element of `xs` has `V st`. -/
def AllV (V : σ → α → Prop) (st : σ) (xs : List α) : Prop := ∀ x ∈ xs, V st x

theorem m4_inv (H : OpsInv A Q V) (st : σ) (a b c d : α) (ha : V st a) (hb : V st b)
    (hc : V st c) (hd : V st d) : AllV V st (m4 A a b c d) := by
  have hm := fun x k (hx : V st x) => H.mulC st x k hx
  intro x hx
  simp only [m4, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    exact H.add _ _ _ (H.add _ _ _ (hm _ _ ha) (hm _ _ hb)) (H.add _ _ _ (hm _ _ hc) (hm _ _ hd))

theorem allV_cons {st : σ} {x : α} {xs : List α} (h : AllV V st (x :: xs)) :
    V st x ∧ AllV V st xs :=
  ⟨h x List.mem_cons_self, fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem m4Blocks_inv (H : OpsInv A Q V) (st : σ) :
    ∀ xs : List α, AllV V st xs → AllV V st (m4Blocks A xs)
  | a :: b :: c :: d :: r, h => by
    obtain ⟨ha, h⟩ := allV_cons h
    obtain ⟨hb, h⟩ := allV_cons h
    obtain ⟨hc, h⟩ := allV_cons h
    obtain ⟨hd, h⟩ := allV_cons h
    intro x hx
    simp only [m4Blocks, List.mem_append] at hx
    rcases hx with hx | hx
    · exact m4_inv H st a b c d ha hb hc hd x hx
    · exact m4Blocks_inv H st r h x hx
  | [], h => by simpa [m4Blocks] using h
  | [_], h => by simpa [m4Blocks] using h
  | [_, _], h => by simpa [m4Blocks] using h
  | [_, _, _], h => by simpa [m4Blocks] using h

theorem sum_inv (H : OpsInv A Q V) (st : σ) : ∀ xs : List α, AllV V st xs → V st (sum A xs)
  | [], _ => H.zero st
  | _ :: xs, h => H.add _ _ _ (allV_cons h).1 (sum_inv H st xs (allV_cons h).2)

theorem colSums_inv (H : OpsInv A Q V) (st : σ) :
    ∀ xs : List α, AllV V st xs →
      V st (colSums A xs).1 ∧ V st (colSums A xs).2.1 ∧ V st (colSums A xs).2.2.1 ∧
        V st (colSums A xs).2.2.2
  | a :: b :: c :: d :: r, h => by
    obtain ⟨ha, h⟩ := allV_cons h
    obtain ⟨hb, h⟩ := allV_cons h
    obtain ⟨hc, h⟩ := allV_cons h
    obtain ⟨hd, h⟩ := allV_cons h
    obtain ⟨h1, h2, h3, h4⟩ := colSums_inv H st r h
    exact ⟨H.add _ _ _ ha h1, H.add _ _ _ hb h2, H.add _ _ _ hc h3, H.add _ _ _ hd h4⟩
  | [], _ => ⟨H.zero st, H.zero st, H.zero st, H.zero st⟩
  | [_], _ => ⟨H.zero st, H.zero st, H.zero st, H.zero st⟩
  | [_, _], _ => ⟨H.zero st, H.zero st, H.zero st, H.zero st⟩
  | [_, _, _], _ => ⟨H.zero st, H.zero st, H.zero st, H.zero st⟩

theorem addColSums_inv (H : OpsInv A Q V) (st : σ) (s : α × α × α × α)
    (hs : V st s.1 ∧ V st s.2.1 ∧ V st s.2.2.1 ∧ V st s.2.2.2) :
    ∀ xs : List α, AllV V st xs → AllV V st (addColSums A s xs)
  | a :: b :: c :: d :: r, h => by
    obtain ⟨ha, h⟩ := allV_cons h
    obtain ⟨hb, h⟩ := allV_cons h
    obtain ⟨hc, h⟩ := allV_cons h
    obtain ⟨hd, h⟩ := allV_cons h
    have := addColSums_inv H st s hs r h
    intro x hx
    simp only [addColSums, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · exact H.add _ _ _ ha hs.1
    · exact H.add _ _ _ hb hs.2.1
    · exact H.add _ _ _ hc hs.2.2.1
    · exact H.add _ _ _ hd hs.2.2.2
    · exact this x hx
  | [], h => by simpa [addColSums] using h
  | [_], h => by simpa [addColSums] using h
  | [_, _], h => by simpa [addColSums] using h
  | [_, _, _], h => by simpa [addColSums] using h

theorem external_inv (H : OpsInv A Q V) (st : σ) (xs : List α) (h : AllV V st xs) :
    AllV V st (external A xs) := by
  have hmap : ∀ ys : List α, AllV V st ys → AllV V st (ys.map fun x => A.add x (sum A ys)) :=
    fun ys hy x hx => by
      obtain ⟨y, hy', rfl⟩ := List.mem_map.mp hx
      exact H.add _ _ _ (hy y hy') (sum_inv H st ys hy)
  have hgen : AllV V st (addColSums A (colSums A (m4Blocks A xs)) (m4Blocks A xs)) := by
    have hm := m4Blocks_inv H st xs h
    exact addColSums_inv H st _ (colSums_inv H st _ hm) _ hm
  match xs, h, hgen with
  | [a, b], h, _ => exact hmap _ h
  | [a, b, c], h, _ => exact hmap _ h
  | [a, b, c, d], h, _ =>
    obtain ⟨ha, h⟩ := allV_cons h
    obtain ⟨hb, h⟩ := allV_cons h
    obtain ⟨hc, h⟩ := allV_cons h
    obtain ⟨hd, -⟩ := allV_cons h
    exact m4_inv H st a b c d ha hb hc hd
  | [], _, hg => exact hg
  | [_], _, hg => exact hg
  | _ :: _ :: _ :: _ :: _ :: _, _, hg => exact hg

theorem zipWith_mulC_inv (H : OpsInv A Q V) (st : σ) (s : α) (hs : V st s) :
    ∀ (xs : List α) (d : List Nat), AllV V st xs →
      AllV V st (List.zipWith (fun x di => A.add (A.mulC x di) s) xs d)
  | [], _, _ => by simp [AllV]
  | _ :: _, [], _ => by simp [AllV]
  | x :: xs, di :: d, h => by
    intro y hy
    simp only [List.zipWith_cons_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact H.add _ _ _ (H.mulC _ _ _ (allV_cons h).1) hs
    · exact zipWith_mulC_inv H st s hs xs d (allV_cons h).2 y hy

theorem internal_inv (H : OpsInv A Q V) (st : σ) (d : List Nat) (xs : List α)
    (h : AllV V st xs) : AllV V st (internal A d xs) :=
  zipWith_mulC_inv H st _ (sum_inv H st xs h) xs d h

theorem zipWith_addC_inv (H : OpsInv A Q V) (st : σ) :
    ∀ (xs : List α) (rc : List Nat), AllV V st xs → AllV V st (List.zipWith A.addC xs rc)
  | [], _, _ => by simp [AllV]
  | _ :: _, [], _ => by simp [AllV]
  | x :: xs, c :: rc, h => by
    intro y hy
    simp only [List.zipWith_cons_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact H.addC _ _ _ (allV_cons h).1
    · exact zipWith_addC_inv H st xs rc (allV_cons h).2 y hy

/-- What the stateful functions keep: the state property, the results, and older values. -/
def Keeps (Q : σ → Prop) (V : σ → α → Prop) (st : σ) (r : List α × σ) : Prop :=
  Q r.2 ∧ AllV V r.2 r.1 ∧ ∀ b, V st b → V r.2 b

theorem Keeps.trans {st : σ} {r r' : List α × σ} (h1 : Keeps Q V st r) (h2 : Keeps Q V r.2 r') :
    Keeps Q V st (r'.1, r'.2) :=
  ⟨h2.1, h2.2.1, fun b hb => h2.2.2 b (h1.2.2 b hb)⟩

theorem sboxAll_inv (H : OpsInv A Q V) :
    ∀ (xs : List α) (st : σ), Q st → AllV V st xs → Keeps Q V st (sboxAll A xs st)
  | [], st, hq, _ => ⟨hq, by simp [AllV, sboxAll], fun _ hb => hb⟩
  | x :: xs, st, hq, h => by
    obtain ⟨hx, h⟩ := allV_cons h
    obtain ⟨hq1, hv1⟩ := H.sbox st x hq hx
    have hm1 : ∀ b, V st b → V (A.sbox x st).2 b := fun b hb => H.mono st x b hq hx hb
    obtain ⟨hq2, hv2, hm2⟩ :=
      sboxAll_inv H xs (A.sbox x st).2 hq1 fun y hy => hm1 y (h y hy)
    refine ⟨hq2, ?_, fun b hb => hm2 b (hm1 b hb)⟩
    intro y hy
    simp only [sboxAll, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hm2 _ hv1
    · exact hv2 y hy

theorem fullRounds_inv (H : OpsInv A Q V) :
    ∀ (rcs : List (List Nat)) (xs : List α) (st : σ), Q st → AllV V st xs →
      Keeps Q V st (fullRounds A rcs xs st)
  | [], xs, st, hq, h => ⟨hq, h, fun _ hb => hb⟩
  | rc :: rcs, xs, st, hq, h => by
    have h1 := sboxAll_inv H _ st hq (zipWith_addC_inv H st xs rc h)
    have h2 := fullRounds_inv H rcs _ _ h1.1 (external_inv H _ _ h1.2.1)
    exact h1.trans h2

theorem partialRounds_inv (H : OpsInv A Q V) (d : List Nat) :
    ∀ (rcs : List Nat) (xs : List α) (st : σ), Q st → AllV V st xs →
      Keeps Q V st (partialRounds A d rcs xs st)
  | [], xs, st, hq, h => ⟨hq, h, fun _ hb => hb⟩
  | _ :: _, [], st, hq, _ => ⟨hq, by simp [AllV, partialRounds], fun _ hb => hb⟩
  | rc :: rcs, x :: xs, st, hq, h => by
    obtain ⟨hx, h⟩ := allV_cons h
    have hx' := H.addC st x rc hx
    obtain ⟨hq1, hv1⟩ := H.sbox st _ hq hx'
    have hm1 : ∀ b, V st b → V (A.sbox (A.addC x rc) st).2 b :=
      fun b hb => H.mono st _ b hq hx' hb
    have hall : AllV V (A.sbox (A.addC x rc) st).2 ((A.sbox (A.addC x rc) st).1 :: xs) := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hv1
      · exact hm1 y (h y hy)
    have h2 := partialRounds_inv H d rcs _ _ hq1 (internal_inv H _ d _ hall)
    exact ⟨h2.1, h2.2.1, fun b hb => h2.2.2 b (hm1 b hb)⟩

theorem permG_inv (H : OpsInv A Q V) (c : Params) (xs : List α) (st : σ) (hq : Q st)
    (h : AllV V st xs) : Keeps Q V st (permG A c xs st) := by
  unfold permG
  have h1 := fullRounds_inv H (c.rcExternal.take (c.roundsF / 2)) _ st hq (external_inv H st xs h)
  have h2 := partialRounds_inv H c.diagM1 c.rcInternal _ _ h1.1 h1.2.1
  have h3 := fullRounds_inv H (c.rcExternal.drop (c.roundsF / 2)) _ _ h2.1 h2.2.1
  exact (h1.trans h2).trans h3

theorem spongeStateG_inv (H : OpsInv A Q V) (st : σ) (t : Nat) (xs : List α)
    (h : AllV V st xs) : AllV V st (spongeStateG A t xs) := by
  intro x hx
  simp only [spongeStateG, List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with (hx | ⟨-, rfl⟩) | rfl
  · exact h x hx
  · exact H.zero st
  · exact H.addC _ _ _ (H.zero st)

end Generic

/-- `linOps` keeps forms over atoms of the table, and the table well-formed. -/
theorem linOps_inv : OpsInv linOps Tab.WF (fun tb l => l.Below tb.next) where
  zero _ := by intro p hp; simp [linOps] at hp
  add _ _ _ ha hb := Lin.below_add ha hb
  addC _ _ _ ha := Lin.below_add ha (Lin.below_const _ _)
  mulC _ _ c ha := Lin.below_scale ha c
  sbox st a hq ha := by
    have := Tab.sbox_wf st a hq ha
    exact ⟨this.1.1, this.2⟩
  mono st a b hq ha hb := hb.mono (Tab.sbox_wf st a hq ha).1.2

/-! ## The checker's run keeps the shape -/

/-- The table is well-formed and every form on the stack or in memory names its atoms. -/
structure St.Inv (st : St) : Prop where
  wf : st.tab.WF
  stk : ∀ v ∈ st.stk, v.Below st.tab.next
  mem : ∀ x ∈ st.mem, x.2.Below st.tab.next

theorem St.Inv.init : St.Inv St.init :=
  ⟨⟨by simp [St.init, Tab.empty], trivial⟩, by simp [St.init], by simp [St.init]⟩

/-- The gas a state records plays no part in `St.Inv`. -/
theorem St.Inv.charge {st : St} (g : Nat) (h : st.Inv) : ({ st with gas := g } : St).Inv :=
  ⟨h.wf, h.stk, h.mem⟩

private theorem ok_bind {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {y : β}
    (h : m >>= f = .ok y) : ∃ x, m = .ok x ∧ f x = .ok y := by
  cases m with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

theorem toLin_inv {v : SV} {tb : Tab} {r : Lin × Nat × Tab} (h : toLin v tb = .ok r)
    (hw : tb.WF) (hv : v.Below tb.next) : tb.Grows r.2.2 ∧ r.1.Below r.2.2.next := by
  unfold toLin at h
  cases v with
  | word w =>
    simp only at h
    split at h
    · cases h; exact ⟨Tab.Grows.refl hw, Lin.below_const _ _⟩
    · cases h; exact Tab.atom_wf tb _ hw trivial
  | lin l b => cases h; exact ⟨Tab.Grows.refl hw, hv⟩
  | pw _ _ _ => cases h

theorem toPow_inv {v : SV} {tb : Tab} {r : Nat × Lin × Nat × Tab} (h : toPow v tb = .ok r)
    (hw : tb.WF) (hv : v.Below tb.next) : tb.Grows r.2.2.2 ∧ r.2.1.Below r.2.2.2.next := by
  unfold toPow at h
  split at h
  · cases h; exact ⟨Tab.Grows.refl hw, hv⟩
  · obtain ⟨q, hq, h2⟩ := ok_bind h
    cases h2
    have := toLin_inv hq hw hv
    exact this

theorem scaleMod_inv {v : SV} {c : Nat} {tb : Tab} {r : SV × Tab} (h : scaleMod v c tb = .ok r)
    (hw : tb.WF) (hv : v.Below tb.next) : tb.Grows r.2 ∧ r.1.Below r.2.next := by
  unfold scaleMod at h
  split at h
  · cases h; exact ⟨Tab.Grows.refl hw, trivial⟩
  · split at h
    · cases h; exact ⟨Tab.Grows.refl hw, hv⟩
    · obtain ⟨q, hq, h2⟩ := ok_bind h
      cases h2
      have := toLin_inv hq hw hv
      exact ⟨this.1, Lin.below_scale (n := q.2.2.next) this.2 c⟩

theorem mulModP_inv {a b : SV} {tb : Tab} {r : SV × Tab} (h : mulModP a b tb = .ok r)
    (hw : tb.WF) (ha : a.Below tb.next) (hb : b.Below tb.next) :
    tb.Grows r.2 ∧ r.1.Below r.2.next := by
  unfold mulModP at h
  split at h
  · cases h; exact ⟨Tab.Grows.refl hw, trivial⟩
  · exact scaleMod_inv h hw hb
  · exact scaleMod_inv h hw ha
  · obtain ⟨⟨ca, la, ka, tb1⟩, h1, h'⟩ := ok_bind h
    obtain ⟨⟨cb, lb, kb, tb2⟩, h2, h''⟩ := ok_bind h'
    obtain ⟨g1, l1⟩ := toPow_inv h1 hw ha
    obtain ⟨g2, -⟩ := toPow_inv h2 g1.1 (hb.mono g1.2)
    have l1' : la.Below tb2.next := Lin.Below.mono (n := tb1.next) l1 g2.2
    dsimp only at h''
    split at h''
    · cases h''
    · split at h''
      · cases h''; exact ⟨g1.trans g2, l1'⟩
      · split at h''
        · cases h''
          have := Tab.sbox_wf tb2 la g2.1 l1'
          exact ⟨(g1.trans g2).trans this.1,
            Lin.below_scale (n := (tb2.sbox la).2.next) this.2 _⟩
        · cases h''

theorem wordBin_word {fs : Facts} {op : Nat} {a b v : SV} (h : wordBin fs op a b = .ok v) :
    ∀ n, v.Below n := by
  unfold wordBin at h
  obtain ⟨wa, -, h⟩ := ok_bind h
  obtain ⟨wb, -, h⟩ := ok_bind h
  split at h
  · cases h; intro n; trivial
  · cases h

theorem addMul_inv {fs : Facts} {op : Nat} {a b : SV} {tb : Tab} {r : SV × Tab}
    (h : addMul fs op a b tb = .ok r) (hw : tb.WF) (ha : a.Below tb.next) (hb : b.Below tb.next) :
    tb.Grows r.2 ∧ r.1.Below r.2.next := by
  unfold addMul at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨Tab.Grows.refl hw, wordBin_word ‹wordBin _ _ _ _ = Except.ok _› _⟩)
    | (cases h
       have i1 := toLin_inv ‹toLin _ tb = Except.ok _› hw (by trivial)
       have i2 := toLin_inv ‹toLin _ (Prod.snd (Prod.snd _)) = Except.ok _› i1.1.1
         (SV.Below.mono (by trivial) i1.1.2)
       exact ⟨i1.1.trans i2.1, Lin.below_add (Lin.Below.mono i1.2 i2.1.2) i2.2⟩)
    | (cases h
       have i1 := toLin_inv ‹toLin _ tb = Except.ok _› hw (by trivial)
       exact ⟨i1.1, Lin.below_scale i1.2 _⟩)

theorem push_inv {s s' : St} {v : SV} (h : push s v = .ok s') (hs : s.Inv)
    (hv : v.Below s.tab.next) : s'.Inv := by
  unfold push at h
  split at h
  · cases h
    refine ⟨hs.wf, ?_, hs.mem⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact hs.stk x hx
  · cases h

theorem pop1_inv {s : St} {r : SV × St} (h : pop1 s = .ok r) (hs : s.Inv) :
    r.2.Inv ∧ r.1.Below r.2.tab.next ∧ r.2.tab = s.tab := by
  unfold pop1 at h
  split at h
  · cases h
    rename_i a t hst
    exact ⟨⟨hs.wf, fun x hx => hs.stk x (by rw [hst]; exact List.mem_cons_of_mem _ hx),
      hs.mem⟩,
      hs.stk a (by rw [hst]; exact List.mem_cons_self), rfl⟩
  · cases h

theorem pop2_inv {s : St} {r : SV × SV × St} (h : pop2 s = .ok r) (hs : s.Inv) :
    r.2.2.Inv ∧ r.1.Below r.2.2.tab.next ∧ r.2.1.Below r.2.2.tab.next ∧
      r.2.2.tab = s.tab := by
  unfold pop2 at h
  split at h
  · cases h
    rename_i a b t hst
    exact ⟨⟨hs.wf, fun x hx => hs.stk x (by rw [hst]; simp [hx]), hs.mem⟩,
      hs.stk a (by rw [hst]; simp), hs.stk b (by rw [hst]; simp), rfl⟩
  · cases h

theorem pop3_inv {s : St} {r : SV × SV × SV × St} (h : pop3 s = .ok r) (hs : s.Inv) :
    r.2.2.2.Inv ∧ r.1.Below r.2.2.2.tab.next ∧ r.2.1.Below r.2.2.2.tab.next ∧
      r.2.2.1.Below r.2.2.2.tab.next ∧ r.2.2.2.tab = s.tab := by
  unfold pop3 at h
  split at h
  · cases h
    rename_i a b c t hst
    exact ⟨⟨hs.wf, fun x hx => hs.stk x (by rw [hst]; simp [hx]), hs.mem⟩,
      hs.stk a (by rw [hst]; simp), hs.stk b (by rw [hst]; simp),
      hs.stk c (by rw [hst]; simp), rfl⟩
  · cases h

theorem St.Inv.tab {s : St} {tb : Tab} (hs : s.Inv) (hg : s.tab.Grows tb) :
    ({ s with tab := tb } : St).Inv :=
  ⟨hg.1, fun v hv => (hs.stk v hv).mono hg.2, fun x hx => (hs.mem x hx).mono hg.2⟩

theorem writeMem_mem (a : Nat) (v : SV) : ∀ (mem mem' : List (Nat × SV)),
    writeMem a v mem = .ok mem' → ∀ x ∈ mem', x = (a, v) ∨ x ∈ mem
  | [], mem', h, x, hx => by
    simp only [writeMem] at h; cases h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact Or.inl hx
  | (k, w) :: r, mem', h, x, hx => by
    simp only [writeMem] at h
    split at h
    · cases h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ hx)
    · split at h
      · cases hw : writeMem a v r with
        | error _ => rw [hw] at h; cases h
        | ok r' =>
          rw [hw] at h; cases h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inr List.mem_cons_self
          · rcases writeMem_mem a v r r' hw x hx with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem _ h)
      · cases h

theorem mstore_inv {s s' : St} {a : Nat} {v : SV} (h : mstore s a v = .ok s') (hs : s.Inv)
    (hv : v.Below s.tab.next) : s'.Inv := by
  unfold mstore at h
  obtain ⟨m, hm, h2⟩ := ok_bind h
  cases h2
  refine ⟨hs.wf, hs.stk, ?_⟩
  intro x hx
  rcases writeMem_mem a v s.mem m hm x hx with rfl | hx
  · exact hv
  · exact hs.mem x hx

theorem mstore_tab {s s' : St} {a : Nat} {v : SV} (h : mstore s a v = .ok s') : s'.tab = s.tab := by
  unfold mstore at h
  obtain ⟨m, -, h2⟩ := ok_bind h
  cases h2; rfl

theorem zeroFill_inv : ∀ (k d : Nat) (s s' : St), zeroFill s k d = .ok s' → s.Inv → s'.Inv
  | 0, _, s, s', h, hs => by cases h; exact hs
  | k + 1, d, s, s', h, hs => by
    obtain ⟨s1, h1, h2⟩ := ok_bind h
    exact zeroFill_inv k _ s1 s' h2 (mstore_inv h1 hs trivial)

theorem cdCopy_inv (fs : Facts) : ∀ (k d src : Nat) (s s' : St), cdCopy fs s k d src = .ok s' →
    s.Inv → s'.Inv
  | 0, _, _, s, s', h, hs => by cases h; exact hs
  | k + 1, d, src, s, s', h, hs => by
    obtain ⟨s1, h1, h2⟩ := ok_bind h
    exact cdCopy_inv fs k _ _ s1 s' h2 (mstore_inv h1 hs trivial)

theorem codeCopy_go_inv : ∀ (k d : Nat) (bs : List Nat) (s s' : St),
    codeCopy.go bs s k d = .ok s' → s.Inv → s'.Inv
  | 0, _, _, s, s', h, hs => by cases h; exact hs
  | k + 1, d, bs, s, s', h, hs => by
    obtain ⟨s1, h1, h2⟩ := ok_bind h
    exact codeCopy_go_inv k _ _ s1 s' h2 (mstore_inv h1 hs trivial)

theorem readMem_below (a n : Nat) : ∀ (mem : List (Nat × SV)) (v : SV), readMem a mem = .ok v →
    (∀ x ∈ mem, x.2.Below n) → v.Below n
  | [], v, h, _ => by simp only [readMem] at h; cases h; trivial
  | (k, w) :: r, v, h, hm => by
    simp only [readMem] at h
    split at h
    · cases h; exact hm _ List.mem_cons_self
    · split at h
      · exact readMem_below a n r v h fun x hx => hm x (List.mem_cons_of_mem _ hx)
      · cases h

theorem set_set_below {n : Nat} {l : List SV} (hl : ∀ v ∈ l, v.Below n) {a b : SV}
    (ha : a.Below n) (hb : b.Below n) (i j : Nat) : ∀ v ∈ (l.set i b).set j a, v.Below n := by
  intro v hv
  rcases List.mem_or_eq_of_mem_set hv with hv | rfl
  · rcases List.mem_or_eq_of_mem_set hv with hv | rfl
    · exact hl v hv
    · exact hb
  · exact ha

theorem SV.below_lin {n : Nat} {v : SV} {l : Lin} {b : Nat} (hv : v.Below n) (h : v = .lin l b) :
    l.Below n := by
  subst h; exact hv

theorem SV.below_eq {n : Nat} {v w : SV} (hv : v.Below n) (h : v = w) : w.Below n := h ▸ hv

/-- A successful `step` keeps `St.Inv`. -/
theorem step_inv (fs : Facts) (code : Code) (i : Ins) (st st' : St)
    (h : step fs code i st = .ok st') (hs : st.Inv) : st'.Inv := by
  unfold Poseidon2.Checker.step at h
  simp only [bind, Except.bind, exactOf, Poseidon2.Checker.codeCopy] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hs)
    | exact push_inv h hs trivial
    | exact push_inv h hs (hs.stk _ (List.mem_of_getElem? ‹st.stk[_]? = some _›))
    | (cases h
       exact ⟨hs.wf, set_set_below hs.stk
         (hs.stk _ (by rw [‹st.stk = _ :: _›]; exact List.mem_cons_self))
         (hs.stk _ (List.mem_of_getElem? ‹st.stk[_]? = some _›)) _ _, hs.mem⟩)
    | (cases h; exact (pop1_inv ‹pop1 st = _› hs).1)
    | exact push_inv h (pop1_inv ‹pop1 st = _› hs).1 trivial
    | exact push_inv h (pop2_inv ‹pop2 st = _› hs).1 trivial
    | exact push_inv h (pop3_inv ‹pop3 st = _› hs).1 trivial
    | exact push_inv h (pop2_inv ‹pop2 st = _› hs).1 (wordBin_word ‹wordBin _ _ _ _ = _› _)
    | (have p := pop2_inv ‹pop2 st = _› hs
       have m := addMul_inv ‹addMul _ _ _ _ _ = _› p.1.wf p.2.1 p.2.2.1
       exact push_inv h (p.1.tab m.1) m.2)
    | (have p := pop2_inv ‹pop2 st = _› hs
       exact push_inv h p.1 (Lin.below_scale (SV.below_lin p.2.2.1 ‹_ = SV.lin _ _›) _))
    | (have p := pop2_inv ‹pop2 st = _› hs
       exact push_inv h p.1 (SV.below_eq p.2.1 ‹_ = SV.pw _ _ _›))
    | (have p := pop2_inv ‹pop2 st = _› hs
       have i := toLin_inv ‹toLin _ (St.tab _) = _› p.1.wf p.2.1
       exact push_inv h (p.1.tab i.1) i.2)
    | (have p := pop3_inv ‹pop3 st = _› hs
       have i1 := toLin_inv ‹toLin _ (St.tab _) = Except.ok _› p.1.wf p.2.1
       have i2 := toLin_inv ‹toLin _ (Prod.snd (Prod.snd _)) = Except.ok _› i1.1.1
         (p.2.2.1.mono i1.1.2)
       exact push_inv h (p.1.tab (i1.1.trans i2.1))
         (Lin.below_add (Lin.Below.mono i1.2 i2.1.2) i2.2))
    | (have p := pop3_inv ‹pop3 st = _› hs
       have m := mulModP_inv ‹mulModP _ _ _ = _› p.1.wf p.2.1 p.2.2.1
       exact push_inv h (p.1.tab m.1) m.2)
    | (have p := pop1_inv ‹pop1 st = _› hs
       exact push_inv h ⟨p.1.wf, p.1.stk, p.1.mem⟩
         (readMem_below _ _ _ _ ‹readMem _ _ = _› p.1.mem))
    | (have p := pop2_inv ‹pop2 st = _› hs
       exact mstore_inv h p.1 p.2.2.1)
    | exact zeroFill_inv _ _ _ _ h (pop3_inv ‹pop3 st = _› hs).1
    | exact cdCopy_inv fs _ _ _ _ _ h (pop3_inv ‹pop3 st = _› hs).1
    | exact codeCopy_go_inv _ _ _ _ _ h (pop3_inv ‹pop3 st = _› hs).1

/-- What `ctl` continues with keeps `St.Inv`. -/
theorem ctl_inv' {fs : Facts} {code : Code} {pc : Nat} {i : Ins} {st st' : St}
    (h : (∃ t, ctl fs code pc i st = .jump t st') ∨ ctl fs code pc i st = .fall st')
    (hs : st.Inv) : st'.Inv := by
  rcases h with ⟨t, h⟩ | h <;>
  · unfold ctl at h
    dsimp only at h
    split at h
    all_goals
      repeat' (split at h)
    all_goals first
      | (cases h; done)
      | (cases h; exact (pop1_inv ‹pop1 st = _› hs).1)
      | (cases h; exact (pop2_inv ‹pop2 st = _› hs).1)
      | (cases h; exact step_inv fs code _ st _ ‹_› hs)

theorem step1_inv {fs : Facts} {code : Code} {is is' : List (Nat × Ins)} {st st' : St}
    (h : step1 fs code is st = .next is' st') (hs : st.Inv) : st'.Inv := by
  match is, h with
  | (p, i) :: rest, h =>
    simp only [step1] at h
    split at h
    · cases h; exact (ctl_inv' (Or.inr ‹ctl _ _ _ _ _ = .fall _›) hs).charge _
    · split at h
      · cases h; exact (ctl_inv' (Or.inl ⟨_, ‹ctl _ _ _ _ _ = .jump _ _›⟩) hs).charge _
      · cases h
    · cases h

/-- Along the run the checker keeps `St.Inv`. -/
theorem runN_inv' {fs : Facts} {code : Code} :
    ∀ (k : Nat) (is is' : List (Nat × Ins)) (st st' : St),
      runN fs code k is st = .next is' st' → st.Inv → st'.Inv
  | 0, _, _, _, _, h, hs => by
    simp only [runN, Out.next.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hs
  | k + 1, is, is', st, st', h, hs => by
    simp only [runN] at h
    split at h
    · exact runN_inv' k _ is' _ st' h (step1_inv ‹_› hs)
    · cases h

/-! ## The spec's forms and their values -/

/-- The input words of a case's expectation. -/
def Expect.inputs : Expect → List Term
  | .perm _ ins => ins
  | .permHead _ ins => ins
  | .hash _ ins => ins
  | .revertEmpty => []

/-- The words a case's expectation returns for a call. -/
def specWords (e : Env) : Expect → List Nat
  | .perm c ins => permutationWords c (ins.map (·.eval e))
  | .permHead c ins => [(permutationWords c (ins.map (·.eval e))).headD 0]
  | .hash c ins => [hashWords c (ins.map (·.eval e))]
  | .revertEmpty => []

/-- The first input form and the table after it. -/
def inputForm (fs : Facts) (t : Term) (tb : Tab) : Lin × Tab :=
  match (mkInput fs t full).exact with
  | some v => (Lin.const v, tb)
  | none => tb.atom (.word t)

theorem inputForms_cons (fs : Facts) (t : Term) (ts : List Term) (tb : Tab) :
    inputForms fs (t :: ts) tb =
      ((inputForm fs t tb).1 :: (inputForms fs ts (inputForm fs t tb).2).1,
        (inputForms fs ts (inputForm fs t tb).2).2) := by
  unfold inputForm
  cases hx : (mkInput fs t full).exact <;>
  · simp only [inputForms, hx]

theorem inputForm_inv (fs : Facts) (t : Term) (tb : Tab) (hw : tb.WF) :
    tb.Grows (inputForm fs t tb).2 ∧ (inputForm fs t tb).1.Below (inputForm fs t tb).2.next := by
  unfold inputForm
  split
  · exact ⟨Tab.Grows.refl hw, Lin.below_const _ _⟩
  · exact Tab.atom_wf tb _ hw trivial

theorem inputForms_inv (fs : Facts) : ∀ (ins : List Term) (tb : Tab), tb.WF →
    tb.Grows (inputForms fs ins tb).2 ∧
      AllV (fun tb l => l.Below tb.next) (inputForms fs ins tb).2 (inputForms fs ins tb).1
  | [], tb, hw => ⟨Tab.Grows.refl hw, by simp [AllV, inputForms]⟩
  | t :: ts, tb, hw => by
    rw [inputForms_cons]
    have h1 := inputForm_inv fs t tb hw
    have h2 := inputForms_inv fs ts _ h1.1.1
    refine ⟨h1.1.trans h2.1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Lin.Below.mono h1.2 h2.1.2
    · exact h2.2 x hx

theorem inputForm_sound (e : Env) (ρ : Nat → F) (fs : Facts) (hf : Facts.Hold e fs) (t : Term)
    (tb : Tab) (ht : t.eval e < W) (hv : Tab.Valid e ρ (inputForm fs t tb).2) :
    (inputForm fs t tb).1.eval ρ = ((t.eval e : Nat) : F) ∧ Tab.Valid e ρ tb := by
  revert hv
  unfold inputForm
  split
  · rename_i v hx
    intro hv
    have hm := mkInput_sound e fs hf t full (full_sound _ ht) ht
    refine ⟨?_, hv⟩
    rw [Lin.eval_const, ← Word.holds_exact e _ hm.1 v hx, hm.2]
  · intro hv
    exact Tab.atom_spec e ρ tb _ hv

theorem inputForms_sound (e : Env) (ρ : Nat → F) (fs : Facts) (hf : Facts.Hold e fs) :
    ∀ (ins : List Term) (tb : Tab), (∀ t ∈ ins, t.eval e < W) →
      Tab.Valid e ρ (inputForms fs ins tb).2 →
      (inputForms fs ins tb).1.map (Lin.eval ρ) = ins.map (fun t => ((t.eval e : Nat) : F)) ∧
        Tab.Valid e ρ tb
  | [], tb, _, hv => ⟨rfl, hv⟩
  | t :: ts, tb, hin, hv => by
    rw [inputForms_cons] at hv ⊢
    obtain ⟨h2, hv1⟩ := inputForms_sound e ρ fs hf ts _
      (fun t' h' => hin t' (List.mem_cons_of_mem _ h')) hv
    have h1 := inputForm_sound e ρ fs hf t tb (hin t List.mem_cons_self) hv1
    refine ⟨?_, h1.2⟩
    rw [List.map_cons, List.map_cons, h2, h1.1]

/-- Returned words that match the spec's forms are the forms' values. -/
theorem outputsMatch_sound (e : Env) (ρ : Nat → F) :
    ∀ (ws : List SV) (fs : List Lin) (xs : List Nat), outputsMatch ws fs = true →
      List.Forall₂ (fun w x => w.Rel e ρ x) ws xs → xs = fs.map fun l => (l.eval ρ).val
  | [], [], [], _, _ => rfl
  | .lin l b :: ws, f :: fs, x :: xs, h, hr => by
    simp only [outputsMatch, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, hl⟩, h⟩ := h
    obtain ⟨⟨hxb, -, hx⟩, hr'⟩ := List.forall₂_cons.mp hr
    rw [← Lin.beq_eq l f hl, List.map_cons, ← hx, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      outputsMatch_sound e ρ ws fs xs h hr']
  | .word w :: ws, f :: fs, x :: xs, h, hr => by
    simp only [outputsMatch] at h
    split at h
    · rename_i v hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hvP, hl⟩, h⟩ := h
      obtain ⟨⟨hw, hx⟩, hr'⟩ := List.forall₂_cons.mp hr
      rw [← Lin.beq_eq _ f hl, List.map_cons, Lin.eval_const, ZMod.val_natCast,
        Nat.mod_eq_of_lt hvP, hx, Word.holds_exact e w hw v hv,
        outputsMatch_sound e ρ ws fs xs h hr']
    · cases h
  | .pw _ _ _ :: _, _ :: _, _, h, _ => by simp [outputsMatch] at h
  | [], _ :: _, _, h, _ => by simp [outputsMatch] at h
  | _ :: _, [], _, h, _ => by simp [outputsMatch] at h
  | [], [], _ :: _, _, hr => by cases hr
  | _ :: _, _ :: _, [], _, hr => by cases hr

/-- `permutationWords` reads its words in the field one by one. -/
theorem permutationWords_eq (c : Params) (ws : List Nat) :
    permutationWords c ws = (permutation c (ws.map fun w : Nat => (w : F))).map ZMod.val := by
  unfold permutationWords
  congr 2
  induction ws with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem hashWords_eq (c : Params) (ws : List Nat) :
    hashWords c ws = (Spec.hash c (ws.map fun w : Nat => (w : F))).val := by
  unfold hashWords
  congr 2
  induction ws with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem map_eval_cast (e : Env) (ins : List Term) :
    (ins.map fun t : Term => (t.eval e : Nat)).map (fun w : Nat => (w : F)) =
      ins.map fun t => ((t.eval e : Nat) : F) := by
  rw [List.map_map]; rfl

/-- **The spec side**: for a well-formed table at the end of the run there is a valuation valid
on it under which the spec's forms are the words the case expects. -/
theorem spec_sound (e : Env) (fs : Facts) (hf : Facts.Hold e fs) (ex : Expect) (tb : Tab)
    (hw : tb.WF) (hin : ∀ t ∈ ex.inputs, t.eval e < W) :
    ∃ ρ, Tab.Valid e ρ tb ∧
      (specForms fs ex tb).map (fun l => (l.eval ρ).val) = specWords e ex := by
  have hperm : ∀ (c : Params) (ins : List Term), (∀ t ∈ ins, t.eval e < W) →
      ∃ ρ, Tab.Valid e ρ tb ∧
        (permG linOps c (inputForms fs ins tb).1 (inputForms fs ins tb).2).1.map (Lin.eval ρ) =
          permutation c (ins.map fun t => ((t.eval e : Nat) : F)) := by
    intro c ins hin
    obtain ⟨g1, a1⟩ := inputForms_inv fs ins tb hw
    have k := permG_inv linOps_inv c _ _ g1.1 a1
    have hv := k.1.valid e
    have hc := permG_hom (linOps_hom e (defsVal e _)) c _ _ hv
    have hi := inputForms_sound e _ fs hf ins tb hin hc.2.1
    refine ⟨_, hi.2, ?_⟩
    rw [hc.1, hi.1]
    rfl
  cases ex with
  | perm c ins =>
    obtain ⟨ρ, hv, h⟩ := hperm c ins hin
    refine ⟨ρ, hv, ?_⟩
    rcases hI : inputForms fs ins tb with ⟨xs, tb1⟩
    rw [hI] at h
    simp only [specForms, hI, specWords, permutationWords_eq]
    rw [map_eval_cast, ← h, List.map_map]
    rfl
  | permHead c ins =>
    obtain ⟨ρ, hv, h⟩ := hperm c ins hin
    refine ⟨ρ, hv, ?_⟩
    rcases hI : inputForms fs ins tb with ⟨xs, tb1⟩
    rw [hI] at h
    simp only [specForms, hI, specWords, permutationWords_eq, List.map_cons, List.map_nil]
    rw [map_eval_cast, ← h]
    cases (permG linOps c xs tb1).1 with
    | nil => simp [linOps, Lin.eval, termsEval]
    | cons a r => rfl
  | hash c ins =>
    obtain ⟨g1, a1⟩ := inputForms_inv fs ins tb hw
    rcases hI : inputForms fs ins tb with ⟨xs, tb1⟩
    rw [hI] at g1 a1
    have k := permG_inv linOps_inv c _ _ g1.1 (spongeStateG_inv linOps_inv _ c.t _ a1)
    have hv := k.1.valid e
    have hh := hashG_bridge e _ c xs tb1 hv
    have hc := permG_hom (linOps_hom e (defsVal e _)) c _ _ hv
    have hi := inputForms_sound e _ fs hf ins tb hin (by rw [hI]; exact hc.2.1)
    rw [hI] at hi
    refine ⟨_, hi.2, ?_⟩
    simp only [specForms, hI, specWords, hashWords_eq, List.map_cons, List.map_nil]
    rw [hh, hi.1, map_eval_cast]
  | revertEmpty => exact ⟨defsVal e tb.defs, hw.valid e, rfl⟩

end Poseidon2.Checker
