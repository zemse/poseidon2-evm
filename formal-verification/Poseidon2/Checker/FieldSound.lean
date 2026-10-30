import Poseidon2.Checker.Bridge
import Poseidon2.Checker.SymExec

/-!
# The field values are sound

`SV.Rel e ρ v x` says the symbolic value `v` describes the 256-bit word `x` of a call `e`, under
an atom valuation `ρ`: an exact word term, a linear form `≡ x (mod P)` with `x` below its bound,
or `c · l^k` equal to `x` (then below `P`). This file proves that the checker's field operations
(`toLin`, `toPow`, `scaleMod`, `mulModP`, the field `ADD` / `MUL` of `addMul`) describe what the
EVM computes (`ADD` / `MUL` modulo `2^256`, `MULMOD` / `ADDMOD` / `MOD` by `P`), for any `ρ`
valid on the atom table the run ends with. With `BoundsSound.lean` this is the value half of the
per-opcode simulation; the stack, memory and control-flow half against EVMLean is in `Evm/`.
-/

namespace Poseidon2.Checker

open Poseidon2.Spec

/-- `v` describes the word `x`. -/
def SV.Rel (e : Env) (ρ : Nat → F) : SV → Nat → Prop
  | .word w, x => w.Holds e ∧ x = w.t.eval e
  | .lin l b, x => x ≤ b ∧ x < W ∧ (x : F) = l.eval ρ
  | .pw c l k, x => x < P ∧ (x : F) = (c : F) * l.eval ρ ^ k

/-- `tb'` extends `tb`: it holds every atom of `tb` (new atoms go in front). -/
def Tab.Ext (tb tb' : Tab) : Prop := tb.defs <:+ tb'.defs

theorem Tab.Ext.refl (tb : Tab) : tb.Ext tb := List.suffix_refl _

theorem Tab.Ext.trans {a b c : Tab} (h1 : a.Ext b) (h2 : b.Ext c) : a.Ext c :=
  List.IsSuffix.trans h1 h2

theorem Tab.Valid.of_ext {e : Env} {ρ : Nat → F} {tb tb' : Tab} (h : tb.Ext tb')
    (hv : Tab.Valid e ρ tb') : Tab.Valid e ρ tb :=
  fun p hp => hv p (h.subset hp)

theorem Tab.atom_ext (tb : Tab) (d : Def) : tb.Ext (tb.atom d).2 := by
  unfold Tab.atom
  split
  · exact Tab.Ext.refl _
  · exact List.suffix_cons _ _

theorem Tab.sbox_ext (l : Lin) (tb : Tab) : tb.Ext (tb.sbox l).2 := by
  unfold Tab.sbox
  split
  · exact Tab.Ext.refl _
  · exact Tab.atom_ext _ _

theorem P_lt_W : P < W := by decide

theorem cast_mod_P (x : Nat) : ((x % P : Nat) : F) = (x : F) := ZMod.natCast_mod x P

variable (e : Env) (ρ : Nat → F)

theorem toLin_sound (v : SV) (x : Nat) (tb tb' : Tab) (l : Lin) (b : Nat)
    (h : toLin v tb = .ok (l, b, tb')) (hr : v.Rel e ρ x) (hv : Tab.Valid e ρ tb') :
    x ≤ b ∧ x < W ∧ (x : F) = l.eval ρ ∧ tb.Ext tb' := by
  unfold toLin at h
  cases v with
  | word w =>
    obtain ⟨hw, hx⟩ := hr
    subst hx
    simp only at h
    split at h
    · rename_i y hy
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have := Word.holds_exact e w hw y hy
      refine ⟨by omega, hw.2.2, by rw [Lin.eval_const, this], Tab.Ext.refl _⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hs := Tab.atom_spec e ρ tb (.word w.t) hv
      refine ⟨hw.2.1, hw.2.2, ?_, Tab.atom_ext _ _⟩
      rw [hs.1]; rfl
  | lin l' b' =>
    obtain ⟨h1, h2, h3⟩ := hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨h1, h2, h3, Tab.Ext.refl _⟩
  | pw _ _ _ => simp at h

theorem toPow_sound (v : SV) (x : Nat) (tb tb' : Tab) (c : Nat) (l : Lin) (k : Nat)
    (h : toPow v tb = .ok (c, l, k, tb')) (hr : v.Rel e ρ x) (hv : Tab.Valid e ρ tb') :
    (x : F) = (c : F) * l.eval ρ ^ k ∧ tb.Ext tb' := by
  unfold toPow at h
  split at h
  · rename_i c' l' k'
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hr.2, Tab.Ext.refl _⟩
  · cases ht : toLin v tb with
    | error _ => simp [ht, bind, Except.bind] at h
    | ok r =>
      obtain ⟨l', b', tb''⟩ := r
      simp only [ht, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have := toLin_sound e ρ v x tb tb'' l' b' ht hr hv
      exact ⟨by rw [this.2.2.1]; simp, this.2.2.2⟩

theorem fieldConst_sound (v : SV) (x c : Nat) (h : fieldConst v = some c) (hr : v.Rel e ρ x) :
    (x : F) = (c : F) := by
  unfold fieldConst at h
  cases v with
  | word w =>
    obtain ⟨hw, rfl⟩ := hr
    rw [Word.holds_exact e w hw c h]
  | lin l b =>
    obtain ⟨-, -, hx⟩ := hr
    rw [hx]
    cases l with
    | mk lc ts =>
      cases ts with
      | nil => simp [Lin.asConst] at h; subst h; simp [Lin.eval, termsEval]
      | cons _ _ => simp [Lin.asConst] at h
  | pw _ _ _ => simp at h

theorem lt_P_eq_zero (z : Nat) (hz : z < P) (h : (z : F) = 0) : z = 0 := by
  have := ZMod.val_natCast (n := P) z
  rw [h, ZMod.val_zero, Nat.mod_eq_of_lt hz] at this
  exact this.symm

theorem eq_of_cast_eq (a b : Nat) (ha : a < P) (hb : b < P) (h : (a : F) = (b : F)) : a = b := by
  have h1 := ZMod.val_natCast (n := P) a
  have h2 := ZMod.val_natCast (n := P) b
  rw [h] at h1
  rw [h1, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact h2

/-- `scaleMod v c`: describes any word `z < P` equal in the field to `c` times `v`'s word. -/
theorem scaleMod_sound (v : SV) (y c z : Nat) (tb tb' : Tab) (r : SV)
    (h : scaleMod v c tb = .ok (r, tb')) (hr : v.Rel e ρ y) (hz : z < P)
    (hzf : (z : F) = (c : F) * (y : F)) (hv : Tab.Valid e ρ tb') :
    r.Rel e ρ z ∧ tb.Ext tb' := by
  unfold scaleMod at h
  split at h
  · rename_i hc
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc0 : (c : F) = 0 := by rw [← cast_mod_P, hc]; simp
    have : z = 0 := lt_P_eq_zero z hz (by rw [hzf, hc0, zero_mul])
    subst this
    exact ⟨⟨Word.const_holds e 0 (by decide), rfl⟩, Tab.Ext.refl _⟩
  · split at h
    · rename_i c' l k
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨hz, ?_⟩, Tab.Ext.refl _⟩
      rw [hzf, hr.2, cast_mod_P]; push_cast; ring
    · cases ht : toLin v tb with
      | error _ => simp [ht, bind, Except.bind] at h
      | ok q =>
        obtain ⟨l, b, tb''⟩ := q
        simp only [ht, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := toLin_sound e ρ v y tb tb'' l b ht hr hv
        refine ⟨⟨by omega, lt_trans hz P_lt_W, ?_⟩, this.2.2.2⟩
        rw [hzf, this.2.2.1, Lin.eval_scale]

theorem toLin_ext (v : SV) (tb tb' : Tab) (l : Lin) (b : Nat)
    (h : toLin v tb = .ok (l, b, tb')) : tb.Ext tb' := by
  unfold toLin at h
  cases v with
  | word w =>
    simp only at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2.2]; exact Tab.Ext.refl _
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2.2]; exact Tab.atom_ext _ _
  | lin _ _ => simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2.2]; exact Tab.Ext.refl _
  | pw _ _ _ => simp at h

theorem toPow_ext (v : SV) (tb tb' : Tab) (c : Nat) (l : Lin) (k : Nat)
    (h : toPow v tb = .ok (c, l, k, tb')) : tb.Ext tb' := by
  unfold toPow at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2.2.2]; exact Tab.Ext.refl _
  · cases ht : toLin v tb with
    | error _ => simp [ht, bind, Except.bind] at h
    | ok r =>
      obtain ⟨l', b', tb''⟩ := r
      simp only [ht, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2.2]; exact toLin_ext v tb tb'' l' b' ht

theorem val_mul_mod (x y cx cy : Nat) (hx : (x : F) = (cx : F)) (hy : (y : F) = (cy : F)) :
    x * y % P = cx * cy % P := by
  apply eq_of_cast_eq _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  rw [cast_mod_P, cast_mod_P]; push_cast; rw [hx, hy]

/-- `MULMOD a b P`: describes `x · y mod P`. -/
theorem mulModP_sound (a b : SV) (x y : Nat) (tb tb' : Tab) (r : SV)
    (h : mulModP a b tb = .ok (r, tb')) (ha : a.Rel e ρ x) (hb : b.Rel e ρ y)
    (hv : Tab.Valid e ρ tb') : r.Rel e ρ (x * y % P) ∧ tb.Ext tb' := by
  have hzP : x * y % P < P := Nat.mod_lt _ (by decide)
  unfold mulModP at h
  split at h
  · rename_i cx cy hcx hcy
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [val_mul_mod x y cx cy (fieldConst_sound e ρ a x cx hcx ha) (fieldConst_sound e ρ b y cy hcy hb)]
    exact ⟨⟨Word.const_holds e _ (lt_trans (Nat.mod_lt _ (by decide)) P_lt_W), rfl⟩, Tab.Ext.refl _⟩
  · rename_i cx hcx _
    exact scaleMod_sound e ρ b y cx _ tb tb' r h hb hzP
      (by rw [cast_mod_P]; push_cast; rw [fieldConst_sound e ρ a x cx hcx ha]) hv
  · rename_i cy _ hcy
    exact scaleMod_sound e ρ a x cy _ tb tb' r h ha hzP
      (by rw [cast_mod_P]; push_cast; rw [fieldConst_sound e ρ b y cy hcy hb]; ring) hv
  · cases hpa : toPow a tb with
    | error _ => simp [hpa, bind, Except.bind] at h
    | ok qa =>
      obtain ⟨ca, la, ka, tb1⟩ := qa
      cases hpb : toPow b tb1 with
      | error _ => simp [hpa, hpb, bind, Except.bind] at h
      | ok qb =>
        obtain ⟨cb, lb, kb, tb2⟩ := qb
        simp only [hpa, hpb, bind, Except.bind] at h
        have e1 := toPow_ext a tb tb1 ca la ka hpa
        have e2 := toPow_ext b tb1 tb2 cb lb kb hpb
        split at h
        · simp at h
        · rename_i hbeq
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hbeq
          have hl : la = lb := Lin.beq_eq la lb (by simpa using hbeq)
          subst hl
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have pa := (toPow_sound e ρ a x tb tb1 ca la ka hpa ha (hv.of_ext e2)).1
            have pb := (toPow_sound e ρ b y tb1 tb2 cb la kb hpb hb hv).1
            refine ⟨⟨hzP, ?_⟩, e1.trans e2⟩
            rw [cast_mod_P, cast_mod_P]; push_cast; rw [pa, pb]; ring
          · split at h
            · rename_i _ hk5
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have e3 := Tab.sbox_ext la tb2
              have pa := (toPow_sound e ρ a x tb tb1 ca la ka hpa ha ((hv.of_ext e3).of_ext e2)).1
              have pb := (toPow_sound e ρ b y tb1 tb2 cb la kb hpb hb (hv.of_ext e3)).1
              have hs := (linOps_hom e ρ).sbox la tb2 hv
              simp only [linOps, ringOps] at hs
              refine ⟨⟨by omega, lt_trans hzP P_lt_W, ?_⟩, (e1.trans e2).trans e3⟩
              rw [Lin.eval_scale, hs, cast_mod_P, cast_mod_P]; push_cast; rw [pa, pb, ← hk5]; ring
            · simp at h

/-- The field `ADD` of `addMul`: two values whose bounds sum below `2^256`. -/
theorem addField_sound (a b : SV) (x y : Nat) (tb tb1 tb2 : Tab) (la lb : Lin) (ba bb : Nat)
    (h1 : toLin a tb = .ok (la, ba, tb1)) (h2 : toLin b tb1 = .ok (lb, bb, tb2))
    (hlt : ba + bb < W) (ha : a.Rel e ρ x) (hb : b.Rel e ρ y) (hv : Tab.Valid e ρ tb2) :
    (SV.lin (la.add lb) (ba + bb)).Rel e ρ ((x + y) % W) ∧ tb.Ext tb2 := by
  have e2 := toLin_ext b tb1 tb2 lb bb h2
  have sa := toLin_sound e ρ a x tb tb1 la ba h1 ha (hv.of_ext e2)
  have sb := toLin_sound e ρ b y tb1 tb2 lb bb h2 hb hv
  rw [Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨by omega, by omega, ?_⟩, sa.2.2.2.trans e2⟩
  rw [Lin.eval_add]; push_cast; rw [sa.2.2.1, sb.2.2.1]

/-- `MOD P` of a linear value. -/
theorem modP_lin (l : Lin) (b x : Nat) (hr : (SV.lin l b).Rel e ρ x) :
    (SV.lin l (min b (P - 1))).Rel e ρ (x % P) := by
  obtain ⟨h1, -, h3⟩ := hr
  have h4 : x % P < P := Nat.mod_lt _ (by decide)
  have h5 : x % P ≤ x := Nat.mod_le _ _
  exact ⟨le_min (by omega) (by omega), lt_trans h4 P_lt_W, by rw [cast_mod_P, h3]⟩

/-- `MOD P` of a power: already below `P`. -/
theorem modP_pw (c : Nat) (l : Lin) (k x : Nat) (hr : (SV.pw c l k).Rel e ρ x) :
    (SV.pw c l k).Rel e ρ (x % P) := by
  rw [Nat.mod_eq_of_lt hr.1]; exact hr

/-- `ADDMOD a b P` of two linear views. -/
theorem addModP_sound (la lb : Lin) (x y : Nat) (hx : (x : F) = la.eval ρ)
    (hy : (y : F) = lb.eval ρ) : (SV.lin (la.add lb) (P - 1)).Rel e ρ ((x + y) % P) := by
  have h4 : (x + y) % P < P := Nat.mod_lt _ (by decide)
  refine ⟨by omega, lt_trans h4 P_lt_W, ?_⟩
  rw [cast_mod_P, Lin.eval_add]; push_cast; rw [hx, hy]

/-- `MUL` of a field value by a constant, the bound kept below `2^256`. -/
theorem mulConst_sound (l : Lin) (bnd c y : Nat) (hb : y ≤ bnd) (hy : (y : F) = l.eval ρ)
    (hlt : bnd * c < W) : (SV.lin (l.scale c) (bnd * c)).Rel e ρ ((c * y) % W) := by
  have : c * y ≤ bnd * c := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hb
  rw [Nat.mod_eq_of_lt (by omega)]
  refine ⟨this, by omega, ?_⟩
  rw [Lin.eval_scale]; push_cast; rw [hy]

/-- `SHL k` of a field value, the bound kept below `2^256`. -/
theorem shlField_sound (l : Lin) (bnd k y : Nat) (hb : y ≤ bnd) (hy : (y : F) = l.eval ρ)
    (hlt : bnd * 2 ^ k < W) :
    (SV.lin (l.scale (2 ^ k)) (bnd * 2 ^ k)).Rel e ρ ((y <<< k) % W) := by
  have : y * 2 ^ k ≤ bnd * 2 ^ k := Nat.mul_le_mul_right _ hb
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  refine ⟨this, by omega, ?_⟩
  rw [Lin.eval_scale]; push_cast; rw [hy]; ring

end Poseidon2.Checker
