import Poseidon2.Checker.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise

/-!
# The word terms are sound

`mkBin` / `mkUn` / `mkInput` build a term and an interval for a word. This file proves that the
term evaluates to what the EVM operation computes on the operands' values, and that the value
lies in the interval, whenever the operands' terms evaluate inside their intervals, every value
is a 256-bit word, and the call satisfies the facts: `mkBin_sound`, `mkUn_sound`,
`mkInput_sound`. These are the word half of the checker's per-opcode simulation.
-/

namespace Poseidon2.Checker

/-- A word holds for a call: its term evaluates inside its interval, to a 256-bit value. -/
def Word.Holds (e : Env) (w : Word) : Prop :=
  w.lo ≤ w.t.eval e ∧ w.t.eval e ≤ w.hi ∧ w.t.eval e < W

/-- The facts hold for a call (as in `Soundness.lean`). -/
def Facts.Hold (e : Env) (fs : Facts) : Prop :=
  ∀ f ∈ fs, f.2.1 ≤ f.1.eval e ∧ f.1.eval e ≤ f.2.2

theorem factOf_mem (t : Term) :
    ∀ (fs : Facts) (r : Nat × Nat), factOf t fs = some r → ∃ t', (t', r) ∈ fs ∧ t.beq t' = true
  | [], _, h => by simp [factOf] at h
  | (t', r') :: fs, r, h => by
    simp only [factOf] at h
    split at h
    · cases h; exact ⟨t', by simp, by assumption⟩
    · obtain ⟨t'', hm, hb⟩ := factOf_mem t fs r h
      exact ⟨t'', List.mem_cons_of_mem _ hm, hb⟩

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

/-- Intersecting with the facts keeps a value inside. -/
theorem withFacts_sound (e : Env) (fs : Facts) (hf : Facts.Hold e fs) (t : Term) (r : Nat × Nat)
    (h : r.1 ≤ t.eval e ∧ t.eval e ≤ r.2) :
    (withFacts fs t r).1 ≤ t.eval e ∧ t.eval e ≤ (withFacts fs t r).2 := by
  unfold withFacts
  split
  · rename_i lo hi hfo
    obtain ⟨t', hm, hb⟩ := factOf_mem t fs (lo, hi) hfo
    have := hf _ hm
    rw [← Term.beq_eq t t' hb] at this
    simp only
    exact ⟨max_le this.1 h.1, le_min this.2 h.2⟩
  · exact h

/-- Every supported binary operation gives a 256-bit word. -/
theorem binOp_lt (op x y v : Nat) (hx : x < W) (hy : y < W) (h : binOp op x y = some v) :
    v < W := by
  have hW : 0 < W := by decide
  unfold binOp at h
  split at h <;> (try (cases h))
  all_goals first
    | exact Nat.mod_lt _ hW
    | exact lt_of_le_of_lt Nat.and_le_left hx
    | exact Nat.or_lt_two_pow hx hy
    | exact Nat.xor_lt_two_pow hx hy
    | (split
       all_goals first
         | decide
         | exact Nat.mod_lt _ hW
         | exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
         | exact lt_of_le_of_lt (Nat.mod_le _ _) hx
         | exact lt_of_le_of_lt (Nat.shiftRight_le y x) hy)

theorem decided_sound (yes no : Bool) (v : Nat) (hy : yes = true → v = 1)
    (hn : no = true → v = 0) (h1 : v ≤ 1) :
    (decided yes no).1 ≤ v ∧ v ≤ (decided yes no).2 := by
  unfold decided
  split
  · have := hy (by assumption); omega
  · split
    · have := hn (by assumption); omega
    · omega

theorem full_sound (v : Nat) (h : v < W) : full.1 ≤ v ∧ v ≤ full.2 := by
  simp only [full]; omega

/-- The interval of a binary operation holds. -/
theorem binRange_sound (op : Nat) (a b : Word) (x y v : Nat) (ha : a.lo ≤ x ∧ x ≤ a.hi)
    (hb : b.lo ≤ y ∧ y ≤ b.hi) (hx : x < W) (hy : y < W) (h : binOp op x y = some v) :
    (binRange op a b).1 ≤ v ∧ v ≤ (binRange op a b).2 := by
  have hv := binOp_lt op x y v hx hy h
  unfold binRange
  have hW : 0 < W := by decide
  split
  -- ADD
  · simp only [binOp, Option.some.injEq] at h; subst h
    split
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · exact full_sound _ hv
  -- SUB
  · simp only [binOp, Option.some.injEq] at h; subst h
    split
    · have e : x + W - y = (x - y) + W := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · split
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · exact full_sound _ hv
  -- MUL
  · simp only [binOp, Option.some.injEq] at h; subst h
    split
    · rename_i hm
      have h1 : x * y ≤ a.hi * b.hi := Nat.mul_le_mul ha.2 hb.2
      have h2 : a.lo * b.lo ≤ x * y := Nat.mul_le_mul ha.1 hb.1
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · exact full_sound _ hv
  -- LT
  · simp only [binOp, Option.some.injEq] at h; subst h
    refine decided_sound _ _ _ (fun hh => ?_) (fun hh => ?_) (by split <;> omega)
    · simp at hh; simp; omega
    · simp at hh; simp; omega
  -- GT
  · simp only [binOp, Option.some.injEq] at h; subst h
    refine decided_sound _ _ _ (fun hh => ?_) (fun hh => ?_) (by split <;> omega)
    · simp at hh; simp; omega
    · simp at hh; simp; omega
  -- SLT
  · simp only [binOp, Option.some.injEq] at h; subst h
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      have nx : neg x = false := by simp [neg]; omega
      have ny : neg y = false := by simp [neg]; omega
      simp only [nx, ny, Bool.false_and, Bool.false_or, beq_self_eq_true, Bool.true_and]
      refine decided_sound _ _ _ (fun hh => ?_) (fun hh => ?_) (by split <;> omega)
      · simp at hh; simp; omega
      · simp at hh; simp; omega
    · split <;> simp
  -- SGT
  · simp only [binOp, Option.some.injEq] at h; subst h
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      have nx : neg x = false := by simp [neg]; omega
      have ny : neg y = false := by simp [neg]; omega
      simp only [nx, ny, Bool.not_false, Bool.true_and, Bool.false_or,
        Bool.and_false, beq_self_eq_true]
      refine decided_sound _ _ _ (fun hh => ?_) (fun hh => ?_) (by split <;> omega)
      · simp at hh; simp; omega
      · simp at hh; simp; omega
    · split <;> simp
  -- EQ
  · simp only [binOp, Option.some.injEq] at h; subst h
    refine decided_sound _ _ _ (fun hh => ?_) (fun hh => ?_) (by split <;> omega)
    · simp at hh; simp; omega
    · simp at hh; simp; omega
  -- AND
  · simp only [binOp, Option.some.injEq] at h; subst h
    have h1 : x &&& y ≤ x := Nat.and_le_left
    have h2 : x &&& y ≤ y := Nat.and_le_right
    simp only; omega
  -- SHR
  · simp only [binOp, Option.some.injEq] at h; subst h
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      have hxe : x = a.lo := by omega
      subst hxe
      simp only [if_pos hs.2, Nat.shiftRight_eq_div_pow]
      exact ⟨Nat.div_le_div_right hb.1, Nat.div_le_div_right hb.2⟩
    · exact full_sound _ hv
  -- SHL
  · simp only [binOp, Option.some.injEq] at h; subst h
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      have hxe : x = a.lo := by omega
      subst hxe
      simp only [if_pos hs.1.2, Nat.shiftLeft_eq] at hv ⊢
      have h1 : y * 2 ^ a.lo ≤ b.hi * 2 ^ a.lo := Nat.mul_le_mul_right _ hb.2
      have h2 : b.lo * 2 ^ a.lo ≤ y * 2 ^ a.lo := Nat.mul_le_mul_right _ hb.1
      rw [Nat.shiftLeft_eq] at hs
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · exact full_sound _ hv
  -- the rest
  · exact full_sound _ hv

theorem mask_eq (s : Nat) (hs : s ≤ 256) : W - 2 ^ s = (2 ^ (256 - s) - 1) <<< s := by
  rw [Nat.shiftLeft_eq, Nat.sub_mul, ← pow_add, Nat.sub_add_cancel hs, one_mul]

theorem testBit_mask (s i : Nat) (hs : s ≤ 256) :
    (W - 2 ^ s).testBit i = (decide (s ≤ i) && decide (i < 256)) := by
  rw [mask_eq s hs, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : s ≤ i
  · simp [h]; omega
  · simp [h]

theorem shl_and (x k s : Nat) (hk : k ≤ s) (hs : s < 256) :
    ((x <<< k) % W) &&& (W - 2 ^ s) = ((x >>> (s - k)) <<< s) % W := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hW : W = 2 ^ 256 := rfl
  rw [Nat.testBit_and, testBit_mask s i (by omega), hW, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h1 : s ≤ i
  · by_cases h2 : i < 256
    · have : s - k + (i - s) = i - k := by omega
      simp [h1, h2, this, show k ≤ i by omega]
    · simp [h2]
  · by_cases h2 : i < 256
    · simp [h1, h2]
    · simp [h2]

theorem lowZeros_spec (m s : Nat) (h : lowZeros m = some s) : m = W - 2 ^ s := by
  unfold lowZeros at h
  have := List.find?_some h
  simp only [decide_eq_true_eq] at this
  omega

theorem binOp_add' (x y : Nat) : binOp 0x01 x y = some ((x + y) % W) := rfl
theorem binOp_sub' (x y : Nat) : binOp 0x03 x y = some ((x + W - y) % W) := rfl
theorem binOp_and' (x y : Nat) : binOp 0x16 x y = some (x &&& y) := rfl
theorem binOp_shl' (x y : Nat) : binOp 0x1b x y = some (if x < 256 then (y <<< x) % W else 0) := rfl
theorem binOp_shr' (x y : Nat) : binOp 0x1c x y = some (if x < 256 then y >>> x else 0) := rfl

/-- The normalizing rewrites keep the value. -/
theorem binTerm_eval (e : Env) (op : Nat) (a b : Term) :
    (binTerm op a b).eval e = (binOp op (a.eval e) (b.eval e)).getD 0 := by
  unfold binTerm
  split
  · rename_i c
    split
    · rename_i hc
      show (binOp 0x03 (a.eval e) (W - c)).getD 0 = (binOp 0x01 (a.eval e) c).getD 0
      rw [binOp_sub', binOp_add', Option.getD_some, Option.getD_some,
        Nat.add_sub_assoc (Nat.sub_le W c), Nat.sub_sub_self (le_of_lt hc.2)]
    · rfl
  · rename_i k x m
    split
    · rename_i s hs
      split
      · rename_i hks
        have hm := lowZeros_spec m s hs
        show (binOp 0x1b s ((binOp 0x1c (s - k) (x.eval e)).getD 0)).getD 0 =
          (binOp 0x16 ((binOp 0x1b k (x.eval e)).getD 0) m).getD 0
        rw [binOp_shr', binOp_shl', binOp_and', binOp_shl', Option.getD_some, Option.getD_some,
          Option.getD_some, Option.getD_some, if_pos hks.2, if_pos (show s - k < 256 by omega),
          if_pos (show k < 256 by omega), hm, shl_and _ k s hks.1 hks.2]
      · rfl
    · rfl
  · rfl

theorem binOp_some (op x y v0 : Nat) (h : binOp op 0 0 = some v0) :
    ∃ v, binOp op x y = some v := by
  unfold binOp at h ⊢
  split <;> simp_all

theorem binOp_comm (op x y : Nat) (h : commutative op = true) : binOp op x y = binOp op y x := by
  simp only [commutative, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;> subst h <;> simp only [binOp]
  · rw [Nat.add_comm]
  · rw [Nat.mul_comm]
  · by_cases hxy : x = y <;> simp [hxy, eq_comm]
  · rw [Nat.land_comm]
  · rw [Nat.lor_comm]
  · rw [Nat.xor_comm]

theorem Word.holds_exact (e : Env) (w : Word) (hw : w.Holds e) (x : Nat) (hx : w.exact = some x) :
    w.t.eval e = x := by
  unfold Word.exact at hx
  split at hx
  · cases hx; obtain ⟨h1, h2, _⟩ := hw; omega
  · cases hx

theorem Word.const_holds (e : Env) (v : Nat) (hv : v < W) : (Word.const v).Holds e := by
  simp [Word.Holds, Word.const, Term.eval, hv]

/-- **`mkBin` is sound**: the new word holds and evaluates to the operation's result. -/
theorem mkBin_sound (e : Env) (fs : Facts) (hf : Facts.Hold e fs) (op : Nat) (a b w : Word)
    (ha : a.Holds e) (hb : b.Holds e) (h : mkBin fs op a b = some w) :
    w.Holds e ∧ some (w.t.eval e) = binOp op (a.t.eval e) (b.t.eval e) := by
  unfold mkBin at h
  split at h
  · rename_i x y hx hy
    rw [Word.holds_exact e a ha x hx, Word.holds_exact e b hb y hy]
    cases hr : binOp op x y with
    | none => simp [hr] at h
    | some v =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      have hv := binOp_lt op x y v (by rw [← Word.holds_exact e a ha x hx]; exact ha.2.2)
        (by rw [← Word.holds_exact e b hb y hy]; exact hb.2.2) hr
      exact ⟨Word.const_holds e v hv, by simp [Word.const, Term.eval]⟩
  · split at h
    · rename_i hEq
      cases h
      have hab := Term.beq_eq a.t b.t hEq.2
      refine ⟨Word.const_holds e 1 (by decide), ?_⟩
      rw [hEq.1, hab]
      simp [Word.const, Term.eval, binOp]
    · split at h
      · cases h
      · rename_i v0 hv0
        have hsome : ∀ x y, ∃ v, binOp op x y = some v := fun x y => binOp_some op x y v0 hv0
        -- the operands, swapped for a commutative operation with a constant first
        have key : ∀ a' b' : Word, a'.Holds e → b'.Holds e →
            binOp op (a'.t.eval e) (b'.t.eval e) = binOp op (a.t.eval e) (b.t.eval e) →
            w = ⟨binTerm op a'.t b'.t, (withFacts fs (binTerm op a'.t b'.t) (binRange op a' b')).1,
              (withFacts fs (binTerm op a'.t b'.t) (binRange op a' b')).2⟩ →
            w.Holds e ∧ some (w.t.eval e) = binOp op (a.t.eval e) (b.t.eval e) := by
          intro a' b' ha' hb' hcomm hw
          subst hw
          obtain ⟨v, hv⟩ := hsome (a'.t.eval e) (b'.t.eval e)
          have he := binTerm_eval e op a'.t b'.t
          rw [hv, Option.getD_some] at he
          have hr := binRange_sound op a' b' _ _ v ⟨ha'.1, ha'.2.1⟩ ⟨hb'.1, hb'.2.1⟩ ha'.2.2 hb'.2.2 hv
          have hlt := binOp_lt op _ _ v ha'.2.2 hb'.2.2 hv
          rw [← he] at hr hlt
          have hfs := withFacts_sound e fs hf _ _ hr
          refine ⟨⟨hfs.1, hfs.2, hlt⟩, ?_⟩
          simp only
          rw [he, ← hv, hcomm]
        by_cases hsw : (commutative op && isConst a.t && !isConst b.t) = true
        · simp only [hsw, if_true, Option.some.injEq] at h
          have hc : commutative op = true := by
            simp only [Bool.and_eq_true] at hsw; exact hsw.1.1
          exact key b a hb ha (binOp_comm op _ _ hc) h.symm
        · simp only [hsw, Option.some.injEq] at h
          exact key a b ha hb rfl h.symm

theorem unOp_iszero (x : Nat) : unOp 0x15 x = some (if x = 0 then 1 else 0) := rfl
theorem unOp_not (x : Nat) : unOp 0x19 x = some (W - 1 - x % W) := rfl

/-- **`mkUn` is sound**. -/
theorem mkUn_sound (e : Env) (fs : Facts) (hf : Facts.Hold e fs) (op : Nat) (a w : Word)
    (ha : a.Holds e) (h : mkUn fs op a = some w) :
    w.Holds e ∧ some (w.t.eval e) = unOp op (a.t.eval e) := by
  have hW : 0 < W := by decide
  unfold mkUn at h
  split at h
  · rename_i x hx
    rw [Word.holds_exact e a ha x hx]
    cases hr : unOp op x with
    | none => simp [hr] at h
    | some v =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      have hv : v < W := by
        unfold unOp at hr
        split at hr <;> (try cases hr)
        · split <;> decide
        · omega
      exact ⟨Word.const_holds e v hv, by simp [Word.const, Term.eval]⟩
  · split at h
    · cases h
    · rename_i v0 hv0
      cases h
      have hx := ha.2.2
      have h1 := ha.1
      have h2 := ha.2.1
      by_cases h15 : op = 0x15
      · subst h15
        have hr : (decided (decide (a.hi = 0)) (decide (0 < a.lo))).1 ≤ (if a.t.eval e = 0 then 1 else 0) ∧
            (if a.t.eval e = 0 then 1 else 0) ≤ (decided (decide (a.hi = 0)) (decide (0 < a.lo))).2 := by
          unfold decided
          split
          · rename_i hy
            simp only [decide_eq_true_eq] at hy
            have hz : a.t.eval e = 0 := by omega
            simp [hz]
          · split
            · rename_i hn
              simp only [decide_eq_true_eq] at hn
              have hz : a.t.eval e ≠ 0 := by omega
              simp [hz]
            · constructor
              · exact Nat.zero_le _
              · split <;> simp
        have hw := withFacts_sound e fs hf (.un 0x15 a.t) _ hr
        refine ⟨⟨hw.1, hw.2, ?_⟩, rfl⟩
        show (if a.t.eval e = 0 then 1 else 0) < W
        split <;> decide
      · by_cases h19 : op = 0x19
        · subst h19
          have hmod : a.t.eval e % W = a.t.eval e := Nat.mod_eq_of_lt hx
          have hr : (W - 1 - a.hi, W - 1 - a.lo).1 ≤ W - 1 - a.t.eval e % W ∧
              W - 1 - a.t.eval e % W ≤ (W - 1 - a.hi, W - 1 - a.lo).2 := by
            rw [hmod]; simp only; omega
          have hw := withFacts_sound e fs hf (.un 0x19 a.t) _ hr
          refine ⟨⟨hw.1, hw.2, ?_⟩, rfl⟩
          show W - 1 - a.t.eval e % W < W
          omega
        · exfalso
          unfold unOp at hv0
          split at hv0 <;> simp_all

/-- **`mkInput` is sound**: an input word inside its interval holds, with its own value. -/
theorem mkInput_sound (e : Env) (fs : Facts) (hf : Facts.Hold e fs) (t : Term) (r : Nat × Nat)
    (h : r.1 ≤ t.eval e ∧ t.eval e ≤ r.2) (hlt : t.eval e < W) :
    (mkInput fs t r).Holds e ∧ (mkInput fs t r).t.eval e = t.eval e := by
  unfold mkInput
  split
  · rename_i v
    exact ⟨Word.const_holds e v hlt, rfl⟩
  · have hw := withFacts_sound e fs hf t r h
    exact ⟨⟨hw.1, hw.2, hlt⟩, rfl⟩

end Poseidon2.Checker
