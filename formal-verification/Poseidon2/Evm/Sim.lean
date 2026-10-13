import Ethereum.Theory.OpcodeLemmas
import Poseidon2.Checker.FieldSound
import Poseidon2.Evm.Eip8024

/-!
# Simulation of single opcodes (first lemmas)

The EVM half of the checker's soundness relates one checker step to one EVMLean `Xstep`. This
file starts it with the stack relation and some of the opcodes the Huff permutation bodies are made
of: `MULMOD` and `ADDMOD` by `P` and `ADD` on field values (`sim_mulmod`, `sim_addmod`,
`sim_add_field`), `POP` and `DUP1` (`sim_pop`, `sim_dup1`). The `Xstep` side comes from
EVMLean's own `Ethereum/Theory/OpcodeLemmas.lean` (`step_mulmod`, ...). Each lemma says: the
EVM runs out of gas, or it takes the step the checker took, and the new stack is described by
the checker's values.
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec

variable (e : Env) (ρ : Nat → F)

/-- The checker's stack describes the EVM's, word by word. -/
def StkRel : List SV → List UInt256 → Prop :=
  List.Forall₂ (fun v w => v.Rel e ρ w.toNat)

theorem toNat_lt (w : UInt256) : w.toNat < W := w.val.isLt

/-- A word value that is exactly `n` describes only the word `n`. -/
theorem rel_exact (v : SV) (w : Nat) (n : Nat) (hv : v.Rel e ρ w) (hn : v.exact = some n) :
    w = n := by
  cases v with
  | word x => obtain ⟨hx, rfl⟩ := hv; exact Word.holds_exact e x hx n hn
  | lin _ _ => simp [SV.exact] at hn
  | pw _ _ _ => simp [SV.exact] at hn

theorem mulMod_P (a b c : UInt256) (hc : c.toNat = P) :
    (UInt256.mulMod a b c).toNat = a.toNat * b.toNat % P := by
  unfold UInt256.mulMod UInt256.eq0
  have : c.toNat ≠ 0 := by rw [hc]; decide
  simp only [UInt256.toNat] at hc this ⊢
  rw [if_neg (by intro h; apply this; simp only [beq_iff_eq] at h; rw [h]; rfl)]
  simp only [UInt256.ofNat, Id.run, Fin.ofNat, hc]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) P_lt_W)

/-- `MULMOD` by `P` on field values: the EVM runs out of gas, or replaces the three top words
by `mulMod`, which the checker's `mulModP` result describes. -/
theorem sim_mulmod (s : State) (x y n : SV) (a b c : UInt256) (t : List UInt256)
    (tb tb' : Tab) (v : SV)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MULMOD, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t) (hlen : t.length + 3 ≤ 1024)
    (hx : x.Rel e ρ a.toNat) (hy : y.Rel e ρ b.toNat) (hn : n.Rel e ρ c.toNat)
    (hnP : n.exact = some P) (hm : mulModP x y tb = .ok (v, tb')) (hv : Tab.Valid e ρ tb') :
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
      ∃ s', Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
        s'.machineState.stack = UInt256.mulMod a b c :: t ∧
        v.Rel e ρ (UInt256.mulMod a b c).toNat := by
  have hc : c.toNat = P := rel_exact e ρ n c.toNat P hn hnP
  have hr := (mulModP_sound e ρ x y a.toNat b.toNat tb tb' v hm hx hy hv).1
  rw [step_mulmod s hdec, hstk]
  have hov : ¬ ((a :: b :: c :: t).length - 3 + 1 > 1024) := by simp only [List.length_cons]; omega
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gmid
  · left; simp only [hg, if_true]
  · right
    simp only [hg, if_false, hov]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [mulMod_P a b c hc]; exact hr

theorem addMod_P (a b c : UInt256) (hc : c.toNat = P) :
    (UInt256.addMod a b c).toNat = (a.toNat + b.toNat) % P := by
  unfold UInt256.addMod UInt256.eq0
  have : c.toNat ≠ 0 := by rw [hc]; decide
  simp only [UInt256.toNat] at hc this ⊢
  rw [if_neg (by intro h; apply this; simp only [beq_iff_eq] at h; rw [h]; rfl)]
  simp only [UInt256.ofNat, Id.run, Fin.ofNat, hc]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) P_lt_W)

theorem add_toNat (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % W := by
  show (a.val + b.val).val = _
  rw [Fin.val_add]; rfl

/-- `ADDMOD a b P` on field values. -/
theorem sim_addmod (s : State) (x y n : SV) (a b c : UInt256) (t : List UInt256)
    (tb tb1 tb2 : Tab) (la lb : Lin) (ba bb : Nat)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.ADDMOD, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t) (hlen : t.length + 3 ≤ 1024)
    (hx : x.Rel e ρ a.toNat) (hy : y.Rel e ρ b.toNat) (hn : n.Rel e ρ c.toNat)
    (hnP : n.exact = some P) (h1 : toLin x tb = .ok (la, ba, tb1))
    (h2 : toLin y tb1 = .ok (lb, bb, tb2)) (hv : Tab.Valid e ρ tb2) :
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
      ∃ s', Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
        s'.machineState.stack = UInt256.addMod a b c :: t ∧
        (SV.lin (la.add lb) (P - 1)).Rel e ρ (UInt256.addMod a b c).toNat := by
  have hc : c.toNat = P := rel_exact e ρ n c.toNat P hn hnP
  have e2 := toLin_ext y tb1 tb2 lb bb h2
  have sa := toLin_sound e ρ x a.toNat tb tb1 la ba h1 hx (hv.of_ext e2)
  have sb := toLin_sound e ρ y b.toNat tb1 tb2 lb bb h2 hy hv
  rw [step_addmod s hdec, hstk]
  have hov : ¬ ((a :: b :: c :: t).length - 3 + 1 > 1024) := by simp only [List.length_cons]; omega
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gmid
  · left; simp only [hg, if_true]
  · right
    simp only [hg, if_false, hov]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [addMod_P a b c hc]
    exact addModP_sound e ρ la lb _ _ sa.2.2.1 sb.2.2.1

/-- `ADD` of two field values whose bounds sum below `2^256`. -/
theorem sim_add_field (s : State) (x y : SV) (a b : UInt256) (t : List UInt256)
    (tb tb1 tb2 : Tab) (la lb : Lin) (ba bb : Nat)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.ADD, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hlen : t.length + 2 ≤ 1024)
    (hx : x.Rel e ρ a.toNat) (hy : y.Rel e ρ b.toNat) (h1 : toLin x tb = .ok (la, ba, tb1))
    (h2 : toLin y tb1 = .ok (lb, bb, tb2)) (hlt : ba + bb < W) (hv : Tab.Valid e ρ tb2) :
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
      ∃ s', Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
        s'.machineState.stack = (a + b) :: t ∧
        (SV.lin (la.add lb) (ba + bb)).Rel e ρ (a + b).toNat := by
  rw [step_add s hdec, hstk]
  have hov : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gverylow
  · left; simp only [hg, if_true]
  · right
    simp only [hg, if_false, hov]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [add_toNat]
    exact (addField_sound e ρ x y _ _ tb tb1 tb2 la lb ba bb h1 h2 hlt hx hy hv).1

/-- `POP`: the rest of the stack still relates. -/
theorem sim_pop (s : State) (x : SV) (r : List SV) (a : UInt256) (t : List UInt256)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.POP, .none))
    (hstk : s.machineState.stack = a :: t) (hlen : t.length + 1 ≤ 1024)
    (hrel : StkRel e ρ (x :: r) (a :: t)) :
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
      ∃ s', Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
        s'.machineState.stack = t ∧ StkRel e ρ r t := by
  rw [step_pop s hdec, hstk]
  have hov : ¬ ((a :: t).length - 1 + 0 > 1024) := by simp only [List.length_cons]; omega
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gbase
  · left; simp only [hg, if_true]
  · right
    simp only [hg, if_false, hov]
    exact ⟨_, rfl, rfl, (List.forall₂_cons.mp hrel).2⟩

/-- `DUP1`: the copy relates as the original does. -/
theorem sim_dup1 (s : State) (x : SV) (r : List SV) (a : UInt256) (t : List UInt256)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.DUP1, .none))
    (hstk : s.machineState.stack = a :: t) (hlen : t.length + 2 ≤ 1024)
    (hrel : StkRel e ρ (x :: r) (a :: t)) :
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
      ∃ s', Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
        s'.machineState.stack = a :: a :: t ∧ StkRel e ρ (x :: x :: r) (a :: a :: t) := by
  rw [step_dup1 s hdec, hstk]
  have hov : ¬ ((a :: t).length - 1 + 2 > 1024) := by simp only [List.length_cons]; omega
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gverylow
  · left; simp only [hg, if_true]
  · right
    simp only [hg, if_false, hov]
    exact ⟨_, rfl, rfl, List.Forall₂.cons (List.forall₂_cons.mp hrel).1 hrel⟩

end Poseidon2.Evm.Sim
