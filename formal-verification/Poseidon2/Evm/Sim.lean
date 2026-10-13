import Poseidon2.Checker.FieldSound
import Poseidon2.Evm.Steps

/-!
# Simulation of single opcodes

The EVM half of the checker's soundness relates one checker step to one EVM step
(`Eip8024.Xstep`: EVMLean's `Xstep` with DUPN / SWAPN). `Simulates e ρ s c n stk` says: the EVM's
step from `s` runs out of gas, or it pays `c` gas, moves `pc` by `n`, leaves everything else
as it was, and its new stack is described by the checker's stack `stk` (`StkRel`).

Each lemma here takes a checker `step` that succeeded on an instruction, a stack the checker's
stack describes, and the instruction EVMLean decodes at `pc`, and proves `Simulates` for the
checker's new stack. Stack overflow cannot happen (the checker's `push` refuses a full stack)
and stack underflow cannot either (the checker's stack has the EVM's length); the only other
exceptional halt of these opcodes is running out of gas. The `Xstep` side comes from EVMLean's
`Ethereum/Theory/OpcodeLemmas.lean` and from `Steps.lean`.

Covered: every instruction `Checker.step` accepts except the memory and data ones (`MLOAD`,
`MSTORE`, `MSIZE`, `CALLDATALOAD`, `CALLDATACOPY`, `CODECOPY`); control flow (`JUMP`, `JUMPI`,
`STOP`, `RETURN`, `REVERT`) is `ctl`, not `step`.
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

variable (e : Env) (ρ : Nat → F)

/-- The checker's stack describes the EVM's, word by word. -/
def StkRel : List SV → List UInt256 → Prop :=
  List.Forall₂ (fun v w => v.Rel e ρ w.toNat)

/-- The EVM's step from `s`, as the checker's step to the stack `stk` describes it: out of gas,
or `c` gas paid, `pc` moved by `n`, and a new stack that `stk` describes, nothing else changed. -/
def Simulates (s : State) (c n : Nat) (stk : List SV) : Prop :=
  Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    ∃ t, StkRel e ρ stk t ∧ c ≤ s.machineState.gasAvailable.toNat ∧
      Eip8024.Xstep (D_J s.executionEnv.code 0) s = .ok ({s with
        machineState.stack := t
        machineState.gasAvailable := s.machineState.gasAvailable.subNat c
        machineState.pc := s.machineState.pc + UInt256.ofNat n
        machineState.execLength := s.machineState.execLength + 1}, none)

/-- The usual shape of a step: the gas check, the stack overflow check, the new state. -/
theorem sim_of (s : State) (c n : Nat) (stk : List SV) (t : List UInt256) (L : Nat)
    (hx : Eip8024.Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.gasAvailable.toNat < c then .error .OutOfGass
      else if L > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := t
        machineState.gasAvailable := s.machineState.gasAvailable.subNat c
        machineState.pc := s.machineState.pc + UInt256.ofNat n
        machineState.execLength := s.machineState.execLength + 1}, none))
    (hL : L ≤ 1024) (hr : StkRel e ρ stk t) : Simulates e ρ s c n stk := by
  rw [Simulates, hx]
  by_cases hg : s.machineState.gasAvailable.toNat < c
  · left; rw [if_pos hg]
  · right
    rw [if_neg hg, if_neg (by omega)]
    exact ⟨t, hr, by omega, rfl⟩

/-! ## Stack lemmas -/

theorem StkRel.length {stk : List SV} {t : List UInt256} (h : StkRel e ρ stk t) :
    stk.length = t.length :=
  List.Forall₂.length_eq h

theorem StkRel.getElem {stk : List SV} {t : List UInt256} (h : StkRel e ρ stk t) (i : Nat)
    (hi : i < stk.length) (ht : i < t.length) : stk[i].Rel e ρ t[i].toNat :=
  List.Forall₂.get h hi ht

theorem StkRel.cons_inv {x : SV} {r : List SV} {t : List UInt256} (h : StkRel e ρ (x :: r) t) :
    ∃ a t', t = a :: t' ∧ x.Rel e ρ a.toNat ∧ StkRel e ρ r t' := by
  cases t with
  | nil => cases h
  | cons a t' => exact ⟨a, t', rfl, (List.forall₂_cons.mp h).1, (List.forall₂_cons.mp h).2⟩

theorem StkRel.set {stk : List SV} {t : List UInt256} (h : StkRel e ρ stk t) (i : Nat)
    (v : SV) (w : UInt256) (hv : v.Rel e ρ w.toNat) : StkRel e ρ (stk.set i v) (t.set i w) := by
  induction h generalizing i with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih =>
    cases i with
    | zero => exact List.Forall₂.cons hv (by assumption)
    | succ i => exact List.Forall₂.cons hab (ih i)

/-! ## Checker steps

What a successful `step` on each instruction looks like. -/

theorem bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {y : β}
    (h : m >>= f = .ok y) : ∃ x, m = .ok x ∧ f x = .ok y := by
  cases m with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

theorem pop1_ok {s s' : St} {a : SV} (h : pop1 s = .ok (a, s')) :
    s.stk = a :: s'.stk ∧ s' = { s with stk := s'.stk } := by
  unfold pop1 at h
  split at h
  · cases h; rename_i hs; exact ⟨hs, rfl⟩
  · cases h

theorem pop2_ok {s s' : St} {a b : SV} (h : pop2 s = .ok (a, b, s')) :
    s.stk = a :: b :: s'.stk ∧ s' = { s with stk := s'.stk } := by
  unfold pop2 at h
  split at h
  · cases h; rename_i hs; exact ⟨hs, rfl⟩
  · cases h

theorem pop3_ok {s s' : St} {a b c : SV} (h : pop3 s = .ok (a, b, c, s')) :
    s.stk = a :: b :: c :: s'.stk ∧ s' = { s with stk := s'.stk } := by
  unfold pop3 at h
  split at h
  · cases h; rename_i hs; exact ⟨hs, rfl⟩
  · cases h

theorem push_ok {s s' : St} {v : SV} (h : push s v = .ok s') :
    s.stk.length < 1024 ∧ s' = { s with stk := v :: s.stk } := by
  unfold push at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h


/-! ## Stack opcodes -/

theorem const_rel (v : Nat) (w : UInt256) (h : w.toNat = v) : (SV.const v).Rel e ρ w.toNat :=
  ⟨Word.const_holds e v (h ▸ toNat_lt w), h⟩

/-- `PUSH1` .. `PUSH32` (the immediate as EVMLean decodes it). -/
theorem sim_push (fs : Facts) (code : Code) (s : State) (st st' : St) (op : Operation.POp)
    (arg : UInt256) (w v : Nat) (hop : op ≠ .PUSH0)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Push op, some (arg, w)))
    (harg : arg.toNat = v) (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.push v) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow (w + 1) st'.stk := by
  obtain ⟨hl, rfl⟩ := push_ok h
  refine sim_of e ρ s _ _ _ (arg :: s.machineState.stack) (s.machineState.stack.length - 0 + 1)
    ?_ (by rw [← hrel.length]; omega) (List.Forall₂.cons (const_rel e ρ v arg harg) hrel)
  rw [xstep_overlay _ s _ _ hdec (by simp)]
  exact step_push s op arg w hop hdec

/-- `PUSH0`. -/
theorem sim_push0 (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.PUSH0, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.push 0) st = .ok st') :
    Simulates e ρ s GasConstants.Gbase 1 st'.stk := by
  obtain ⟨hl, rfl⟩ := push_ok h
  refine sim_of e ρ s _ _ _ (⟨0⟩ :: s.machineState.stack) (s.machineState.stack.length - 0 + 1)
    ?_ (by rw [← hrel.length]; omega) (List.Forall₂.cons (const_rel e ρ 0 ⟨0⟩ rfl) hrel)
  rw [xstep_overlay _ s _ _ hdec (by simp)]
  exact step_push0 s hdec

/-- `DUP1` .. `DUP16`: the checker's `DUP` byte `b` and EVMLean's `DUPn` with `n = b - 0x7f`. -/
theorem sim_dup (fs : Facts) (code : Code) (s : State) (st st' : St) (b : Nat)
    (d : Operation.DOp) (hb : 0x80 ≤ b ∧ b ≤ 0x8f) (hd : dupN d = b - 0x7f)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Dup d, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.op b) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_pos hb] at h
  split at h
  · rename_i v hv
    obtain ⟨hl, rfl⟩ := push_ok h
    have hi : b - 0x80 < st.stk.length := (List.getElem?_eq_some_iff.mp hv).1
    have hv' : st.stk[b - 0x80] = v := (List.getElem?_eq_some_iff.mp hv).2
    have hlen := hrel.length
    have hn : ¬ s.machineState.stack.length < dupN d := by omega
    have hx := xstep_dup s d hdec
    rw [if_neg hn] at hx
    refine sim_of e ρ s _ 1 _
      ((s.machineState.stack.take (dupN d)).getLast! :: s.machineState.stack)
      (s.machineState.stack.length + 1) ?_ (by omega) ?_
    · rw [xstep_overlay _ s _ _ hdec (by simp), hx]; rfl
    · rw [take_getLast _ _ (by omega) (by omega)]
      refine List.Forall₂.cons ?_ hrel
      have := hrel.getElem e ρ (b - 0x80) hi (by omega)
      rw [hv'] at this
      have e1 : dupN d - 1 = b - 0x80 := by omega
      simp only [e1]; exact this
  · cases h

/-- The checker's swap describes EVMLean's. -/
theorem swap_rel (stk : List SV) (t : List UInt256) (n : Nat) (a c : SV) (hn : 1 ≤ n)
    (hrel : StkRel e ρ stk t) (ha : stk[0]? = some a) (hc : stk[n]? = some c) :
    n < t.length ∧ StkRel e ρ ((stk.set 0 c).set n a) (swapList n t) := by
  have hl := hrel.length
  have hn' : n < stk.length := (List.getElem?_eq_some_iff.mp hc).1
  have h0 : 0 < stk.length := by omega
  refine ⟨by omega, ?_⟩
  rw [swapList_eq n t hn (by omega)]
  have r0 := hrel.getElem e ρ 0 h0 (by omega)
  have rn := hrel.getElem e ρ n hn' (by omega)
  rw [(List.getElem?_eq_some_iff.mp ha).2] at r0
  rw [(List.getElem?_eq_some_iff.mp hc).2] at rn
  exact (hrel.set e ρ 0 c _ rn).set e ρ n a _ r0

/-- `SWAP1` .. `SWAP16`. -/
theorem sim_swap (fs : Facts) (code : Code) (s : State) (st st' : St) (b : Nat)
    (x : Operation.ExOp) (hb : 0x90 ≤ b ∧ b ≤ 0x9f) (hx : swapN x = b - 0x8f)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Exchange x, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hlen : st.stk.length ≤ 1024)
    (h : step fs code (.op b) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by omega), if_pos hb] at h
  split at h
  · rename_i a tl c hs hc
    cases h
    obtain ⟨hlt, hr⟩ := swap_rel e ρ st.stk _ (b - 0x8f) a c (by omega) hrel (by simp [hs]) hc
    have hn : ¬ s.machineState.stack.length < swapN x + 1 := by omega
    have hx' := xstep_swap s x hdec
    rw [if_neg hn] at hx'
    refine sim_of e ρ s _ 1 _ (swapList (swapN x) s.machineState.stack)
      s.machineState.stack.length ?_ (by rw [← hrel.length]; exact hlen) (by rw [hx]; exact hr)
    rw [xstep_overlay _ s _ _ hdec (by simp), hx']; rfl
  · cases h

/-- `sim_of` with the stack check first (as `Eip8024.exec` does it). -/
theorem sim_of' (s : State) (c n : Nat) (stk : List SV) (t : List UInt256) (L : Nat)
    (hx : Eip8024.Xstep (D_J s.executionEnv.code 0) s =
      if L > 1024 then .error .StackOverflow
      else if s.machineState.gasAvailable.toNat < c then .error .OutOfGass
      else .ok ({s with
        machineState.stack := t
        machineState.gasAvailable := s.machineState.gasAvailable.subNat c
        machineState.pc := s.machineState.pc + UInt256.ofNat n
        machineState.execLength := s.machineState.execLength + 1}, none))
    (hL : L ≤ 1024) (hr : StkRel e ρ stk t) : Simulates e ρ s c n stk := by
  rw [Simulates, hx, if_neg (by omega)]
  by_cases hg : s.machineState.gasAvailable.toNat < c
  · left; rw [if_pos hg]
  · right; rw [if_neg hg]; exact ⟨t, hr, by omega, rfl⟩

/-- DUPN (EIP-8024). -/
theorem sim_dupn (fs : Facts) (code : Code) (s : State) (st st' : St) (n : Nat) (hn : 1 ≤ n)
    (hdec : Eip8024.decode s.executionEnv.code s.machineState.pc.toNat = some (some (.dupn n)))
    (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.dupn n) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 2 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  split at h
  · rename_i v hv
    obtain ⟨hl, rfl⟩ := push_ok h
    have hi : n - 1 < st.stk.length := (List.getElem?_eq_some_iff.mp hv).1
    have hv' : st.stk[n - 1] = v := (List.getElem?_eq_some_iff.mp hv).2
    have hlen := hrel.length
    have hx := xstep_dupn (D_J s.executionEnv.code 0) s n hdec
    rw [if_neg (by omega)] at hx
    refine sim_of' e ρ s _ 2 _ ((s.machineState.stack.take n).getLast! :: s.machineState.stack)
      (s.machineState.stack.length + 1) hx (by omega) ?_
    rw [take_getLast _ _ hn (by omega)]
    refine List.Forall₂.cons ?_ hrel
    have := hrel.getElem e ρ (n - 1) hi (by omega)
    rw [hv'] at this; exact this
  · cases h

/-- SWAPN (EIP-8024). -/
theorem sim_swapn (fs : Facts) (code : Code) (s : State) (st st' : St) (n : Nat) (hn : 1 ≤ n)
    (hdec : Eip8024.decode s.executionEnv.code s.machineState.pc.toNat = some (some (.swapn n)))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hlen : st.stk.length ≤ 1024)
    (h : step fs code (.swapn n) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 2 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  split at h
  · rename_i a tl c hs hc
    cases h
    obtain ⟨hlt, hr⟩ := swap_rel e ρ st.stk _ n a c hn hrel (by simp [hs]) hc
    have hx := xstep_swapn (D_J s.executionEnv.code 0) s n hdec
    rw [if_neg (by omega)] at hx
    exact sim_of' e ρ s _ 2 _ (swapList n s.machineState.stack)
      (s.machineState.stack.length + 0) hx (by rw [← hrel.length]; omega) hr
  · cases h

/-- `POP`. -/
theorem sim_pop (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.POP, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hlen : st.stk.length ≤ 1024)
    (h : step fs code (.op 0x50) st = .ok st') :
    Simulates e ρ s GasConstants.Gbase 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, st1⟩, hp, h⟩ := bind_ok h
  cases h
  obtain ⟨hs, -⟩ := pop1_ok hp
  rw [hs] at hrel hlen
  obtain ⟨a, t, ht, -, hr⟩ := hrel.cons_inv
  have hl := hr.length
  refine sim_of e ρ s _ 1 _ t ((a :: t).length - 1 + 0) ?_ (by simp at hlen ⊢; omega) hr
  rw [xstep_overlay _ s _ _ hdec (by simp), step_pop s hdec, ht]
  rfl


/-- `JUMPDEST`. -/
theorem sim_jumpdest (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.JUMPDEST, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hlen : st.stk.length ≤ 1024)
    (h : step fs code (.op 0x5b) st = .ok st') :
    Simulates e ρ s GasConstants.Gjumpdest 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  cases h
  refine sim_of e ρ s _ 1 _ s.machineState.stack (s.machineState.stack.length - 0 + 0) ?_
    (by rw [← hrel.length]; omega) hrel
  rw [xstep_overlay _ s _ _ hdec (by simp), step_jumpdest s hdec]
  rfl

/-- An input word the checker pushes describes its value. -/
theorem input_rel (fs : Facts) (hf : Facts.Hold e fs) (t : Term) (w : UInt256)
    (hw : w.toNat = t.eval e) : (SV.word (mkInput fs t full)).Rel e ρ w.toNat := by
  have hlt : t.eval e < W := hw ▸ toNat_lt w
  have := mkInput_sound e fs hf t full (full_sound _ hlt) hlt
  exact ⟨this.1, by rw [this.2, hw]⟩

/-- `CALLVALUE`, for a call whose value is the environment's. -/
theorem sim_callvalue (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hcv : s.executionEnv.weiValue.toNat = e.cv % W)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CALLVALUE, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.op 0x34) st = .ok st') :
    Simulates e ρ s GasConstants.Gbase 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨hl, rfl⟩ := push_ok h
  refine sim_of e ρ s _ 1 _ (s.executionEnv.weiValue :: s.machineState.stack)
    (s.machineState.stack.length - 0 + 1) ?_ (by rw [← hrel.length]; omega)
    (List.Forall₂.cons (input_rel e ρ fs hf .cv _ hcv) hrel)
  rw [xstep_overlay _ s _ _ hdec (by simp), step_callvalue s hdec]
  rfl

/-- `CALLDATASIZE`, for a call whose calldata is the environment's. -/
theorem sim_calldatasize (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hf : Facts.Hold e fs) (hcd : s.executionEnv.calldata.size = e.cd.length)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CALLDATASIZE, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.op 0x36) st = .ok st') :
    Simulates e ρ s GasConstants.Gbase 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨hl, rfl⟩ := push_ok h
  refine sim_of e ρ s _ 1 _ (UInt256.ofNat s.executionEnv.calldata.size :: s.machineState.stack)
    (s.machineState.stack.length - 0 + 1) ?_ (by rw [← hrel.length]; omega)
    (List.Forall₂.cons (input_rel e ρ fs hf .cds _ (by rw [toNat_ofNat, hcd]; rfl)) hrel)
  rw [xstep_overlay _ s _ _ hdec (by simp), step_calldatasize s hdec]
  rfl

/-- `RETURNDATASIZE`: zero, as nothing here sets return data. -/
theorem sim_returndatasize (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hrd : s.machineState.returnData.size = 0)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.RETURNDATASIZE, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.op 0x3d) st = .ok st') :
    Simulates e ρ s GasConstants.Gbase 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨hl, rfl⟩ := push_ok h
  refine sim_of e ρ s _ 1 _ (UInt256.ofNat s.machineState.returnData.size :: s.machineState.stack)
    (s.machineState.stack.length - 0 + 1) ?_ (by rw [← hrel.length]; omega)
    (List.Forall₂.cons (const_rel e ρ 0 _ (by rw [toNat_ofNat, hrd]; rfl)) hrel)
  rw [xstep_overlay _ s _ _ hdec (by simp), step_returndatasize s hdec]
  rfl

end Poseidon2.Evm.Sim
