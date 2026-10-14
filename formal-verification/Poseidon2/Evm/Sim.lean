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
`MSTORE`, `MSIZE`, `CALLDATALOAD`, `CALLDATACOPY`, `CODECOPY`, which `MemSim.lean` covers with
the memory relation of `Memory.lean`, where `sim_lift` carries every lemma here over); control
flow (`JUMP`, `JUMPI`, `STOP`, `RETURN`, `REVERT`) is `ctl`, not `step`.

What the lemmas assume and the composition has to supply: the instruction EVMLean decodes at
`pc` for the checker's instruction (`DUPn` with `dupN d = b - 0x7f`, `SWAPn` with
`swapN x = b - 0x8f`, the `PUSH` immediate's value, DUPN / SWAPN with `1 ≤ n`); a checker
stack of at most 1024 items (`POP`, `JUMPDEST`, `SWAP`, SWAPN); a valuation valid on the
checker's new atom table (the field operations); the facts of the case (word terms); for
`CALLVALUE` / `CALLDATASIZE` the call's value and calldata, and for `RETURNDATASIZE` empty
return data.
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
  (s.machineState.gasAvailable.toNat < c ∧
    Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass) ∨
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
  · left; exact ⟨hg, by rw [if_pos hg]⟩
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
    (h : step fs code (.op 0x5f) st = .ok st') :
    Simulates e ρ s GasConstants.Gbase 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
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
  · left; exact ⟨hg, by rw [if_pos hg]⟩
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


/-! ## Arithmetic and comparison -/

/-- The shape of a unary operation `f` in EVMLean's `Xstep`. -/
def UnStep (s : State) (c : Nat) (f : UInt256 → UInt256) : Prop :=
  ∀ a t, s.machineState.stack = a :: t →
    Eip8024.Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.gasAvailable.toNat < c then .error .OutOfGass
      else if (a :: t).length - 1 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := f a :: t
        machineState.gasAvailable := s.machineState.gasAvailable.subNat c
        machineState.pc := s.machineState.pc + UInt256.ofNat 1
        machineState.execLength := s.machineState.execLength + 1}, none)

/-- The shape of a binary operation `f` (top of the stack first). -/
def BinStep (s : State) (c : Nat) (f : UInt256 → UInt256 → UInt256) : Prop :=
  ∀ a b t, s.machineState.stack = a :: b :: t →
    Eip8024.Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.gasAvailable.toNat < c then .error .OutOfGass
      else if (a :: b :: t).length - 2 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := f a b :: t
        machineState.gasAvailable := s.machineState.gasAvailable.subNat c
        machineState.pc := s.machineState.pc + UInt256.ofNat 1
        machineState.execLength := s.machineState.execLength + 1}, none)

/-- The shape of a ternary operation `f`. -/
def TriStep (s : State) (c : Nat) (f : UInt256 → UInt256 → UInt256 → UInt256) : Prop :=
  ∀ a b d t, s.machineState.stack = a :: b :: d :: t →
    Eip8024.Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.gasAvailable.toNat < c then .error .OutOfGass
      else if (a :: b :: d :: t).length - 3 + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := f a b d :: t
        machineState.gasAvailable := s.machineState.gasAvailable.subNat c
        machineState.pc := s.machineState.pc + UInt256.ofNat 1
        machineState.execLength := s.machineState.execLength + 1}, none)

theorem sim_un (s : State) (c : Nat) (f : UInt256 → UInt256) (hx : UnStep s c f)
    (x v : SV) (r : List SV) (hrel : StkRel e ρ (x :: r) s.machineState.stack)
    (hl : r.length < 1024) (hv : ∀ a, x.Rel e ρ a.toNat → v.Rel e ρ (f a).toNat) :
    Simulates e ρ s c 1 (v :: r) := by
  obtain ⟨a, t, ht, ha, hr⟩ := hrel.cons_inv
  have := hr.length
  exact sim_of e ρ s c 1 _ (f a :: t) _ (hx a t ht) (by simp; omega)
    (List.Forall₂.cons (hv a ha) hr)

theorem sim_bin (s : State) (c : Nat) (f : UInt256 → UInt256 → UInt256) (hx : BinStep s c f)
    (x y v : SV) (r : List SV) (hrel : StkRel e ρ (x :: y :: r) s.machineState.stack)
    (hl : r.length < 1024)
    (hv : ∀ a b, x.Rel e ρ a.toNat → y.Rel e ρ b.toNat → v.Rel e ρ (f a b).toNat) :
    Simulates e ρ s c 1 (v :: r) := by
  obtain ⟨a, t1, ht1, ha, hr1⟩ := hrel.cons_inv
  obtain ⟨b, t, ht, hb, hr⟩ := hr1.cons_inv
  subst ht
  have := hr.length
  exact sim_of e ρ s c 1 _ (f a b :: t) _ (hx a b t ht1) (by simp; omega)
    (List.Forall₂.cons (hv a b ha hb) hr)

theorem sim_tri (s : State) (c : Nat) (f : UInt256 → UInt256 → UInt256 → UInt256)
    (hx : TriStep s c f) (x y z v : SV) (r : List SV)
    (hrel : StkRel e ρ (x :: y :: z :: r) s.machineState.stack) (hl : r.length < 1024)
    (hv : ∀ a b d, x.Rel e ρ a.toNat → y.Rel e ρ b.toNat → z.Rel e ρ d.toNat →
      v.Rel e ρ (f a b d).toNat) :
    Simulates e ρ s c 1 (v :: r) := by
  obtain ⟨a, t1, ht1, ha, hr1⟩ := hrel.cons_inv
  obtain ⟨b, t2, ht2, hb, hr2⟩ := hr1.cons_inv
  obtain ⟨d, t, ht, hd, hr⟩ := hr2.cons_inv
  subst ht ht2
  have := hr.length
  exact sim_of e ρ s c 1 _ (f a b d :: t) _ (hx a b d t ht1) (by simp; omega)
    (List.Forall₂.cons (hv a b d ha hb hd) hr)

/-- A word operation the checker built with `mkBin` describes the EVM's result. -/
theorem wordBin_rel (fs : Facts) (hf : Facts.Hold e fs) (op : Nat) (x y v : SV)
    (f : UInt256 → UInt256 → UInt256)
    (hbin : ∀ a b : UInt256, binOp op a.toNat b.toNat = some (f a b).toNat)
    (h : wordBin fs op x y = .ok v) (a b : UInt256) (ha : x.Rel e ρ a.toNat)
    (hb : y.Rel e ρ b.toNat) : v.Rel e ρ (f a b).toNat := by
  unfold wordBin wordOf at h
  cases x with
  | lin _ _ => cases h
  | pw _ _ _ => cases h
  | word wa =>
    cases y with
    | lin _ _ => cases h
    | pw _ _ _ => cases h
    | word wb =>
      simp only [bind, Except.bind] at h
      split at h
      · rename_i w hw
        cases h
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        have := mkBin_sound e fs hf op wa wb w ha1 hb1 hw
        refine ⟨this.1, ?_⟩
        have h2 := this.2
        rw [← ha2, ← hb2, hbin] at h2
        exact (Option.some.inj h2).symm
      · cases h

/-- The word-only binary operations of `step`. -/
def WordBinOp (b : Nat) : Prop :=
  b = 0x03 ∨ b = 0x04 ∨ b = 0x10 ∨ b = 0x11 ∨ b = 0x12 ∨ b = 0x13 ∨ b = 0x14 ∨ b = 0x16 ∨
    b = 0x17 ∨ b = 0x18 ∨ b = 0x1c

theorem step_wordBin (fs : Facts) (code : Code) (st st' : St) (b : Nat) (hb : WordBinOp b)
    (h : step fs code (.op b) st = .ok st') :
    ∃ x y r v, st.stk = x :: y :: r ∧ wordBin fs b x y = .ok v ∧ r.length < 1024 ∧
      st'.stk = v :: r := by
  have h' : (do let (x, y, s) ← pop2 st; push s (← wordBin fs b x y)) = Except.ok st' := by
    unfold WordBinOp at hb
    unfold Checker.step at h; dsimp only at h
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [if_neg (by decide), if_neg (by decide)] at h; exact h
  obtain ⟨⟨x, y, st1⟩, hp, h1⟩ := bind_ok h'
  obtain ⟨v, hw, h2⟩ := bind_ok h1
  obtain ⟨hs, -⟩ := pop2_ok hp
  obtain ⟨hl, rfl⟩ := push_ok h2
  exact ⟨x, y, st1.stk, v, hs, hw, hl, rfl⟩

/-- `SUB`, `DIV`, `LT`, `GT`, `SLT`, `SGT`, `EQ`, `AND`, `OR`, `XOR`, `SHR` (on words), given
EVMLean's step for the operation `f`. -/
theorem sim_wordBin (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (b c : Nat) (hb : WordBinOp b) (f : UInt256 → UInt256 → UInt256)
    (hbin : ∀ a b' : UInt256, binOp b a.toNat b'.toNat = some (f a b').toNat)
    (hx : BinStep s c f) (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.op b) st = .ok st') : Simulates e ρ s c 1 st'.stk := by
  obtain ⟨x, y, r, v, hs, hw, hl, hst⟩ := step_wordBin fs code st st' b hb h
  rw [hst]
  rw [hs] at hrel
  exact sim_bin e ρ s c f hx x y v r hrel hl (wordBin_rel e ρ fs hf b x y v f hbin hw)


/-- `SUB`. -/
theorem sim_sub (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SUB, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x03) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x03 _ (by unfold WordBinOp; decide) (UInt256.sub) binOp_sub
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_sub s hdec, ht]; rfl) hrel h

/-- `DIV`. -/
theorem sim_div (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.DIV, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x04) st = .ok st') :
    Simulates e ρ s GasConstants.Glow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x04 _ (by unfold WordBinOp; decide) (UInt256.div) binOp_div
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_div s hdec, ht]; rfl) hrel h

/-- `LT`. -/
theorem sim_lt (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.LT, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x10) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x10 _ (by unfold WordBinOp; decide) (UInt256.lt) binOp_lt
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_lt s hdec, ht]; rfl) hrel h

/-- `GT`. -/
theorem sim_gt (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.GT, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x11) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x11 _ (by unfold WordBinOp; decide) (UInt256.gt) binOp_gt
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_gt s hdec, ht]; rfl) hrel h

/-- `SLT`. -/
theorem sim_slt (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SLT, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x12) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x12 _ (by unfold WordBinOp; decide) (UInt256.slt) binOp_slt
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_slt s hdec, ht]; rfl) hrel h

/-- `SGT`. -/
theorem sim_sgt (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SGT, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x13) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x13 _ (by unfold WordBinOp; decide) (UInt256.sgt) binOp_sgt
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_sgt s hdec, ht]; rfl) hrel h

/-- `EQ`. -/
theorem sim_eq (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.EQ, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x14) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x14 _ (by unfold WordBinOp; decide) (UInt256.eq) binOp_eq
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_eq s hdec, ht]; rfl) hrel h

/-- `AND`. -/
theorem sim_and (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.AND, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x16) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x16 _ (by unfold WordBinOp; decide) (UInt256.land) binOp_and
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_and s hdec, ht]; rfl) hrel h

/-- `OR`. -/
theorem sim_or (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.OR, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x17) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x17 _ (by unfold WordBinOp; decide) (UInt256.lor) binOp_or
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_or s hdec, ht]; rfl) hrel h

/-- `XOR`. -/
theorem sim_xor (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.XOR, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x18) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x18 _ (by unfold WordBinOp; decide) (UInt256.xor) binOp_xor
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_xor s hdec, ht]; rfl) hrel h

/-- `SHR`. -/
theorem sim_shr (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SHR, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x1c) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_wordBin e ρ fs code s st st' hf 0x1c _ (by unfold WordBinOp; decide) (fun a b => UInt256.shiftRight b a) binOp_shr
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_shr s hdec, ht]; rfl) hrel h


/-- A word operation the checker built with `mkBin` describes the operation's value. -/
theorem wordBin_rel' (fs : Facts) (hf : Facts.Hold e fs) (op : Nat) (x y v : SV)
    (h : wordBin fs op x y = .ok v) (a b : Nat) (ha : x.Rel e ρ a) (hb : y.Rel e ρ b) :
    v.Rel e ρ ((binOp op a b).getD 0) := by
  unfold wordBin wordOf at h
  cases x with
  | lin _ _ => cases h
  | pw _ _ _ => cases h
  | word wa =>
    cases y with
    | lin _ _ => cases h
    | pw _ _ _ => cases h
    | word wb =>
      simp only [bind, Except.bind] at h
      split at h
      · rename_i w hw
        cases h
        obtain ⟨ha1, rfl⟩ := ha
        obtain ⟨hb1, rfl⟩ := hb
        have := mkBin_sound e fs hf op wa wb w ha1 hb1 hw
        refine ⟨this.1, ?_⟩
        rw [← this.2]; rfl
      · cases h

/-- A value the checker knows exactly describes only that word. -/
theorem rel_exact (v : SV) (w n : Nat) (hv : v.Rel e ρ w) (hn : v.exact = some n) : w = n := by
  cases v with
  | word x => obtain ⟨hx, rfl⟩ := hv; exact Word.holds_exact e x hx n hn
  | lin _ _ => simp [SV.exact] at hn
  | pw _ _ _ => simp [SV.exact] at hn

/-- The field `ADD` / `MUL` of `addMul`. -/
theorem fieldAddMul_rel (op : Nat) (hop : op = 0x01 ∨ op = 0x02) (x y v : SV) (tb tb' : Tab)
    (h : (if op = 1 then do
        let (la, ba, tb) ← toLin x tb
        let (lb, bb, tb) ← toLin y tb
        if ba + bb < W then .ok (.lin (la.add lb) (ba + bb), tb)
        else .error "ADD may overflow"
      else
        match x.exact, y.exact with
        | some c, _ => do
          let (l, bnd, tb) ← toLin y tb
          if bnd * c < W then .ok (.lin (l.scale c) (bnd * c), tb) else .error "MUL may overflow"
        | _, some c => do
          let (l, bnd, tb) ← toLin x tb
          if bnd * c < W then .ok (.lin (l.scale c) (bnd * c), tb) else .error "MUL may overflow"
        | _, _ => .error "MUL of two field values") = Except.ok (v, tb'))
    (hv : Tab.Valid e ρ tb') (a b : Nat) (ha : x.Rel e ρ a) (hb : y.Rel e ρ b) :
    v.Rel e ρ ((binOp op a b).getD 0) := by
  split at h
  · rename_i hop1
    subst hop1
    obtain ⟨⟨la, ba, tb1⟩, h1, h'⟩ := bind_ok h
    obtain ⟨⟨lb, bb, tb2⟩, h2, h''⟩ := bind_ok h'
    dsimp only at h''
    split at h''
    · cases h''
      rename_i hlt
      exact (addField_sound e ρ x y a b tb tb1 _ la lb ba bb h1 h2 hlt ha hb hv).1
    · cases h''
  · have hop2 : op = 2 := by omega
    subst hop2
    cases hc : x.exact with
    | some c =>
      simp only [hc] at h
      obtain ⟨⟨l, bnd, tb1⟩, h1, h'⟩ := bind_ok h
      dsimp only at h'
      split at h'
      · cases h'
        rename_i hlt
        have := toLin_sound e ρ y b tb _ l bnd h1 hb hv
        have hac := rel_exact e ρ x a c ha hc
        subst hac
        exact mulConst_sound e ρ l bnd a b this.1 this.2.2.1 hlt
      · cases h'
    | none =>
      cases hd : y.exact with
      | some c =>
        simp only [hc, hd] at h
        obtain ⟨⟨l, bnd, tb1⟩, h1, h'⟩ := bind_ok h
        dsimp only at h'
        split at h'
        · cases h'
          rename_i hlt
          have := toLin_sound e ρ x a tb _ l bnd h1 ha hv
          have hbc := rel_exact e ρ y b c hb hd
          subst hbc
          show SV.Rel e ρ _ ((a * b) % W)
          rw [Nat.mul_comm a b]
          exact mulConst_sound e ρ l bnd b a this.1 this.2.2.1 hlt
        · cases h'
      | none => simp [hc, hd] at h

/-- `addMul` (the checker's `ADD` / `MUL`) describes the EVM's result. -/
theorem addMul_rel (fs : Facts) (hf : Facts.Hold e fs) (op : Nat) (hop : op = 0x01 ∨ op = 0x02)
    (x y v : SV) (tb tb' : Tab) (h : addMul fs op x y tb = .ok (v, tb'))
    (hv : Tab.Valid e ρ tb') (a b : Nat) (ha : x.Rel e ρ a) (hb : y.Rel e ρ b) :
    v.Rel e ρ ((binOp op a b).getD 0) := by
  unfold addMul at h
  dsimp only at h
  split at h <;> split at h
  all_goals first
    | (obtain ⟨v', hw, h2⟩ := bind_ok h
       cases h2
       exact wordBin_rel' e ρ fs hf op _ _ v hw a b ha hb)
    | exact fieldAddMul_rel e ρ op hop _ _ v tb tb' h hv a b ha hb

theorem sim_addMul (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (b c : Nat) (hb : b = 0x01 ∨ b = 0x02) (f : UInt256 → UInt256 → UInt256)
    (hbin : ∀ a b' : UInt256, binOp b a.toNat b'.toNat = some (f a b').toNat)
    (hx : BinStep s c f) (hrel : StkRel e ρ st.stk s.machineState.stack)
    (hv : Tab.Valid e ρ st'.tab) (h : step fs code (.op b) st = .ok st') :
    Simulates e ρ s c 1 st'.stk := by
  have h' : (do
      let (x, y, s) ← pop2 st
      let (v, tb) ← addMul fs b x y s.tab
      push { s with tab := tb } v) = Except.ok st' := by
    unfold Checker.step at h; dsimp only at h
    rcases hb with rfl | rfl <;>
    · rw [if_neg (by decide), if_neg (by decide)] at h; exact h
  obtain ⟨⟨x, y, st1⟩, hp, h1⟩ := bind_ok h'
  obtain ⟨⟨v, tb⟩, hw, h2⟩ := bind_ok h1
  obtain ⟨hs, -⟩ := pop2_ok hp
  obtain ⟨hl, rfl⟩ := push_ok h2
  rw [hs] at hrel
  refine sim_bin e ρ s c f hx x y v st1.stk hrel hl (fun a b' ha hb' => ?_)
  have := addMul_rel e ρ fs hf b hb x y v st1.tab tb hw hv a.toNat b'.toNat ha hb'
  rw [hbin] at this
  exact this

/-- `ADD`: on words, or on field values whose bounds sum below `2^256`. -/
theorem sim_add (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.ADD, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hv : Tab.Valid e ρ st'.tab)
    (h : step fs code (.op 0x01) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_addMul e ρ fs code s st st' hf 0x01 _ (.inl rfl) UInt256.add binOp_add
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_add s hdec, ht]; rfl)
    hrel hv h

/-- `MUL`: on words, or a field value by a constant, the bound kept below `2^256`. -/
theorem sim_mul (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MUL, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hv : Tab.Valid e ρ st'.tab)
    (h : step fs code (.op 0x02) st = .ok st') :
    Simulates e ρ s GasConstants.Glow 1 st'.stk :=
  sim_addMul e ρ fs code s st st' hf 0x02 _ (.inr rfl) UInt256.mul binOp_mul
    (fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_mul s hdec, ht]; rfl)
    hrel hv h

/-- `ISZERO`, `NOT` (on words). -/
theorem sim_unWord (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (b c : Nat) (hb : b = 0x15 ∨ b = 0x19) (f : UInt256 → UInt256)
    (hun : ∀ a : UInt256, unOp b a.toNat = some (f a).toNat)
    (hx : UnStep s c f) (hrel : StkRel e ρ st.stk s.machineState.stack)
    (h : step fs code (.op b) st = .ok st') :
    Simulates e ρ s c 1 st'.stk := by
  have h' : (do
      let (x, s) ← pop1 st
      let w ← wordOf x
      match mkUn fs b w with
      | some w => push s (.word w)
      | none => .error "unsupported unary operation") = Except.ok st' := by
    unfold Checker.step at h; dsimp only at h
    rcases hb with rfl | rfl <;>
    · rw [if_neg (by decide), if_neg (by decide)] at h; exact h
  obtain ⟨⟨x, st1⟩, hp, h1⟩ := bind_ok h'
  obtain ⟨wx, hw, h2⟩ := bind_ok h1
  obtain ⟨hs, -⟩ := pop1_ok hp
  rw [hs] at hrel
  split at h2
  · rename_i w hmk
    obtain ⟨hl, rfl⟩ := push_ok h2
    have hxw : x = .word wx := by
      unfold wordOf at hw; split at hw <;> cases hw; rfl
    subst hxw
    refine sim_un e ρ s c f hx _ _ st1.stk hrel hl (fun a ha => ?_)
    obtain ⟨ha1, ha2⟩ := ha
    have := mkUn_sound e fs hf b wx w ha1 hmk
    refine ⟨this.1, ?_⟩
    have h3 := this.2
    rw [← ha2, hun] at h3
    exact (Option.some.inj h3).symm
  · cases h2

/-- `ISZERO`. -/
theorem sim_iszero (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.ISZERO, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x15) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_unWord e ρ fs code s st st' hf 0x15 _ (.inl rfl) UInt256.isZero unOp_iszero
    (fun a t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_iszero s hdec, ht]; rfl)
    hrel h

/-- `NOT`. -/
theorem sim_not (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.NOT, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x19) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk :=
  sim_unWord e ρ fs code s st st' hf 0x19 _ (.inr rfl) UInt256.lnot unOp_not
    (fun a t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_not s hdec, ht]; rfl)
    hrel h

/-- `SHL`: on words, or `v · 2^k` of a field value with the bound kept below `2^256`. -/
theorem sim_shl (fs : Facts) (code : Code) (s : State) (st st' : St) (hf : Facts.Hold e fs)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SHL, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (h : step fs code (.op 0x1b) st = .ok st') :
    Simulates e ρ s GasConstants.Gverylow 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, y, st1⟩, hp, h1⟩ := bind_ok h
  obtain ⟨hs, -⟩ := pop2_ok hp
  rw [hs] at hrel
  have hx : BinStep s GasConstants.Gverylow (fun a b => UInt256.shiftLeft b a) :=
    fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_shl s hdec, ht]; rfl
  dsimp only at h1
  split at h1
  · rename_i k l bnd hk
    split at h1
    · rename_i hlt
      obtain ⟨hl, rfl⟩ := push_ok h1
      refine sim_bin e ρ s _ _ hx x _ _ st1.stk hrel hl (fun a b ha hb => ?_)
      have hak := rel_exact e ρ x a.toNat k ha hk
      obtain ⟨hb1, -, hb3⟩ := hb
      have := shlField_sound e ρ l bnd k b.toNat hb1 hb3 hlt.2
      have e1 := binOp_shl a b
      rw [hak, binOp, if_pos hlt.1] at e1
      rw [← Option.some.inj e1]
      exact this
    · cases h1
  · obtain ⟨v, hw, h2⟩ := bind_ok h1
    obtain ⟨hl, rfl⟩ := push_ok h2
    exact sim_bin e ρ s _ _ hx x _ v st1.stk hrel hl
      (wordBin_rel e ρ fs hf 0x1b x _ v _ binOp_shl hw)

theorem exactOf_ok {what : String} {v : SV} {n : Nat} (h : exactOf what v = .ok n) :
    v.exact = some n := by
  unfold exactOf at h
  split at h
  · cases h; assumption
  · cases h


theorem mod_toNat (a b : UInt256) :
    (UInt256.mod a b).toNat = if b.toNat = 0 then 0 else a.toNat % b.toNat := by
  have := binOp_mod a b
  simp only [binOp] at this
  exact (Option.some.inj this).symm

/-- `MOD`: of exact words, or by `P`. -/
theorem sim_mod (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MOD, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hv : Tab.Valid e ρ st'.tab)
    (h : step fs code (.op 0x06) st = .ok st') :
    Simulates e ρ s GasConstants.Glow 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, n, st1⟩, hp, h1⟩ := bind_ok h
  obtain ⟨hs, -⟩ := pop2_ok hp
  rw [hs] at hrel
  dsimp only at h1
  obtain ⟨m, hm, h2⟩ := bind_ok h1
  have hn := exactOf_ok hm
  have hx : BinStep s GasConstants.Glow UInt256.mod :=
    fun a b t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_mod s hdec, ht]; rfl
  split at h2
  · rename_i v hxv
    obtain ⟨hl, rfl⟩ := push_ok h2
    refine sim_bin e ρ s _ _ hx x n _ st1.stk hrel hl (fun a b ha hb => ?_)
    refine const_rel e ρ _ _ ?_
    rw [mod_toNat, rel_exact e ρ x a.toNat v ha hxv, rel_exact e ρ n b.toNat m hb hn]
  · split at h2
    · cases h2
    · rename_i hmP
      have hmP' : m = P := by simpa using hmP
      subst hmP'
      have hP : ∀ b : UInt256, n.Rel e ρ b.toNat → ¬ b.toNat = 0 ∧ b.toNat = P := fun b hb => by
        have := rel_exact e ρ n b.toNat P hb hn
        exact ⟨by rw [this]; decide, this⟩
      split at h2
      · obtain ⟨hl, rfl⟩ := push_ok h2
        refine sim_bin e ρ s _ _ hx _ n _ st1.stk hrel hl (fun a b ha hb => ?_)
        rw [mod_toNat, if_neg (hP b hb).1, (hP b hb).2]
        exact modP_pw e ρ _ _ _ _ ha
      · obtain ⟨⟨l, bnd, tb⟩, ht, h3⟩ := bind_ok h2
        obtain ⟨hl, rfl⟩ := push_ok h3
        refine sim_bin e ρ s _ _ hx _ n _ st1.stk hrel hl (fun a b ha hb => ?_)
        rw [mod_toNat, if_neg (hP b hb).1, (hP b hb).2]
        have := toLin_sound e ρ _ a.toNat _ _ l bnd ht ha hv
        exact modP_lin e ρ l bnd a.toNat ⟨this.1, this.2.1, this.2.2.1⟩


/-- `ADDMOD`: of exact words, or by `P`. -/
theorem sim_addmod (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.ADDMOD, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hv : Tab.Valid e ρ st'.tab)
    (h : step fs code (.op 0x08) st = .ok st') :
    Simulates e ρ s GasConstants.Gmid 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, y, n, st1⟩, hp, h1⟩ := bind_ok h
  obtain ⟨hs, -⟩ := pop3_ok hp
  rw [hs] at hrel
  dsimp only at h1
  obtain ⟨m, hm, h2⟩ := bind_ok h1
  have hn := exactOf_ok hm
  have hx : TriStep s GasConstants.Gmid UInt256.addMod :=
    fun a b d t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_addmod s hdec, ht]; rfl
  split at h2
  · rename_i u w hxu hyw
    obtain ⟨hl, rfl⟩ := push_ok h2
    refine sim_tri e ρ s _ _ hx x y n _ st1.stk hrel hl (fun a b d ha hb hd => ?_)
    refine const_rel e ρ _ _ ?_
    rw [toNat_addMod, rel_exact e ρ x a.toNat u ha hxu, rel_exact e ρ y b.toNat w hb hyw,
      rel_exact e ρ n d.toNat m hd hn]
  · split at h2
    · cases h2
    · rename_i hmP
      have hmP' : m = P := by simpa using hmP
      subst hmP'
      obtain ⟨⟨la, ba, tb1⟩, h3, h4⟩ := bind_ok h2
      obtain ⟨⟨lb, bb, tb2⟩, h5, h6⟩ := bind_ok h4
      obtain ⟨hl, rfl⟩ := push_ok h6
      refine sim_tri e ρ s _ _ hx x y n _ st1.stk hrel hl (fun a b d ha hb hd => ?_)
      have hdP := rel_exact e ρ n d.toNat P hd hn
      rw [toNat_addMod, hdP, if_neg (by decide)]
      have e2 := toLin_ext y tb1 tb2 lb bb h5
      have sa := toLin_sound e ρ x a.toNat _ tb1 la ba h3 ha (hv.of_ext e2)
      have sb := toLin_sound e ρ y b.toNat tb1 tb2 lb bb h5 hb hv
      exact addModP_sound e ρ la lb _ _ sa.2.2.1 sb.2.2.1

/-- `MULMOD`: of exact words, or by `P` (`mulModP`). -/
theorem sim_mulmod (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MULMOD, none))
    (hrel : StkRel e ρ st.stk s.machineState.stack) (hv : Tab.Valid e ρ st'.tab)
    (h : step fs code (.op 0x09) st = .ok st') :
    Simulates e ρ s GasConstants.Gmid 1 st'.stk := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, y, n, st1⟩, hp, h1⟩ := bind_ok h
  obtain ⟨hs, -⟩ := pop3_ok hp
  rw [hs] at hrel
  dsimp only at h1
  obtain ⟨m, hm, h2⟩ := bind_ok h1
  have hn := exactOf_ok hm
  have hx : TriStep s GasConstants.Gmid UInt256.mulMod :=
    fun a b d t ht => by rw [xstep_overlay _ s _ _ hdec (by simp), step_mulmod s hdec, ht]; rfl
  split at h2
  · rename_i u w hxu hyw
    obtain ⟨hl, rfl⟩ := push_ok h2
    refine sim_tri e ρ s _ _ hx x y n _ st1.stk hrel hl (fun a b d ha hb hd => ?_)
    refine const_rel e ρ _ _ ?_
    rw [toNat_mulMod, rel_exact e ρ x a.toNat u ha hxu, rel_exact e ρ y b.toNat w hb hyw,
      rel_exact e ρ n d.toNat m hd hn]
  · split at h2
    · cases h2
    · rename_i hmP
      have hmP' : m = P := by simpa using hmP
      subst hmP'
      obtain ⟨⟨v, tb⟩, h3, h4⟩ := bind_ok h2
      obtain ⟨hl, rfl⟩ := push_ok h4
      refine sim_tri e ρ s _ _ hx x y n _ st1.stk hrel hl (fun a b d ha hb hd => ?_)
      have hdP := rel_exact e ρ n d.toNat P hd hn
      rw [toNat_mulMod, hdP, if_neg (by decide)]
      exact (mulModP_sound e ρ x y a.toNat b.toNat _ _ v h3 ha hb hv).1

end Poseidon2.Evm.Sim
