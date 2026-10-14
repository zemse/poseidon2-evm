import Poseidon2.Evm.Control
import Poseidon2.Soundness

/-!
# The run: the checker's instructions as EVM steps, iterated with gas

* `step_len`, `step_ext`, `ctl_inv`, `runN_inv`: along the checker's run the stack has at most
  1024 items and the atom table only grows (so a valuation valid on the last table is valid on
  every earlier one);
* `sim_step`: every instruction `step` accepts, at a `pc` the run reaches, is one EVM step
  (`SimulatesM`) that costs at least 1 gas; it picks the opcode's lemma from `Sim.lean` /
  `MemSim.lean` and discharges its decoding hypotheses with `Decode.lean`;
* `step1_sim`: one instruction of the run (`step1`), control flow included (`Control.lean`),
  from states related by `At` to states related by `At`, or out of gas;
* `runN_sim`: `Eip8024.X` iterated over `runN`: as long as the checker's run continues, the EVM
  runs out of gas or reaches the related state, with more fuel left than gas, so the fuel
  `Ξ` gives (gas + 1) never runs out first;
* `reaches_final`: for an accepted case, the checker's run reaches its `RETURN` or `REVERT`
  (`run_final`), and the EVM's run of the call from `fresh` (the state `Ξ` starts from,
  `Xi_eq`) runs out of gas or reaches a state related to the checker's at that instruction.
  The segment checkpoints of `Proofs/` need nothing more: `seg_run` turns them into this one
  `run`.

The last instruction, `RETURN` or `REVERT` from a state related by `At`, the valuation `ρ` on
the last atom table and `CheckerSound` itself are in `Final.lean`.
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

/-! ## Invariants of the checker's run -/

theorem mstore_stk {s s' : St} {a : Nat} {v : SV} (h : mstore s a v = .ok s') :
    s'.stk = s.stk ∧ s'.tab = s.tab := by
  unfold mstore at h
  obtain ⟨m, -, h2⟩ := bind_ok h
  cases h2; exact ⟨rfl, rfl⟩

theorem zeroFill_stk : ∀ (k d : Nat) (s s' : St), zeroFill s k d = .ok s' →
    s'.stk = s.stk ∧ s'.tab = s.tab
  | 0, _, s, s', h => by cases h; exact ⟨rfl, rfl⟩
  | k + 1, d, s, s', h => by
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    have a := mstore_stk h1
    have b := zeroFill_stk k _ s1 s' h2
    exact ⟨b.1.trans a.1, b.2.trans a.2⟩

theorem cdCopy_stk (fs : Facts) : ∀ (k d src : Nat) (s s' : St), cdCopy fs s k d src = .ok s' →
    s'.stk = s.stk ∧ s'.tab = s.tab
  | 0, _, _, s, s', h => by cases h; exact ⟨rfl, rfl⟩
  | k + 1, d, src, s, s', h => by
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    have a := mstore_stk h1
    have b := cdCopy_stk fs k _ _ s1 s' h2
    exact ⟨b.1.trans a.1, b.2.trans a.2⟩

theorem codeCopy_go_stk : ∀ (k d : Nat) (bs : List Nat) (s s' : St),
    codeCopy.go bs s k d = .ok s' → s'.stk = s.stk ∧ s'.tab = s.tab
  | 0, _, _, s, s', h => by cases h; exact ⟨rfl, rfl⟩
  | k + 1, d, bs, s, s', h => by
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    have a := mstore_stk h1
    have b := codeCopy_go_stk k _ _ s1 s' h2
    exact ⟨b.1.trans a.1, b.2.trans a.2⟩

theorem pop1_len {s : St} {v : SV × St} (h : pop1 s = .ok v) :
    v.2.stk.length < s.stk.length ∧ v.2.tab = s.tab := by
  unfold pop1 at h; split at h <;> cases h; rename_i hs; simp [hs]

theorem pop2_len {s : St} {v : SV × SV × St} (h : pop2 s = .ok v) :
    v.2.2.stk.length < s.stk.length ∧ v.2.2.tab = s.tab := by
  unfold pop2 at h; split at h <;> cases h; rename_i hs; simp [hs]

theorem pop3_len {s : St} {v : SV × SV × SV × St} (h : pop3 s = .ok v) :
    v.2.2.2.stk.length < s.stk.length ∧ v.2.2.2.tab = s.tab := by
  unfold pop3 at h; split at h <;> cases h; rename_i hs; simp [hs]; omega

/-- A successful `step` leaves at most 1024 stack items. -/
theorem step_len (fs : Facts) (code : Code) (i : Ins) (st st' : St)
    (h : step fs code i st = .ok st') (hl : st.stk.length ≤ 1024) : st'.stk.length ≤ 1024 := by
  unfold Poseidon2.Checker.step at h
  simp only [bind, Except.bind, push, exactOf, Poseidon2.Checker.codeCopy] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hl)
    | (cases h; simp only [List.length_cons, List.length_set]; omega)
    | (cases h; have := (pop1_len (by assumption)).1; omega)
    | (rw [(mstore_stk h).1]; exact le_trans (Nat.le_of_lt (pop2_len (by assumption)).1) hl)
    | (rw [(zeroFill_stk _ _ _ _ h).1]
       exact le_trans (Nat.le_of_lt (pop3_len (by assumption)).1) hl)
    | (rw [(cdCopy_stk _ _ _ _ _ _ h).1]
       exact le_trans (Nat.le_of_lt (pop3_len (by assumption)).1) hl)
    | (rw [(codeCopy_go_stk _ _ _ _ _ h).1]
       exact le_trans (Nat.le_of_lt (pop3_len (by assumption)).1) hl)

theorem toLin_ext' {v : SV} {tb : Tab} {r : Lin × Nat × Tab} (h : toLin v tb = .ok r) :
    tb.Ext r.2.2 := toLin_ext v tb r.2.2 r.1 r.2.1 h

theorem scaleMod_ext {v : SV} {c : Nat} {tb : Tab} {r : SV × Tab} (h : scaleMod v c tb = .ok r) :
    tb.Ext r.2 := by
  unfold scaleMod at h
  split at h
  · cases h; exact Tab.Ext.refl _
  · split at h
    · cases h; exact Tab.Ext.refl _
    · obtain ⟨q, hq, h2⟩ := bind_ok h
      cases h2; exact toLin_ext' hq

theorem mulModP_ext {a b : SV} {tb : Tab} {r : SV × Tab} (h : mulModP a b tb = .ok r) :
    tb.Ext r.2 := by
  unfold mulModP at h
  split at h
  · cases h; exact Tab.Ext.refl _
  · exact scaleMod_ext h
  · exact scaleMod_ext h
  · obtain ⟨⟨ca, la, ka, tb1⟩, h1, h'⟩ := bind_ok h
    obtain ⟨⟨cb, lb, kb, tb2⟩, h2, h''⟩ := bind_ok h'
    have e1 := toPow_ext a tb tb1 ca la ka h1
    have e2 := toPow_ext b tb1 tb2 cb lb kb h2
    dsimp only at h''
    split at h''
    · cases h''
    · split at h''
      · cases h''; exact e1.trans e2
      · split at h''
        · cases h''; exact (e1.trans e2).trans (Tab.sbox_ext _ _)
        · cases h''

theorem addMul_ext {fs : Facts} {op : Nat} {a b : SV} {tb : Tab} {r : SV × Tab}
    (h : addMul fs op a b tb = .ok r) : tb.Ext r.2 := by
  unfold addMul at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact Tab.Ext.refl _)
    | (cases h; exact toLin_ext' (by assumption))
    | (cases h; exact (toLin_ext' (by assumption)).trans (toLin_ext' (by assumption)))

/-- A successful `step` only adds atoms to the table. -/
theorem step_ext (fs : Facts) (code : Code) (i : Ins) (st st' : St)
    (h : step fs code i st = .ok st') : st.tab.Ext st'.tab := by
  unfold Poseidon2.Checker.step at h
  simp only [bind, Except.bind, push, exactOf, Poseidon2.Checker.codeCopy] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact Tab.Ext.refl _)
    | (cases h; rw [← (pop1_len (by assumption)).2]; exact Tab.Ext.refl _)
    | (cases h; rw [← (pop2_len (by assumption)).2]; exact Tab.Ext.refl _)
    | (cases h; rw [← (pop3_len (by assumption)).2]; exact Tab.Ext.refl _)
    | (cases h; rw [← (pop2_len (by assumption)).2]; exact addMul_ext (by assumption))
    | (cases h; rw [← (pop2_len (by assumption)).2]; exact toLin_ext' (by assumption))
    | (cases h; rw [← (pop3_len (by assumption)).2]; exact mulModP_ext (by assumption))
    | (cases h; rw [← (pop3_len (by assumption)).2];
       exact (toLin_ext' (by assumption)).trans (toLin_ext' (by assumption)))
    | (rw [(mstore_stk h).2, ← (pop2_len (by assumption)).2]; exact Tab.Ext.refl _)
    | (rw [(zeroFill_stk _ _ _ _ h).2, ← (pop3_len (by assumption)).2]; exact Tab.Ext.refl _)
    | (rw [(cdCopy_stk _ _ _ _ _ _ h).2, ← (pop3_len (by assumption)).2]; exact Tab.Ext.refl _)
    | (rw [(codeCopy_go_stk _ _ _ _ _ h).2, ← (pop3_len (by assumption)).2]; exact Tab.Ext.refl _)

/-! ## Decoded instructions and the instructions `step` accepts

`decodeOne_op`, `decodeOne_push`, `decodeOne_dupn`, `decodeOne_swapn`: the byte and the length
behind each instruction the checker decoded. -/

theorem decodeOne_op {b : Nat} {tl : List Nat} {b' n : Nat} {r : Option (List Nat)}
    (h : decodeOne b tl = (.op b', n, r)) :
    b' = b ∧ ¬ (0x60 ≤ b ∧ b ≤ 0x7f) ∧ b ≠ 0xe6 ∧ b ≠ 0xe7 ∧ n = 1 := by
  unfold decodeOne at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp only [Prod.mk.injEq, Ins.op.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨by omega, by omega, by omega, by omega, rfl⟩
    · split at h
      · split at h <;> (try split at h) <;> simp at h
      · simp only [Prod.mk.injEq, Ins.op.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        refine ⟨rfl, by assumption, ?_, ?_, rfl⟩ <;> omega

theorem decodeOne_push {b : Nat} {tl : List Nat} {v n : Nat} {r : Option (List Nat)}
    (h : decodeOne b tl = (.push v, n, r)) :
    0x60 ≤ b ∧ b ≤ 0x7f ∧ (∃ rest, takeBytes (b - 0x5f) tl 0 = some (v, rest)) ∧
      n = 1 + (b - 0x5f) := by
  unfold decodeOne at h
  split at h
  · rename_i hb
    split at h
    · rename_i v' rest ht
      simp only [Prod.mk.injEq, Ins.push.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨hb.1, hb.2, ⟨rest, ht⟩, rfl⟩
    · simp at h
  · split at h
    · simp at h
    · split at h
      · split at h <;> (try split at h) <;> simp at h
      · simp at h

theorem decodeOne_dupn {b : Nat} {tl : List Nat} {m n : Nat} {r : Option (List Nat)}
    (h : decodeOne b tl = (.dupn m, n, r)) :
    b = 0xe6 ∧ Checker.decodeSingle (tl.headD 0) = some m ∧ n = 2 := by
  unfold decodeOne at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hb
        split at h
        · rename_i m' hm
          split at h
          · simp only [Prod.mk.injEq, Ins.dupn.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact ⟨by assumption, hm, rfl⟩
          · simp at h
        · simp at h
      · simp at h

theorem decodeOne_swapn {b : Nat} {tl : List Nat} {m n : Nat} {r : Option (List Nat)}
    (h : decodeOne b tl = (.swapn m, n, r)) :
    b = 0xe7 ∧ Checker.decodeSingle (tl.headD 0) = some m ∧ n = 2 := by
  unfold decodeOne at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hb
        split at h
        · rename_i m' hm
          split at h
          · simp at h
          · simp only [Prod.mk.injEq, Ins.swapn.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact ⟨by omega, hm, rfl⟩
        · simp at h
      · simp at h

/-- The opcodes `step` accepts. -/
def stepOps : List Nat :=
  [0x01, 0x02, 0x1b, 0x03, 0x04, 0x10, 0x11, 0x12, 0x13, 0x14, 0x16, 0x17, 0x18, 0x1c, 0x15,
   0x19, 0x06, 0x08, 0x09, 0x34, 0x35, 0x36, 0x3d, 0x37, 0x39, 0x50, 0x51, 0x52, 0x59, 0x5b,
   0x5f]

theorem step_op_cases {fs : Facts} {code : Code} {b : Nat} {st st' : St}
    (h : step fs code (.op b) st = .ok st') :
    (0x80 ≤ b ∧ b ≤ 0x8f) ∨ (0x90 ≤ b ∧ b ≤ 0x9f) ∨ b ∈ stepOps := by
  unfold Poseidon2.Checker.step at h
  dsimp only at h
  split at h
  · exact Or.inl (by assumption)
  · split at h
    · exact Or.inr (Or.inl (by assumption))
    · right; right
      split at h <;> first | (cases h; done) | simp [stepOps]

variable (e : Env) (ρ : Nat → F)

/-- What a call keeps fixed and the opcode simulations assume about it. -/
structure Frame (bs : List Nat) (s : State) : Prop where
  code : s.executionEnv.code = codeBA bs
  cd : s.executionEnv.calldata.data.toList = e.cd
  cdl : e.cd.length < W
  cv : s.executionEnv.weiValue.toNat = e.cv % W
  rd : s.machineState.returnData.size = 0

theorem bytes_codeBA {bs : List Nat} (hall : bs.all (· < 256) = true) :
    bs = (codeBA bs).data.toList.map UInt8.toNat := by
  simp only [codeBA, List.map_map]
  conv_lhs => rw [← List.map_id bs]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp, id, UInt8.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (lt_of_all hall hx)).symm

theorem Frame.size {bs : List Nat} {s : State} (h : Frame e bs s) :
    s.executionEnv.calldata.size = e.cd.length := by
  rw [← h.cd, Array.length_toList, ByteArray.size_data]

/-- A `SimulatesM` step of an instruction that keeps memory, at static gas `c`, is a step at the
checker's gas `insGas`. -/
theorem keepM {fs : Facts} {code : Code} {i : Ins} {s : State} {c n : Nat} {st st' : St}
    (h : step fs code i st = .ok st') (hi : i ∉ [.op 0x37, .op 0x39, .op 0x51, .op 0x52])
    (hs : SimulatesM e ρ s c n st') (hc : staticGas i st = c) (hc1 : 1 ≤ c) :
    1 ≤ insGas i st st' ∧ SimulatesM e ρ s (insGas i st st') n st' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  have hk := step_mem fs code i st st' h hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have he : insGas i st st' = c := by rw [insGas, hk.2, hc]; simp
  rw [he]; exact ⟨hc1, hs⟩

/-- A `Simulates` step of an instruction that keeps memory, at the checker's gas. -/
theorem lift1 {fs : Facts} {code : Code} {i : Ins} {s : State} {c n : Nat} {st st' : St}
    (h : step fs code i st = .ok st') (hi : i ∉ [.op 0x37, .op 0x39, .op 0x51, .op 0x52])
    (hr : StRel e ρ st s.machineState) (hs : Simulates e ρ s c n st'.stk)
    (hc : staticGas i st = c) (hc1 : 1 ≤ c) :
    1 ≤ insGas i st st' ∧ SimulatesM e ρ s (insGas i st st') n st' := by
  refine keepM e ρ h hi ?_ hc hc1
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  exact sim_lift e ρ fs code i s c n st st' h hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hr hs

theorem insGas_pos {i : Ins} {st st' : St} (h : 1 ≤ staticGas i st) : 1 ≤ insGas i st st' := by
  unfold insGas; omega

/-- **One instruction of `step`**: wherever the checker's run decoded instruction `i` (of
`n` bytes) from the code, a successful `step` is one EVM step costing the checker's gas
`insGas i st st'`, at least 1. -/
theorem sim_step (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts)
    (hf : Facts.Hold e fs) (s : State) (st st' : St) (hF : Frame e bs s)
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (hv : Tab.Valid e ρ st'.tab) {b : Nat} {tl : List Nat} {i : Ins} {n : Nat}
    {r : Option (List Nat)} (hd : bs.drop s.machineState.pc.toNat = b :: tl)
    (hpc : s.machineState.pc.toNat + 33 ≤ 33 * codeFuel) (ho : decodeOne b tl = (i, n, r))
    (h : step fs (Code.ofBytes bs) i st = .ok st') :
    1 ≤ insGas i st st' ∧ SimulatesM e ρ s (insGas i st st') n st' := by
  have hrel := hr.stk
  have hD : ∀ op, parseInstr (UInt8.ofNat b) = some op → ¬ (0x60 ≤ b ∧ b ≤ 0x7f) →
      EVM.decode s.executionEnv.code s.machineState.pc = some (op, none) :=
    fun op hp hb => hF.code ▸ decode_op hall hd hb hp
  have h64 : s.machineState.pc.toNat + 33 < 2 ^ 64 := by unfold codeFuel at hpc; omega
  cases i with
  | push v =>
    obtain ⟨hb1, hb2, ⟨rest, ht⟩, rfl⟩ := decodeOne_push ho
    obtain ⟨op, arg, hdec, hop, harg⟩ := decode_push hall hd ⟨hb1, hb2⟩ ht h64
    rw [← hF.code] at hdec
    have := sim_push e ρ fs _ s st st' op arg (b - 0x5f) v hop hdec harg hrel h
    rw [show 1 + (b - 0x5f) = b - 0x5f + 1 by omega]
    exact lift1 e ρ h (by simp) hr this rfl (by decide)
  | dupn m =>
    obtain ⟨rfl, hm, rfl⟩ := decodeOne_dupn ho
    obtain ⟨hdec, hm17⟩ := decode_dupn hall hd hm
    rw [← hF.code] at hdec
    exact lift1 e ρ h (by simp) hr
      (sim_dupn e ρ fs _ s st st' m (by omega) hdec hrel h) rfl (by decide)
  | swapn m =>
    obtain ⟨rfl, hm, rfl⟩ := decodeOne_swapn ho
    obtain ⟨hdec, hm17⟩ := decode_swapn hall hd hm
    rw [← hF.code] at hdec
    exact lift1 e ρ h (by simp) hr
      (sim_swapn e ρ fs _ s st st' m (by omega) hdec hrel hlen h) rfl (by decide)
  | bad b' => simp [Checker.step] at h
  | op b' =>
    obtain ⟨rfl, hnp, -, -, rfl⟩ := decodeOne_op ho
    rcases step_op_cases h with hb | hb | hb
    · obtain ⟨d, hp, hdn⟩ := dupOk_eq (parse_dup b' (head_lt hall hd) hb.1 hb.2)
      exact lift1 e ρ h (by
          have := hb
          simp only [List.mem_cons, List.not_mem_nil, Ins.op.injEq, or_false]; omega) hr
        (sim_dup e ρ fs _ s st st' b' d hb hdn (hD _ hp hnp) hrel h)
        (by simp only [staticGas]; rw [if_pos (by omega)]; rfl) (by decide)
    · obtain ⟨x, hp, hxn⟩ := swapOk_eq (parse_swap b' (head_lt hall hd) hb.1 hb.2)
      exact lift1 e ρ h (by
          have := hb
          simp only [List.mem_cons, List.not_mem_nil, Ins.op.injEq, or_false]; omega) hr
        (sim_swap e ρ fs _ s st st' b' x hb hxn (hD _ hp hnp) hrel hlen h)
        (by simp only [staticGas]; rw [if_pos (by omega)]; rfl) (by decide)
    · simp only [stepOps, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact lift1 e ρ h (by decide) hr (sim_add e ρ fs _ s st st' hf (hD _ rfl hnp) hrel hv h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_mul e ρ fs _ s st st' hf (hD _ rfl hnp) hrel hv h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_shl e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_sub e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_div e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_lt e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_gt e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_slt e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_sgt e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_eq e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_and e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_or e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_xor e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_shr e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_iszero e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_not e ρ fs _ s st st' hf (hD _ rfl hnp) hrel h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_mod e ρ fs _ s st st' (hD _ rfl hnp) hrel hv h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_addmod e ρ fs _ s st st' (hD _ rfl hnp) hrel hv h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_mulmod e ρ fs _ s st st' (hD _ rfl hnp) hrel hv h)
          rfl (by decide)
      · exact lift1 e ρ h (by decide) hr
          (sim_callvalue e ρ fs _ s st st' hf hF.cv (hD _ rfl hnp) hrel h) rfl (by decide)
      · exact keepM e ρ h (by decide)
          (sim_calldataload e ρ fs _ s st st' hf hF.cd (hD _ rfl hnp) hr h) rfl (by decide)
      · exact lift1 e ρ h (by decide) hr
          (sim_calldatasize e ρ fs _ s st st' hf (hF.size e) (hD _ rfl hnp) hrel h) rfl (by decide)
      · exact lift1 e ρ h (by decide) hr
          (sim_returndatasize e ρ fs _ s st st' hF.rd (hD _ rfl hnp) hrel h) rfl (by decide)
      · exact ⟨insGas_pos (by show 1 ≤ 3 + _; omega),
          sim_calldatacopy e ρ fs _ s st st' hf hF.cd hF.cdl (hD _ rfl hnp) hr hlen h⟩
      · exact ⟨insGas_pos (by show 1 ≤ 3 + _; omega),
          sim_codecopy e ρ fs _ s st st' (by rw [hF.code]; exact bytes_codeBA hall)
            (hD _ rfl hnp) hr hlen h⟩
      · exact lift1 e ρ h (by decide) hr (sim_pop e ρ fs _ s st st' (hD _ rfl hnp) hrel hlen h)
          rfl (by decide)
      · exact ⟨insGas_pos (by show 1 ≤ 3; decide), sim_mload e ρ fs _ s st st' (hD _ rfl hnp) hr h⟩
      · exact ⟨insGas_pos (by show 1 ≤ 3; decide), sim_mstore e ρ fs _ s st st' (hD _ rfl hnp) hr hlen h⟩
      · exact keepM e ρ h (by decide) (sim_msize e ρ fs _ s st st' (hD _ rfl hnp) hr h) rfl
          (by decide)
      · exact lift1 e ρ h (by decide) hr
          (sim_jumpdest e ρ fs _ s st st' (hD _ rfl hnp) hrel hlen h) rfl (by decide)
      · exact lift1 e ρ h (by decide) hr (sim_push0 e ρ fs _ s st st' (hD _ rfl hnp) hrel h)
          rfl (by decide)

theorem toNat_add_ofNat (a : UInt256) (n : Nat) :
    (a + UInt256.ofNat n).toNat = (a.toNat + n) % W := by
  show (a.toNat + n % W) % W = _
  simp only [Nat.add_mod_mod]

/-! ## Control flow: one instruction of the run -/

/-- `ctl` falls through only on `JUMPI` (zero condition) or on a successful `step`. -/
theorem ctl_fall {fs : Facts} {code : Code} {pc : Nat} {i : Ins} {st st' : St}
    (h : ctl fs code pc i st = .fall st') : i = .op 0x57 ∨ step fs code i st = .ok st' := by
  unfold ctl at h
  dsimp only at h
  split at h
  all_goals first
    | (left; rfl)
    | (repeat' (split at h)) <;> first | (cases h; done) | (right; cases h; assumption)

/-- `ctl` jumps only on `JUMP` and `JUMPI`. -/
theorem ctl_jump {fs : Facts} {code : Code} {pc t : Nat} {i : Ins} {st st' : St}
    (h : ctl fs code pc i st = .jump t st') : i = .op 0x56 ∨ i = .op 0x57 := by
  unfold ctl at h
  dsimp only at h
  split at h
  all_goals first
    | (left; rfl)
    | (right; rfl)
    | (repeat' (split at h)) <;> cases h

/-- What `ctl` continues with has at most 1024 stack items and extends the atom table. -/
theorem ctl_inv {fs : Facts} {code : Code} {pc : Nat} {i : Ins} {st st' : St}
    (h : (∃ t, ctl fs code pc i st = .jump t st') ∨ ctl fs code pc i st = .fall st')
    (hl : st.stk.length ≤ 1024) : st'.stk.length ≤ 1024 ∧ st.tab.Ext st'.tab := by
  have hstep : step fs code i st = .ok st' →
      st'.stk.length ≤ 1024 ∧ st.tab.Ext st'.tab :=
    fun hs => ⟨step_len fs code i st st' hs hl, step_ext fs code i st st' hs⟩
  rcases h with ⟨t, h⟩ | h <;>
  · unfold ctl at h
    dsimp only at h
    split at h
    all_goals
      repeat' (split at h)
    all_goals first
      | (cases h; done)
      | (cases h; have := pop1_len (by assumption); dsimp only at this
         exact ⟨by omega, by rw [this.2]; exact Tab.Ext.refl _⟩)
      | (cases h; have := pop2_len (by assumption); dsimp only at this
         exact ⟨by omega, by rw [this.2]; exact Tab.Ext.refl _⟩)
      | (cases h; exact hstep (by assumption))

/-- `JUMP` and `JUMPI` keep the memory size. -/
theorem ctl_keep_msize {fs : Facts} {code : Code} {pc b : Nat} {st st' : St}
    (hb : b = 0x56 ∨ b = 0x57)
    (h : (∃ t, ctl fs code pc (.op b) st = .jump t st') ∨ ctl fs code pc (.op b) st = .fall st') :
    st'.msize = st.msize := by
  rcases hb with rfl | rfl <;> rcases h with ⟨t, h⟩ | h <;>
  · simp only [ctl] at h
    repeat' (split at h)
    all_goals first
      | (cases h; done)
      | (cases h; exact (pop1_keep ‹pop1 _ = _›).2)
      | (cases h; exact (pop2_keep ‹pop2 _ = _›).2)

/-- One instruction of the run: `ctl` falls through or jumps to `st1`, and the run continues
from `st1` with the instruction's gas added. -/
theorem step1_next {fs : Facts} {code : Code} {is is' : List (Nat × Ins)} {st st' : St}
    (h : step1 fs code is st = .next is' st') :
    ∃ p i rest st1, is = (p, i) :: rest ∧ st' = { st1 with gas := st.gas + insGas i st st1 } ∧
      ((ctl fs code p i st = .fall st1 ∧ is' = rest) ∨
        ∃ t, ctl fs code p i st = .jump t st1 ∧ findDest t code.dests = some is') := by
  match is, h with
  | (p, i) :: rest, h =>
    simp only [step1] at h
    split at h
    · rename_i s1 hc
      cases h; exact ⟨p, i, _, s1, rfl, rfl, Or.inl ⟨hc, rfl⟩⟩
    · rename_i t s1 hc
      split at h
      · rename_i is1 hf
        cases h; exact ⟨p, i, _, s1, rfl, rfl, Or.inr ⟨t, hc, hf⟩⟩
      · cases h
    · cases h

theorem runN_inv {fs : Facts} {code : Code} :
    ∀ (k : Nat) (is is' : List (Nat × Ins)) (st st' : St),
      runN fs code k is st = .next is' st' →
      st.stk.length ≤ 1024 → st'.stk.length ≤ 1024 ∧ st.tab.Ext st'.tab
  | 0, _, _, _, _, h, hl => by
    simp only [runN, Out.next.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hl, Tab.Ext.refl _⟩
  | k + 1, is, is', st, st', h, hl => by
    simp only [runN] at h
    split at h
    · rename_i is1 st1 h1
      obtain ⟨p, i, rest, st2, -, rfl, hc⟩ := step1_next h1
      have h2 := ctl_inv (by
        rcases hc with ⟨hc, -⟩ | ⟨t, hc, -⟩
        · exact Or.inr hc
        · exact Or.inl ⟨t, hc⟩) hl
      have h3 := runN_inv k is1 is' _ st' h h2.1
      exact ⟨h3.1, h2.2.trans h3.2⟩
    · cases h

/-- Along the run the gas used only grows. -/
theorem runN_gas {fs : Facts} {code : Code} :
    ∀ (k : Nat) (is is' : List (Nat × Ins)) (st st' : St),
      runN fs code k is st = .next is' st' → st.gas ≤ st'.gas
  | 0, _, _, _, _, h => by
    simp only [runN, Out.next.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact le_refl _
  | k + 1, is, is', st, st', h => by
    simp only [runN] at h
    split at h
    · rename_i is1 st1 h1
      obtain ⟨p, i, rest, st2, -, rfl, -⟩ := step1_next h1
      have := runN_gas k is1 is' _ st' h
      simp only at this
      omega
    · cases h

/-! ## The relation along the run -/

/-- The checker about to run the instruction list `is` in state `st`, and the EVM in state `s`:
the frame, `StRel`, at most 1024 stack items, `is` reachable, and the EVM's `pc` at the first
instruction of `is`. -/
structure At (bs : List Nat) (is : List (Nat × Ins)) (st : St) (s : State) : Prop where
  frame : Frame e bs s
  rel : StRel e ρ st s.machineState
  len : st.stk.length ≤ 1024
  dec : Dec bs is
  pc : ∀ p i rest, is = (p, i) :: rest → s.machineState.pc.toNat = p

/-- The gas a checker state records plays no part in `StRel`. -/
theorem StRel.charge {st : St} {μ : MachineState} (g : Nat) (h : StRel e ρ st μ) :
    StRel e ρ { st with gas := g } μ :=
  ⟨h.stk, h.mem, h.msize, h.gas⟩

/-- The EVM's step from `s` as one checker step of gas `c` to `is'`, `st'`: out of gas, with less
than `c` gas available, or a step that pays `c`, keeps the execution environment and reaches a
related state. -/
def StepTo (bs : List Nat) (s : State) (c : Nat) (is' : List (Nat × Ins)) (st' : St) : Prop :=
  (s.machineState.gasAvailable.toNat < c ∧
    Eip8024.Xstep (D_J (codeBA bs) 0) s = .error .OutOfGass) ∨
    ∃ s', c ≤ s.machineState.gasAvailable.toNat ∧
      Eip8024.Xstep (D_J (codeBA bs) 0) s = .ok (s', none) ∧
      s'.machineState.gasAvailable.toNat = s.machineState.gasAvailable.toNat - c ∧
      s'.executionEnv = s.executionEnv ∧ At e ρ bs is' st' s'

theorem stepTo_of_simAt {bs : List Nat} {s : State} {is' : List (Nat × Ins)} {st' : St}
    {c : Nat} {pc : UInt256} (hF : Frame e bs s) (hs : SimAt e ρ s c pc st') (g : Nat)
    (hlen : st'.stk.length ≤ 1024) (hdec : Dec bs is')
    (hpc : ∀ p i rest, is' = (p, i) :: rest → pc.toNat = p) :
    StepTo e ρ bs s c is' { st' with gas := g } := by
  have hcode : D_J s.executionEnv.code 0 = D_J (codeBA bs) 0 := by rw [hF.code]
  rcases hs with ⟨hg, h⟩ | ⟨t, m, aw, hcg, hx, hr⟩
  · exact Or.inl ⟨hg, hcode ▸ h⟩
  · refine Or.inr ⟨nextAt s c pc t m aw, hcg, hcode ▸ hx, rfl, rfl, ?_⟩
    exact ⟨⟨hF.code, hF.cd, hF.cdl, hF.cv, hF.rd⟩, hr.charge e ρ g, hlen, hdec, hpc⟩

/-- The gas of `JUMP` or `JUMPI`: the static gas, no memory expansion. -/
theorem insGas_jump {fs : Facts} {code : Code} {pc b : Nat} {st st' : St}
    (hb : b = 0x56 ∨ b = 0x57)
    (h : (∃ t, ctl fs code pc (.op b) st = .jump t st') ∨ ctl fs code pc (.op b) st = .fall st') :
    insGas (.op b) st st' = staticGas (.op b) st := by
  rw [insGas, ctl_keep_msize hb h, Nat.sub_self, Nat.add_zero]

/-- **One instruction of the run**: a checker step from related states is an EVM step to
related states that costs what the checker added to its gas (at least 1), or the EVM runs out of
gas with less than that available. -/
theorem step1_sim (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts)
    (hf : Facts.Hold e fs) (is is' : List (Nat × Ins)) (st st' : St) (s : State)
    (hA : At e ρ bs is st s) (h : step1 fs (Code.ofBytes bs) is st = .next is' st')
    (hv : Tab.Valid e ρ st'.tab) :
    ∃ c, 1 ≤ c ∧ st'.gas = st.gas + c ∧ StepTo e ρ bs s c is' st' := by
  obtain ⟨p, i, rest, st1, rfl, rfl, hc⟩ := step1_next h
  obtain ⟨b, tl, n, r, hd, ho, hpc, hrest, hnext⟩ := hA.dec.cons
  have hp := hA.pc p i rest rfl
  rw [← hp] at hd hpc
  have hW : s.machineState.pc.toNat + 33 < W := by unfold codeFuel at hpc; unfold W; omega
  have hinv := ctl_inv (by
    rcases hc with ⟨hc, -⟩ | ⟨t, hc, -⟩
    · exact Or.inr hc
    · exact Or.inl ⟨t, hc⟩) hA.len
  have hD : ∀ op, parseInstr (UInt8.ofNat b) = some op → ¬ (0x60 ≤ b ∧ b ≤ 0x7f) →
      EVM.decode s.executionEnv.code s.machineState.pc = some (op, none) :=
    fun op hp hb => hA.frame.code ▸ decode_op hall hd hb hp
  refine ⟨insGas i st st1, ?_, rfl, ?_⟩
  rotate_left
  rcases hc with ⟨hc, rfl⟩ | ⟨t, hc, hfd⟩
  · -- falls through to `pc + n`
    have hsim : 1 ≤ insGas i st st1 ∧ SimulatesM e ρ s (insGas i st st1) n st1 := by
      rcases ctl_fall hc with rfl | hs
      · obtain ⟨rfl, hnp, -, -, rfl⟩ := decodeOne_op ho
        rw [insGas_jump (Or.inr rfl) (Or.inr hc)]
        exact ⟨by show 1 ≤ 10; decide,
          sim_jumpi_fall e ρ fs _ s st st1 p (hD _ rfl hnp) hA.rel hA.len hc⟩
      · exact sim_step e ρ bs hall fs hf s st st1 hA.frame hA.rel hA.len hv hd hpc ho hs
    refine stepTo_of_simAt e ρ hA.frame (SimulatesM.at e ρ hsim.2) _ hinv.1 hrest ?_
    intro p' i' rest' he
    have := (decodeOne_rest b tl).1
    rw [ho] at this; dsimp only at this
    rw [hnext p' i' rest' he, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · -- jumps to `t`
    obtain ⟨hj, ⟨rest1, rfl⟩, hdec1⟩ := findDest_ofBytes bs t is' hfd
    obtain ⟨-, -, -, -, -, -, ht33, -, -⟩ := hdec1.cons
    have htW : t < W := by unfold codeFuel at ht33; unfold W; omega
    have hpc' : ∀ p' i' rest', (t, Ins.op 0x5b) :: rest1 = (p', i') :: rest' →
        (UInt256.ofNat t).toNat = p' := by
      intro p' i' rest' he
      simp only [List.cons.injEq, Prod.mk.injEq] at he
      rw [← he.1.1, toNat_ofNat, Nat.mod_eq_of_lt htW]
    rcases ctl_jump hc with rfl | rfl
    · obtain ⟨rfl, hnp, -, -, -⟩ := decodeOne_op ho
      rw [insGas_jump (Or.inl rfl) (Or.inl ⟨t, hc⟩)]
      exact stepTo_of_simAt e ρ hA.frame
        (sim_jump e ρ bs hall fs s st st1 p t hA.frame.code (hD _ rfl hnp) hA.rel hA.len hc hj)
        _ hinv.1 hdec1 hpc'
    · obtain ⟨rfl, hnp, -, -, -⟩ := decodeOne_op ho
      rw [insGas_jump (Or.inr rfl) (Or.inl ⟨t, hc⟩)]
      exact stepTo_of_simAt e ρ hA.frame
        (sim_jumpi_jump e ρ bs hall fs s st st1 p t hA.frame.code (hD _ rfl hnp) hA.rel hA.len
          hc hj)
        _ hinv.1 hdec1 hpc'
  · -- the gas is at least 1
    rcases hc with ⟨hc, -⟩ | ⟨t, hc, -⟩
    · rcases ctl_fall hc with rfl | hs
      · rw [insGas_jump (Or.inr rfl) (Or.inr hc)]; show 1 ≤ 10; decide
      · obtain ⟨b, tl, n, r, hd, ho, hpc, -, -⟩ := hA.dec.cons
        rw [← hp] at hd hpc
        exact (sim_step e ρ bs hall fs hf s st st1 hA.frame hA.rel hA.len hv hd hpc ho hs).1
    · rcases ctl_jump hc with rfl | rfl
      · rw [insGas_jump (Or.inl rfl) (Or.inl ⟨t, hc⟩)]; show 1 ≤ 8; decide
      · rw [insGas_jump (Or.inr rfl) (Or.inl ⟨t, hc⟩)]; show 1 ≤ 10; decide

/-! ## Iterating `X` with gas -/

theorem X_oog (vj : Array UInt256) (f : Nat) (s : State)
    (h : Eip8024.Xstep vj s = .error .OutOfGass) :
    Eip8024.X (f + 1) vj s = .error .OutOfGass := by
  simp only [Eip8024.X, h, bind, Except.bind]

theorem X_next (vj : Array UInt256) (f : Nat) (s s' : State)
    (h : Eip8024.Xstep vj s = .ok (s', none)) (he : s'.executionEnv = s.executionEnv) :
    Eip8024.X (f + 1) vj s = Eip8024.X f vj s' := by
  simp only [Eip8024.X, h, bind, Except.bind]
  rw [← he]

/-- **The run**: from related states, as long as the checker's run continues (`runN` of `k`
instructions), the EVM either runs out of gas, having had less than the checker's gas for those
instructions (`st'.gas - st.gas`), or `X` reaches a state related to where the checker stands,
having paid exactly that gas, with more fuel than gas left. Every step pays at least 1 gas, so
`X`'s fuel (`Ξ` gives gas + 1) never runs out first. -/
theorem runN_sim (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts)
    (hf : Facts.Hold e fs) :
    ∀ (k : Nat) (is is' : List (Nat × Ins)) (st st' : St) (s : State) (f : Nat),
      runN fs (Code.ofBytes bs) k is st = .next is' st' → Tab.Valid e ρ st'.tab →
      At e ρ bs is st s → s.machineState.gasAvailable.toNat < f →
      (s.machineState.gasAvailable.toNat + st.gas < st'.gas ∧
        Eip8024.X f (D_J (codeBA bs) 0) s = .error .OutOfGass) ∨
        ∃ s' f', Eip8024.X f (D_J (codeBA bs) 0) s = Eip8024.X f' (D_J (codeBA bs) 0) s' ∧
          At e ρ bs is' st' s' ∧ s'.machineState.gasAvailable.toNat < f' ∧
          s'.machineState.gasAvailable.toNat + st'.gas = s.machineState.gasAvailable.toNat + st.gas
  | 0, is, is', st, st', s, f, h, _, hA, hg => by
    simp only [runN, Out.next.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨s, f, rfl, hA, hg, rfl⟩
  | k + 1, is, is', st, st', s, f, h, hv, hA, hg => by
    simp only [runN] at h
    split at h
    · rename_i is1 st1 h1
      have hv1 : Tab.Valid e ρ st1.tab :=
        hv.of_ext (runN_inv k is1 is' st1 st' h (by
          obtain ⟨p, i, rest, st2, -, rfl, hc⟩ := step1_next h1
          exact (ctl_inv (st' := st2) (by
            rcases hc with ⟨hc, -⟩ | ⟨t, hc, -⟩
            · exact Or.inr hc
            · exact Or.inl ⟨t, hc⟩) hA.len).1)).2
      have hmono := runN_gas k is1 is' st1 st' h
      obtain ⟨f0, rfl⟩ : ∃ f0, f = f0 + 1 := ⟨f - 1, by omega⟩
      obtain ⟨c, hc1, hgas, hstep⟩ := step1_sim e ρ bs hall fs hf is is1 st st1 s hA h1 hv1
      rcases hstep with ⟨hlt, hx⟩ | ⟨s1, hcg, hx, hg1, henv, hA1⟩
      · exact Or.inl ⟨by omega, X_oog _ f0 s hx⟩
      · rw [X_next _ f0 s s1 hx henv]
        rcases runN_sim bs hall fs hf k is1 is' st1 st' s1 f0 h hv hA1 (by omega) with
          ⟨hlt, hx'⟩ | ⟨s', f', hx', hA', hg', heq⟩
        · exact Or.inl ⟨by omega, hx'⟩
        · exact Or.inr ⟨s', f', hx', hA', hg', by omega⟩
    · cases h

/-! ## From the check to the last instruction -/

/-- The state `Eip8024.Ξ` starts `X` from. -/
def fresh (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) : State :=
  let defState : State := default
  { defState with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      machineState.gasAvailable := .ofUInt256 g }

/-- `Eip8024.Ξ` is `X` from `fresh` with fuel `g + 1`, its result repackaged. -/
theorem Xi_eq (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Eip8024.Ξ σ σ₀ g A I =
      (Eip8024.X (g.toNat + 1) (D_J I.code 0) (fresh σ σ₀ g A I)).bind fun
        | .success s o =>
          .ok (.success (s.accountMap, s.machineState.gasAvailable.toUInt256, s.substate) o)
        | .revert g' o => .ok (.revert g' o) := rfl

theorem ins_head (bs : List Nat) {p : Nat} {i : Ins} {rest : List (Nat × Ins)}
    (h : (Code.ofBytes bs).ins = (p, i) :: rest) : p = 0 := by
  have : (Code.ofBytes bs).ins = Checker.decode codeFuel 0 bs := rfl
  rw [this, show codeFuel = (codeFuel - 1) + 1 from rfl] at h
  cases bs with
  | nil => simp [Checker.decode] at h
  | cons b bs =>
    rw [Checker.decode] at h
    simp only [List.cons.injEq, Prod.mk.injEq] at h
    exact h.1.1.symm

/-- A run ending in `RETURN` or `REVERT` (the only ends a check accepts). -/
def IsFinal : Res → Prop
  | .ret _ _ _ => True
  | .revert _ _ => True
  | _ => False

theorem final_of_resultOk {fs : Facts} {ex : Expect} {r : Res} (h : resultOk fs ex r = true) :
    IsFinal r := by
  cases r <;> simp_all [resultOk, IsFinal]

/-- A run that ends in `RETURN` or `REVERT` reaches that instruction: after `k` instructions
the checker stands at it, and `ctl` ends the run there. -/
theorem run_final (fs : Facts) (code : Code) :
    ∀ (f : Nat) (is : List (Nat × Ins)) (st : St), IsFinal (run fs code f is st) →
      ∃ k p i rest st', runN fs code k is st = .next ((p, i) :: rest) st' ∧
        ctl fs code p i st' = .stop (run fs code f is st)
  | 0, _, _, h => by simp [run, IsFinal] at h
  | f + 1, is, st, h => by
    simp only [run] at h ⊢
    split at h
    · rename_i is1 st1 h1
      obtain ⟨k, p, i, rest, st', h2, h3⟩ := run_final fs code f is1 st1 h
      exact ⟨k + 1, p, i, rest, st', by simp only [runN, h1, h2], h3⟩
    · rename_i r h1
      match is, h1 with
      | [], h1 => simp only [step1, Out.done.injEq] at h1; subst h1; simp [IsFinal] at h
      | (p, i) :: rest, h1 =>
        simp only [step1] at h1
        split at h1
        · cases h1
        · split at h1
          · cases h1
          · cases h1; simp [IsFinal] at h
        · rename_i r' hc
          cases h1
          exact ⟨0, p, i, rest, st, rfl, hc⟩

/-- `ctl` returns words only at `RETURN`. -/
theorem ctl_ret {fs : Facts} {code : Code} {pc : Nat} {i : Ins} {st : St} {ws : List SV}
    {tb : Tab} {g : Nat} (h : ctl fs code pc i st = .stop (.ret ws tb g)) : i = .op 0xf3 := by
  unfold ctl at h
  dsimp only at h
  split at h
  all_goals first
    | rfl
    | (repeat' (split at h)) <;> cases h

/-- `ctl` reverts only at `REVERT`. -/
theorem ctl_revert {fs : Facts} {code : Code} {pc : Nat} {i : Ins} {st : St} {n g : Nat}
    (h : ctl fs code pc i st = .stop (.revert n g)) : i = .op 0xfd := by
  unfold ctl at h
  dsimp only at h
  split at h
  all_goals first
    | rfl
    | (repeat' (split at h)) <;> cases h

/-- **The run up to the last instruction.** If the checker accepts a case, its run reaches a
`RETURN` or `REVERT` at `p` in state `st'` after `k` instructions, and for every valuation valid
on the atom table there, the EVM's run of the call (`X` from `fresh`, as `Eip8024.Ξ` starts it)
runs out of gas, the call's gas `g` being below the checker's gas up to there (`st'.gas`), or
reaches a state `s` related to the checker's at that instruction (`At`), having paid exactly
`st'.gas`, with more fuel than gas. What is left is the last instruction (`ctl` at `p`). -/
theorem reaches_final (bs : List Nat) (hall : bs.all (· < 256) = true) (cs : Case)
    (hc : checkCase (Code.ofBytes bs) cs = true) (cd : List UInt8) (v : Nat)
    (hcd : cd.length < 2 ^ 64) (hfs : Facts.Hold ⟨cd, v⟩ cs.facts) (σ σ₀ : AccountMap)
    (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (henv : Soundness.env (codeBA bs) cd v I) :
    ∃ k p i rest st',
      runN cs.facts (Code.ofBytes bs) k (Code.ofBytes bs).ins St.init =
        .next ((p, i) :: rest) st' ∧
      ctl cs.facts (Code.ofBytes bs) p i st' = .stop (runCase (Code.ofBytes bs) cs) ∧
      (i = .op 0xf3 ∨ i = .op 0xfd) ∧
      ∀ ρ, Tab.Valid ⟨cd, v⟩ ρ st'.tab →
        (g.toNat < st'.gas ∧
          Eip8024.X (g.toNat + 1) (D_J I.code 0) (fresh σ σ₀ g A I) = .error .OutOfGass) ∨
        ∃ s f, Eip8024.X (g.toNat + 1) (D_J I.code 0) (fresh σ σ₀ g A I) =
            Eip8024.X f (D_J I.code 0) s ∧
          At ⟨cd, v⟩ ρ bs ((p, i) :: rest) st' s ∧
          s.machineState.gasAvailable.toNat < f ∧
          s.machineState.gasAvailable.toNat + st'.gas = g.toNat := by
  have hfin := final_of_resultOk hc
  obtain ⟨k, p, i, rest, st', hk, hctl⟩ := run_final cs.facts (Code.ofBytes bs) fuel _ _ hfin
  refine ⟨k, p, i, rest, st', hk, hctl, ?_, fun ρ hv => ?_⟩
  · unfold runCase at hfin
    revert hctl hfin
    cases run cs.facts (Code.ofBytes bs) fuel (Code.ofBytes bs).ins St.init with
    | ret ws tb _ => intro _ hctl; exact Or.inl (ctl_ret hctl)
    | revert n _ => intro _ hctl; exact Or.inr (ctl_revert hctl)
    | stop => intro h; simp [IsFinal] at h
    | fail _ _ => intro h; simp [IsFinal] at h
  · obtain ⟨hcode, hcdl, hcv⟩ := henv
    have hF : Frame ⟨cd, v⟩ bs (fresh σ σ₀ g A I) :=
      { code := hcode
        cd := hcdl
        cdl := lt_of_lt_of_le hcd (Nat.pow_le_pow_right (by decide) (by decide))
        cv := by show I.weiValue.toNat = v % W; rw [hcv]; rfl
        rd := rfl }
    have hA : At ⟨cd, v⟩ ρ bs (Code.ofBytes bs).ins St.init (fresh σ σ₀ g A I) :=
      { frame := hF
        rel := StRel.init _ ρ _ rfl rfl rfl
        len := by simp [St.init]
        dec := Dec.ins bs
        pc := fun p i rest h => by rw [ins_head bs h]; rfl }
    have hg0 : (fresh σ σ₀ g A I).machineState.gasAvailable.toNat = g.toNat := rfl
    rw [show D_J I.code 0 = D_J (codeBA bs) 0 by rw [hcode]]
    rcases runN_sim _ ρ bs hall cs.facts hfs k _ _ St.init st' _ (g.toNat + 1) hk hv hA
      (by rw [hg0]; omega) with ⟨hlt, hx⟩ | ⟨s, f, hx, hA', hf, heq⟩
    · rw [hg0] at hlt
      exact Or.inl ⟨by simpa [St.init] using hlt, hx⟩
    · rw [hg0] at heq
      exact Or.inr ⟨s, f, hx, hA', hf, by simpa [St.init] using heq⟩

end Poseidon2.Evm.Sim
