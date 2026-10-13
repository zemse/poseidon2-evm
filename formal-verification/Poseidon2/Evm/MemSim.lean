import Poseidon2.Evm.Memory

/-!
# Simulation of the memory and data opcodes

`SimulatesM` lemmas (`Memory.lean`) for the instructions of `Checker.step` that read or write
memory or data, in the forms the checker accepts: `MLOAD` and `MSTORE` at exact addresses,
`MSIZE`, `CALLDATALOAD` at an exact offset (the checker's calldata word), `CALLDATACOPY` of
whole words from an exact offset or from `CALLDATASIZE` (zeros), and `CODECOPY` of whole words
from an exact offset of the code. Each pays the memory expansion EVMLean charges
(`memoryExpansionCost`) and its own gas, or runs out of gas.

What they assume and the composition has to supply: the checker's state describes the EVM's
(`StRel`); the instruction EVMLean decodes at `pc`; for the copies, at most 1024 stack items;
the case's facts (calldata words); the calldata of the call is the environment's
(`calldata.data.toList = e.cd`, the shape of `Soundness.env`), shorter than `2^256` bytes for
the zero-filling `CALLDATACOPY`; the checker's code bytes are the EVM's code (`CODECOPY`).
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

variable (e : Env) (ρ : Nat → F)

/-- The shape of a memory step: memory expansion `m` paid first, then `c`. -/
theorem simM_mem (s : State) (m c n : Nat) (st' : St) (t : List UInt256) (mem : ByteArray)
    (aw : UInt256) (L : Nat)
    (hx : Eip8024.Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.gasAvailable.toNat < m then .error .OutOfGass
      else if (s.machineState.gasAvailable.subNat m).toNat < c then .error .OutOfGass
      else if L > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := t
        machineState.memory := mem
        machineState.activeWords := aw
        machineState.gasAvailable := (s.machineState.gasAvailable.subNat m).subNat c
        machineState.pc := s.machineState.pc + UInt256.ofNat n
        machineState.execLength := s.machineState.execLength + 1}, none))
    (hL : L ≤ 1024)
    (hr : m ≤ s.machineState.gasAvailable.toNat → c ≤ s.machineState.gasAvailable.toNat - m →
      StRel e ρ st' (next s (m + c) n t mem aw).machineState) :
    SimulatesM e ρ s (m + c) n st' := by
  rw [SimulatesM, hx]
  by_cases h1 : s.machineState.gasAvailable.toNat < m
  · left; rw [if_pos h1]
  by_cases h2 : (s.machineState.gasAvailable.subNat m).toNat < c
  · left; rw [if_neg h1, if_pos h2]
  right
  rw [toNat_subNat] at h2
  refine ⟨t, mem, aw, by omega, ?_, hr (by omega) (by omega)⟩
  rw [if_neg h1, if_neg (by rw [toNat_subNat]; exact h2), if_neg (by omega), subNat_subNat]
  rfl

theorem StRel.mem_eq {st st1 : St} {μ : MachineState} (h : StRel e ρ st μ)
    (h1 : st1 = { st with stk := st1.stk }) : MemRel e ρ st1.mem (byteAt μ.memory) := by
  rw [h1]; exact h.mem

/-- `MLOAD` at an exact address. -/
theorem sim_mload (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MLOAD, none))
    (hr : StRel e ρ st s.machineState) (h : step fs code (.op 0x51) st = .ok st') :
    SimulatesM e ρ s (memoryExpansionCost s .MLOAD + GasConstants.Gverylow) 1 st' := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, st1⟩, hp, h⟩ := bind_ok h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨v, hv, h⟩ := bind_ok h
  obtain ⟨hl, rfl⟩ := push_ok h
  obtain ⟨hs, hst1⟩ := pop1_ok hp
  have hrs := hr.stk
  rw [hs] at hrs
  obtain ⟨w, t, ht, hw, hrt⟩ := hrs.cons_inv
  have hwa : w.toNat = a := rel_exact e ρ x _ _ hw (exactOf_ok ha)
  have hm1 := hr.mem_eq e ρ hst1
  have hlen := hrt.length
  have hl' : st1.stk.length < 1024 := hl
  have hmc : memoryExpansionCost s .MLOAD =
      Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat w.toNat 32)) -
        Cₘ s.machineState.activeWords := by
    unfold memoryExpansionCost memoryExpansionCost.μᵢ'; rw [ht]; rfl
  refine simM_mem e ρ s _ _ 1 _
    ((if w.toNat ≥ s.machineState.memory.size then (⟨0⟩ : UInt256)
      else UInt256.ofNat (fromByteArrayBigEndian (s.machineState.memory.readWithPadding w.toNat 32)))
      :: t) s.machineState.memory
    (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat w.toNat 32))
    ((w :: t).length - 1 + 1) ?_ (by simp; omega) ?_
  · rw [xstep_overlay _ s _ _ hdec (by simp), step_mload s hdec]
    simp only [ht]
    rfl
  · intro hg1 hg2
    refine ⟨List.Forall₂.cons ?_ hrt, hm1, ?_, ?_⟩
    · show v.Rel e ρ (UInt256.toNat (if _ then _ else _))
      rw [mload_toNat, hwa]
      exact readMem_rel e ρ _ _ hm1 a v hv
    · show (UInt256.ofNat _).toNat * 32 = touch st1.msize a 32
      rw [toNat_M _ _ _ _ hr.gas (toNat_lt w) (by decide), M_touch, hr.msize, hwa]
      rw [hst1]
    · show Cₘ (UInt256.ofNat _) + (s.machineState.gasAvailable.toNat - _) < W
      have := gas_bound s.machineState.activeWords s.machineState.gasAvailable.toNat w.toNat 32
        GasConstants.Gverylow hr.gas (toNat_lt w) (by decide)
        (by rw [← hmc]; exact hg1)
      rw [hmc]; omega

/-- The memory after EVMLean's write is `fill` of the old one. -/
theorem memRel_write (mem : List (Nat × SV)) (D S : ByteArray) (sa d n : Nat) (G : Nat → Nat)
    (hm : MemRel e ρ mem (fill (byteAt D) d n G)) (hG : ∀ j, G j = byteAt S (sa + j)) :
    MemRel e ρ mem (byteAt (S.write sa D d n)) :=
  hm.congr e ρ fun i => by rw [byteAt_write]; unfold fill; split <;> simp only [hG]

/-- `MSTORE` at an exact address. -/
theorem sim_mstore (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, none))
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (h : step fs code (.op 0x52) st = .ok st') :
    SimulatesM e ρ s (memoryExpansionCost s .MSTORE + GasConstants.Gverylow) 1 st' := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, v, st1⟩, hp, h⟩ := bind_ok h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨hs, hst1⟩ := pop2_ok hp
  have hrs := hr.stk
  rw [hs] at hrs hlen
  obtain ⟨w, t1, ht1, hw, hrt1⟩ := hrs.cons_inv
  obtain ⟨b, t, ht2, hb, hrt⟩ := hrt1.cons_inv
  subst ht2
  have hwa : w.toNat = a := rel_exact e ρ x _ _ hw (exactOf_ok ha)
  have hm1 := hr.mem_eq e ρ hst1
  have hlen' := hrt.length
  have hmc : memoryExpansionCost s .MSTORE =
      Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat w.toNat 32)) -
        Cₘ s.machineState.activeWords := by
    unfold memoryExpansionCost memoryExpansionCost.μᵢ'; rw [ht1]; rfl
  have hv : v.Rel e ρ (wordAt (fun j => byteAt b.toByteArray (0 + j)) 0) := by
    have : wordAt (fun j => byteAt b.toByteArray (0 + j)) 0 = b.toNat := by
      unfold wordAt
      simp only [Nat.zero_add]
      rw [← size_toByteArray b, ← toList_map, beVal_toByteArray]
    rw [this]; exact hb
  obtain ⟨hm', hz', hk', -⟩ := mstore_fill e ρ st1 st' _ hm1 a v _ hv h
  refine simM_mem e ρ s _ _ 1 _ t (b.toByteArray.write 0 s.machineState.memory w.toNat 32)
    (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat w.toNat 32))
    ((w :: b :: t).length - 2 + 0) ?_ (by simp at hlen ⊢; omega) ?_
  · rw [xstep_overlay _ s _ _ hdec (by simp), step_mstore s hdec]
    simp only [ht1]
    rfl
  · intro hg1 hg2
    refine ⟨hk' ▸ hrt, ?_, ?_, ?_⟩
    · exact memRel_write e ρ _ _ _ 0 _ 32 _ (hwa ▸ hm') (fun _ => rfl)
    · show (UInt256.ofNat _).toNat * 32 = st'.msize
      rw [toNat_M _ _ _ _ hr.gas (toNat_lt w) (by decide), M_touch, hr.msize, hwa, hz', hst1]
    · show Cₘ (UInt256.ofNat _) + (s.machineState.gasAvailable.toNat - _) < W
      have := gas_bound s.machineState.activeWords s.machineState.gasAvailable.toNat w.toNat 32
        GasConstants.Gverylow hr.gas (toNat_lt w) (by decide) (by rw [← hmc]; exact hg1)
      rw [hmc]; omega

/-- `MSIZE`. -/
theorem sim_msize (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MSIZE, none))
    (hr : StRel e ρ st s.machineState) (h : step fs code (.op 0x59) st = .ok st') :
    SimulatesM e ρ s GasConstants.Gbase 1 st' := by
  have h' := h
  unfold Checker.step at h'; dsimp only at h'
  rw [if_neg (by decide), if_neg (by decide)] at h'
  obtain ⟨hl, hst'⟩ := push_ok h'
  refine sim_lift e ρ fs code _ s _ _ st st' h (by decide) (by decide) (by decide) (by decide) hr ?_
  rw [hst']
  have haw := aw_lt _ _ hr.gas
  refine sim_of e ρ s _ 1 _ ((s.machineState.activeWords * ⟨32⟩) :: s.machineState.stack)
    (s.machineState.stack.length - 0 + 1) ?_ (by rw [← hr.stk.length]; omega)
    (List.Forall₂.cons (const_rel e ρ _ _ ?_) hr.stk)
  · rw [xstep_overlay _ s _ _ hdec (by simp), step_msize s hdec]
    rfl
  · show s.machineState.activeWords.toNat * 32 % W = st.msize
    rw [Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 133 * 32 < W := by decide
                             omega), hr.msize]

/-- Byte `i` of the calldata is the environment's. -/
theorem byteAt_cd (m : ByteArray) (cd : List UInt8) (h : m.data.toList = cd) (i : Nat) :
    byteAt m i = (cd.getD i 0).toNat := by
  unfold byteAt
  rw [List.getD_eq_getElem?_getD, ← h, Array.getElem?_toList]

/-- `CALLDATALOAD` at an exact offset. -/
theorem sim_calldataload (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hf : Facts.Hold e fs) (hcd : s.executionEnv.calldata.data.toList = e.cd)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CALLDATALOAD, none))
    (hr : StRel e ρ st s.machineState) (h : step fs code (.op 0x35) st = .ok st') :
    SimulatesM e ρ s GasConstants.Gverylow 1 st' := by
  have h' := h
  unfold Checker.step at h'; dsimp only at h'
  rw [if_neg (by decide), if_neg (by decide)] at h'
  obtain ⟨⟨x, st1⟩, hp, h'⟩ := bind_ok h'
  obtain ⟨off, ho, h'⟩ := bind_ok h'
  obtain ⟨hl, hst'⟩ := push_ok h'
  obtain ⟨hs, -⟩ := pop1_ok hp
  refine sim_lift e ρ fs code _ s _ _ st st' h (by decide) (by decide) (by decide) (by decide) hr ?_
  rw [hst']
  have hrs := hr.stk
  rw [hs] at hrs
  obtain ⟨w, t, ht, hw, hrt⟩ := hrs.cons_inv
  have hwo : w.toNat = off := rel_exact e ρ x _ _ hw (exactOf_ok ho)
  have hlen := hrt.length
  refine sim_of e ρ s _ 1 _
    (uInt256OfByteArray (s.executionEnv.calldata.readBytes w.toNat 32) :: t)
    ((w :: t).length - 1 + 1) ?_ (by simp; have : st1.stk.length < 1024 := hl; omega)
    (List.Forall₂.cons (input_rel e ρ fs hf (.cdl off) _ ?_) hrt)
  · rw [xstep_overlay _ s _ _ hdec (by simp), step_calldataload s hdec]
    simp only [ht]
    rfl
  · rw [calldataload_toNat, hwo]
    show _ = cdWord e.cd off
    unfold wordAt cdWord beVal
    simp only [byteAt_cd _ e.cd hcd]

/-- The EVM side of `CALLDATACOPY` / `CODECOPY` of `c` bytes from offset `b` of `S` to `a`,
given what the checker's copy did to its state. -/
theorem simM_copy (s : State) (op : Operation) (S : ByteArray) (st st' : St)
    (a b c : UInt256) (t : List UInt256) (ht : s.machineState.stack = a :: b :: c :: t)
    (hx : Eip8024.Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.gasAvailable.toNat < memoryExpansionCost s op then .error .OutOfGass
      else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s op)).toNat <
        GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) then .error .OutOfGass
      else if (a :: b :: c :: t).length - 3 + 0 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := t
        machineState.memory := S.write b.toNat s.machineState.memory a.toNat c.toNat
        machineState.activeWords :=
          UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)
        machineState.gasAvailable := (s.machineState.gasAvailable.subNat
          (memoryExpansionCost s op)).subNat
            (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32))
        machineState.pc := s.machineState.pc + UInt256.ofNat 1
        machineState.execLength := s.machineState.execLength + 1}, none))
    (hmc : memoryExpansionCost s op =
      Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
        Cₘ s.machineState.activeWords)
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (hstk : StkRel e ρ st'.stk t) (G : Nat → Nat) (hG : ∀ j, G j = byteAt S (b.toNat + j))
    (hmem : MemRel e ρ st'.mem (fill (byteAt s.machineState.memory) a.toNat c.toNat G))
    (hms : st'.msize = touch st.msize a.toNat c.toNat) :
    SimulatesM e ρ s (memoryExpansionCost s op +
      (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32))) 1 st' := by
  have hl := hr.stk.length
  rw [ht] at hl
  refine simM_mem e ρ s _ _ 1 _ t _ _ ((a :: b :: c :: t).length - 3 + 0) hx
    (by simp at hl ⊢; omega) ?_
  intro hg1 hg2
  refine ⟨hstk, memRel_write e ρ _ _ _ _ _ _ G hmem hG, ?_, ?_⟩
  · show (UInt256.ofNat _).toNat * 32 = st'.msize
    rw [toNat_M _ _ _ _ hr.gas (toNat_lt a) (toNat_lt c), M_touch, hr.msize, hms]
  · show Cₘ (UInt256.ofNat _) + (s.machineState.gasAvailable.toNat - _) < W
    have := gas_bound s.machineState.activeWords s.machineState.gasAvailable.toNat a.toNat c.toNat
      (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) hr.gas (toNat_lt a)
      (toNat_lt c) (by rw [← hmc]; exact hg1)
    rw [hmc]; omega

/-- `CALLDATACOPY` of whole words to an exact address: from an exact offset (the checker's
calldata words), or from `CALLDATASIZE` (zeros). -/
theorem sim_calldatacopy (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hf : Facts.Hold e fs) (hcd : s.executionEnv.calldata.data.toList = e.cd)
    (hcdl : e.cd.length < W)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CALLDATACOPY, none))
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (h : step fs code (.op 0x37) st = .ok st') :
    SimulatesM e ρ s (memoryExpansionCost s .CALLDATACOPY +
      (GasConstants.Gverylow + GasConstants.Gcopy * ((s.machineState.stack[2]!.toNat + 31) / 32)))
      1 st' := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, y, z, st1⟩, hp, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨n, hn, h⟩ := bind_ok h
  obtain ⟨hs, hst1⟩ := pop3_ok hp
  have hrs := hr.stk
  rw [hs] at hrs
  obtain ⟨a, t1, ht1, ha, hrt1⟩ := hrs.cons_inv
  obtain ⟨b, t2, ht2, hb, hrt2⟩ := hrt1.cons_inv
  obtain ⟨c, t, ht3, hc, hrt⟩ := hrt2.cons_inv
  subst ht2 ht3
  have had : a.toNat = d := rel_exact e ρ x _ _ ha (exactOf_ok hd)
  have hcn : c.toNat = n := rel_exact e ρ z _ _ hc (exactOf_ok hn)
  have hm1 := hr.mem_eq e ρ hst1
  have hmc : memoryExpansionCost s .CALLDATACOPY =
      Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
        Cₘ s.machineState.activeWords := by
    unfold memoryExpansionCost memoryExpansionCost.μᵢ'; rw [ht1]; rfl
  have hc2 : s.machineState.stack[2]! = c := by rw [ht1]; rfl
  rw [hc2]
  have key := simM_copy e ρ s .CALLDATACOPY s.executionEnv.calldata st st' a b c t ht1
    (by rw [xstep_overlay _ s _ _ hdec (by simp), step_calldatacopy s hdec]; simp only [ht1]; rfl)
    hmc hr hlen
  have hsz : s.executionEnv.calldata.size = e.cd.length := by
    rw [← ByteArray.size_data, ← Array.length_toList, hcd]
  split at h
  · cases h
  rename_i h32
  have h32' : 32 * (n / 32) = n := by omega
  split at h
  · -- from `CALLDATASIZE`: zeros
    rename_i lo hi heq
    obtain ⟨hm', hz', hk', -⟩ := zeroFill_rel e ρ _ _ st1 st' _ hm1 h
    rw [h32'] at hm' hz'
    have hbv : b.toNat = e.cd.length := by
      rw [show y = SV.word ⟨.cds, lo, hi⟩ from heq] at hb; rw [hb.2]; show e.cd.length % W = _; exact Nat.mod_eq_of_lt hcdl
    refine key (hk' ▸ hrt) _ ?_
      (by rw [had, hcn]; exact hm') (by rw [had, hcn, hz', hst1])
    intro j
    rw [byteAt_of_le _ _ (by rw [hsz, hbv]; omega)]
  · obtain ⟨src, hsr, h⟩ := bind_ok h
    have hbs : b.toNat = src := rel_exact e ρ y _ _ hb (exactOf_ok hsr)
    obtain ⟨hm', hz', hk', -⟩ := cdCopy_rel e ρ fs hf _ _ _ st1 st' _ hm1 h
    rw [h32'] at hm' hz'
    refine key (hk' ▸ hrt) _ ?_
      (by rw [had, hcn]; exact hm') (by rw [had, hcn, hz', hst1])
    intro j
    rw [byteAt_cd _ e.cd hcd, hbs]
    rfl

/-- `CODECOPY` of whole words from an exact offset of the code to an exact address. -/
theorem sim_codecopy (fs : Facts) (code : Code) (s : State) (st st' : St)
    (hcode : code.bytes = s.executionEnv.code.data.toList.map UInt8.toNat)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CODECOPY, none))
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (h : step fs code (.op 0x39) st = .ok st') :
    SimulatesM e ρ s (memoryExpansionCost s .CODECOPY +
      (GasConstants.Gverylow + GasConstants.Gcopy * ((s.machineState.stack[2]!.toNat + 31) / 32)))
      1 st' := by
  unfold Checker.step at h; dsimp only at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  obtain ⟨⟨x, y, z, st1⟩, hp, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨src, hsr, h⟩ := bind_ok h
  obtain ⟨n, hn, h⟩ := bind_ok h
  obtain ⟨hs, hst1⟩ := pop3_ok hp
  have hrs := hr.stk
  rw [hs] at hrs
  obtain ⟨a, t1, ht1, ha, hrt1⟩ := hrs.cons_inv
  obtain ⟨b, t2, ht2, hb, hrt2⟩ := hrt1.cons_inv
  obtain ⟨c, t, ht3, hc, hrt⟩ := hrt2.cons_inv
  subst ht2 ht3
  have had : a.toNat = d := rel_exact e ρ x _ _ ha (exactOf_ok hd)
  have hbs : b.toNat = src := rel_exact e ρ y _ _ hb (exactOf_ok hsr)
  have hcn : c.toNat = n := rel_exact e ρ z _ _ hc (exactOf_ok hn)
  have hm1 := hr.mem_eq e ρ hst1
  have hmc : memoryExpansionCost s .CODECOPY =
      Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat)) -
        Cₘ s.machineState.activeWords := by
    unfold memoryExpansionCost memoryExpansionCost.μᵢ'; rw [ht1]; rfl
  have hc2 : s.machineState.stack[2]! = c := by rw [ht1]; rfl
  rw [hc2]
  have key := simM_copy e ρ s .CODECOPY s.executionEnv.code st st' a b c t ht1
    (by rw [xstep_overlay _ s _ _ hdec (by simp), step_codecopy s hdec]; simp only [ht1]; rfl)
    hmc hr hlen
  split at h
  · cases h
  rename_i h32
  have h32' : 32 * (n / 32) = n := by omega
  unfold Checker.codeCopy at h
  have hb256 : ∀ v ∈ code.bytes.drop src, v < 256 := by
    intro v hv
    rw [hcode] at hv
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hv)
    exact UInt8.toNat_lt u
  obtain ⟨hm', hz', hk', -⟩ := codeCopy_go_rel e ρ _ _ _ st1 st' _ hb256 hm1 h
  rw [h32'] at hm' hz'
  refine key (hk' ▸ hrt) _ ?_
    (by rw [had, hcn]; exact hm') (by rw [had, hcn, hz', hst1])
  intro j
  unfold codeBytes byteAt
  rw [hbs, List.getD_eq_getElem?_getD, List.getElem?_drop, hcode, List.getElem?_map,
    Array.getElem?_toList]
  cases s.executionEnv.code.data[src + j]? <;> rfl

/-- At the start of a call (empty stack and memory, no active words) the checker's initial
state describes the EVM's. -/
theorem StRel.init (μ : MachineState) (hs : μ.stack = []) (hm : μ.memory = .empty)
    (ha : μ.activeWords.toNat = 0) : StRel e ρ St.init μ := by
  refine ⟨by rw [hs]; exact List.Forall₂.nil, ⟨List.Pairwise.nil, by simp [St.init], ?_⟩, ?_, ?_⟩
  · intro i _; rw [hm]; exact byteAt_of_le _ _ (Nat.zero_le _)
  · rw [ha]; rfl
  · rw [Cm_eq, ha]; have := μ.gasAvailable.isLt; rw [size_eq] at this
    show 3 * 0 + 0 * 0 / 512 + μ.gasAvailable.val < W; omega

end Poseidon2.Evm.Sim
