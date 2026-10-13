import Poseidon2.Evm.Decode

/-!
# Simulation of control flow

The instructions of `Checker.ctl` that change control flow, against `Eip8024.Xstep`:

* `SimAt e ρ s c pc st'`: `SimulatesM` with `pc` set rather than advanced: the EVM's step runs out
  of gas, or pays `c`, sets `pc`, changes only the stack, memory and active words, and `st'`
  describes the new machine state. `SimulatesM` is `SimAt` at `pc + n` (`SimulatesM.at`);
* `sim_jump`: `JUMP` to the exact target the checker found (a `JUMPDEST` of `jumpdests`, so in
  EVMLean's `D_J` by `mem_D_J`): `Gmid` paid, `pc` set to the target;
* `sim_jumpi_jump`, `sim_jumpi_fall`: `JUMPI` on a condition the checker decided, both ways
  (`Ghigh`; the target or `pc + 1`);
* `sim_stop`: `STOP` halts with empty output (the checker's run never accepts a `STOP`, so the
  composition does not need it; stated for completeness).
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

variable (e : Env) (ρ : Nat → F)

/-- The EVM state after a step that pays `c`, sets `pc`, the stack, the memory and the active
words. -/
def nextAt (s : State) (c : Nat) (pc : UInt256) (t : List UInt256) (m : ByteArray)
    (aw : UInt256) : State :=
  { s with
    machineState.stack := t
    machineState.memory := m
    machineState.activeWords := aw
    machineState.gasAvailable := s.machineState.gasAvailable.subNat c
    machineState.pc := pc
    machineState.execLength := s.machineState.execLength + 1 }

/-- The EVM's step from `s` as the checker's step to `st'` describes it, `pc` set to `pc`: out of
gas, or `c` paid, only the stack, memory and active words changed, `st'` describes the new
machine state. -/
def SimAt (s : State) (c : Nat) (pc : UInt256) (st' : St) : Prop :=
  Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    ∃ t m aw, c ≤ s.machineState.gasAvailable.toNat ∧
      Eip8024.Xstep (D_J s.executionEnv.code 0) s = .ok (nextAt s c pc t m aw, none) ∧
      StRel e ρ st' (nextAt s c pc t m aw).machineState

theorem SimulatesM.at {s : State} {c n : Nat} {st' : St} (h : SimulatesM e ρ s c n st') :
    SimAt e ρ s c (s.machineState.pc + UInt256.ofNat n) st' := h

/-- A step that pops the stack to `t`, pays `c` and keeps the memory keeps `StRel`. -/
theorem StRel.pop {st st' : St} {μ : MachineState} (h : StRel e ρ st μ)
    (hm : st'.mem = st.mem) (hz : st'.msize = st.msize) (t : List UInt256)
    (ht : StkRel e ρ st'.stk t) (c : Nat) (pc : UInt256) (x : Nat) :
    StRel e ρ st' { μ with
      stack := t
      memory := μ.memory
      activeWords := μ.activeWords
      gasAvailable := μ.gasAvailable.subNat c
      pc := pc
      execLength := x } := by
  have := h.gas
  exact ⟨ht, hm ▸ h.mem, hz ▸ h.msize, by
    show Cₘ μ.activeWords + (μ.gasAvailable.toNat - c) < W; omega⟩

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a :=
  toNat_inj.mp (by rw [toNat_ofNat]; exact Nat.mod_eq_of_lt (toNat_lt a))

/-- `JUMP` to the target the checker found. -/
theorem sim_jump (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts) (s : State)
    (st st' : St) (pc tg : Nat) (hcode : s.executionEnv.code = codeBA bs)
    (hdec : EVM.decode s.executionEnv.code s.machineState.pc = some (.JUMP, none))
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (h : ctl fs (Code.ofBytes bs) pc (.op 0x56) st = .jump tg st')
    (hj : tg ∈ jumpdests codeFuel 0 bs) :
    SimAt e ρ s GasConstants.Gmid (UInt256.ofNat tg) st' := by
  simp only [ctl] at h
  split at h
  · rename_i x st1 hp
    split at h
    · cases h
    · rename_i tg' hx
      cases h
      obtain ⟨hs, hst1⟩ := pop1_ok hp
      have hrel := hr.stk
      rw [hs] at hrel hlen
      obtain ⟨a, t, ht, ha, hrt⟩ := hrel.cons_inv
      have hat : a.toNat = tg := rel_exact e ρ x a.toNat tg ha hx
      have hag : a = UInt256.ofNat tg := by rw [← hat, ofNat_toNat]
      rw [Sim.SimAt, xstep_overlay _ s _ _ hdec (by simp), step_jump s hdec, ht]
      dsimp only
      by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gmid
      · left; rw [if_pos hg]
      · right
        have hc : (D_J s.executionEnv.code 0).contains a = true := by
          rw [hcode, hag]; exact mem_D_J hall hj
        have hl := hrt.length
        rw [if_neg hg, if_neg (by simp [Array.contains_iff_mem.mp hc]), if_neg (by simp at hlen ⊢; omega)]
        refine ⟨t, s.machineState.memory, s.machineState.activeWords, by omega, ?_, ?_⟩
        · rw [hag]; rfl
        · exact StRel.pop e ρ hr (by rw [hst1]) (by rw [hst1]) t hrt _ _ _
  · cases h

theorem pop2_mem {s s' : St} {a b : SV} (h : pop2 s = .ok (a, b, s')) :
    s'.mem = s.mem ∧ s'.msize = s.msize := by
  obtain ⟨-, h2⟩ := pop2_ok h; rw [h2]; exact ⟨rfl, rfl⟩

/-- `JUMPI` on a condition the checker knows is not zero: the jump. -/
theorem sim_jumpi_jump (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts)
    (s : State) (st st' : St) (pc tg : Nat) (hcode : s.executionEnv.code = codeBA bs)
    (hdec : EVM.decode s.executionEnv.code s.machineState.pc = some (.JUMPI, none))
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (h : ctl fs (Code.ofBytes bs) pc (.op 0x57) st = .jump tg st')
    (hj : tg ∈ jumpdests codeFuel 0 bs) :
    SimAt e ρ s GasConstants.Ghigh (UInt256.ofNat tg) st' := by
  simp only [ctl] at h
  split at h
  · rename_i x c st1 hp
    obtain ⟨hs, hst1⟩ := pop2_ok hp
    have hrel := hr.stk
    rw [hs] at hrel hlen
    obtain ⟨a, t1, ht1, ha, hrt1⟩ := hrel.cons_inv
    obtain ⟨b, t, ht, hb, hrt⟩ := hrt1.cons_inv
    split at h
    · rename_i w
      split at h
      · rename_i hlo
        split at h
        · cases h
        · rename_i tg' hx
          cases h
          have hat : a.toNat = tg := rel_exact e ρ x a.toNat tg ha hx
          have hag : a = UInt256.ofNat tg := by rw [← hat, ofNat_toNat]
          have hb0 : (b != (⟨0⟩ : UInt256)) = true := by
            obtain ⟨⟨h1, -, -⟩, h2⟩ := hb
            have : b.toNat ≠ 0 := by omega
            simp only [bne_iff_ne, ne_eq]
            intro e0; rw [e0] at this; exact this rfl
          rw [Sim.SimAt, xstep_overlay _ s _ _ hdec (by simp), step_jumpi s hdec, ht1, ht]
          dsimp only
          by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Ghigh
          · left; rw [if_pos hg]
          · right
            have hc : (D_J s.executionEnv.code 0).contains a = true := by
              rw [hcode, hag]; exact mem_D_J hall hj
            have hl := hrt.length
            rw [if_neg hg, if_neg (by simp [Array.contains_iff_mem.mp hc]), if_neg (by simp at hlen ⊢; omega)]
            refine ⟨t, s.machineState.memory, s.machineState.activeWords, by omega, ?_, ?_⟩
            · rw [hb0, if_pos rfl, hag]; rfl
            · exact StRel.pop e ρ hr (by rw [hst1]) (by rw [hst1]) t hrt _ _ _
      · split at h
        · cases h
        · cases h
    · cases h
  · cases h

/-- `JUMPI` on a condition the checker knows is zero: falls through to `pc + 1`. -/
theorem sim_jumpi_fall (fs : Facts) (code : Code) (s : State) (st st' : St) (pc : Nat)
    (hdec : EVM.decode s.executionEnv.code s.machineState.pc = some (.JUMPI, none))
    (hr : StRel e ρ st s.machineState) (hlen : st.stk.length ≤ 1024)
    (h : ctl fs code pc (.op 0x57) st = .fall st') :
    SimulatesM e ρ s GasConstants.Ghigh 1 st' := by
  simp only [ctl] at h
  split at h
  · rename_i x c st1 hp
    obtain ⟨hs, hst1⟩ := pop2_ok hp
    have hrel := hr.stk
    rw [hs] at hrel hlen
    obtain ⟨a, t1, ht1, ha, hrt1⟩ := hrel.cons_inv
    obtain ⟨b, t, ht, hb, hrt⟩ := hrt1.cons_inv
    split at h
    · rename_i w
      split at h
      · split at h <;> cases h
      · split at h
        · rename_i hhi
          cases h
          have hb0 : b = (⟨0⟩ : UInt256) := by
            obtain ⟨⟨-, h1, -⟩, h2⟩ := hb
            apply toNat_inj.mp
            show b.toNat = 0
            omega
          rw [SimulatesM, xstep_overlay _ s _ _ hdec (by simp), step_jumpi s hdec, ht1, ht]
          dsimp only
          by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Ghigh
          · left; rw [if_pos hg]
          · right
            have hl := hrt.length
            rw [if_neg hg, if_neg (by simp [hb0]), if_neg (by simp at hlen ⊢; omega)]
            refine ⟨t, s.machineState.memory, s.machineState.activeWords, by omega, ?_, ?_⟩
            · simp only [hb0, bne_self_eq_false, Bool.false_eq_true, if_false]
              rfl
            · exact StRel.pop e ρ hr (by rw [hst1]) (by rw [hst1]) t hrt _ _ _
        · cases h
    · cases h
  · cases h

/-- `STOP` halts with empty output. -/
theorem sim_stop (s : State) (stk : List SV) (hrel : StkRel e ρ stk s.machineState.stack)
    (hlen : stk.length ≤ 1024)
    (hdec : EVM.decode s.executionEnv.code s.machineState.pc = some (.STOP, none)) :
    Eip8024.Xstep (D_J s.executionEnv.code 0) s = .ok ({s with
      machineState.gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Gzero
      machineState.execLength := s.machineState.execLength + 1
      machineState.returnData := .empty }, some (.success, .empty)) := by
  rw [xstep_overlay _ s _ _ hdec (by simp), step_stop s hdec,
    if_neg (by have := hrel.length; omega)]

end Poseidon2.Evm.Sim
