import Poseidon2.Evm.Final

/-!
# Runs without EIP-8024: the overlay is EVMLean

The theorems are about `Eip8024.Ξ`, EVMLean with the EIP-8024 overlay. The overlay differs from
EVMLean's `EVM.Ξ` (Cancun) only at `0xe6` .. `0xe8`, so on a run that never executes one of
those bytes the two are equal. This file proves it for the runs the checker follows:

* `ovSeg` / `ovFree`: a check on the decoded code: from `pc = 0` and from every jump
  destination, the instructions the run can fall through to, up to one it cannot fall through
  (`fallsThrough`), contain no DUPN / SWAPN. EXCHANGE and an invalid immediate never get that far,
  the checker rejects them;
* `runN_agree`, `final_agree`: along the checker's run (`At`), every EVM step is at an
  instruction of the checked segments, so `Eip8024.Xstep` is `EVM.Xstep` there (`xstep_cancun`),
  and `Eip8024.X` is `EVM.X`;
* `xi_cancun`: for an accepted case, a code that passes `ovFree` and every call that meets the
  case's facts, `Eip8024.Ξ σ σ₀ g A I = EVM.Ξ σ σ₀ g A I`.

`Theorems.lean` turns this into one statement per contract kind (`huffPerm_cancun`, ...), and
every Osaka target (the Huff Osaka contracts, the Yul builds, the deployed v2) proves `ovFree` by
kernel evaluation (`Proofs/`), so its theorems hold verbatim of EVMLean's Cancun `Ξ`.
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

/-! ## The check -/

/-- The instructions after which the checker's run can go on to the next one: PUSH, DUP, SWAP,
`JUMPI` and the opcodes `step` runs (`stepOps`); DUPN / SWAPN are handled by `ovSeg`. -/
def fallsThrough : Ins → Bool
  | .push _ => true
  | .op b => b == 0x57 || (0x80 ≤ b && b ≤ 0x9f) || stepOps.contains b
  | _ => false

/-- The instructions the checker's run executes: those it falls through, `JUMP`, `RETURN` and
`REVERT`. -/
def runs (i : Ins) : Bool :=
  fallsThrough i || i == .op 0x56 || i == .op 0xf3 || i == .op 0xfd

/-- No DUPN / SWAPN among the instructions the run can fall through to from the head of `is`. -/
def ovSeg : List (Nat × Ins) → Bool
  | [] => true
  | (_, .dupn _) :: _ => false
  | (_, .swapn _) :: _ => false
  | (_, i) :: rest => if fallsThrough i then ovSeg rest else true

/-- `ovSeg` from `pc = 0` and from every jump destination. -/
def ovFree (code : Code) : Bool :=
  ovSeg code.ins && code.dests.all (fun d => ovSeg d.2)

theorem ovSeg_head {p : Nat} {i : Ins} {rest : List (Nat × Ins)}
    (h : ovSeg ((p, i) :: rest) = true) : (∀ n, i ≠ .dupn n) ∧ (∀ n, i ≠ .swapn n) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩ <;> (subst hn; simp [ovSeg] at h)

theorem ovSeg_tail {p : Nat} {i : Ins} {rest : List (Nat × Ins)}
    (h : ovSeg ((p, i) :: rest) = true) (hf : fallsThrough i = true) : ovSeg rest = true := by
  cases i with
  | dupn n => simp [ovSeg] at h
  | swapn n => simp [ovSeg] at h
  | op b => simpa [ovSeg, hf] using h
  | push v => simpa [ovSeg, hf] using h
  | bad b => simp [fallsThrough] at hf

theorem ovFree_dest {code : Code} (h : ovFree code = true) {t : Nat} {is : List (Nat × Ins)}
    (hd : findDest t code.dests = some is) : ovSeg is = true := by
  obtain ⟨d, hmem, -, rfl⟩ := findDest_some t _ is hd
  simp only [ovFree, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 d hmem

/-- `ctl` falls through only after an instruction `fallsThrough` accepts, or DUPN / SWAPN. -/
theorem ctl_fall_ft {fs : Facts} {code : Code} {pc : Nat} {i : Ins} {st st' : St}
    (h : ctl fs code pc i st = .fall st') :
    fallsThrough i = true ∨ (∃ n, i = .dupn n) ∨ (∃ n, i = .swapn n) := by
  rcases ctl_fall h with rfl | hs
  · left; rfl
  · cases i with
    | push v => left; rfl
    | dupn n => right; left; exact ⟨n, rfl⟩
    | swapn n => right; right; exact ⟨n, rfl⟩
    | bad b => simp [Checker.step] at hs
    | op b =>
      left
      rcases step_op_cases hs with h1 | h1 | h1
      · simp only [fallsThrough, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          decide_eq_true_eq]
        omega
      · simp only [fallsThrough, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          decide_eq_true_eq]
        omega
      · simp only [fallsThrough, Bool.or_eq_true, List.contains_iff_mem]
        exact Or.inr h1

/-! ## The EVM side -/

/-- An instruction the run executes, other than DUPN / SWAPN, is not at a `0xe6` .. `0xe8`
byte. -/
theorem head_runs {b : Nat} {tl : List Nat} {i : Ins} {n : Nat} {r : Option (List Nat)}
    (h : decodeOne b tl = (i, n, r)) (hr : runs i = true) (hd : ∀ n, i ≠ .dupn n)
    (hs : ∀ n, i ≠ .swapn n) : b ≠ 0xe6 ∧ b ≠ 0xe7 ∧ b ≠ 0xe8 := by
  cases i with
  | dupn k => exact absurd rfl (hd k)
  | swapn k => exact absurd rfl (hs k)
  | bad k => simp [runs, fallsThrough] at hr
  | push v =>
    obtain ⟨hb1, hb2, -⟩ := decodeOne_push h
    omega
  | op b' =>
    obtain ⟨rfl, -, h6, h7, -⟩ := decodeOne_op h
    refine ⟨h6, h7, fun h8 => ?_⟩
    subst h8
    revert hr
    decide

theorem uint8_ofNat_ne {b : Nat} (hb : b < 256) (c : UInt8) (hc : b ≠ c.toNat) :
    UInt8.ofNat b ≠ c := by
  intro h
  apply hc
  rw [← h, UInt8.toNat_ofNat']
  omega

/-- The overlay does not decode a byte other than `0xe6` .. `0xe8`. -/
theorem decode_none {bs : List Nat} (hall : bs.all (· < 256) = true) {p b : Nat}
    {tl : List Nat} (hd : bs.drop p = b :: tl) (h6 : b ≠ 0xe6) (h7 : b ≠ 0xe7) (h8 : b ≠ 0xe8) :
    Eip8024.decode (codeBA bs) p = none := by
  have hb := head_lt hall hd
  unfold Eip8024.decode
  rw [get?_codeBA hd]
  have n6 := uint8_ofNat_ne hb 0xe6 (by simpa using h6)
  have n7 := uint8_ofNat_ne hb 0xe7 (by simpa using h7)
  have n8 := uint8_ofNat_ne hb 0xe8 (by simpa using h8)
  split
  · rename_i h; simp only [Option.some.injEq] at h; exact absurd h n6
  · rename_i h; simp only [Option.some.injEq] at h; exact absurd h n7
  · rename_i h; simp only [Option.some.injEq] at h; exact absurd h n8
  · rfl

/-- Where the overlay decodes nothing, it is EVMLean. -/
theorem xstep_cancun (vj : Array UInt256) (s : State)
    (h : Eip8024.decode s.executionEnv.code s.machineState.pc.toNat = none) :
    Eip8024.Xstep vj s = EVM.Xstep vj s := by
  unfold Eip8024.Xstep
  rw [h]

theorem evmX_zero (vj : Array UInt256) (s : State) : EVM.X 0 vj s = .error .OutOfFuel := by
  rw [EVM.X]

theorem evmX_error (vj : Array UInt256) (f : Nat) (s : State) (x : EVM.ExecutionException)
    (h : EVM.Xstep vj s = .error x) : EVM.X (f + 1) vj s = .error x := by
  rw [EVM.X]
  simp only [h, bind, Except.bind]

theorem evmX_next (vj : Array UInt256) (f : Nat) (s s' : State)
    (h : EVM.Xstep vj s = .ok (s', none)) (he : s'.executionEnv = s.executionEnv) :
    EVM.X (f + 1) vj s = EVM.X f vj s' := by
  rw [EVM.X]
  simp only [h, bind, Except.bind]
  rw [← he]

/-- One step the two agree on, and that does not go on, gives the same `X`. -/
theorem X_agree_halt (vj : Array UInt256) (f : Nat) (s : State)
    (h : Eip8024.Xstep vj s = EVM.Xstep vj s) (hn : ∀ s', EVM.Xstep vj s ≠ .ok (s', none)) :
    Eip8024.X (f + 1) vj s = EVM.X (f + 1) vj s := by
  rw [EVM.X]
  simp only [Eip8024.X, h, bind, Except.bind]
  rcases hx : EVM.Xstep vj s with x | ⟨s', _ | ⟨c, o⟩⟩
  · rfl
  · exact absurd hx (hn s')
  · cases c <;> rfl

variable (e : Env) (ρ : Nat → F)

/-- At a related state whose instruction the run executes and is not DUPN / SWAPN, the overlay's
step is EVMLean's. -/
theorem xstep_at {bs : List Nat} (hall : bs.all (· < 256) = true) {p : Nat} {i : Ins}
    {rest : List (Nat × Ins)} {st : St} {s : State} (hA : At e ρ bs ((p, i) :: rest) st s)
    (hr : runs i = true) (hd : ∀ n, i ≠ .dupn n) (hs : ∀ n, i ≠ .swapn n) (vj : Array UInt256) :
    Eip8024.Xstep vj s = EVM.Xstep vj s := by
  obtain ⟨b, tl, n, r, hdrop, ho, -, -, -⟩ := hA.dec.cons
  obtain ⟨h6, h7, h8⟩ := head_runs ho hr hd hs
  apply xstep_cancun
  rw [hA.frame.code, hA.pc p i rest rfl]
  exact decode_none hall hdrop h6 h7 h8

/-- The run's last instruction, `RETURN` or `REVERT`, gives the same `X` in both. -/
theorem final_agree (bs : List Nat) (hall : bs.all (· < 256) = true) {p : Nat} {i : Ins}
    {rest : List (Nat × Ins)} {st : St} {s : State} (hA : At e ρ bs ((p, i) :: rest) st s)
    (hi : i = .op 0xf3 ∨ i = .op 0xfd) (f : Nat) :
    Eip8024.X f (D_J (codeBA bs) 0) s = EVM.X f (D_J (codeBA bs) 0) s := by
  cases f with
  | zero => rw [evmX_zero]; rfl
  | succ f =>
    have hx := xstep_at e ρ hall hA (by rcases hi with rfl | rfl <;> rfl)
      (by rcases hi with rfl | rfl <;> simp) (by rcases hi with rfl | rfl <;> simp)
      (D_J (codeBA bs) 0)
    refine X_agree_halt _ f s hx fun s' => ?_
    rw [← hA.frame.code]
    rcases hi with rfl | rfl
    · rw [step_return s (decode_at e ρ hall hA rfl)]
      split <;> simp; split_ifs <;> simp
    · rw [step_revert s (decode_at e ρ hall hA rfl)]
      split <;> simp; split_ifs <;> simp

/-- **Along the run** the overlay is EVMLean: from related states at an instruction list that
passes `ovSeg`, as long as the checker's run continues (`runN`), `Eip8024.X` and `EVM.X` agree
if they agree where the run stands then. -/
theorem runN_agree (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts)
    (hf : Facts.Hold e fs) (hov : ovFree (Code.ofBytes bs) = true) :
    ∀ (k : Nat) (is is' : List (Nat × Ins)) (st st' : St) (s : State) (f : Nat),
      runN fs (Code.ofBytes bs) k is st = .next is' st' → Tab.Valid e ρ st'.tab →
      At e ρ bs is st s → s.machineState.gasAvailable.toNat < f → ovSeg is = true →
      (∀ s' f', At e ρ bs is' st' s' →
        Eip8024.X f' (D_J (codeBA bs) 0) s' = EVM.X f' (D_J (codeBA bs) 0) s') →
      Eip8024.X f (D_J (codeBA bs) 0) s = EVM.X f (D_J (codeBA bs) 0) s
  | 0, is, is', st, st', s, f, h, _, hA, _, _, hend => by
    simp only [runN, Out.next.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hend s f hA
  | k + 1, is, is', st, st', s, f, h, hv, hA, hg, hseg, hend => by
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
      obtain ⟨p, i, rest, st2, rfl, -, hc⟩ := step1_next h1
      obtain ⟨hnd, hns⟩ := ovSeg_head hseg
      have hrun : runs i = true ∧ ovSeg is1 = true := by
        rcases hc with ⟨hc, rfl⟩ | ⟨t, hc, hfd⟩
        · rcases ctl_fall_ft hc with hft | ⟨n, rfl⟩ | ⟨n, rfl⟩
          · exact ⟨by simp [runs, hft], ovSeg_tail hseg hft⟩
          · exact absurd rfl (hnd n)
          · exact absurd rfl (hns n)
        · refine ⟨?_, ovFree_dest hov hfd⟩
          rcases ctl_jump hc with rfl | rfl <;> rfl
      have hx := xstep_at e ρ hall hA hrun.1 hnd hns (D_J (codeBA bs) 0)
      obtain ⟨f0, rfl⟩ : ∃ f0, f = f0 + 1 := ⟨f - 1, by omega⟩
      obtain ⟨c, hc1, -, hstep⟩ := step1_sim e ρ bs hall fs hf _ is1 st st1 s hA h1 hv1
      rcases hstep with ⟨-, hoog⟩ | ⟨s1, hcg, hx1, hg1, henv, hA1⟩
      · rw [X_oog _ f0 s hoog, evmX_error _ f0 s _ (hx ▸ hoog)]
      · rw [X_next _ f0 s s1 hx1 henv, evmX_next _ f0 s s1 (hx ▸ hx1) henv]
        exact runN_agree bs hall fs hf hov k is1 is' st1 st' s1 f0 h hv hA1 (by omega)
          hrun.2 hend
    · cases h

/-- `EVM.Ξ` is EVMLean's `X` from `fresh` with fuel `g + 1`, its result repackaged, as
`Eip8024.Ξ` is the overlay's (`Xi_eq`). -/
theorem evmXi_eq (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    EVM.Ξ σ σ₀ g A I =
      (EVM.X (g.toNat + 1) (D_J I.code 0) (fresh σ σ₀ g A I)).bind fun
        | .success s o =>
          .ok (.success (s.accountMap, s.machineState.gasAvailable.toUInt256, s.substate) o)
        | .revert g' o => .ok (.revert g' o) := by
  unfold EVM.Ξ
  rfl

/-- **The overlay is EVMLean on these runs**: if the checker accepts a case on a code that
passes `ovFree`, every call that meets the case's facts gets the same result from `Eip8024.Ξ` and
from EVMLean's `EVM.Ξ`. -/
theorem xi_cancun (bs : List Nat) (hall : bs.all (· < 256) = true) (cs : Case)
    (hc : checkCase (Code.ofBytes bs) cs = true) (hov : ovFree (Code.ofBytes bs) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64)
    (hfs : Soundness.FactsHold ⟨cd, v⟩ cs.facts)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (henv : Soundness.env (codeBA bs) cd v I) :
    Eip8024.Ξ σ σ₀ g A I = EVM.Ξ σ σ₀ g A I := by
  obtain ⟨k, p, i, rest, st', hk, -, hi, -⟩ :=
    reaches_final bs hall cs hc cd v hcd hfs σ σ₀ g A I henv
  have hinv := runN_inv' k _ _ _ _ hk St.Inv.init
  have hv := hinv.wf.valid ⟨cd, v⟩
  obtain ⟨hcode, hcdl, hcv⟩ := henv
  have hF : Frame ⟨cd, v⟩ bs (fresh σ σ₀ g A I) :=
    { code := hcode
      cd := hcdl
      cdl := lt_of_lt_of_le hcd (Nat.pow_le_pow_right (by decide) (by decide))
      cv := by show I.weiValue.toNat = v % W; rw [hcv]; rfl
      rd := rfl }
  have hA : At ⟨cd, v⟩ (defsVal ⟨cd, v⟩ st'.tab.defs) bs (Code.ofBytes bs).ins St.init
      (fresh σ σ₀ g A I) :=
    { frame := hF
      rel := StRel.init _ _ _ rfl rfl rfl
      len := by simp [St.init]
      dec := Dec.ins bs
      pc := fun p i rest h => by rw [ins_head bs h]; rfl }
  rw [Xi_eq, evmXi_eq, hcode]
  have hov' := hov
  simp only [ovFree, Bool.and_eq_true] at hov'
  have := runN_agree ⟨cd, v⟩ _ bs hall cs.facts hfs hov k _ _ St.init st' _ (g.toNat + 1) hk hv hA
    (by show g.toNat < g.toNat + 1; omega) hov'.1
    (fun s' f' hA' => final_agree ⟨cd, v⟩ _ bs hall hA' hi f')
  rw [this]
  rfl

end Poseidon2.Evm.Sim
