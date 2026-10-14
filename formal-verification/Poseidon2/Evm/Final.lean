import Poseidon2.Evm.Run
import Poseidon2.Checker.Valuation

/-!
# The last instruction and the soundness of the checker

* `final_return`: the checker's `RETURN` of words `ws`, from a state related by `At`, is the EVM's
  `RETURN`: the run halts with output `encodeWords xs` for values `xs` the words describe, having
  paid the memory expansion the checker adds to its gas, or runs out of gas with less than that;
* `final_revert`: the checker's `REVERT` of size 0 is the EVM's `REVERT` with empty output (it
  costs nothing, so it cannot run out of gas);
* `checker_core`: for an accepted case and a call that meets its facts, the EVM runs out of gas
  exactly when the call's gas is below the gas of the checker's run, and otherwise ends exactly
  as the case expects with that gas used. `reaches_final` (`Run.lean`) brings the EVM to the last
  instruction, the valuation comes from `spec_sound` (`Checker/Valuation.lean`), and the returned
  values are the spec's words by `outputsMatch_sound` and the spec bridge;
* `checkerSound`, `checkerTotal`: **`CheckerSound` and `CheckerTotal` hold**, from
  `checker_core`.
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

variable (e : Env) (ρ : Nat → F)

/-! ## The checker's `RETURN` and `REVERT` -/

theorem ctl_ret_inv {fs : Facts} {code : Code} {pc : Nat} {st : St} {ws : List SV} {tb : Tab}
    {G : Nat} (h : ctl fs code pc (.op 0xf3) st = .stop (.ret ws tb G)) :
    ∃ off sz s1 o n, pop2 st = .ok (off, sz, s1) ∧ off.exact = some o ∧ sz.exact = some n ∧
      n % 32 = 0 ∧ readWords s1.mem (n / 32) o = .ok ws ∧ tb = s1.tab ∧
      G = s1.gas + (memCost (touch s1.msize o n) - memCost s1.msize) := by
  simp only [ctl] at h
  split at h
  · rename_i off sz s1 hp
    split at h
    · rename_i o n ho hn
      split at h
      · cases h
      · rename_i hmod
        split at h
        · rename_i ws' hr
          cases h
          exact ⟨off, sz, s1, o, n, hp, ho, hn, by omega, hr, rfl, rfl⟩
        · cases h
    · cases h
  · cases h

theorem ctl_revert_inv {fs : Facts} {code : Code} {pc : Nat} {st : St} {n G : Nat}
    (h : ctl fs code pc (.op 0xfd) st = .stop (.revert n G)) :
    ∃ off sz s1, pop2 st = .ok (off, sz, s1) ∧ sz.exact = some n ∧ G = st.gas := by
  simp only [ctl] at h
  split at h
  · rename_i off sz s1 hp
    split at h
    · rename_i m hm
      cases h
      exact ⟨off, sz, s1, hp, hm, rfl⟩
    · cases h
  · cases h

/-! ## The returned bytes -/

/-- The words at `a`, `a + 32`, .. of a byte function. -/
def wordsAt (f : Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, a => wordAt f a :: wordsAt f k (a + 32)

theorem readWords_rel (mem : List (Nat × SV)) (f : Nat → Nat) (hm : MemRel e ρ mem f) :
    ∀ (k a : Nat) (ws : List SV), readWords mem k a = .ok ws →
      List.Forall₂ (fun w x => w.Rel e ρ x) ws (wordsAt f k a)
  | 0, _, ws, h => by cases h; exact List.Forall₂.nil
  | k + 1, a, ws, h => by
    obtain ⟨v, hv, h⟩ := bind_ok h
    obtain ⟨vs, hvs, h⟩ := bind_ok h
    cases h
    exact List.Forall₂.cons (readMem_rel e ρ mem f hm a v hv) (readWords_rel mem f hm k _ vs hvs)

/-- `32 k` bytes, byte `j` being `f (a + j)`, are the encoding of the words at `a`, `a + 32`, ... -/
theorem bytes_wordsAt (f : Nat → Nat) : ∀ (k a : Nat) (l : List UInt8), l.length = 32 * k →
    (∀ j (hj : j < l.length), l[j].toNat = f (a + j)) →
    l = Spec.Interface.encodeWords (wordsAt f k a)
  | 0, _, l, hl, _ => by
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rfl
  | k + 1, a, l, hl, hb => by
    have h32 : (l.take 32).length = 32 := by rw [List.length_take]; omega
    have hhead : l.take 32 = Spec.Interface.wordBytes (wordAt f a) := by
      rw [bytes_eq_wordBytes (l.take 32) h32]
      congr 1
      unfold wordAt
      congr 1
      apply List.ext_getElem
      · simp [h32]; omega
      · intro j h1 h2
        simp only [List.getElem_map, List.getElem_take, List.getElem_range]
        exact hb j (by simp at h1; omega)
    have htail := bytes_wordsAt f k (a + 32) (l.drop 32) (by rw [List.length_drop]; omega)
      (fun j hj => by
        rw [List.getElem_drop, hb (32 + j) (by rw [List.length_drop] at hj; omega)]
        congr 1; omega)
    calc l = l.take 32 ++ l.drop 32 := (List.take_append_drop 32 l).symm
      _ = _ := by
        rw [hhead, htail]
        simp only [wordsAt, Spec.Interface.encodeWords, List.flatMap_cons]

/-- What EVMLean's `RETURN` outputs, `n = 32 k` bytes of memory from `a`, is the encoding of the
words there. -/
theorem readWithPadding_words (m : ByteArray) (a k : Nat) :
    (m.readWithPadding a (32 * k)).data.toList =
      Spec.Interface.encodeWords (wordsAt (byteAt m) k a) := by
  apply bytes_wordsAt (byteAt m) k a
  · rw [Array.length_toList, ByteArray.size_data, size_readWithPadding]
  · intro j hj
    have hj' : j < 32 * k := by
      rw [Array.length_toList, ByteArray.size_data, size_readWithPadding] at hj; exact hj
    have := byteAt_readWithPadding m a (32 * k) j
    rw [if_pos hj'] at this
    rw [← this]
    have hj2 : j < (m.readWithPadding a (32 * k)).data.size := by simpa using hj
    simp only [Array.getElem_toList, byteAt, Array.getElem?_eq_getElem hj2, Option.getD_some]

/-! ## The EVM's `RETURN` and `REVERT` -/

theorem X_success (vj : Array UInt256) (f : Nat) (s s' : State) (o : ByteArray)
    (h : Eip8024.Xstep vj s = .ok (s', some (.success, o))) :
    Eip8024.X (f + 1) vj s = .ok (.success s' o) := by
  simp only [Eip8024.X, h, bind, Except.bind]

theorem X_revert (vj : Array UInt256) (f : Nat) (s s' : State) (o : ByteArray)
    (h : Eip8024.Xstep vj s = .ok (s', some (.revert, o))) :
    Eip8024.X (f + 1) vj s = .ok (.revert s'.machineState.gasAvailable.toUInt256 o) := by
  simp only [Eip8024.X, h, bind, Except.bind]

theorem xstep_return (s : State)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.RETURN, none))
    (a b : UInt256) (t : List UInt256) (hs : s.machineState.stack = a :: b :: t)
    (hl : t.length ≤ 1024) :
    (s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURN ∧
      Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass) ∨
      ∃ s', Eip8024.Xstep (D_J s.executionEnv.code 0) s =
        .ok (s', some (.success, s.machineState.memory.readWithPadding a.toNat b.toNat)) ∧
        memoryExpansionCost s .RETURN ≤ s.machineState.gasAvailable.toNat ∧
        s'.machineState.gasAvailable.toNat =
          s.machineState.gasAvailable.toNat - memoryExpansionCost s .RETURN := by
  rw [xstep_overlay _ s _ _ hdec (by simp), step_return s hdec]
  simp only [hs]
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exfalso; simp only [List.length_cons] at h2; omega
  · refine Or.inr ⟨_, rfl, by omega, ?_⟩
    simp only [toNat_subNat, GasConstants.Gzero, Nat.sub_zero]

theorem xstep_revert (s : State)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.REVERT, none))
    (a b : UInt256) (t : List UInt256) (hs : s.machineState.stack = a :: b :: t)
    (hl : t.length ≤ 1024) :
    (s.machineState.gasAvailable.toNat < memoryExpansionCost s .REVERT ∧
      Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass) ∨
      ∃ s', Eip8024.Xstep (D_J s.executionEnv.code 0) s =
        .ok (s', some (.revert, s.machineState.memory.readWithPadding a.toNat b.toNat)) ∧
        s'.machineState.gasAvailable.toNat =
          s.machineState.gasAvailable.toNat - memoryExpansionCost s .REVERT := by
  rw [xstep_overlay _ s _ _ hdec (by simp), step_revert s hdec]
  simp only [hs]
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, rfl⟩
  · exfalso; simp only [List.length_cons] at h2; omega
  · refine Or.inr ⟨_, rfl, ?_⟩
    simp only [toNat_subNat, GasConstants.Gzero, Nat.sub_zero]

/-- The checker's `.op b` at the run's position is what EVMLean decodes at the EVM's `pc`. -/
theorem decode_at {bs : List Nat} (hall : bs.all (· < 256) = true) {p b : Nat}
    {rest : List (Nat × Ins)} {st : St} {s : State} (hA : At e ρ bs ((p, .op b) :: rest) st s)
    {op : Operation} (hop : parseInstr (UInt8.ofNat b) = some op) :
    EVM.decode s.executionEnv.code s.machineState.pc = some (op, none) := by
  obtain ⟨b', tl, n, r, hd, ho, -, -, -⟩ := hA.dec.cons
  have hp := hA.pc p _ rest rfl
  rw [← hp] at hd
  obtain ⟨rfl, hnp, -, -, -⟩ := decodeOne_op ho
  exact hA.frame.code ▸ decode_op hall hd hnp hop

/-- Below the two popped items, at most 1024 stack items. -/
theorem stack2 {st s1 : St} {off sz : SV} {μ : MachineState} (hr : StRel e ρ st μ)
    (hl : st.stk.length ≤ 1024) (hp : pop2 st = .ok (off, sz, s1)) :
    ∃ a b t, μ.stack = a :: b :: t ∧ off.Rel e ρ a.toNat ∧ sz.Rel e ρ b.toNat ∧
      t.length ≤ 1024 := by
  obtain ⟨hs, -⟩ := pop2_ok hp
  have hrs := hr.stk
  rw [hs] at hrs hl
  obtain ⟨a, t1, ht1, ha, hrt1⟩ := hrs.cons_inv
  obtain ⟨b, t, ht2, hb, hrt⟩ := hrt1.cons_inv
  subst ht2
  have := hrt.length
  simp only [List.length_cons] at hl
  exact ⟨a, b, t, ht1, ha, hb, by omega⟩

/-- **`RETURN`**: from a state related by `At`, the checker's `RETURN` of words `ws`, ending a
run of gas `G`, is the EVM halting with the encoding of values the words describe, having paid
`G - st.gas` (the memory expansion), or running out of gas with less than that. -/
theorem final_return (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts) (p : Nat)
    (rest : List (Nat × Ins)) (st : St) (s : State) (f : Nat) (ws : List SV) (tb : Tab)
    (G : Nat) (hA : At e ρ bs ((p, .op 0xf3) :: rest) st s)
    (hc : ctl fs (Code.ofBytes bs) p (.op 0xf3) st = .stop (.ret ws tb G))
    (hg : s.machineState.gasAvailable.toNat < f) :
    tb = st.tab ∧ st.gas ≤ G ∧ ∃ xs, List.Forall₂ (fun w x => w.Rel e ρ x) ws xs ∧
      ((s.machineState.gasAvailable.toNat + st.gas < G ∧
        Eip8024.X f (D_J (codeBA bs) 0) s = .error .OutOfGass) ∨
        ∃ s' o, Eip8024.X f (D_J (codeBA bs) 0) s = .ok (.success s' o) ∧
          o.data.toList = Spec.Interface.encodeWords xs ∧
          s'.machineState.gasAvailable.toNat + G = s.machineState.gasAvailable.toNat + st.gas) := by
  obtain ⟨off, sz, s1, o, n, hp, ho, hn, hmod, hr, rfl, rfl⟩ := ctl_ret_inv hc
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hmod
  rw [Nat.mul_div_cancel_left k (by decide)] at hr
  have hs1 := (pop2_ok hp).2
  have hg1 : s1.gas = st.gas := by rw [hs1]
  have hz1 : s1.msize = st.msize := by rw [hs1]
  obtain ⟨a, b, t, ht, ha, hb, hlen⟩ := stack2 e ρ hA.rel hA.len hp
  have hao : a.toNat = o := rel_exact e ρ off _ _ ha ho
  have hbn : b.toNat = 32 * k := rel_exact e ρ sz _ _ hb hn
  have hm := hA.rel.mem_eq e ρ hs1
  have hmc : memoryExpansionCost s .RETURN =
      memCost (touch s1.msize o (32 * k)) - memCost s1.msize := by
    have : memoryExpansionCost s .RETURN =
        Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
          Cₘ s.machineState.activeWords := by
      unfold memoryExpansionCost memoryExpansionCost.μᵢ'; rw [ht]; rfl
    rw [this, memCost_M _ _ _ _ hA.rel.gas (toNat_lt a) (toNat_lt b), hA.rel.msize, hao, hbn,
      hz1]
  refine ⟨by rw [hs1], by omega, wordsAt (byteAt s.machineState.memory) k o,
    readWords_rel e ρ s1.mem _ hm k o ws hr, ?_⟩
  have hdec := decode_at e ρ hall hA (op := .RETURN) rfl
  obtain ⟨f0, rfl⟩ : ∃ f0, f = f0 + 1 := ⟨f - 1, by omega⟩
  rw [← hA.frame.code]
  rcases xstep_return s hdec a b t ht hlen with ⟨hlt, hx⟩ | ⟨s', hx, hle, hgs⟩
  · exact Or.inl ⟨by omega, X_oog _ f0 s hx⟩
  · refine Or.inr ⟨s', _, X_success _ f0 s s' _ hx, ?_, by omega⟩
    rw [hao, hbn]
    exact readWithPadding_words _ o k

/-- **`REVERT`** of size 0: from a state related by `At`, the EVM reverts with empty output,
paying nothing (no memory expansion for size 0), and the run's gas `G` is the checker's
`st.gas`. -/
theorem final_revert (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts) (p : Nat)
    (rest : List (Nat × Ins)) (st : St) (s : State) (f : Nat) (G : Nat)
    (hA : At e ρ bs ((p, .op 0xfd) :: rest) st s)
    (hc : ctl fs (Code.ofBytes bs) p (.op 0xfd) st = .stop (.revert 0 G))
    (hg : s.machineState.gasAvailable.toNat < f) :
    G = st.gas ∧ ∃ g' o, Eip8024.X f (D_J (codeBA bs) 0) s = .ok (.revert g' o) ∧
      o.data.toList = [] ∧ g'.toNat = s.machineState.gasAvailable.toNat := by
  obtain ⟨off, sz, s1, hp, hn, rfl⟩ := ctl_revert_inv hc
  obtain ⟨a, b, t, ht, -, hb, hlen⟩ := stack2 e ρ hA.rel hA.len hp
  have hb0 : b.toNat = 0 := rel_exact e ρ sz _ _ hb hn
  have hmc : memoryExpansionCost s .REVERT = 0 := by
    have : memoryExpansionCost s .REVERT =
        Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)) -
          Cₘ s.machineState.activeWords := by
      unfold memoryExpansionCost memoryExpansionCost.μᵢ'; rw [ht]; rfl
    rw [this, hb0, M_eq, if_pos rfl, ofNat_toNat, Nat.sub_self]
  have hdec := decode_at e ρ hall hA (op := .REVERT) rfl
  obtain ⟨f0, rfl⟩ : ∃ f0, f = f0 + 1 := ⟨f - 1, by omega⟩
  rw [← hA.frame.code]
  refine ⟨rfl, ?_⟩
  rcases xstep_revert s hdec a b t ht hlen with ⟨hlt, -⟩ | ⟨s', hx, hgs⟩
  · rw [hmc] at hlt; omega
  · refine ⟨_, _, X_revert _ f0 s s' _ hx, ?_, ?_⟩
    · apply List.eq_nil_of_length_eq_zero
      rw [Array.length_toList, ByteArray.size_data, size_readWithPadding, hb0]
    · show s'.machineState.gasAvailable.toNat = _
      rw [hgs, hmc, Nat.sub_zero]

end Poseidon2.Evm.Sim

namespace Poseidon2.Soundness

open Ethereum Poseidon2.Spec Poseidon2.Checker Poseidon2.Spec.Interface Poseidon2.Evm
open Poseidon2.Evm.Sim

theorem outcome_ret (e : Env) (ex : Expect) (h : ex ≠ .revertEmpty) :
    outcome e ex = .ret (encodeWords (specWords e ex)) := by
  cases ex with
  | revertEmpty => exact absurd rfl h
  | _ => rfl

/-- **The core of both statements**: for an accepted case and every call that meets its facts,
with gas `g`, the call runs out of gas if `g` is below the gas `G` of the checker's run, and
otherwise ends exactly as the case expects, with `g - G` gas left. -/
theorem checker_core (bs : List Nat) (cs : Case) (hall : bs.all (· < 256) = true)
    (hc : checkCase (Code.ofBytes bs) cs = true) (cd : List UInt8) (v : Nat)
    (hcd : cd.length < 2 ^ 64) (hv : v < W) (hfs : FactsHold ⟨cd, v⟩ cs.facts)
    (hin : ∀ t ∈ cs.expect.inputs, t.eval ⟨cd, v⟩ < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (henv : env ⟨(bs.map UInt8.ofNat).toArray⟩ cd v I) :
    (g.toNat < (runCase (Code.ofBytes bs) cs).gas ∧
      Eip8024.Ξ σ σ₀ g A I = .error .OutOfGass) ∨
    ((runCase (Code.ofBytes bs) cs).gas ≤ g.toNat ∧
      Exact (g.toNat - (runCase (Code.ofBytes bs) cs).gas) (Eip8024.Ξ σ σ₀ g A I)
        (outcome ⟨cd, v⟩ cs.expect)) := by
  obtain ⟨k, p, i, rest, st', hk, hctl, -, hX⟩ :=
    reaches_final bs hall cs hc cd v hcd hfs σ σ₀ g A I henv
  have hinv := runN_inv' k _ _ _ _ hk St.Inv.init
  have hcode : I.code = codeBA bs := henv.1
  rw [Xi_eq]
  unfold checkCase at hc
  generalize runCase (Code.ofBytes bs) cs = r at hc hctl ⊢
  cases r with
  | ret ws tb G =>
    obtain rfl := ctl_ret hctl
    have hex : cs.expect ≠ .revertEmpty := by
      intro h; rw [h] at hc; simp [resultOk] at hc
    have hom : outputsMatch ws (specForms cs.facts cs.expect tb) = true := by
      revert hc; cases cs.expect <;> simp [resultOk]
    obtain ⟨off, sz, s1, o, n, hp, -, -, -, -, rfl, hG⟩ := ctl_ret_inv hctl
    have hg1 : s1.gas = st'.gas := by rw [(pop2_ok hp).2]
    have htb : s1.tab = st'.tab := by rw [(pop2_ok hp).2]
    obtain ⟨ρ, hv, hw⟩ :=
      spec_sound ⟨cd, v⟩ cs.facts hfs cs.expect s1.tab (htb ▸ hinv.wf) hin
    simp only [Res.gas]
    rcases hX ρ (htb ▸ hv) with ⟨hlt, hx⟩ | ⟨s, f, hx, hA, hg, heq⟩
    · exact Or.inl ⟨by omega, by rw [hx]; rfl⟩
    · rw [hx, hcode]
      obtain ⟨-, hG, xs, hxs, hfin⟩ :=
        final_return ⟨cd, v⟩ ρ bs hall cs.facts p rest st' s f ws s1.tab G hA hctl hg
      rcases hfin with ⟨hlt, hf⟩ | ⟨s', o', hf, ho, hgs⟩
      · exact Or.inl ⟨by omega, by rw [hf]; rfl⟩
      · refine Or.inr ⟨by omega, ?_⟩
        rw [hf, outcome_ret _ _ hex]
        refine ⟨?_, ?_⟩
        · rw [ho, outputsMatch_sound _ ρ ws _ xs hom hxs, hw]
        · show s'.machineState.gasAvailable.toNat = _
          omega
  | revert n G =>
    obtain rfl := ctl_revert hctl
    have hex : cs.expect = .revertEmpty ∧ n = 0 := by
      revert hc; cases cs.expect <;> simp [resultOk]
    obtain ⟨hex, rfl⟩ := hex
    rw [hex]
    obtain ⟨-, -, -, -, -, rfl⟩ := ctl_revert_inv hctl
    simp only [Res.gas]
    rcases hX _ (hinv.wf.valid _) with ⟨hlt, hx⟩ | ⟨s, f, hx, hA, hg, heq⟩
    · exact Or.inl ⟨hlt, by rw [hx]; rfl⟩
    · rw [hx, hcode]
      obtain ⟨-, g', o, hf, ho, hgs⟩ :=
        final_revert _ _ bs hall cs.facts p rest st' s f _ hA hctl hg
      refine Or.inr ⟨by omega, ?_⟩
      rw [hf]
      exact ⟨ho, by omega⟩
  | stop => simp [resultOk] at hc
  | fail _ _ => simp [resultOk] at hc

/-- **The checker is sound** (`CheckerSound`, `Soundness.lean`): an accepted case is what the
EVM does, for every call that satisfies the case's facts, with any gas. -/
theorem checkerSound : CheckerSound := by
  intro bs cs hall hc cd v hcd hv hfs hin σ σ₀ g A I henv
  rcases checker_core bs cs hall hc cd v hcd hv hfs hin σ σ₀ g A I henv with ⟨-, h⟩ | ⟨-, h⟩
  · rw [h]; trivial
  · exact h.matches

/-- **Total correctness** (`CheckerTotal`, `Soundness.lean`): a case accepted with gas `G` is
what the EVM does for every call given at least `G` gas, using exactly `G`, and every call given
less runs out of gas. -/
theorem checkerTotal : CheckerTotal := by
  intro bs cs G hall hc cd v hcd hv hfs hin σ σ₀ g A I henv
  obtain ⟨hc', rfl⟩ := checkCaseGas_eq hc
  rcases checker_core bs cs hall hc' cd v hcd hv hfs hin σ σ₀ g A I henv with
    ⟨hlt, h⟩ | ⟨hle, h⟩
  · exact ⟨fun hle => absurd hle (by omega), fun _ => h⟩
  · exact ⟨fun _ => h, fun hlt => absurd hle (by omega)⟩

end Poseidon2.Soundness
