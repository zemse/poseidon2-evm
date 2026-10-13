import Poseidon2.Evm.Run
import Poseidon2.Checker.Valuation

/-!
# The last instruction and the soundness of the checker

* `final_return`: the checker's `RETURN` of words `ws`, from a state related by `At`, is the EVM's
  `RETURN`: the run halts with output `encodeWords xs` for values `xs` the words describe, or
  runs out of gas (memory expansion);
* `final_revert`: the checker's `REVERT` of size 0 is the EVM's `REVERT` with empty output, or out
  of gas;
* `checkerSound`: **`CheckerSound` holds.** `reaches_final` (`Run.lean`) brings the EVM to the
  last instruction, the valuation comes from `spec_sound` (`Checker/Valuation.lean`), and the
  returned values are the spec's words by `outputsMatch_sound` and the spec bridge.
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

variable (e : Env) (ρ : Nat → F)

/-! ## The checker's `RETURN` and `REVERT` -/

theorem ctl_ret_inv {fs : Facts} {code : Code} {pc : Nat} {st : St} {ws : List SV} {tb : Tab}
    (h : ctl fs code pc (.op 0xf3) st = .stop (.ret ws tb)) :
    ∃ off sz s1 o n, pop2 st = .ok (off, sz, s1) ∧ off.exact = some o ∧ sz.exact = some n ∧
      n % 32 = 0 ∧ readWords s1.mem (n / 32) o = .ok ws ∧ tb = s1.tab := by
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
          exact ⟨off, sz, s1, o, n, hp, ho, hn, by omega, hr, rfl⟩
        · cases h
    · cases h
  · cases h

theorem ctl_revert_inv {fs : Facts} {code : Code} {pc : Nat} {st : St} {n : Nat}
    (h : ctl fs code pc (.op 0xfd) st = .stop (.revert n)) :
    ∃ off sz s1, pop2 st = .ok (off, sz, s1) ∧ sz.exact = some n := by
  simp only [ctl] at h
  split at h
  · rename_i off sz s1 hp
    split at h
    · rename_i m hm
      cases h
      exact ⟨off, sz, s1, hp, hm⟩
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
    Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
      ∃ s', Eip8024.Xstep (D_J s.executionEnv.code 0) s =
        .ok (s', some (.success, s.machineState.memory.readWithPadding a.toNat b.toNat)) := by
  rw [xstep_overlay _ s _ _ hdec (by simp), step_return s hdec]
  simp only [hs]
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exfalso; simp only [List.length_cons] at h2; omega
  · exact Or.inr ⟨_, rfl⟩

theorem xstep_revert (s : State)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.REVERT, none))
    (a b : UInt256) (t : List UInt256) (hs : s.machineState.stack = a :: b :: t)
    (hl : t.length ≤ 1024) :
    Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
      ∃ s', Eip8024.Xstep (D_J s.executionEnv.code 0) s =
        .ok (s', some (.revert, s.machineState.memory.readWithPadding a.toNat b.toNat)) := by
  rw [xstep_overlay _ s _ _ hdec (by simp), step_revert s hdec]
  simp only [hs]
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exfalso; simp only [List.length_cons] at h2; omega
  · exact Or.inr ⟨_, rfl⟩

/-- The checker's `.op b` at the run's position is what EVMLean decodes at the EVM's `pc`. -/
theorem decode_at {bs : List Nat} (hall : bs.all (· < 256) = true) {p b : Nat}
    {rest : List (Nat × Ins)} {st : St} {s : State} (hA : At e ρ bs ((p, .op b) :: rest) st s)
    {op : Operation} (hop : parseInstr (UInt8.ofNat b) = some op) :
    EVM.decode s.executionEnv.code s.machineState.pc = some (op, none) := by
  obtain ⟨b', tl, n, r, hd, ho, -, -, -⟩ := hA.dec.cons
  have hp := hA.pc p _ rest rfl
  rw [← hp] at hd
  obtain ⟨rfl, hnp, -, -, -, -⟩ := decodeOne_op ho
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

/-- **`RETURN`**: from a state related by `At`, the checker's `RETURN` of words `ws` is the EVM
halting with the encoding of values the words describe, or running out of gas. -/
theorem final_return (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts) (p : Nat)
    (rest : List (Nat × Ins)) (st : St) (s : State) (f : Nat) (ws : List SV) (tb : Tab)
    (hA : At e ρ bs ((p, .op 0xf3) :: rest) st s)
    (hc : ctl fs (Code.ofBytes bs) p (.op 0xf3) st = .stop (.ret ws tb))
    (hg : s.machineState.gasAvailable.toNat < f) :
    tb = st.tab ∧ ∃ xs, List.Forall₂ (fun w x => w.Rel e ρ x) ws xs ∧
      (Eip8024.X f (D_J (codeBA bs) 0) s = .error .OutOfGass ∨
        ∃ s' o, Eip8024.X f (D_J (codeBA bs) 0) s = .ok (.success s' o) ∧
          o.data.toList = Spec.Interface.encodeWords xs) := by
  obtain ⟨off, sz, s1, o, n, hp, ho, hn, hmod, hr, rfl⟩ := ctl_ret_inv hc
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hmod
  rw [Nat.mul_div_cancel_left k (by decide)] at hr
  have hs1 := (pop2_ok hp).2
  obtain ⟨a, b, t, ht, ha, hb, hlen⟩ := stack2 e ρ hA.rel hA.len hp
  have hao : a.toNat = o := rel_exact e ρ off _ _ ha ho
  have hbn : b.toNat = 32 * k := rel_exact e ρ sz _ _ hb hn
  have hm := hA.rel.mem_eq e ρ hs1
  refine ⟨by rw [hs1], wordsAt (byteAt s.machineState.memory) k o,
    readWords_rel e ρ s1.mem _ hm k o ws hr, ?_⟩
  have hdec := decode_at e ρ hall hA (op := .RETURN) rfl
  obtain ⟨f0, rfl⟩ : ∃ f0, f = f0 + 1 := ⟨f - 1, by omega⟩
  rw [← hA.frame.code]
  rcases xstep_return s hdec a b t ht hlen with hx | ⟨s', hx⟩
  · exact Or.inl (X_oog _ f0 s hx)
  · refine Or.inr ⟨s', _, X_success _ f0 s s' _ hx, ?_⟩
    rw [hao, hbn]
    exact readWithPadding_words _ o k

/-- **`REVERT`** of size 0: from a state related by `At`, the EVM reverts with empty output, or
runs out of gas. -/
theorem final_revert (bs : List Nat) (hall : bs.all (· < 256) = true) (fs : Facts) (p : Nat)
    (rest : List (Nat × Ins)) (st : St) (s : State) (f : Nat)
    (hA : At e ρ bs ((p, .op 0xfd) :: rest) st s)
    (hc : ctl fs (Code.ofBytes bs) p (.op 0xfd) st = .stop (.revert 0))
    (hg : s.machineState.gasAvailable.toNat < f) :
    Eip8024.X f (D_J (codeBA bs) 0) s = .error .OutOfGass ∨
      ∃ g' o, Eip8024.X f (D_J (codeBA bs) 0) s = .ok (.revert g' o) ∧ o.data.toList = [] := by
  obtain ⟨off, sz, s1, hp, hn⟩ := ctl_revert_inv hc
  obtain ⟨a, b, t, ht, -, hb, hlen⟩ := stack2 e ρ hA.rel hA.len hp
  have hb0 : b.toNat = 0 := rel_exact e ρ sz _ _ hb hn
  have hdec := decode_at e ρ hall hA (op := .REVERT) rfl
  obtain ⟨f0, rfl⟩ : ∃ f0, f = f0 + 1 := ⟨f - 1, by omega⟩
  rw [← hA.frame.code]
  rcases xstep_revert s hdec a b t ht hlen with hx | ⟨s', hx⟩
  · exact Or.inl (X_oog _ f0 s hx)
  · refine Or.inr ⟨_, _, X_revert _ f0 s s' _ hx, ?_⟩
    apply List.eq_nil_of_length_eq_zero
    rw [Array.length_toList, ByteArray.size_data, size_readWithPadding, hb0]

end Poseidon2.Evm.Sim

namespace Poseidon2.Soundness

open Ethereum Poseidon2.Spec Poseidon2.Checker Poseidon2.Spec.Interface Poseidon2.Evm
open Poseidon2.Evm.Sim

theorem outcome_ret (e : Env) (ex : Expect) (h : ex ≠ .revertEmpty) :
    outcome e ex = .ret (encodeWords (specWords e ex)) := by
  cases ex with
  | revertEmpty => exact absurd rfl h
  | _ => rfl

/-- **The checker is sound** (`CheckerSound`, `Soundness.lean`): an accepted case is what the
EVM does, for every call that satisfies the case's facts, with any gas. -/
theorem checkerSound : CheckerSound := by
  intro bs cs hall hc cd v hcd hv hfs hin σ σ₀ g A I henv
  obtain ⟨k, p, i, rest, st', hk, hctl, -, hX⟩ :=
    reaches_final bs hall cs hc cd v hcd hfs σ σ₀ g A I henv
  have hinv := runN_inv' k _ _ _ _ hk St.Inv.init
  have hcode : I.code = codeBA bs := henv.1
  rw [Xi_eq]
  unfold checkCase at hc
  generalize runCase (Code.ofBytes bs) cs = r at hc hctl
  cases r with
  | ret ws tb =>
    obtain rfl := ctl_ret hctl
    have hex : cs.expect ≠ .revertEmpty := by
      intro h; rw [h] at hc; simp [resultOk] at hc
    have hom : outputsMatch ws (specForms cs.facts cs.expect tb) = true := by
      revert hc; cases cs.expect <;> simp [resultOk]
    obtain ⟨off, sz, s1, o, n, hp, -, -, -, -, rfl⟩ := ctl_ret_inv hctl
    have htb : s1.tab = st'.tab := by rw [(pop2_ok hp).2]
    obtain ⟨ρ, hv, hw⟩ :=
      spec_sound ⟨cd, v⟩ cs.facts hfs cs.expect s1.tab (htb ▸ hinv.wf) hin
    rcases hX ρ (htb ▸ hv) with hx | ⟨s, f, hx, hA, hg⟩
    · rw [hx]; trivial
    · rw [hx, hcode]
      obtain ⟨-, xs, hxs, hfin⟩ :=
        final_return ⟨cd, v⟩ ρ bs hall cs.facts p rest st' s f ws s1.tab hA hctl hg
      rcases hfin with hf | ⟨s', o', hf, ho⟩
      · rw [hf]; trivial
      · rw [hf, outcome_ret _ _ hex]
        show o'.data.toList = _
        rw [ho, outputsMatch_sound _ ρ ws _ xs hom hxs, hw]
  | revert n =>
    obtain rfl := ctl_revert hctl
    have hex : cs.expect = .revertEmpty ∧ n = 0 := by
      revert hc; cases cs.expect <;> simp [resultOk]
    obtain ⟨hex, rfl⟩ := hex
    rw [hex]
    rcases hX _ (hinv.wf.valid _) with hx | ⟨s, f, hx, hA, hg⟩
    · rw [hx]; trivial
    · rw [hx, hcode]
      rcases final_revert _ _ bs hall cs.facts p rest st' s f hA hctl hg with
        hf | ⟨g', o, hf, ho⟩
      · rw [hf]; trivial
      · rw [hf]
        exact ho
  | stop => simp [resultOk] at hc
  | fail _ _ => simp [resultOk] at hc

end Poseidon2.Soundness
