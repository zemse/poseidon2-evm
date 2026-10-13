import Poseidon2.Evm.Bytes
import Poseidon2.Evm.Sim

/-!
# The checker's word memory against EVMLean's byte memory

The checker keeps memory as a list of words keyed by exact addresses (`St.mem`) and its size in
bytes (`St.msize`); EVMLean keeps a `ByteArray`, the number of active words and the gas. Here:

* `MemRel mem f`: the checker's words describe the byte function `f` (`byteAt` of the EVM's
  memory): the words do not overlap, each describes the 32 bytes at its address (`wordAt`), and
  every byte no word covers is zero;
* `StRel st s`: the stack (`StkRel`), the memory, `activeWords · 32 = msize`, and the gas
  bound `Cₘ activeWords + gas < 2^256`, which every step keeps (memory expansion is paid for)
  and which keeps the memory size far below `2^256`;
* `SimulatesM e ρ s c n st'`: `Simulates` with the memory: the EVM's step runs out of gas, or
  pays `c`, moves `pc` by `n`, changes only the stack, memory and active words, and the
  checker's new state describes the new machine state (`StRel`);
* `step_mem` and `Simulates.lift`: every instruction other than `MLOAD`, `MSTORE`,
  `CALLDATACOPY`, `CODECOPY` leaves the checker's memory and size as they were, so every
  `Simulates` lemma of `Sim.lean` gives `SimulatesM` (EVMLean's step leaves memory alone too);
* the checker's memory operations (`readMem`, `writeMem`, `mstore` and the copy loops) against
  the byte function: `mstore_fill`, `zeroFill_rel`, `cdCopy_rel`, `codeCopy_rel`.
-/

namespace Poseidon2.Evm.Sim

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Spec Poseidon2.Evm

set_option linter.unusedSimpArgs false

variable (e : Env) (ρ : Nat → F)

/-- The words at `a` and `b` do not overlap. -/
def Disj (a b : Nat) : Prop := a + 32 ≤ b ∨ b + 32 ≤ a

/-- The checker's word memory describes the byte function `f`. -/
structure MemRel (mem : List (Nat × SV)) (f : Nat → Nat) : Prop where
  disj : mem.Pairwise fun x y => Disj x.1 y.1
  word : ∀ x ∈ mem, x.2.Rel e ρ (wordAt f x.1)
  zero : ∀ i, (∀ x ∈ mem, ¬ (x.1 ≤ i ∧ i < x.1 + 32)) → f i = 0

theorem MemRel.congr {mem : List (Nat × SV)} {f g : Nat → Nat} (h : MemRel e ρ mem f)
    (hfg : ∀ i, f i = g i) : MemRel e ρ mem g := by
  have : f = g := funext hfg
  subst this; exact h

/-- Bytes `[d, d + n)` from `G`, the others from `f`. -/
def fill (f : Nat → Nat) (d n : Nat) (G : Nat → Nat) (i : Nat) : Nat :=
  if d ≤ i ∧ i < d + n then G (i - d) else f i

theorem fill_zero (f : Nat → Nat) (d : Nat) (G : Nat → Nat) : fill f d 0 G = f := by
  funext i; unfold fill; rw [if_neg (by omega)]

theorem fill_fill (f : Nat → Nat) (d n : Nat) (G : Nat → Nat) :
    fill (fill f d 32 G) (d + 32) n (fun j => G (j + 32)) = fill f d (n + 32) G := by
  funext i; unfold fill; dsimp only
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem wordAt_fill (f : Nat → Nat) (d : Nat) (G : Nat → Nat) :
    wordAt (fill f d 32 G) d = wordAt G 0 := by
  unfold wordAt
  congr 1
  apply List.map_congr_left
  intro j hj
  have := List.mem_range.mp hj
  unfold fill
  rw [if_pos (by omega)]
  congr 1; omega

theorem wordAt_zero (f : Nat → Nat) (a : Nat) (h : ∀ j, j < 32 → f (a + j) = 0) :
    wordAt f a = 0 := by
  unfold wordAt
  rw [List.map_congr_left (g := fun _ => 0) (fun j hj => h j (List.mem_range.mp hj)),
    show (List.range 32).map (fun _ => 0) = List.replicate 32 0 ++ [] by simp, beVal_zeros_append]
  rfl

/-! ## The checker's memory operations -/

theorem readMem_ok (a : Nat) : ∀ (mem : List (Nat × SV)) (v : SV), readMem a mem = .ok v →
    (a, v) ∈ mem ∨ (v = SV.const 0 ∧ ∀ x ∈ mem, Disj x.1 a)
  | [], v, h => by simp only [readMem] at h; cases h; right; simp
  | (k, w) :: r, v, h => by
    simp only [readMem] at h
    split at h
    · cases h; left; rename_i hk; subst hk; simp
    · split at h
      · rcases readMem_ok a r v h with h1 | ⟨h1, h2⟩
        · left; exact List.mem_cons_of_mem _ h1
        · right; refine ⟨h1, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · unfold Disj; omega
          · exact h2 x hx
      · cases h

theorem writeMem_ok (a : Nat) (v : SV) : ∀ (mem mem' : List (Nat × SV)),
    mem.Pairwise (fun x y => Disj x.1 y.1) → writeMem a v mem = .ok mem' →
    mem'.Pairwise (fun x y => Disj x.1 y.1) ∧ (a, v) ∈ mem' ∧
      (∀ x ∈ mem', x = (a, v) ∨ (x ∈ mem ∧ Disj x.1 a)) ∧ (∀ x ∈ mem, x ∈ mem' ∨ x.1 = a)
  | [], mem', _, h => by
    simp only [writeMem] at h; cases h
    simp
  | (k, w) :: r, mem', hp, h => by
    simp only [writeMem] at h
    have hp' := List.pairwise_cons.mp hp
    split at h
    · cases h; rename_i hk; subst hk
      refine ⟨List.Pairwise.cons hp'.1 hp'.2, by simp, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · left; rfl
        · right; exact ⟨List.mem_cons_of_mem _ hx, by
            have := hp'.1 x hx; unfold Disj at this ⊢; omega⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · right; rfl
        · left; exact List.mem_cons_of_mem _ hx
    · split at h
      · rename_i hd
        obtain ⟨r', hr', rfl⟩ : ∃ r', writeMem a v r = .ok r' ∧ mem' = (k, w) :: r' := by
          cases hw : writeMem a v r with
          | error _ => rw [hw] at h; cases h
          | ok r' => rw [hw] at h; cases h; exact ⟨r', rfl, rfl⟩
        obtain ⟨h1, h2, h3, h4⟩ := writeMem_ok a v r r' hp'.2 hr'
        refine ⟨List.Pairwise.cons ?_ h1, List.mem_cons_of_mem _ h2, ?_, ?_⟩
        · intro y hy
          rcases h3 y hy with rfl | ⟨hy, -⟩
          · unfold Disj; omega
          · exact hp'.1 y hy
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · right; exact ⟨List.mem_cons_self .., by unfold Disj; omega⟩
          · rcases h3 x hx with h | ⟨h, h'⟩
            · left; exact h
            · right; exact ⟨List.mem_cons_of_mem _ h, h'⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · left; exact List.mem_cons_self ..
          · rcases h4 x hx with h | h
            · left; exact List.mem_cons_of_mem _ h
            · right; exact h
      · cases h

/-- A read describes the word at its address. -/
theorem readMem_rel (mem : List (Nat × SV)) (f : Nat → Nat) (hm : MemRel e ρ mem f) (a : Nat)
    (v : SV) (h : readMem a mem = .ok v) : v.Rel e ρ (wordAt f a) := by
  rcases readMem_ok a mem v h with h1 | ⟨rfl, h2⟩
  · exact hm.word _ h1
  · rw [wordAt_zero f a (fun j _ => hm.zero _ (fun x hx => by
      have := h2 x hx; unfold Disj at this; omega))]
    exact ⟨Word.const_holds e 0 (by decide), rfl⟩

/-- A write of a value describing the 32 bytes `G 0 .. G 31` at `a`. -/
theorem writeMem_rel (mem mem' : List (Nat × SV)) (f : Nat → Nat) (hm : MemRel e ρ mem f)
    (a : Nat) (v : SV) (G : Nat → Nat) (hv : v.Rel e ρ (wordAt G 0))
    (h : writeMem a v mem = .ok mem') : MemRel e ρ mem' (fill f a 32 G) := by
  obtain ⟨h1, h2, h3, h4⟩ := writeMem_ok a v mem mem' hm.disj h
  refine ⟨h1, ?_, ?_⟩
  · intro x hx
    rcases h3 x hx with rfl | ⟨hx, hd⟩
    · rw [wordAt_fill]; exact hv
    · have := hm.word x hx
      rwa [wordAt_congr (fill f a 32 G) f x.1 (fun j _ => by
        unfold fill; unfold Disj at hd; rw [if_neg (by omega)])]
  · intro i hi
    unfold fill
    rw [if_neg (fun h => hi (a, v) h2 h)]
    apply hm.zero i
    intro x hx hc
    rcases h4 x hx with h | h
    · exact hi x h hc
    · rw [h] at hc; exact hi (a, v) h2 hc

theorem touch_touch (m d n : Nat) :
    touch (touch m d 32) (d + 32) (32 * n) = touch m d (32 * (n + 1)) := by
  unfold touch
  simp only [Nat.max_def]
  split_ifs <;> first | omega | contradiction

/-- `mstore`: the new memory describes `fill f a 32 G`, the size is touched, the rest kept. -/
theorem mstore_fill (st st' : St) (f : Nat → Nat) (hm : MemRel e ρ st.mem f) (a : Nat) (v : SV)
    (G : Nat → Nat) (hv : v.Rel e ρ (wordAt G 0)) (h : mstore st a v = .ok st') :
    MemRel e ρ st'.mem (fill f a 32 G) ∧ st'.msize = touch st.msize a 32 ∧ st'.stk = st.stk ∧
      st'.tab = st.tab := by
  unfold mstore at h
  obtain ⟨mem, hw, h⟩ := bind_ok h
  cases h
  exact ⟨writeMem_rel e ρ _ _ f hm a v G hv hw, rfl, rfl, rfl⟩

theorem touch_zero (m d : Nat) : touch m d 0 = m := by unfold touch; rw [if_pos rfl]

/-- An input word the checker builds describes its value. -/
theorem input_relN (fs : Facts) (hf : Facts.Hold e fs) (t : Term) (hlt : t.eval e < W) :
    (SV.word (mkInput fs t full)).Rel e ρ (t.eval e) :=
  let h := mkInput_sound e fs hf t full (full_sound _ hlt) hlt
  ⟨h.1, h.2.symm⟩

theorem const_relN (v : Nat) (hv : v < W) : (SV.const v).Rel e ρ v :=
  ⟨Word.const_holds e v hv, rfl⟩

/-- `zeroFill`: `k` zero words from `d`. -/
theorem zeroFill_rel : ∀ (k d : Nat) (st st' : St) (f : Nat → Nat), MemRel e ρ st.mem f →
    zeroFill st k d = .ok st' →
    MemRel e ρ st'.mem (fill f d (32 * k) fun _ => 0) ∧ st'.msize = touch st.msize d (32 * k) ∧
      st'.stk = st.stk ∧ st'.tab = st.tab
  | 0, d, st, st', f, hm, h => by
    simp only [zeroFill] at h; cases h
    rw [Nat.mul_zero, fill_zero, touch_zero]; exact ⟨hm, rfl, rfl, rfl⟩
  | k + 1, d, st, st', f, hm, h => by
    simp only [zeroFill] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    obtain ⟨m1, z1, k1, t1⟩ := mstore_fill e ρ st s1 f hm d _ (fun _ => 0)
      (by rw [wordAt_zero _ 0 (fun _ _ => rfl)]; exact const_relN e ρ 0 (by decide)) h1
    obtain ⟨m2, z2, k2, t2⟩ := zeroFill_rel k (d + 32) s1 st' _ m1 h2
    have := fill_fill f d (32 * k) (fun _ => 0)
    rw [this, show 32 * k + 32 = 32 * (k + 1) by ring] at m2
    refine ⟨m2, ?_, k2.trans k1, t2.trans t1⟩
    rw [z2, z1, touch_touch]

/-- The calldata's bytes from `src`. -/
def cdBytes (cd : List UInt8) (src : Nat) (j : Nat) : Nat := (cd.getD (src + j) 0).toNat

theorem cdWord_eq (cd : List UInt8) (src : Nat) : cdWord cd src = wordAt (cdBytes cd src) 0 := by
  unfold cdWord wordAt cdBytes beVal
  simp only [Nat.zero_add]

/-- `cdCopy`: `k` calldata words from `src` to `d`. -/
theorem cdCopy_rel (fs : Facts) (hf : Facts.Hold e fs) : ∀ (k d src : Nat) (st st' : St)
    (f : Nat → Nat), MemRel e ρ st.mem f → cdCopy fs st k d src = .ok st' →
    MemRel e ρ st'.mem (fill f d (32 * k) (cdBytes e.cd src)) ∧
      st'.msize = touch st.msize d (32 * k) ∧ st'.stk = st.stk ∧ st'.tab = st.tab
  | 0, d, src, st, st', f, hm, h => by
    simp only [cdCopy] at h; cases h
    rw [Nat.mul_zero, fill_zero, touch_zero]; exact ⟨hm, rfl, rfl, rfl⟩
  | k + 1, d, src, st, st', f, hm, h => by
    simp only [cdCopy] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    have hv := input_relN e ρ fs hf (.cdl src)
      (by show cdWord e.cd src < W; rw [cdWord_eq]; exact wordAt_lt _ 0 (fun _ => UInt8.toNat_lt _))
    simp only [Term.eval] at hv
    rw [cdWord_eq] at hv
    obtain ⟨m1, z1, k1, t1⟩ := mstore_fill e ρ st s1 f hm d _ _ hv h1
    obtain ⟨m2, z2, k2, t2⟩ := cdCopy_rel fs hf k (d + 32) (src + 32) s1 st' _ m1 h2
    have := fill_fill f d (32 * k) (cdBytes e.cd src)
    have hs : (fun j => cdBytes e.cd src (j + 32)) = cdBytes e.cd (src + 32) := by
      funext j; unfold cdBytes; congr 2; omega
    rw [hs] at this
    rw [this, show 32 * k + 32 = 32 * (k + 1) by ring] at m2
    refine ⟨m2, ?_, k2.trans k1, t2.trans t1⟩
    rw [z2, z1, touch_touch]

/-- The code's bytes, zero past the end. -/
def codeBytes (bs : List Nat) (j : Nat) : Nat := bs.getD j 0

theorem codeWord_eq (bs : List Nat) : codeWord bs 0 = wordAt (codeBytes bs) 0 := by
  unfold codeWord wordAt codeBytes beVal
  congr 1
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.drop_zero, List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [List.getElem_append]
    split
    · rename_i hj
      simp only [List.getElem_take]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hj; omega)]
      rfl
    · rename_i hj
      simp only [List.getElem_replicate]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp at hj h1; omega)]
      rfl

/-- `codeCopy`'s loop: `k` code words from the start of `bs` to `d`. -/
theorem codeCopy_go_rel : ∀ (k d : Nat) (bs : List Nat) (st st' : St) (f : Nat → Nat),
    (∀ x ∈ bs, x < 256) → MemRel e ρ st.mem f → codeCopy.go bs st k d = .ok st' →
    MemRel e ρ st'.mem (fill f d (32 * k) (codeBytes bs)) ∧
      st'.msize = touch st.msize d (32 * k) ∧ st'.stk = st.stk ∧ st'.tab = st.tab
  | 0, d, bs, st, st', f, _, hm, h => by
    simp only [codeCopy.go] at h; cases h
    rw [Nat.mul_zero, fill_zero, touch_zero]; exact ⟨hm, rfl, rfl, rfl⟩
  | k + 1, d, bs, st, st', f, hb, hm, h => by
    simp only [codeCopy.go] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    have hlt : wordAt (codeBytes bs) 0 < W := wordAt_lt _ 0 (fun i => by
      unfold codeBytes
      rw [List.getD_eq_getElem?_getD]
      cases hi : bs[i]? with
      | none => simp
      | some x => exact hb x (List.mem_of_getElem? hi))
    have hv := const_relN e ρ _ hlt
    rw [← codeWord_eq] at hv
    rw [codeWord_eq] at hv h1
    obtain ⟨m1, z1, k1, t1⟩ := mstore_fill e ρ st s1 f hm d _ _ hv h1
    obtain ⟨m2, z2, k2, t2⟩ := codeCopy_go_rel k (d + 32) (bs.drop 32) s1 st' _
      (fun x hx => hb x (List.mem_of_mem_drop hx)) m1 h2
    have := fill_fill f d (32 * k) (codeBytes bs)
    have hs : (fun j => codeBytes bs (j + 32)) = codeBytes (bs.drop 32) := by
      funext j; unfold codeBytes
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; omega
    rw [hs] at this
    rw [this, show 32 * k + 32 = 32 * (k + 1) by ring] at m2
    refine ⟨m2, ?_, k2.trans k1, t2.trans t1⟩
    rw [z2, z1, touch_touch]

theorem pop1_keep {s : St} {v : SV × St} (h : pop1 s = .ok v) :
    v.2.mem = s.mem ∧ v.2.msize = s.msize := by
  unfold pop1 at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

theorem pop2_keep {s : St} {v : SV × SV × St} (h : pop2 s = .ok v) :
    v.2.2.mem = s.mem ∧ v.2.2.msize = s.msize := by
  unfold pop2 at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

theorem pop3_keep {s : St} {v : SV × SV × SV × St} (h : pop3 s = .ok v) :
    v.2.2.2.mem = s.mem ∧ v.2.2.2.msize = s.msize := by
  unfold pop3 at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- Every instruction other than `CALLDATACOPY`, `CODECOPY`, `MLOAD`, `MSTORE` leaves the
checker's memory and memory size as they were. -/
theorem step_mem (fs : Facts) (code : Code) (i : Ins) (st st' : St)
    (h : step fs code i st = .ok st') (h1 : i ≠ .op 0x37) (h2 : i ≠ .op 0x39)
    (h3 : i ≠ .op 0x51) (h4 : i ≠ .op 0x52) : st'.mem = st.mem ∧ st'.msize = st.msize := by
  unfold Checker.step at h
  simp only [bind, Except.bind, push, exactOf] at h
  repeat' (split at h)
  all_goals first | (cases h; done) | (cases h; exact ⟨rfl, rfl⟩) | skip
  all_goals first | (cases h; first | exact pop1_keep (by assumption) |
    exact pop2_keep (by assumption) | exact pop3_keep (by assumption)) | skip
  all_goals exfalso; first | exact h1 rfl | exact h2 rfl | exact h3 rfl | exact h4 rfl

/-! ## The state relation and the step with memory -/

/-- The checker's state describes the EVM's machine state: the stack, the memory, the memory
size, and the gas bound `Cₘ activeWords + gas < 2^256` (true at the start of a call, where no
memory is active, and kept by every step, since memory expansion is paid for). -/
structure StRel (st : St) (μ : MachineState) : Prop where
  stk : StkRel e ρ st.stk μ.stack
  mem : MemRel e ρ st.mem (byteAt μ.memory)
  msize : μ.activeWords.toNat * 32 = st.msize
  gas : Cₘ μ.activeWords + μ.gasAvailable.toNat < W

/-- The EVM state after a step that pays `c`, moves `pc` by `n` and sets the stack, the memory
and the active words. -/
def next (s : State) (c n : Nat) (t : List UInt256) (m : ByteArray) (aw : UInt256) : State :=
  { s with
    machineState.stack := t
    machineState.memory := m
    machineState.activeWords := aw
    machineState.gasAvailable := s.machineState.gasAvailable.subNat c
    machineState.pc := s.machineState.pc + UInt256.ofNat n
    machineState.execLength := s.machineState.execLength + 1 }

/-- The EVM's step from `s`, as the checker's step to `st'` describes it: out of gas, or `c` gas
paid, `pc` moved by `n`, only the stack, memory and active words changed, and `st'` describes
the new machine state. -/
def SimulatesM (s : State) (c n : Nat) (st' : St) : Prop :=
  Eip8024.Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    ∃ t m aw, c ≤ s.machineState.gasAvailable.toNat ∧
      Eip8024.Xstep (D_J s.executionEnv.code 0) s = .ok (next s c n t m aw, none) ∧
      StRel e ρ st' (next s c n t m aw).machineState

theorem toNat_subNat (a : Sat256) (c : Nat) : (a.subNat c).toNat = a.toNat - c := rfl

theorem subNat_subNat (a : Sat256) (m c : Nat) : (a.subNat m).subNat c = a.subNat (m + c) := by
  cases a; simp only [Sat256.subNat, Nat.sub_sub]

/-- A `Simulates` step whose checker step keeps the memory is a `SimulatesM` step. -/
theorem Simulates.lift {s : State} {c n : Nat} {st st' : St} (hs : Simulates e ρ s c n st'.stk)
    (hr : StRel e ρ st s.machineState) (hm : st'.mem = st.mem) (hz : st'.msize = st.msize) :
    SimulatesM e ρ s c n st' := by
  rcases hs with h | ⟨t, ht, hc, hx⟩
  · exact Or.inl h
  · refine Or.inr ⟨t, s.machineState.memory, s.machineState.activeWords, hc, by rw [hx]; rfl, ?_⟩
    have := hr.gas
    exact ⟨ht, hm ▸ hr.mem, hz ▸ hr.msize, by
      show Cₘ s.machineState.activeWords + (s.machineState.gasAvailable.toNat - c) < W; omega⟩

/-- Every `Simulates` lemma of `Sim.lean` gives `SimulatesM`: those instructions keep the
checker's memory. -/
theorem sim_lift (fs : Facts) (code : Code) (i : Ins) (s : State) (c n : Nat) (st st' : St)
    (h : step fs code i st = .ok st') (h1 : i ≠ .op 0x37) (h2 : i ≠ .op 0x39)
    (h3 : i ≠ .op 0x51) (h4 : i ≠ .op 0x52) (hr : StRel e ρ st s.machineState)
    (hs : Simulates e ρ s c n st'.stk) : SimulatesM e ρ s c n st' :=
  let hk := step_mem fs code i st st' h h1 h2 h3 h4
  hs.lift e ρ hr hk.1 hk.2

/-! ## Memory expansion -/

theorem M_eq (s f l : Nat) : MachineState.M s f l = if l = 0 then s else max s ((f + l + 31) / 32) := by
  cases l <;> rfl

theorem Cm_eq (a : UInt256) : Cₘ a = 3 * a.toNat + a.toNat * a.toNat / 512 := rfl

/-- The gas bound keeps the active words below `2^133`. -/
theorem aw_lt (aw : UInt256) (g : Nat) (h : Cₘ aw + g < W) : aw.toNat < 2 ^ 133 := by
  rw [Cm_eq] at h
  by_contra hc
  have h1 : 2 ^ 133 * 2 ^ 133 ≤ aw.toNat * aw.toNat := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 2 ^ 133 * 2 ^ 133 / 512 ≤ aw.toNat * aw.toNat / 512 := Nat.div_le_div_right h1
  have : W ≤ 2 ^ 133 * 2 ^ 133 / 512 := by decide
  omega

/-- The new active words of an access `[a, a + l)` (EVMLean's `M`, no wrap-around). -/
theorem toNat_M (aw : UInt256) (g a l : Nat) (h : Cₘ aw + g < W) (ha : a < W) (hl : l < W) :
    (UInt256.ofNat (MachineState.M aw.toNat a l)).toNat = MachineState.M aw.toNat a l := by
  have := aw_lt aw g h
  rw [toNat_ofNat, M_eq]
  apply Nat.mod_eq_of_lt
  have hW : (2 : Nat) ^ 133 < W := by decide
  split
  · omega
  · simp only [Nat.max_def]; split <;> omega

theorem M_touch (aw a l : Nat) : MachineState.M aw a l * 32 = touch (aw * 32) a l := by
  rw [M_eq]; unfold touch
  split
  · rfl
  · simp only [Nat.max_def]; split_ifs <;> omega

theorem Cm_mono (a b : UInt256) (h : a.toNat ≤ b.toNat) : Cₘ a ≤ Cₘ b := by
  rw [Cm_eq, Cm_eq]
  have := Nat.div_le_div_right (c := 512) (Nat.mul_le_mul h h)
  omega

/-- After an access `[a, a + l)` that does not run out of gas, the gas bound still holds. -/
theorem gas_bound (aw : UInt256) (g a l c : Nat) (h : Cₘ aw + g < W) (ha : a < W) (hl : l < W)
    (hm : Cₘ (UInt256.ofNat (MachineState.M aw.toNat a l)) - Cₘ aw ≤ g) :
    Cₘ (UInt256.ofNat (MachineState.M aw.toNat a l)) +
      (g - (Cₘ (UInt256.ofNat (MachineState.M aw.toNat a l)) - Cₘ aw) - c) < W := by
  have hmono : Cₘ aw ≤ Cₘ (UInt256.ofNat (MachineState.M aw.toNat a l)) := by
    apply Cm_mono
    rw [toNat_M aw g a l h ha hl, M_eq]
    split
    · exact le_refl _
    · exact le_max_left _ _
  omega

end Poseidon2.Evm.Sim
