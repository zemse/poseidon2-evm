import Poseidon2.Evm.Cancun

/-!
# Contract theorems from the checker

For each contract kind, two statements about every call of an accepted bytecode by the EVM
(EVMLean with EIP-8024) with calldata shorter than `2^64` bytes:

* `*_correct` (partial correctness, any gas): if the checker accepts the bytecode on every case of
  the kind (a kernel computation, `Proofs/`), the call either runs out of gas or ends as
  `Spec/Interface.lean` says. From `checkerSound`.
* `*_total` (total correctness): if the checker accepts every case `j` of the kind with gas
  `gas[j]` (`CheckedGas`), the call falls in some case `j`, and given at least `gas[j]` gas it
  ends exactly as `Spec/Interface.lean` says with `gas[j]` used, while given less it runs out of
  gas (`Total`). From `checkerTotal`.

Both come from one dispatch per kind (`huffPerm_of`, ...): the cases of the kind cover every
call, and each case's outcome is the interface's for the calls in it. The cases' input words are
calldata words and the capacity word, all below `2^256`, as `CheckerSound` asks.

A third, `*_cancun`, comes from the same dispatch and `Sim.xi_cancun`: if the code also passes
`Sim.ovFree` (no DUPN / SWAPN where the run can get to), every call gets the same result from
`Eip8024.Ξ` as from EVMLean's Cancun `EVM.Ξ`, so the other two hold of `EVM.Ξ` verbatim.
-/

namespace Poseidon2.Theorems

open Ethereum Poseidon2.Spec Poseidon2.Checker Poseidon2.Spec.Interface Poseidon2.Soundness
open Poseidon2.Bytecode Poseidon2.Evm

theorem cdWord_eq (cd : List UInt8) (off : Nat) : cdWord cd off = calldataWord cd off := rfl

theorem cdlWords_eval (e : Env) (off n : Nat) :
    (cdlWords off n).map (·.eval e) = calldataWords e.cd off n := by
  simp [cdlWords, calldataWords, Term.eval, cdWord_eq]

theorem wordBytes_lt (w : Nat) : (Bytecode.wordBytes w).all (· < 256) = true := by
  simp [Bytecode.wordBytes]; omega

theorem wordsBytes_lt : ∀ ws : List Nat, (wordsBytes ws).all (· < 256) = true
  | [] => rfl
  | w :: ws => by
    simp only [wordsBytes, List.all_append, Bool.and_eq_true]
    exact ⟨wordBytes_lt w, wordsBytes_lt ws⟩

theorem bytes_lt (a : Artifact) : a.bytes.all (· < 256) = true := by
  have := wordsBytes_lt a.words
  simp only [Artifact.bytes, List.all_eq_true] at this ⊢
  exact fun x hx => this x (List.mem_of_mem_take hx)

theorem foldl_bytes_lt : ∀ (l : List Nat) (acc n : Nat), (∀ b ∈ l, b < 256) → acc < 256 ^ n →
    l.foldl (fun acc b => acc * 256 + b) acc < 256 ^ (n + l.length)
  | [], acc, n, _, h => by simpa using h
  | b :: l, acc, n, hb, h => by
    simp only [List.foldl_cons, List.length_cons]
    have hb0 := hb b (by simp)
    have : acc * 256 + b < 256 ^ (n + 1) := by rw [Nat.pow_succ]; omega
    have := foldl_bytes_lt l (acc * 256 + b) (n + 1) (fun x hx => hb x (by simp [hx])) this
    rwa [show n + 1 + l.length = n + (l.length + 1) by omega] at this

theorem calldataWord_lt (cd : List UInt8) (off : Nat) : calldataWord cd off < 2 ^ 256 := by
  have := foldl_bytes_lt ((List.range 32).map fun i => (cd.getD (off + i) 0).toNat) 0 0
    (by simp only [List.mem_map, List.mem_range]; rintro _ ⟨i, -, rfl⟩; exact UInt8.toNat_lt _)
    (by simp)
  simpa [calldataWord] using this

/-- Calldata words are 256-bit words (the input words `CheckerSound` asks for). -/
theorem cdlWords_lt (e : Env) (off n : Nat) : ∀ t ∈ cdlWords off n, t.eval e < W := by
  intro t ht
  simp only [cdlWords, List.mem_map, List.mem_range] at ht
  obtain ⟨i, -, rfl⟩ := ht
  simp only [Term.eval, cdWord_eq]
  exact calldataWord_lt e.cd _

theorem yulCapacity_lt (n : Nat) : yulCapacity n < W := by
  unfold yulCapacity; exact Nat.mod_lt _ (by decide)

/-- The call `I` runs artifact `a` on calldata `cd` with call value `v`. -/
abbrev Runs (a : Artifact) (cd : List UInt8) (v : Nat) (I : ExecutionEnv) : Prop :=
  env a.code cd v I

/-- `Runs` is met by a call frame for every artifact, calldata and call value (the rest of the
frame, the accounts, the substate and the gas are arbitrary in the theorems). -/
theorem runs_exists (a : Artifact) (cd : List UInt8) (v : Nat) : ∃ I, Runs a cd v I :=
  ⟨{ (default : ExecutionEnv) with
      code := a.code, calldata := ⟨cd.toArray⟩, weiValue := .ofNat v }, rfl, by simp, rfl⟩


/-! ## What a list of cases gives -/

/-- Every case of `cases` that a call meets (its facts, and input words below `2^256`) gives its
outcome under `R`. The dispatch lemmas below turn this into `R` of the interface's outcome. -/
def CasesGive (cases : List Case) (cd : List UInt8) (v : Nat) (R : Outcome → Prop) : Prop :=
  ∀ cs ∈ cases, (∀ t ∈ cs.expect.inputs, t.eval ⟨cd, v⟩ < W) → FactsHold ⟨cd, v⟩ cs.facts →
    R (outcome ⟨cd, v⟩ cs.expect)

/-- Accepted cases give the partial-correctness outcome (`checkerSound`). -/
theorem sound_gives (a : Artifact) (cases : List Case)
    (hc : cases.all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    CasesGive cases cd v (Matches (Eip8024.Ξ σ σ₀ g A I)) :=
  fun cs hcs hin hf => checkerSound a.bytes cs (bytes_lt a) (List.all_eq_true.mp hc cs hcs)
    cd v hcd hv hf hin σ σ₀ g A I hI

/-- **Total correctness of a call** with gas `g` and result `r`, for the outcome `o`: the call
meets the facts of some case `j`, with at least `gas[j]` gas `r` is exactly `o` with `gas[j]`
used (`Exact`), and with less `r` is out of gas. -/
def Total (cases : List Case) (gas : List Nat) (e : Env) (g : Nat)
    (r : Except EVM.ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate)))
    (o : Outcome) : Prop :=
  ∃ j, j < cases.length ∧ FactsHold e (cases.getD j default).facts ∧
    (gas.getD j 0 ≤ g → Exact (g - gas.getD j 0) r o) ∧
    (g < gas.getD j 0 → r = .error .OutOfGass)

/-- Cases accepted with their gas give total correctness (`checkerTotal`). -/
theorem total_gives (a : Artifact) (cases : List Case) (gas : List Nat)
    (hc : CheckedGas (Code.ofBytes a.bytes) cases gas)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    CasesGive cases cd v (Total cases gas ⟨cd, v⟩ g.toNat (Eip8024.Ξ σ σ₀ g A I)) := by
  intro cs hcs hin hf
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcs
  have hd : cases.getD j default = cases[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have := checkerTotal a.bytes _ _ (bytes_lt a) (hd ▸ hc.2 j hj) cd v hcd hv hf hin σ σ₀ g A I hI
  exact ⟨j, hj, hd ▸ hf, this.1, this.2⟩

/-- With at least the most gas of any case, total correctness is an exact outcome. -/
theorem Total.exact {cases : List Case} {gas : List Nat} {e : Env} {g : Nat}
    {r : Except EVM.ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate))}
    {o : Outcome} (h : Total cases gas e g r o) (hg : maxGas gas ≤ g) :
    ∃ G, G ≤ maxGas gas ∧ Exact (g - G) r o := by
  obtain ⟨j, -, -, h1, -⟩ := h
  exact ⟨gas.getD j 0, le_maxGas gas j, h1 (le_trans (le_maxGas gas j) hg)⟩

/-! ## Huff permutation entries -/

/-- The case of `huffPerm` covers every call. -/
theorem huffPerm_of (c : Params) (cd : List UInt8) (v : Nat) (R : Outcome → Prop)
    (h : CasesGive (huffPermCases c) cd v R) : R (huffPerm c cd) := by
  have := h ⟨"any calldata", [], .perm c (cdlWords 0 c.t)⟩ (by simp [huffPermCases])
    (cdlWords_lt _ _ _) (by simp [FactsHold])
  simpa [outcome, huffPerm, cdlWords_eval] using this

/-- A Huff permutation entry accepted by the checker computes `huffPerm`. -/
theorem huffPerm_correct (a : Artifact) (c : Params)
    (hc : (huffPermCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (huffPerm c cd) :=
  huffPerm_of c cd v _ (sound_gives a _ hc cd v hcd hv σ σ₀ g A I hI)

/-- A Huff permutation entry accepted with gas `gas` computes `huffPerm` with that gas. -/
theorem huffPerm_total (a : Artifact) (c : Params) (gas : List Nat)
    (hc : CheckedGas (Code.ofBytes a.bytes) (huffPermCases c) gas)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Total (huffPermCases c) gas ⟨cd, v⟩ g.toNat (Eip8024.Ξ σ σ₀ g A I) (huffPerm c cd) :=
  huffPerm_of c cd v _ (total_gives a _ gas hc cd v hcd hv σ σ₀ g A I hI)

theorem eval_cds (cd : List UInt8) (v : Nat) (h : cd.length < 2 ^ 64) :
    Term.eval ⟨cd, v⟩ .cds = cd.length := by
  simp only [Term.eval]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

/-! ## The t = 4 Huff hash entry -/

/-- The three cases of `huffHash` cover every call. -/
theorem huffHash_of (c : Params) (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64)
    (R : Outcome → Prop) (h : CasesGive (huffHashCases c) cd v R) : R (huffHash c cd) := by
  have hl := eval_cds cd v hcd
  rcases Nat.lt_trichotomy cd.length 0x44 with hlt | heq | hgt
  · have := h ⟨"hash_1 (size < 0x44)", [(.cds, 0, 0x43)], .hash c (cdlWords 4 1)⟩
      (by simp [huffHashCases]) (cdlWords_lt _ _ _)
      (by simp [FactsHold, hl]; omega)
    simpa [outcome, huffHash, huffArity, hlt, cdlWords_eval] using this
  · have := h ⟨"hash_2 (size = 0x44)", [(.cds, 0x44, 0x44)], .hash c (cdlWords 4 2)⟩
      (by simp [huffHashCases]) (cdlWords_lt _ _ _)
      (by simp [FactsHold, hl, heq])
    simpa [outcome, huffHash, huffArity, heq, cdlWords_eval] using this
  · have := h ⟨"hash_3 (size > 0x44)", [(.cds, 0x45, cdsMax)], .hash c (cdlWords 4 3)⟩
      (by simp [huffHashCases]) (cdlWords_lt _ _ _)
      (by simp [FactsHold, hl, cdsMax]; omega)
    have h1' : ¬ cd.length < 0x44 := by omega
    have h2' : cd.length ≠ 0x44 := by omega
    simpa [outcome, huffHash, huffArity, h1', h2', cdlWords_eval] using this

/-- The t = 4 Huff hash entry accepted by the checker computes `huffHash`. -/
theorem huffHash_correct (a : Artifact) (c : Params)
    (hc : (huffHashCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (huffHash c cd) :=
  huffHash_of c cd v hcd _ (sound_gives a _ hc cd v hcd hv σ σ₀ g A I hI)

/-- The t = 4 Huff hash entry accepted with gas `gas` computes `huffHash` with that gas. -/
theorem huffHash_total (a : Artifact) (c : Params) (gas : List Nat)
    (hc : CheckedGas (Code.ofBytes a.bytes) (huffHashCases c) gas)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Total (huffHashCases c) gas ⟨cd, v⟩ g.toNat (Eip8024.Ξ σ σ₀ g A I) (huffHash c cd) :=
  huffHash_of c cd v hcd _ (total_gives a _ gas hc cd v hcd hv σ σ₀ g A I hI)

/-! ## The `Poseidon2YulT<t>` wrappers -/

/-- The input words of the `yulPerm` cases: none, or calldata words. -/
theorem yulPermCases_inputs (c : Params) (sel : Nat) (e : Env) :
    ∀ cs ∈ yulPermCases c sel, ∀ t ∈ cs.expect.inputs, t.eval e < W := by
  intro cs hcs
  simp only [yulPermCases, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcs
  split at hcs <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hcs
    repeat' rcases hcs with rfl | hcs
    all_goals first
      | exact cdlWords_lt _ _ _
      | (intro t ht; simp [Expect.inputs] at ht)

theorem eval_cv (cd : List UInt8) (v : Nat) (hv : v < W) : Term.eval ⟨cd, v⟩ .cv = v := by
  simp only [Term.eval]; exact Nat.mod_eq_of_lt hv

theorem eval_sel (cd : List UInt8) (v : Nat) :
    Term.eval ⟨cd, v⟩ selTerm = calldataWord cd 0 / 2 ^ 224 := by
  simp [selTerm, Term.eval, binOp, cdWord_eq, Nat.shiftRight_eq_div_pow]

theorem sel_lt (cd : List UInt8) : calldataWord cd 0 / 2 ^ 224 < 2 ^ 32 := by
  have := calldataWord_lt cd 0
  omega

theorem factsHold_nil (e : Env) : FactsHold e [] := by simp [FactsHold]

theorem factsHold_cons (e : Env) (t : Term) (lo hi : Nat) (fs : Facts) :
    FactsHold e ((t, lo, hi) :: fs) ↔ (lo ≤ t.eval e ∧ t.eval e ≤ hi) ∧ FactsHold e fs := by
  simp [FactsHold]

/-- The cases of `yulPerm` cover every call. -/
theorem yulPerm_of (c : Params) (sel : Nat) (hsel0 : sel ≠ 0) (cd : List UInt8) (v : Nat)
    (hcd : cd.length < 2 ^ 64) (hv : v < W) (R : Outcome → Prop)
    (h : CasesGive (yulPermCases c sel) cd v R) : R (yulPerm c sel cd v) := by
  have hl := eval_cds cd v hcd
  have hcv := eval_cv cd v hv
  have hx := eval_sel cd v
  have hxl := sel_lt cd
  have hW : (2 : Nat) ^ 64 - 1 < W := by decide
  have go := fun cs hcs hf => h cs hcs (yulPermCases_inputs c sel _ cs hcs) hf
  simp only [yulPermCases, hsel0, if_false, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at go
  unfold yulPerm
  by_cases h4 : cd.length < 4
  · rw [if_pos h4]
    by_cases hv0 : v = 0
    · have := go _ (Or.inl rfl)
        (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv]; omega)
      simpa [outcome] using this
    · have := go _ (Or.inr (Or.inl rfl))
        (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv]; omega)
      simpa [outcome] using this
  · rw [if_neg h4]
    rcases Nat.lt_trichotomy (calldataWord cd 0 / 2 ^ 224) sel with hlt | heq | hgt
    · have hne : calldataWord cd 0 / 2 ^ 224 ≠ sel := by omega
      rw [if_pos hne]
      by_cases hv0 : v = 0
      · have := go _ (Or.inr (Or.inr (Or.inl rfl)))
          (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, hx, cdsMax]; omega)
        simpa [outcome] using this
      · have := go _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, hx, cdsMax]; omega)
        simpa [outcome] using this
    · rw [if_neg (not_not.mpr heq)]
      by_cases hv0 : v = 0
      · rw [if_neg (not_not.mpr hv0)]
        by_cases ha : cd.length - 4 < 32 * c.t
        · rw [if_pos ha]
          have := go _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
            (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, hx]; omega)
          simpa [outcome] using this
        · rw [if_neg ha]
          have := go _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
            (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, hx, cdsMax]; omega)
          simpa [outcome, cdlWords_eval] using this
      · rw [if_pos hv0]
        have := go _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
          (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, hx, cdsMax]; omega)
        simpa [outcome] using this
    · have hne : calldataWord cd 0 / 2 ^ 224 ≠ sel := by omega
      rw [if_pos hne]
      by_cases hv0 : v = 0
      · have := go _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, hx, cdsMax]; omega)
        simpa [outcome] using this
      · have := go _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
          (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, hx, cdsMax]; omega)
        simpa [outcome] using this

/-- A `Poseidon2YulT<t>` wrapper accepted by the checker computes `yulPerm`. -/
theorem yulPerm_correct (a : Artifact) (c : Params) (sel : Nat)
    (hsel0 : sel ≠ 0) (hsel : sel < 2 ^ 32)
    (hc : (yulPermCases c sel).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (yulPerm c sel cd v) :=
  yulPerm_of c sel hsel0 cd v hcd hv _ (sound_gives a _ hc cd v hcd hv σ σ₀ g A I hI)

/-- A `Poseidon2YulT<t>` wrapper accepted with gas `gas` computes `yulPerm` with that gas. -/
theorem yulPerm_total (a : Artifact) (c : Params) (sel : Nat)
    (hsel0 : sel ≠ 0) (hsel : sel < 2 ^ 32) (gas : List Nat)
    (hc : CheckedGas (Code.ofBytes a.bytes) (yulPermCases c sel) gas)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Total (yulPermCases c sel) gas ⟨cd, v⟩ g.toNat (Eip8024.Ξ σ σ₀ g A I) (yulPerm c sel cd v) :=
  yulPerm_of c sel hsel0 cd v hcd hv _ (total_gives a _ gas hc cd v hcd hv σ σ₀ g A I hI)

/-! ## `Poseidon2Yul_BN254` and the deployed v2 contracts -/

theorem calldataWord_past (cd : List UInt8) (off : Nat) (h : cd.length ≤ off) :
    calldataWord cd off = 0 := by
  have : (List.range 32).map (fun i => (cd.getD (off + i) 0).toNat) = List.replicate 32 0 := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_replicate]
      simp [List.getElem?_eq_none (show cd.length ≤ off + i by omega)]
  rw [calldataWord, this]
  decide

theorem eval_cdl_past (cd : List UInt8) (v off : Nat) (h : cd.length ≤ off) :
    Term.eval ⟨cd, v⟩ (.cdl off) = 0 := by
  simp only [Term.eval, cdWord_eq]; exact calldataWord_past cd off h

theorem capTerm_short (n : Nat) (hn : n < 4) (cv : Facts) (hcv : cv = [(.cv, 0, 0)] ∨ cv = []) :
    capTerm (shortFacts n ++ cv) = .const (yulCapacity n) := by
  rcases hcv with rfl | rfl <;> (match n, hn with | 0, _ | 1, _ | 2, _ | 3, _ => decide)

theorem capTerm_long (cv : Facts) (hcv : cv = [(.cv, 0, 0)] ∨ cv = []) :
    capTerm ([(.cds, 4, cdsMax)] ++ cv) =
      .bin 0x1b (.const 64) (.bin 0x1c (.const 5) (.bin 0x03 .cds (.const 4))) := by
  rcases hcv with rfl | rfl <;> decide

theorem binOp_sub (a : Nat) : binOp 0x03 a 4 = some ((a + W - 4) % W) := rfl
theorem binOp_shr (a : Nat) : binOp 0x1c 5 a = some (a >>> 5) := rfl
theorem binOp_shl (a : Nat) : binOp 0x1b 64 a = some ((a <<< 64) % W) := rfl

theorem eval_capTerm_long (cd : List UInt8) (v : Nat)
    (hcd : cd.length < 2 ^ 64) :
    Term.eval ⟨cd, v⟩ (.bin 0x1b (.const 64) (.bin 0x1c (.const 5) (.bin 0x03 .cds (.const 4)))) =
      yulCapacity cd.length := by
  have hl := eval_cds cd v hcd
  simp only [Term.eval] at hl ⊢
  rw [hl, binOp_sub, Option.getD_some, binOp_shr, Option.getD_some, binOp_shl, Option.getD_some,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  unfold yulCapacity W
  rfl

/-- The input words of the hash cases: three calldata words and the capacity word. -/
theorem capInputs_lt (e : Env) (cap : Term) (hcap : cap.eval e < W) :
    ∀ t ∈ cdlWords 4 3 ++ [cap], t.eval e < W := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact cdlWords_lt e 4 3 t ht
  · rw [List.mem_singleton.mp ht]; exact hcap

/-- The cases of `hashCapCases`: every call with calldata shorter than `2^64` bytes that
satisfies the call value facts `cvf` gets the permutation of three words and the capacity. -/
theorem hashCap_of (c : Params) (cases : List Case)
    (cvf : Facts) (hcvf : cvf = [(.cv, 0, 0)] ∨ cvf = []) (hsub : ∀ cs ∈ hashCapCases cvf c, cs ∈ cases)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hf : FactsHold ⟨cd, v⟩ cvf)
    (R : Outcome → Prop) (hR : CasesGive cases cd v R) :
    R (.ret (encodeWords [(permutationWords c (calldataWords cd 4 3 ++
        [yulCapacity cd.length])).headD 0])) := by
  have hl := eval_cds cd v hcd
  have go := fun cs hcs hin hf => hR cs (hsub cs hcs) hin hf
  have hfa : ∀ fs : Facts, FactsHold ⟨cd, v⟩ fs → FactsHold ⟨cd, v⟩ (fs ++ cvf) := by
    intro fs h f hf'
    rcases List.mem_append.mp hf' with h1 | h1
    · exact h f h1
    · exact hf f h1
  by_cases h4 : cd.length < 4
  · have hz : ∀ off, 4 ≤ off → Term.eval ⟨cd, v⟩ (.cdl off) = 0 :=
      fun off ho => eval_cdl_past cd v off (by omega)
    have := go ⟨s!"size {cd.length}", shortFacts cd.length ++ cvf,
      .permHead c (cdlWords 4 3 ++ [capTerm (shortFacts cd.length ++ cvf)])⟩
      (by
        simp only [hashCapCases]
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨cd.length, by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega, rfl⟩)
      (capInputs_lt _ _ (by rw [capTerm_short cd.length h4 cvf hcvf]; exact yulCapacity_lt _))
      (hfa _ (by
        simp only [shortFacts, factsHold_cons, factsHold_nil, and_true, hl,
          hz 4 (by omega), hz 0x24 (by omega), hz 0x44 (by omega)]
        omega))
    rw [capTerm_short cd.length h4 cvf hcvf] at this
    simpa [outcome, cdlWords_eval, Term.eval] using this
  · have := go ⟨"size >= 4", [(.cds, 4, cdsMax)] ++ cvf,
      .permHead c (cdlWords 4 3 ++ [capTerm ([(.cds, 4, cdsMax)] ++ cvf)])⟩
      (by simp only [hashCapCases]; exact List.mem_append_right _ (by simp))
      (capInputs_lt _ _ (by
        rw [capTerm_long cvf hcvf, eval_capTerm_long cd v hcd]; exact yulCapacity_lt _))
      (hfa _ (by simp only [factsHold_cons, factsHold_nil, and_true, hl, cdsMax]; omega))
    rw [capTerm_long cvf hcvf] at this
    simpa [outcome, cdlWords_eval, eval_capTerm_long cd v hcd] using this

theorem hashCap_correct (a : Artifact) (c : Params) (cases : List Case)
    (cvf : Facts) (hcvf : cvf = [(.cv, 0, 0)] ∨ cvf = []) (hsub : ∀ cs ∈ hashCapCases cvf c, cs ∈ cases)
    (hc : cases.all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (hf : FactsHold ⟨cd, v⟩ cvf)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I)
      (.ret (encodeWords [(permutationWords c (calldataWords cd 4 3 ++
        [yulCapacity cd.length])).headD 0])) :=
  hashCap_of c cases cvf hcvf hsub cd v hcd hf _ (sound_gives a _ hc cd v hcd hv σ σ₀ g A I hI)

/-- The cases of `yulHash` cover every call. -/
theorem yulHash_of (c : Params) (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64)
    (hv : v < W) (R : Outcome → Prop) (hR : CasesGive (yulHashCases c) cd v R) :
    R (yulHash c cd v) := by
  have hl := eval_cds cd v hcd
  have hcv := eval_cv cd v hv
  unfold yulHash
  by_cases hv0 : v = 0
  · rw [if_neg (not_not.mpr hv0)]
    exact hashCap_of c _ [(.cv, 0, 0)] (Or.inl rfl)
      (fun cs hcs => List.mem_cons_of_mem _ hcs) cd v hcd
      (by simp only [factsHold_cons, factsHold_nil, and_true, hcv]; omega) R hR
  · rw [if_pos hv0]
    have := hR _ List.mem_cons_self (by simp [Expect.inputs])
      (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, cdsMax]; omega)
    simpa [outcome] using this

/-- `Poseidon2Yul_BN254` accepted by the checker computes `yulHash`. -/
theorem yulHash_correct (a : Artifact) (c : Params)
    (hc : (yulHashCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (yulHash c cd v) :=
  yulHash_of c cd v hcd hv _ (sound_gives a _ hc cd v hcd hv σ σ₀ g A I hI)

/-- `Poseidon2Yul_BN254` accepted with gas `gas` computes `yulHash` with that gas. -/
theorem yulHash_total (a : Artifact) (c : Params) (gas : List Nat)
    (hc : CheckedGas (Code.ofBytes a.bytes) (yulHashCases c) gas)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Total (yulHashCases c) gas ⟨cd, v⟩ g.toNat (Eip8024.Ξ σ σ₀ g A I) (yulHash c cd v) :=
  yulHash_of c cd v hcd hv _ (total_gives a _ gas hc cd v hcd hv σ σ₀ g A I hI)

theorem hashV2Short_lt : Interface.hashV2Short < P := by decide

/-- The cases of `hashV2` cover every call: the fixed word below 4 bytes of calldata, the
permutation from 4 on. -/
theorem hashV2_of (c : Params) (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64)
    (R : Outcome → Prop) (hR : CasesGive (hashV2Cases c) cd v R) :
    R (hashV2 c cd) := by
  have hl := eval_cds cd v hcd
  by_cases h4 : cd.length < 4
  · have hz : ∀ off, 4 ≤ off → Term.eval ⟨cd, v⟩ (.cdl off) = 0 :=
      fun off ho => eval_cdl_past cd v off (by omega)
    have := hR ⟨s!"size {cd.length}", shortFacts cd.length, .words [Interface.hashV2Short]⟩
      (by
        simp only [hashV2Cases]
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨cd.length, by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega, rfl⟩)
      (by simp [Expect.inputs])
      (by
        simp only [shortFacts, factsHold_cons, factsHold_nil, and_true, hl,
          hz 4 (by omega), hz 0x24 (by omega), hz 0x44 (by omega)]
        omega)
    simpa [hashV2, h4, outcome, Nat.mod_eq_of_lt hashV2Short_lt] using this
  · have := hR ⟨"size >= 4", [(.cds, 4, cdsMax)] ++ [],
        .permHead c (cdlWords 4 3 ++ [capTerm ([(.cds, 4, cdsMax)] ++ [])])⟩
      (by simp [hashV2Cases, hashCapCases])
      (capInputs_lt _ _ (by
        rw [capTerm_long [] (Or.inr rfl), eval_capTerm_long cd v hcd]; exact yulCapacity_lt _))
      (by simp only [List.append_nil, factsHold_cons, factsHold_nil, and_true, hl, cdsMax]; omega)
    rw [capTerm_long [] (Or.inr rfl)] at this
    simpa [hashV2, h4, outcome, cdlWords_eval, eval_capTerm_long cd v hcd] using this

/-- The deployed v2 Huff entry accepted by the checker computes `hashV2`. -/
theorem hashV2_correct (a : Artifact) (c : Params)
    (hc : (hashV2Cases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (hashV2 c cd) :=
  hashV2_of c cd v hcd _ (sound_gives a _ hc cd v hcd hv σ σ₀ g A I hI)

/-- The deployed v2 Huff entry accepted with gas `gas` computes `hashV2` with that gas. -/
theorem hashV2_total (a : Artifact) (c : Params) (gas : List Nat)
    (hc : CheckedGas (Code.ofBytes a.bytes) (hashV2Cases c) gas)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Total (hashV2Cases c) gas ⟨cd, v⟩ g.toNat (Eip8024.Ξ σ σ₀ g A I) (hashV2 c cd) :=
  hashV2_of c cd v hcd _ (total_gives a _ gas hc cd v hcd hv σ σ₀ g A I hI)

/-! ## Without the overlay: EVMLean's Cancun `Ξ` -/

/-- The result of a call by `Eip8024.Ξ` is EVMLean's `EVM.Ξ`'s. -/
abbrev SameXi (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) : Prop :=
  Eip8024.Ξ σ σ₀ g A I = EVM.Ξ σ σ₀ g A I

/-- Accepted cases on a code that passes `ovFree` give the same result in both
(`Sim.xi_cancun`). -/
theorem cancun_gives (a : Artifact) (cases : List Case)
    (hc : cases.all (checkCase (Code.ofBytes a.bytes)) = true)
    (hov : Sim.ovFree (Code.ofBytes a.bytes) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    CasesGive cases cd v (fun _ => SameXi σ σ₀ g A I) :=
  fun cs hcs _ hf => Sim.xi_cancun a.bytes (bytes_lt a) cs (List.all_eq_true.mp hc cs hcs) hov
    cd v hcd hf σ σ₀ g A I hI

theorem huffPerm_cancun (a : Artifact) (c : Params)
    (hc : (huffPermCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (hov : Sim.ovFree (Code.ofBytes a.bytes) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (_hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    SameXi σ σ₀ g A I :=
  huffPerm_of c cd v (fun _ => SameXi σ σ₀ g A I)
    (cancun_gives a _ hc hov cd v hcd σ σ₀ g A I hI)

theorem huffHash_cancun (a : Artifact) (c : Params)
    (hc : (huffHashCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (hov : Sim.ovFree (Code.ofBytes a.bytes) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (_hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    SameXi σ σ₀ g A I :=
  huffHash_of c cd v hcd (fun _ => SameXi σ σ₀ g A I)
    (cancun_gives a _ hc hov cd v hcd σ σ₀ g A I hI)

theorem yulPerm_cancun (a : Artifact) (c : Params) (sel : Nat)
    (hsel0 : sel ≠ 0) (_hsel : sel < 2 ^ 32)
    (hc : (yulPermCases c sel).all (checkCase (Code.ofBytes a.bytes)) = true)
    (hov : Sim.ovFree (Code.ofBytes a.bytes) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    SameXi σ σ₀ g A I :=
  yulPerm_of c sel hsel0 cd v hcd hv (fun _ => SameXi σ σ₀ g A I)
    (cancun_gives a _ hc hov cd v hcd σ σ₀ g A I hI)

theorem yulHash_cancun (a : Artifact) (c : Params)
    (hc : (yulHashCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (hov : Sim.ovFree (Code.ofBytes a.bytes) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    SameXi σ σ₀ g A I :=
  yulHash_of c cd v hcd hv (fun _ => SameXi σ σ₀ g A I)
    (cancun_gives a _ hc hov cd v hcd σ σ₀ g A I hI)

theorem hashV2_cancun (a : Artifact) (c : Params)
    (hc : (hashV2Cases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (hov : Sim.ovFree (Code.ofBytes a.bytes) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (_hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    SameXi σ σ₀ g A I :=
  hashV2_of c cd v hcd (fun _ => SameXi σ σ₀ g A I)
    (cancun_gives a _ hc hov cd v hcd σ σ₀ g A I hI)

end Poseidon2.Theorems
