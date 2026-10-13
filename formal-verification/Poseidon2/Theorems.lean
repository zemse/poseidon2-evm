import Poseidon2.Soundness

/-!
# Contract theorems from the checker

For each contract kind: if the checker accepts a bytecode on every case of the kind (a kernel
computation, `Proofs/`), and `CheckerSound` holds, then every call of the bytecode by the EVM
(EVMLean with EIP-8024) with calldata shorter than `2^64` bytes either runs out of gas or ends
as `Spec/Interface.lean` says. `CheckerSound` is a hypothesis of every theorem here: it is
**not proven** (see `Soundness.lean`), so these are conditional results.
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

/-- The call `I` runs artifact `a` on calldata `cd` with call value `v`. -/
abbrev Runs (a : Artifact) (cd : List UInt8) (v : Nat) (I : ExecutionEnv) : Prop :=
  env a.code cd v I

/-- A Huff permutation entry accepted by the checker computes `huffPerm`. -/
theorem huffPerm_correct (hs : CheckerSound) (a : Artifact) (c : Params)
    (hc : (huffPermCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (huffPerm c cd) := by
  have h1 : checkCase (Code.ofBytes a.bytes) ⟨"any calldata", [], .perm c (cdlWords 0 c.t)⟩ = true := by
    simpa [huffPermCases] using hc
  have := hs a.bytes _ (bytes_lt a) h1 cd v hcd hv (by simp [FactsHold]) σ σ₀ g A I hI
  simpa [outcome, huffPerm, cdlWords_eval] using this

theorem eval_cds (cd : List UInt8) (v : Nat) (h : cd.length < 2 ^ 64) :
    Term.eval ⟨cd, v⟩ .cds = cd.length := by
  simp only [Term.eval]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

/-- The t = 4 Huff hash entry accepted by the checker computes `huffHash`. -/
theorem huffHash_correct (hs : CheckerSound) (a : Artifact) (c : Params)
    (hc : (huffHashCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (huffHash c cd) := by
  simp only [huffHashCases, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have hl := eval_cds cd v hcd
  rcases Nat.lt_trichotomy cd.length 0x44 with hlt | heq | hgt
  · have := hs a.bytes _ (bytes_lt a) h1 cd v hcd hv
      (by simp [FactsHold, hl]; omega) σ σ₀ g A I hI
    simpa [outcome, huffHash, huffArity, hlt, cdlWords_eval] using this
  · have := hs a.bytes _ (bytes_lt a) h2 cd v hcd hv
      (by simp [FactsHold, hl, heq]) σ σ₀ g A I hI
    simpa [outcome, huffHash, huffArity, heq, cdlWords_eval] using this
  · have := hs a.bytes _ (bytes_lt a) h3 cd v hcd hv
      (by simp [FactsHold, hl, cdsMax]; omega) σ σ₀ g A I hI
    have h1' : ¬ cd.length < 0x44 := by omega
    have h2' : cd.length ≠ 0x44 := by omega
    simpa [outcome, huffHash, huffArity, h1', h2', cdlWords_eval] using this

/-- A case in an accepted list gives its outcome. -/
theorem of_mem (hs : CheckerSound) (a : Artifact) (cases : List Case) (cs : Case)
    (hcs : cs ∈ cases) (hc : cases.all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (hf : FactsHold ⟨cd, v⟩ cs.facts)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (outcome ⟨cd, v⟩ cs.expect) :=
  hs a.bytes cs (bytes_lt a) (List.all_eq_true.mp hc cs hcs) cd v hcd hv hf σ σ₀ g A I hI

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

/-- A `Poseidon2YulT<t>` wrapper accepted by the checker computes `yulPerm`. -/
theorem yulPerm_correct (hs : CheckerSound) (a : Artifact) (c : Params) (sel : Nat)
    (hsel0 : sel ≠ 0) (hsel : sel < 2 ^ 32)
    (hc : (yulPermCases c sel).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (yulPerm c sel cd v) := by
  have hl := eval_cds cd v hcd
  have hcv := eval_cv cd v hv
  have hx := eval_sel cd v
  have hxl := sel_lt cd
  have hW : (2 : Nat) ^ 64 - 1 < W := by decide
  have go := fun cs hcs hf => of_mem hs a _ cs hcs hc cd v hcd hv hf σ σ₀ g A I hI
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

/-- The cases of `hashCapCases`: every call with calldata shorter than `2^64` bytes that
satisfies the call value facts `cvf` gets the permutation of three words and the capacity. -/
theorem hashCap_correct (hs : CheckerSound) (a : Artifact) (c : Params) (cases : List Case)
    (cvf : Facts) (hcvf : cvf = [(.cv, 0, 0)] ∨ cvf = []) (hsub : ∀ cs ∈ hashCapCases cvf c, cs ∈ cases)
    (hc : cases.all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (hf : FactsHold ⟨cd, v⟩ cvf)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I)
      (.ret (encodeWords [(permutationWords c (calldataWords cd 4 3 ++
        [yulCapacity cd.length])).headD 0])) := by
  have hl := eval_cds cd v hcd
  have go := fun cs hcs hf => of_mem hs a cases cs (hsub cs hcs) hc cd v hcd hv hf σ σ₀ g A I hI
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
      (hfa _ (by
        simp only [shortFacts, factsHold_cons, factsHold_nil, and_true, hl,
          hz 4 (by omega), hz 0x24 (by omega), hz 0x44 (by omega)]
        omega))
    rw [capTerm_short cd.length h4 cvf hcvf] at this
    simpa [outcome, cdlWords_eval, Term.eval] using this
  · have := go ⟨"size >= 4", [(.cds, 4, cdsMax)] ++ cvf,
      .permHead c (cdlWords 4 3 ++ [capTerm ([(.cds, 4, cdsMax)] ++ cvf)])⟩
      (by simp only [hashCapCases]; exact List.mem_append_right _ (by simp))
      (hfa _ (by simp only [factsHold_cons, factsHold_nil, and_true, hl, cdsMax]; omega))
    rw [capTerm_long cvf hcvf] at this
    simpa [outcome, cdlWords_eval, eval_capTerm_long cd v hcd] using this

/-- `Poseidon2Yul_BN254` accepted by the checker computes `yulHash`. -/
theorem yulHash_correct (hs : CheckerSound) (a : Artifact) (c : Params)
    (hc : (yulHashCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (yulHash c cd v) := by
  have hl := eval_cds cd v hcd
  have hcv := eval_cv cd v hv
  unfold yulHash
  by_cases hv0 : v = 0
  · rw [if_neg (not_not.mpr hv0)]
    exact hashCap_correct hs a c _ [(.cv, 0, 0)] (Or.inl rfl)
      (fun cs hcs => List.mem_cons_of_mem _ hcs) hc cd v hcd hv
      (by simp only [factsHold_cons, factsHold_nil, and_true, hcv]; omega) σ σ₀ g A I hI
  · rw [if_pos hv0]
    have := of_mem hs a _ _ (List.mem_cons_self) hc cd v hcd hv
      (by simp only [factsHold_cons, factsHold_nil, and_true, hl, hcv, cdsMax]; omega) σ σ₀ g A I hI
    simpa [outcome] using this

/-- The deployed v2 Huff entry accepted by the checker computes `hashV2` from 4 bytes of
calldata on. -/
theorem hashV2_correct (hs : CheckerSound) (a : Artifact) (c : Params)
    (hc : (hashV2Cases c).all (checkCase (Code.ofBytes a.bytes)) = true)
    (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (h4 : 4 ≤ cd.length) (hv : v < W)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
    Matches (Eip8024.Ξ σ σ₀ g A I) (hashV2 c cd) := by
  have hl := eval_cds cd v hcd
  have := of_mem hs a _ ⟨"size >= 4", [(.cds, 4, cdsMax)] ++ [],
      .permHead c (cdlWords 4 3 ++ [capTerm ([(.cds, 4, cdsMax)] ++ [])])⟩
    (by simp [hashV2Cases, hashCapCases]) hc cd v hcd hv
    (by simp only [List.append_nil, factsHold_cons, factsHold_nil, and_true, hl, cdsMax]; omega)
    σ σ₀ g A I hI
  rw [capTerm_long [] (Or.inr rfl)] at this
  simpa [hashV2, outcome, cdlWords_eval, eval_capTerm_long cd v hcd] using this

end Poseidon2.Theorems
