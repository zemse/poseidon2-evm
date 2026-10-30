import Poseidon2.Spec.Interface

/-!
# The t = 4 hash interfaces on ABI calldata

ABI calldata of `hash_1`, `hash_2`, `hash_3` (`IPoseidon2`): 4 selector bytes, any, then the
`n = 1, 2, 3` input words, each below `2^256`, as 32 big-endian bytes (`sel ++ encodeWords ws`).
On it `huffHash`, `yulHash` with call value 0 and `hashV2` return the one word
`hashWords c ws` (`huffHash_abi`, `yulHash_abi`, `hashV2_abi`), and for t = 4 `hashWords` is
the Barretenberg / Noir sponge `Poseidon2::hash` of the inputs read modulo `P`
(`hashWords_eq_sponge`). With the contract theorems (`Theorems.lean`, `Proofs/`) the t = 4 hash
contracts compute `hash_1` / `hash_2` / `hash_3` on every ABI call, not only on the samples of
`hash_entries_abi`.
-/

namespace Poseidon2.Spec.Interface

/-- The first `k` of a word's 32 bytes, most significant first, read back. -/
theorem foldl_wordBytes (w k : Nat) (hk : k ≤ 32) :
    ((List.range k).map fun i => (UInt8.ofNat (w / 256 ^ (31 - i) % 256)).toNat).foldl
      (fun acc b => acc * 256 + b) 0 = w / 256 ^ (32 - k) % 256 ^ k := by
  induction k with
  | zero => rw [Nat.pow_zero, Nat.mod_one]; rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have h : 256 ^ (32 - k) = 256 ^ (31 - k) * 256 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [h, ← Nat.div_div_eq_div_mul, show 32 - (k + 1) = 31 - k by omega, Nat.pow_succ',
      Nat.mod_mul]
    generalize w / 256 ^ (31 - k) = q
    simp only [UInt8.toNat_ofNat', Nat.mod_mod]
    omega

theorem wordBytes_length (w : Nat) : (wordBytes w).length = 32 := by
  simp [wordBytes]

theorem wordBytes_getD (w i : Nat) (hi : i < 32) :
    (wordBytes w).getD i 0 = UInt8.ofNat (w / 256 ^ (31 - i) % 256) := by
  simp [wordBytes, List.getD_eq_getElem?_getD, hi]

theorem encodeWords_getD (ws : List Nat) (j i : Nat) (hi : i < 32) :
    (encodeWords ws).getD (32 * j + i) 0 = (wordBytes (ws.getD j 0)).getD i 0 := by
  rw [wordBytes_getD _ _ hi]
  induction ws generalizing j with
  | nil => simp [encodeWords]
  | cons w ws ih =>
    have hw : (wordBytes w).length = 32 := wordBytes_length w
    simp only [encodeWords, List.flatMap_cons, List.getD_eq_getElem?_getD] at ih ⊢
    cases j with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD, wordBytes_getD _ _ hi]
      rfl
    | succ j =>
      rw [List.getElem?_append_right (by omega), hw,
        show 32 * (j + 1) + i - 32 = 32 * j + i by omega, ih j]
      rfl

/-- The word at `4 + 32 j` of ABI calldata is input `j` (zero past the inputs), modulo `2^256`. -/
theorem calldataWord_abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat) (j : Nat) :
    calldataWord (sel ++ encodeWords ws) (4 + 32 * j) = ws.getD j 0 % 2 ^ 256 := by
  have hb : ∀ i ∈ List.range 32, ((sel ++ encodeWords ws).getD (4 + 32 * j + i) 0).toNat =
      (UInt8.ofNat (ws.getD j 0 / 256 ^ (31 - i) % 256)).toNat := by
    intro i hi
    have hi : i < 32 := List.mem_range.mp hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hsel,
      show 4 + 32 * j + i - 4 = 32 * j + i by omega, ← List.getD_eq_getElem?_getD,
      encodeWords_getD _ _ _ hi, wordBytes_getD _ _ hi]
  unfold calldataWord
  rw [List.map_congr_left hb, foldl_wordBytes _ 32 (Nat.le_refl _)]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
  rfl

theorem getD_lt (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 256) (j : Nat) :
    ws.getD j 0 < 2 ^ 256 := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : ws[j]? with _ | w
  · exact Nat.two_pow_pos _
  · exact hws w (List.mem_of_getElem? h)

theorem calldataWords_abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) : calldataWords (sel ++ encodeWords ws) 4 ws.length = ws := by
  apply List.ext_getElem (by simp [calldataWords])
  intro j h1 h2
  simp only [calldataWords, List.getElem_map, List.getElem_range, calldataWord_abi sel hsel,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  exact Nat.mod_eq_of_lt (hws _ (List.getElem_mem h2))

theorem headD_val (l : List F) : (l.map ZMod.val).headD 0 = (l.headD 0).val := by
  cases l <;> simp

theorem encodeWords_length (ws : List Nat) : (encodeWords ws).length = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [encodeWords, List.flatMap_cons, List.length_append, wordBytes_length,
      List.length_cons] at ih ⊢
    omega

/-- The words `yulHash` and `hashV2` permute on ABI calldata, read into the field, are the
sponge state `hash` permutes. -/
theorem capWords_abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3) :
    (calldataWords (sel ++ encodeWords ws) 4 3 ++
        [yulCapacity (sel ++ encodeWords ws).length]).map (fun w => (w : F)) =
      spongeState 4 (ws.map fun w => (w : F)) := by
  have hlen : (sel ++ encodeWords ws).length = 4 + 32 * ws.length := by
    simp [hsel, encodeWords_length]
  have hw : ∀ j, calldataWord (sel ++ encodeWords ws) (4 + 32 * j) = ws.getD j 0 := fun j => by
    rw [calldataWord_abi sel hsel, Nat.mod_eq_of_lt (getD_lt ws hws j)]
  have hcap := yulCapacity_abi _ h3
  have h3w :
      calldataWords (sel ++ encodeWords ws) 4 3 = [ws.getD 0 0, ws.getD 1 0, ws.getD 2 0] := by
    simp only [calldataWords, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.map_append, ← hw]; rfl
  rw [hlen, hcap, h3w, spongeState_eq]
  rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩
  · simp at h1
  · simp
  · simp
  · simp
  · simp at h3; omega

theorem permWords_abi (c : Params) (hc : c.t = 4) (sel : List UInt8) (hsel : sel.length = 4)
    (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3) :
    (permutationWords c (calldataWords (sel ++ encodeWords ws) 4 3 ++
        [yulCapacity (sel ++ encodeWords ws).length])).headD 0 = hashWords c ws := by
  rw [permutationWords, capWords_abi sel hsel ws hws h1 h3, headD_val, hashWords,
    Poseidon2.Spec.hash_eq, hc]

/-- `hash_1` / `hash_2` / `hash_3` of the Huff t = 4 entry. -/
theorem huffHash_abi (c : Params) (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3) :
    huffHash c (sel ++ encodeWords ws) = .ret (encodeWords [hashWords c ws]) := by
  have hlen : (sel ++ encodeWords ws).length = 4 + 32 * ws.length := by
    simp [hsel, encodeWords_length]
  simp only [huffHash, hlen, huffArity_abi _ h1 h3, calldataWords_abi sel hsel ws hws]

/-- `hash_1` / `hash_2` / `hash_3` of `Poseidon2Yul_BN254` (call value 0). -/
theorem yulHash_abi (c : Params) (hc : c.t = 4) (sel : List UInt8) (hsel : sel.length = 4)
    (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3) :
    yulHash c (sel ++ encodeWords ws) 0 = .ret (encodeWords [hashWords c ws]) := by
  simp only [yulHash, ne_eq, not_true_eq_false, if_false,
    permWords_abi c hc sel hsel ws hws h1 h3]

/-- `hash_1` / `hash_2` / `hash_3` of the deployed v2 Huff t = 4 contract. -/
theorem hashV2_abi (c : Params) (hc : c.t = 4) (sel : List UInt8) (hsel : sel.length = 4)
    (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3) :
    hashV2 c (sel ++ encodeWords ws) = .ret (encodeWords [hashWords c ws]) := by
  have hlen : ¬(sel ++ encodeWords ws).length < 4 := by simp [hsel]
  simp only [hashV2, hlen, if_false, permWords_abi c hc sel hsel ws hws h1 h3]

/-- For t = 4 and 1 to 3 inputs, `hashWords` is the Barretenberg / Noir sponge
(`Poseidon2::hash`) of the inputs read modulo `P`. -/
theorem hashWords_eq_sponge (c : Params) (hc : c.t = 4) (ws : List Nat) (h1 : 1 ≤ ws.length)
    (h3 : ws.length ≤ 3) : hashWords c ws = (sponge c (ws.map fun w => (w : F))).val := by
  match ws, h1, h3 with
  | [a], _, _ => simp [hashWords, sponge_eq_hash_1 c hc]
  | [a, b], _, _ => simp [hashWords, sponge_eq_hash_2 c hc]
  | [a, b, d], _, _ => simp [hashWords, sponge_eq_hash_3 c hc]

end Poseidon2.Spec.Interface
