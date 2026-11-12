import Poseidon2.Evm.Steps
import Poseidon2.Spec.Interface

/-!
# Bytes: EVMLean's byte arrays as functions, big-endian words

EVMLean keeps memory, calldata and code as `ByteArray`s and edits them with `copySlice`. Here
a byte array is read as the function `byteAt m : Nat → Nat` (zero past its end), and every
operation the memory and data opcodes use is stated on that function:

* `byteAt_write`: `ByteArray.write` (memory writes, `CALLDATACOPY`, `CODECOPY`) changes exactly
  the bytes `[da, da + len)`, to the source's bytes (zero past the source's end);
* `byteAt_readWithPadding`, `byteAt_readBytes`: the reads of `MLOAD` / `RETURN` and of
  `CALLDATALOAD`, `n` bytes from `a`, zero past the end;
* `toList_map`: a byte array's bytes as a list (what `RETURN` hands back);
* big-endian words: `beVal` (the checker's and the spec's `foldl (· * 256 + ·)`), EVMLean's
  `fromBytesBigEndian` is `beVal` (`fromBytesBigEndian_eq`), `UInt256.toByteArray` is 32 bytes
  of value `toNat` (`size_toByteArray`, `beVal_toByteArray`), and 32 bytes are determined by
  their value: they are `wordBytes` of it (`bytes_eq_wordBytes`), the spec's encoding of a
  returned word.
-/

namespace Poseidon2.Evm

open Ethereum Poseidon2.Checker

set_option linter.unusedSimpArgs false

/-- Byte `i` of `m`, zero past its end. -/
def byteAt (m : ByteArray) (i : Nat) : Nat := (m.data[i]?.getD 0).toNat

theorem byteAt_lt (m : ByteArray) (i : Nat) : byteAt m i < 256 := UInt8.toNat_lt _

theorem byteAt_of_le (m : ByteArray) (i : Nat) (h : m.size ≤ i) : byteAt m i = 0 := by
  unfold byteAt
  rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; exact h)]
  rfl

theorem byteAt_append (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) i = if i < a.size then byteAt a i else byteAt b (i - a.size) := by
  unfold byteAt
  rw [ByteArray.data_append, Array.getElem?_append, ByteArray.size_data]
  split <;> rfl

theorem byteAt_zeroes (n i : Nat) : byteAt (ByteArray.zeroes n) i = 0 := by
  unfold byteAt ByteArray.zeroes
  simp only [Array.getElem?_replicate]
  split <;> rfl

theorem size_zeroes (n : Nat) : (ByteArray.zeroes n).size = n := ByteArray_zeroes_size n

/-- `copySlice` as a function of the index: the destination before `destOff`, then the copied
source bytes, then the rest of the destination. -/
theorem byteAt_copySlice (S : ByteArray) (so : Nat) (A : ByteArray) (d len : Nat) (ex : Bool)
    (i : Nat) :
    byteAt (S.copySlice so A d len ex) i =
      if i < min d A.size then byteAt A i
      else if i - min d A.size < min (so + len) S.size - so then
        byteAt S (so + (i - min d A.size))
      else byteAt A (d + min len (S.size - so) +
        (i - min d A.size - (min (so + len) S.size - so))) := by
  unfold byteAt ByteArray.copySlice
  simp only [Array.getElem?_append, Array.getElem?_extract, Array.size_append,
    Array.size_extract, ByteArray.size_data, Nat.zero_add, Nat.sub_zero]
  have h1 : min d (min d A.size) = min d A.size := by omega
  have h2 : min A.size A.size = A.size := by omega
  simp only [h1, h2, Nat.sub_add_eq]
  split_ifs <;> first | rfl | omega | skip
  rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega)]

/-- `ByteArray.write` (EVMLean's memory write): the bytes `[da, da + len)` are the source's
from `sa` (zero past its end), every other byte is the destination's. -/
theorem byteAt_write (S : ByteArray) (sa : Nat) (D : ByteArray) (da len i : Nat) :
    byteAt (S.write sa D da len) i =
      if da ≤ i ∧ i < da + len then byteAt S (sa + (i - da)) else byteAt D i := by
  have hS := byteAt_of_le S (sa + (i - da))
  have hD := byteAt_of_le D i
  unfold ByteArray.write
  by_cases h0 : len = 0
  · rw [if_pos h0, if_neg (by omega)]
  rw [if_neg h0]
  by_cases hs : sa ≥ S.size
  · rw [if_pos hs]
    simp only [byteAt_copySlice, size_zeroes, byteAt_zeroes]
    split_ifs <;> first | rfl | omega | (congr 1; omega) |
      (rw [hS (by omega), byteAt_of_le D _ (by omega)])
  · rw [if_neg hs]
    simp only [byteAt_copySlice, byteAt_append, size_zeroes, byteAt_zeroes, ByteArray.size_append]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem size_copySlice (S : ByteArray) (so : Nat) (A : ByteArray) (d len : Nat) (ex : Bool) :
    (S.copySlice so A d len ex).size =
      min d A.size + (min (so + len) S.size - so) +
        (A.size - (d + min len (S.size - so))) := by
  rw [← ByteArray.size_data]
  unfold ByteArray.copySlice
  simp only [Array.size_append, Array.size_extract, ByteArray.size_data]
  omega

/-- A slice copied into an empty array: `len` bytes from `so`, zero past the source's end. -/
theorem byteAt_slice (S : ByteArray) (so len : Nat) (ex : Bool) (j : Nat) :
    byteAt (S.copySlice so ByteArray.empty 0 len ex) j =
      if j < len then byteAt S (so + j) else 0 := by
  have := byteAt_of_le S (so + j)
  have h0 : ByteArray.empty.size = 0 := rfl
  rw [byteAt_copySlice]
  simp only [h0, Nat.min_zero, Nat.zero_le, Nat.sub_zero,
    byteAt_of_le ByteArray.empty _ (Nat.zero_le _)]
  split_ifs <;> first | rfl | omega

theorem size_slice (S : ByteArray) (so len : Nat) (ex : Bool) :
    (S.copySlice so ByteArray.empty 0 len ex).size ≤ len := by
  rw [size_copySlice]
  have h0 : ByteArray.empty.size = 0 := rfl
  rw [h0]; omega

theorem size_empty : ByteArray.empty.size = 0 := rfl

theorem size_readWithPadding (m : ByteArray) (a n : Nat) : (m.readWithPadding a n).size = n := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding ByteArray.extract
  dsimp only
  split
  · rw [ByteArray.size_append, size_zeroes, size_empty]; omega
  · rw [ByteArray.size_append, size_zeroes, size_copySlice, size_empty]; omega

/-- `readWithPadding` (`MLOAD`, `RETURN`): `n` bytes from `a`, zero past the end. -/
theorem byteAt_readWithPadding (m : ByteArray) (a n j : Nat) :
    byteAt (m.readWithPadding a n) j = if j < n then byteAt m (a + j) else 0 := by
  have hm := byteAt_of_le m (a + j)
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding ByteArray.extract
  dsimp only
  split
  · simp only [byteAt_append, byteAt_zeroes, size_empty]
    split_ifs <;> first | rfl | omega
  · simp only [byteAt_append, byteAt_zeroes, byteAt_slice, size_copySlice, size_empty]
    split_ifs <;> first | rfl | omega

/-- `ByteArray.toList` is the bytes of the underlying array. -/
theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  suffices h : ∀ i r, ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i by
    simpa using h 0 []
  intro i r
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hi ih =>
    rw [ih]
    have hi' : i < b.data.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hi']
    simp [ByteArray.get!, getElem!_pos b.data i (by simpa using hi)]
  | case2 i r hi =>
    rw [List.drop_eq_nil_of_le (by simpa using hi)]
    simp

/-- A byte array's bytes as numbers. -/
theorem toList_map (b : ByteArray) :
    b.data.toList.map UInt8.toNat = (List.range b.size).map (byteAt b) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, byteAt]
    rw [Array.getElem?_eq_getElem (by simpa using h1)]
    rfl

theorem size_readBytes (m : ByteArray) (a n : Nat) : (m.readBytes a n).size = n := by
  unfold ByteArray.readBytes
  dsimp only
  split
  · have := size_slice m a n true
    rw [ByteArray.size_append, size_zeroes]; omega
  · have hs : ∀ l : List UInt8, (⟨⟨l⟩⟩ : ByteArray).size = l.length := fun _ => rfl
    rw [ByteArray.size_append, size_zeroes, hs, List.length_take]; omega

/-- `readBytes` (`CALLDATALOAD`): `n` bytes from `a`, zero past the end. -/
theorem byteAt_readBytes (m : ByteArray) (a n j : Nat) :
    byteAt (m.readBytes a n) j = if j < n then byteAt m (a + j) else 0 := by
  have hm := byteAt_of_le m (a + j)
  unfold ByteArray.readBytes
  dsimp only
  split
  · simp only [byteAt_append, byteAt_zeroes, byteAt_slice, size_copySlice, size_empty]
    split_ifs <;> first | rfl | omega
  · simp only [byteAt_append, byteAt_zeroes]
    have hs : ∀ l : List UInt8, (⟨⟨l⟩⟩ : ByteArray).size = l.length := fun _ => rfl
    have hb : ∀ (l : List UInt8) k, byteAt ⟨⟨l⟩⟩ k = (l[k]?.getD 0).toNat := fun _ _ => by
      simp [byteAt]
    rw [hs, hb, toList_eq, List.getElem?_take, List.getElem?_drop, List.length_take,
      List.length_drop]
    simp only [Array.getElem?_toList, Array.length_toList, ByteArray.size_data]
    unfold byteAt
    split_ifs <;> first | rfl | omega |
      (rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega)]; rfl)

/-! ## Big-endian words -/

/-- The value of big-endian bytes, as the checker (`cdWord`, `codeWord`) and the spec
(`calldataWord`) compute it. -/
def beVal (l : List Nat) : Nat := l.foldl (fun acc b => acc * 256 + b) 0

theorem foldl_be (l : List Nat) (acc : Nat) :
    l.foldl (fun acc b => acc * 256 + b) acc = acc * 256 ^ l.length + beVal l := by
  induction l generalizing acc with
  | nil => simp [beVal]
  | cons b l ih =>
    simp only [List.foldl_cons, beVal]
    rw [ih, ih (0 * 256 + b)]
    simp only [List.length_cons, Nat.pow_succ]
    ring

theorem beVal_cons (b : Nat) (l : List Nat) : beVal (b :: l) = b * 256 ^ l.length + beVal l := by
  unfold beVal
  rw [List.foldl_cons, foldl_be]
  simp [beVal]

theorem beVal_lt (l : List Nat) (h : ∀ x ∈ l, x < 256) : beVal l < 256 ^ l.length := by
  induction l with
  | nil => simp [beVal]
  | cons b l ih =>
    rw [beVal_cons, List.length_cons, Nat.pow_succ]
    have hb := h b (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    nlinarith

/-- Byte `j` of big-endian bytes is a digit of their value. -/
theorem beVal_digit (l : List Nat) (h : ∀ x ∈ l, x < 256) (j : Nat) (hj : j < l.length) :
    l[j] = beVal l / 256 ^ (l.length - 1 - j) % 256 := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b l ih =>
    have hb := h b (by simp)
    have hl : ∀ x ∈ l, x < 256 := fun x hx => h x (by simp [hx])
    have hv := beVal_lt l hl
    rw [beVal_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, List.length_cons]
      rw [show l.length + 1 - 1 - 0 = l.length by omega, Nat.add_comm,
        Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv]
      omega
    | succ j =>
      simp only [List.getElem_cons_succ, List.length_cons] at hj ⊢
      rw [ih hl j (by omega), show l.length + 1 - 1 - (j + 1) = l.length - 1 - j by omega]
      generalize he : l.length - 1 - j = e
      have hn : l.length = e + (j + 1) := by omega
      rw [hn, Nat.pow_add, show b * (256 ^ e * 256 ^ (j + 1)) + beVal l =
        beVal l + 256 ^ e * (b * 256 ^ (j + 1)) by ring, Nat.add_mul_div_left _ _ (by positivity),
        show b * 256 ^ (j + 1) = 256 * (b * 256 ^ j) by ring, Nat.add_mul_mod_self_left]

/-- Little-endian value of a list with one more byte at the end. -/
theorem fromBytes'_append (l : List UInt8) (b : UInt8) :
    fromBytes' (l ++ [b]) = fromBytes' l + 256 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [fromBytes']
  | cons a l ih =>
    simp only [List.cons_append, fromBytes', ih, List.length_cons, Nat.pow_succ]
    ring

/-- EVMLean's big-endian value is `beVal`. -/
theorem fromBytesBigEndian_eq (l : List UInt8) :
    fromBytesBigEndian l = beVal (l.map UInt8.toNat) := by
  show fromBytes' l.reverse = _
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_append]
    simp only [fromBytes']
    rw [ih]
    unfold beVal
    rw [List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [show (b.toFin : Nat) = b.toNat from rfl]
    ring

/-- Little-endian bytes of `x` and back (EVMLean proves it privately). -/
theorem fromBytes'_toBytes' (x : Nat) : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp
    show (n + 1) % 256 + 256 * ((n + 1) / 256) = n + 1
    omega

theorem beVal_zeros_append (n : Nat) (l : List Nat) :
    beVal (List.replicate n 0 ++ l) = beVal l := by
  unfold beVal
  rw [List.foldl_append]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldl_cons]; simpa using ih

theorem size_toByteArray (w : UInt256) : w.toByteArray.size = 32 :=
  (UInt256.toByteArrayWithSizeProof w).2

/-- `UInt256.toByteArray` (`MSTORE`) is 32 bytes whose big-endian value is the word. -/
theorem beVal_toByteArray (w : UInt256) :
    beVal (w.toByteArray.data.toList.map UInt8.toNat) = w.toNat := by
  unfold UInt256.toByteArray BE
  dsimp only
  rw [ByteArray.toList_data_append, List.map_append]
  have hz : (ByteArray.zeroes (32 - (toBytesBigEndian w.toNat).toByteArray.size)).data.toList.map
      UInt8.toNat = List.replicate (32 - (toBytesBigEndian w.toNat).toByteArray.size) 0 := by
    simp [ByteArray.zeroes]
  simp only [Function.comp]
  rw [hz, beVal_zeros_append, List.toList_data_toByteArray, ← fromBytesBigEndian_eq]
  unfold fromBytesBigEndian toBytesBigEndian
  simp only [Function.comp, List.reverse_reverse]
  exact fromBytes'_toBytes' _

/-- The word at `a` of a memory given as a byte function. -/
def wordAt (f : Nat → Nat) (a : Nat) : Nat := beVal ((List.range 32).map fun j => f (a + j))

theorem wordAt_congr (f g : Nat → Nat) (a : Nat) (h : ∀ j, j < 32 → f (a + j) = g (a + j)) :
    wordAt f a = wordAt g a := by
  unfold wordAt
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.mp hj)

theorem wordAt_lt (f : Nat → Nat) (a : Nat) (h : ∀ i, f i < 256) : wordAt f a < W := by
  have := beVal_lt ((List.range 32).map fun j => f (a + j)) (by simp [h])
  simpa using this

/-- Big-endian bytes of `m` from `a`, as EVMLean reads them, are `wordAt`. -/
theorem fromByteArrayBigEndian_eq (r : ByteArray) :
    fromByteArrayBigEndian r = beVal ((List.range r.size).map (byteAt r)) := by
  unfold fromByteArrayBigEndian
  rw [toList_eq, fromBytesBigEndian_eq, toList_map]

theorem range_map_byteAt (r : ByteArray) (m : ByteArray) (a n : Nat) (hs : r.size = n)
    (h : ∀ j, j < n → byteAt r j = byteAt m (a + j)) :
    (List.range r.size).map (byteAt r) = (List.range n).map fun j => byteAt m (a + j) := by
  subst hs
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.mp hj)

/-- What EVMLean's `MLOAD` pushes is the word at `a`. -/
theorem mload_toNat (m : ByteArray) (a : Nat) :
    (if a ≥ m.size then (⟨0⟩ : UInt256)
      else UInt256.ofNat (fromByteArrayBigEndian (m.readWithPadding a 32))).toNat =
      wordAt (byteAt m) a := by
  split
  · rename_i h
    unfold wordAt
    rw [List.map_congr_left (g := fun _ => 0) (fun j _ => byteAt_of_le m _ (by omega)),
      show (List.range 32).map (fun _ => 0) = List.replicate 32 0 ++ [] by simp,
      beVal_zeros_append]
    rfl
  · rw [toNat_ofNat, fromByteArrayBigEndian_eq,
      range_map_byteAt _ m a 32 (size_readWithPadding m a 32)
        (fun j hj => by rw [byteAt_readWithPadding, if_pos hj])]
    exact Nat.mod_eq_of_lt (wordAt_lt _ a (byteAt_lt m))

/-- What EVMLean's `CALLDATALOAD` pushes is the word at `a`. -/
theorem calldataload_toNat (m : ByteArray) (a : Nat) :
    (uInt256OfByteArray (m.readBytes a 32)).toNat = wordAt (byteAt m) a := by
  have hs := size_readBytes m a 32
  show (fromBytesBigEndian (m.readBytes a 32).data.toList) % W = _
  rw [fromBytesBigEndian_eq, toList_map,
    range_map_byteAt _ m a 32 hs (fun j hj => by rw [byteAt_readBytes, if_pos hj])]
  exact Nat.mod_eq_of_lt (wordAt_lt _ a (byteAt_lt m))

/-- 32 bytes are the spec's encoding (`wordBytes`) of their big-endian value. -/
theorem bytes_eq_wordBytes (l : List UInt8) (hl : l.length = 32) :
    l = Spec.Interface.wordBytes (beVal (l.map UInt8.toNat)) := by
  apply List.ext_getElem
  · simp [Spec.Interface.wordBytes, hl]
  · intro j h1 h2
    simp only [Spec.Interface.wordBytes, List.getElem_map, List.getElem_range]
    have := beVal_digit (l.map UInt8.toNat)
      (fun x hx => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact UInt8.toNat_lt y) j
      (by simpa using h1)
    simp only [List.getElem_map, List.length_map, hl] at this
    rw [← this]
    simp

end Poseidon2.Evm
