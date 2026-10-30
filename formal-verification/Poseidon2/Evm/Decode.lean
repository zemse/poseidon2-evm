import Poseidon2.Evm.MemSim
import Poseidon2.Checker.Segments

/-!
# The checker's decoder against EVMLean's

The checker decodes the code once (`Code.ofBytes`: `Checker.decode` with the literal budget
`codeFuel`, and `jumpdests`); EVMLean decodes the instruction at `pc` on every step
(`EVM.decode`, `Eip8024.decode` for DUPN / SWAPN) and finds the jump destinations with `D_J`.
Here they agree at every `pc` the checker's run reaches:

* `Dec bs is`: the instruction lists the run reaches are decoded from the code at their first
  `pc` with budget left (`Dec.ins`, `Dec.suffix`, `Dec.cons`), so their `pc`s stay below
  `33 · 2^20` (no `UInt256` wrap) and consecutive `pc`s differ by the instruction's length;
* `decode_op`, `decode_push`, `decode_push0`, `decode_dupn`, `decode_swapn`: what EVMLean
  decodes at such a `pc`. A `PUSH` the checker accepts has all its immediate bytes (a `PUSH`
  cut by the end of the code is `.bad`, which `step` rejects), so EVMLean's reading of a cut
  `PUSH` without zero padding never matters. DUPN / SWAPN immediates decode to `17 ≤ n`;
* `mem_D_J`: every jump destination the checker finds is in EVMLean's `D_J` (with EIP-8024
  `D_J` is unchanged: EVMLean reads `0xe6` / `0xe7` as one-byte `INVALID`, as `jumpdests` does);
* the opcode table facts (`parse_*`), checked over all 256 bytes by `decide +kernel`.
-/

namespace Poseidon2.Evm

open Ethereum Ethereum.EVM Poseidon2.Checker

set_option linter.unusedSimpArgs false

/-- The code as the EVM holds it (`Soundness.env`). -/
def codeBA (bs : List Nat) : ByteArray := ⟨(bs.map UInt8.ofNat).toArray⟩

/-! ## The checker's side -/

/-- An instruction list the checker's run can reach: decoded from the code at its first `pc`,
with the decoding budget that is left. -/
def Dec (bs : List Nat) (is : List (Nat × Ins)) : Prop :=
  ∃ f q, is = Checker.decode f q (bs.drop q) ∧ q + 33 * f ≤ 33 * codeFuel

theorem Dec.nil (bs : List Nat) : Dec bs [] := ⟨0, 0, by simp [Checker.decode], by omega⟩

theorem Dec.ins (bs : List Nat) : Dec bs (Code.ofBytes bs).ins :=
  ⟨codeFuel, 0, by simp [Code.ofBytes], by omega⟩

/-- `takeBytes` reads `k` bytes big-endian. -/
theorem takeBytes_eq : ∀ (k : Nat) (l : List Nat) (acc v : Nat) (r : List Nat),
    takeBytes k l acc = some (v, r) →
      k ≤ l.length ∧ r = l.drop k ∧ v = acc * 256 ^ k + beVal (l.take k)
  | 0, l, acc, v, r, h => by
    simp only [takeBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [beVal]
  | k + 1, b :: l, acc, v, r, h => by
    simp only [takeBytes] at h
    obtain ⟨h1, h2, h3⟩ := takeBytes_eq k l _ v r h
    refine ⟨by simp; omega, by simpa using h2, ?_⟩
    rw [h3, List.take_succ_cons, beVal_cons, List.length_take, Nat.min_eq_left h1]
    ring
  | _ + 1, [], _, _, _, h => by simp [takeBytes] at h

/-- One decoded instruction: its length is at most 33 bytes, and decoding goes on right after
it. -/
theorem decodeOne_rest (b : Nat) (tl : List Nat) :
    (decodeOne b tl).2.1 ≤ 33 ∧
      ∀ r, (decodeOne b tl).2.2 = some r → r = tl.drop ((decodeOne b tl).2.1 - 1) := by
  unfold decodeOne
  split
  · rename_i hb
    split
    · rename_i v r h
      obtain ⟨-, h2, -⟩ := takeBytes_eq _ _ _ _ _ h
      refine ⟨by simp; omega, fun r' hr => ?_⟩
      simp only [Option.some.injEq] at hr
      rw [← hr, h2]; simp
    · simp
  · split
    · simp
    · split
      · split <;> simp [List.drop_one]
      · simp

/-- The head of a reachable instruction list: its bytes in the code, its decoding, its `pc`
far below `2^256`, and the next instruction at `pc` plus its length. -/
theorem Dec.cons {bs : List Nat} {p : Nat} {i : Ins} {rest : List (Nat × Ins)}
    (h : Dec bs ((p, i) :: rest)) :
    ∃ b tl n r, bs.drop p = b :: tl ∧ decodeOne b tl = (i, n, r) ∧
      p + 33 ≤ 33 * codeFuel ∧ Dec bs rest ∧
      ∀ p' i' rest', rest = (p', i') :: rest' → p' = p + n := by
  obtain ⟨f, q, he, hb⟩ := h
  cases f with
  | zero => simp [Checker.decode] at he
  | succ f =>
    cases hd : bs.drop q with
    | nil => rw [hd] at he; simp [Checker.decode] at he
    | cons b tl =>
      rw [hd] at he
      rcases ho : decodeOne b tl with ⟨i0, n, r⟩
      have hn := decodeOne_len b tl
      have hr := decodeOne_rest b tl
      rw [ho] at hn hr
      simp only [Checker.decode, ho, List.cons.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨rfl, rfl⟩, he⟩ := he
      refine ⟨b, tl, n, r, hd, ho, by omega, ?_, ?_⟩
      · cases r with
        | none => rw [he]; exact Dec.nil bs
        | some r =>
          refine ⟨f, p + n, ?_, by simp at hr; omega⟩
          rw [he, hr.2 r rfl]
          have : bs.drop (p + 1) = tl := by
            rw [← List.drop_drop, hd]; rfl
          rw [show p + n = p + 1 + (n - 1) by simp at hn; omega, ← List.drop_drop, this]
      · intro p' i' rest' hrest
        cases r with
        | none => rw [he] at hrest; cases hrest
        | some r =>
          rw [he] at hrest
          cases f with
          | zero => simp [Checker.decode] at hrest
          | succ f =>
            cases r with
            | nil => simp [Checker.decode] at hrest
            | cons b' tl' =>
              simp only [Checker.decode, List.cons.injEq, Prod.mk.injEq] at hrest
              exact hrest.1.1.symm

/-- Every suffix of a reachable instruction list is reachable. -/
theorem Dec.suffix {bs : List Nat} :
    ∀ {is l : List (Nat × Ins)}, Dec bs is → l <:+ is → Dec bs l
  | [], l, _, hl => by rw [List.suffix_nil.mp hl]; exact Dec.nil bs
  | (p, i) :: rest, l, h, hl => by
    rcases List.suffix_cons_iff.mp hl with rfl | hl
    · exact h
    · obtain ⟨-, -, -, -, -, -, -, hrest, -⟩ := h.cons
      exact Dec.suffix hrest hl

/-- A jump destination the checker finds: a `JUMPDEST` of `jumpdests`, and the instructions from
it on, a suffix of the decoded code. -/
theorem destSuffixes_mem (dj : List Nat) :
    ∀ (l : List (Nat × Ins)), ∀ d ∈ destSuffixes dj l,
      d.1 ∈ dj ∧ (∃ rest, d.2 = (d.1, .op 0x5b) :: rest) ∧ d.2 <:+ l
  | [], d, hd => by simp [destSuffixes] at hd
  | (pc, i) :: rest, d, hd => by
    have tail : ∀ d ∈ destSuffixes dj rest,
        d.1 ∈ dj ∧ (∃ rest, d.2 = (d.1, .op 0x5b) :: rest) ∧ d.2 <:+ (pc, i) :: rest :=
      fun d hd => let h := destSuffixes_mem dj rest d hd
        ⟨h.1, h.2.1, h.2.2.trans (List.suffix_cons _ _)⟩
    simp only [destSuffixes] at hd
    split at hd
    · split at hd
      · rename_i hc
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact ⟨by simpa using hc, ⟨rest, rfl⟩, List.suffix_refl _⟩
        · exact tail d hd
      · exact tail d hd
    · exact tail d hd

theorem findDest_some (t : Nat) :
    ∀ (ds : List (Nat × List (Nat × Ins))) (is : List (Nat × Ins)),
      findDest t ds = some is → ∃ d ∈ ds, d.1 = t ∧ d.2 = is
  | [], _, h => by simp [findDest] at h
  | (p, l) :: ds, is, h => by
    simp only [findDest] at h
    split at h
    · rename_i hp
      exact ⟨(p, l), by simp, hp, by simpa using h⟩
    · obtain ⟨d, hd, e⟩ := findDest_some t ds is h
      exact ⟨d, by simp [hd], e⟩

/-- A jump the checker takes lands on a `JUMPDEST` that `jumpdests` found, in a reachable
instruction list. -/
theorem findDest_ofBytes (bs : List Nat) (t : Nat) (is : List (Nat × Ins))
    (h : findDest t (Code.ofBytes bs).dests = some is) :
    t ∈ jumpdests codeFuel 0 bs ∧ (∃ rest, is = (t, .op 0x5b) :: rest) ∧ Dec bs is := by
  obtain ⟨d, hd, h1, h2⟩ := findDest_some t _ is h
  obtain ⟨m1, ⟨rest, m2⟩, m3⟩ := destSuffixes_mem _ _ d hd
  subst h1 h2
  exact ⟨m1, ⟨rest, m2⟩, (Dec.ins bs).suffix m3⟩

/-! ## The code as the EVM holds it -/

theorem size_codeBA (bs : List Nat) : (codeBA bs).size = bs.length := by
  simp [codeBA, ByteArray.size]

theorem get?_eq (a : ByteArray) (n : Nat) : a.get? n = a.data[n]? := by
  unfold ByteArray.get?
  split
  · rename_i h
    rw [Array.getElem?_eq_getElem (by simpa using h)]
    rfl
  · rename_i h
    rw [Array.getElem?_eq_none (by simpa using h)]

theorem data_codeBA (bs : List Nat) (i : Nat) : (codeBA bs).data[i]? = bs[i]?.map UInt8.ofNat := by
  simp [codeBA]

theorem lt_of_all {bs : List Nat} (hall : bs.all (· < 256) = true) {x : Nat} (hx : x ∈ bs) :
    x < 256 := by
  simpa using List.all_eq_true.mp hall x hx

theorem head_lt {bs : List Nat} (hall : bs.all (· < 256) = true) {p b : Nat} {tl : List Nat}
    (hd : bs.drop p = b :: tl) : b < 256 :=
  lt_of_all hall (List.mem_of_mem_drop (a := b) (i := p) (by rw [hd]; simp))

theorem get?_codeBA {bs : List Nat} {p b : Nat} {tl : List Nat}
    (hd : bs.drop p = b :: tl) : (codeBA bs).get? p = some (UInt8.ofNat b) := by
  have : bs[p]? = some b := by
    have := congrArg (·[0]?) hd
    simpa [List.getElem?_drop] using this
  rw [get?_eq, data_codeBA, this]
  rfl

theorem byteAt_codeBA {bs : List Nat} (hall : bs.all (· < 256) = true) (i : Nat) :
    byteAt (codeBA bs) i = bs.getD i 0 := by
  unfold byteAt
  rw [data_codeBA, List.getD_eq_getElem?_getD]
  cases h : bs[i]? with
  | none => rfl
  | some x =>
    have := lt_of_all hall (List.mem_of_getElem? h)
    simp only [Option.map_some, Option.getD_some, UInt8.toNat_ofNat']
    omega

/-! ## The opcode table, over all 256 bytes -/

theorem parse_some : ∀ n, n < 256 → (parseInstr (UInt8.ofNat n)).isSome = true := by
  decide +kernel

/-- The immediate width EVMLean gives each byte: `PUSH1` .. `PUSH32` only. -/
theorem parse_width : ∀ n, n < 256 →
    argOnNBytesOfInstr ((parseInstr (UInt8.ofNat n)).getD .INVALID) =
      if 0x60 ≤ n ∧ n ≤ 0x7f then n - 0x5f else 0 := by
  decide +kernel

theorem parse_jumpdest : ∀ n, n < 256 →
    (parseInstr (UInt8.ofNat n) = some .JUMPDEST ↔ n = 0x5b) := by
  decide +kernel

/-- `PUSH1` .. `PUSH32`. -/
def pushOk : Option Operation → Bool
  | some (.Push op) => op != .PUSH0
  | _ => false

/-- `DUPn` with `n = b - 0x7f`. -/
def dupOk (b : Nat) : Option Operation → Bool
  | some (.Dup d) => dupN d == b - 0x7f
  | _ => false

/-- `SWAPn` with `n = b - 0x8f`. -/
def swapOk (b : Nat) : Option Operation → Bool
  | some (.Exchange x) => swapN x == b - 0x8f
  | _ => false

theorem parse_push : ∀ n, n < 256 → 0x60 ≤ n → n ≤ 0x7f →
    pushOk (parseInstr (UInt8.ofNat n)) = true := by
  decide +kernel

theorem parse_dup : ∀ n, n < 256 → 0x80 ≤ n → n ≤ 0x8f →
    dupOk n (parseInstr (UInt8.ofNat n)) = true := by
  decide +kernel

theorem parse_swap : ∀ n, n < 256 → 0x90 ≤ n → n ≤ 0x9f →
    swapOk n (parseInstr (UInt8.ofNat n)) = true := by
  decide +kernel

theorem dupOk_eq {b : Nat} {o : Option Operation} (h : dupOk b o = true) :
    ∃ d, o = some (.Dup d) ∧ dupN d = b - 0x7f := by
  unfold dupOk at h
  split at h
  · exact ⟨_, rfl, by simpa using h⟩
  · cases h

theorem swapOk_eq {b : Nat} {o : Option Operation} (h : swapOk b o = true) :
    ∃ x, o = some (.Exchange x) ∧ swapN x = b - 0x8f := by
  unfold swapOk at h
  split at h
  · exact ⟨_, rfl, by simpa using h⟩
  · cases h

theorem pushOk_eq {o : Option Operation} (h : pushOk o = true) :
    ∃ op, o = some (.Push op) ∧ op ≠ .PUSH0 := by
  unfold pushOk at h
  split at h
  · exact ⟨_, rfl, by simpa using h⟩
  · cases h

/-! ## What EVMLean decodes where the checker decoded -/

/-- An instruction without immediate. -/
theorem decode_op {bs : List Nat} (hall : bs.all (· < 256) = true) {pc : UInt256} {b : Nat}
    {tl : List Nat} (hd : bs.drop pc.toNat = b :: tl) (hb : ¬ (0x60 ≤ b ∧ b ≤ 0x7f))
    {op : Operation} (hp : parseInstr (UInt8.ofNat b) = some op) :
    EVM.decode (codeBA bs) pc = some (op, none) := by
  have hw := parse_width b (head_lt hall hd)
  rw [hp, if_neg hb] at hw
  simp only [Option.getD_some] at hw
  unfold EVM.decode
  simp [get?_codeBA hd, hp, hw, bind, Option.bind]

/-- `PUSH1` .. `PUSH32` with all its immediate bytes: EVMLean pushes the checker's value. -/
theorem decode_push {bs : List Nat} (hall : bs.all (· < 256) = true) {pc : UInt256} {b : Nat}
    {tl : List Nat} (hd : bs.drop pc.toNat = b :: tl) (hb : 0x60 ≤ b ∧ b ≤ 0x7f) {v : Nat}
    {r : List Nat} (ht : takeBytes (b - 0x5f) tl 0 = some (v, r)) (hpc : pc.toNat + 33 < 2 ^ 64) :
    ∃ op arg, EVM.decode (codeBA bs) pc = some (.Push op, some (arg, b - 0x5f)) ∧
      op ≠ .PUSH0 ∧ arg.toNat = v := by
  have hb256 := head_lt hall hd
  have hpush := parse_push b hb256 hb.1 hb.2
  have hw := parse_width b hb256
  rw [if_pos hb] at hw
  obtain ⟨hk, -, hv⟩ := takeBytes_eq _ _ _ _ _ ht
  simp only [zero_mul, zero_add] at hv
  obtain ⟨op, hq, hpush⟩ := pushOk_eq hpush
  · rw [hq] at hw
    simp only [Option.getD_some] at hw
    have hlen : bs.length = pc.toNat + 1 + tl.length := by
      have := congrArg List.length hd
      simp at this; omega
    refine ⟨op, uInt256OfByteArray ((codeBA bs).extract' pc.toNat.succ
      (pc.toNat.succ + (b - 0x5f))), ?_, hpush, ?_⟩
    · unfold EVM.decode
      simp only [get?_codeBA hd, hq, hw, bind, Option.bind]
      rw [if_neg (by simp; omega)]
    · -- the immediate bytes, read as EVMLean reads them
      have hx : (codeBA bs).extract' pc.toNat.succ (pc.toNat.succ + (b - 0x5f)) =
          (codeBA bs).copySlice (pc.toNat + 1) ByteArray.empty 0 (b - 0x5f) := by
        unfold ByteArray.extract'
        rw [if_pos (by simp; omega)]
        unfold ByteArray.extract
        congr 1; omega
      rw [hx]
      show (fromBytesBigEndian _) % W = v
      rw [fromBytesBigEndian_eq, toList_map]
      have hs : ((codeBA bs).copySlice (pc.toNat + 1) ByteArray.empty 0 (b - 0x5f)).size =
          b - 0x5f := by
        rw [size_copySlice, size_codeBA, size_empty]; omega
      rw [range_map_byteAt _ (codeBA bs) (pc.toNat + 1) _ hs
        (fun j hj => by rw [byteAt_slice, if_pos hj])]
      have hl : (List.range (b - 0x5f)).map (fun j => byteAt (codeBA bs) (pc.toNat + 1 + j)) =
          tl.take (b - 0x5f) := by
        apply List.ext_getElem
        · simp; omega
        · intro j h1 h2
          simp only [List.getElem_map, List.getElem_range, List.getElem_take, byteAt_codeBA hall]
          have htl : bs.drop (pc.toNat + 1) = tl := by rw [← List.drop_drop, hd]; rfl
          rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, htl,
            List.getElem?_eq_getElem (by simp at h2; omega)]
          rfl
      rw [hl, hv]
      apply Nat.mod_eq_of_lt
      have := beVal_lt (tl.take (b - 0x5f))
        (fun x hx => lt_of_all hall (List.mem_of_mem_drop (i := pc.toNat + 1)
          (by rw [← List.drop_drop, hd]; exact List.mem_of_mem_take (by simpa using hx))))
      calc _ < 256 ^ (tl.take (b - 0x5f)).length := this
        _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) (by simp; omega)
        _ = W := rfl

/-- The immediate EIP-8024 reads is the checker's next byte. -/
theorem immediate_codeBA {bs : List Nat} (hall : bs.all (· < 256) = true) {p b : Nat}
    {tl : List Nat} (hd : bs.drop p = b :: tl) : Eip8024.immediate (codeBA bs) p = tl.headD 0 := by
  unfold Eip8024.immediate
  cases tl with
  | nil =>
    have : bs.length = p + 1 := by
      have := congrArg List.length hd
      simp at this; omega
    unfold ByteArray.get?
    rw [dif_neg (by rw [size_codeBA]; omega)]
    rfl
  | cons x tl =>
    have hx : bs.drop (p + 1) = x :: tl := by rw [← List.drop_drop, hd]; rfl
    rw [get?_codeBA hx]
    have := head_lt hall hx
    simp only [Option.getD_some, UInt8.toNat_ofNat', List.headD_cons]
    omega

theorem decodeSingle_ge {x n : Nat} (hx : x < 256) (h : Checker.decodeSingle x = some n) :
    17 ≤ n := by
  unfold Checker.decodeSingle at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · cases h

theorem immediate_lt {bs : List Nat} (hall : bs.all (· < 256) = true) {p b : Nat}
    {tl : List Nat} (hd : bs.drop p = b :: tl) : tl.headD 0 < 256 := by
  cases tl with
  | nil => simp
  | cons x tl =>
    exact head_lt hall (show bs.drop (p + 1) = x :: tl by rw [← List.drop_drop, hd]; rfl)

/-- DUPN as the checker decodes it is EIP-8024's DUPN, with `17 ≤ n`. -/
theorem decode_dupn {bs : List Nat} (hall : bs.all (· < 256) = true) {p : Nat} {tl : List Nat}
    (hd : bs.drop p = 0xe6 :: tl) {n : Nat} (hn : Checker.decodeSingle (tl.headD 0) = some n) :
    Eip8024.decode (codeBA bs) p = some (some (.dupn n)) ∧ 17 ≤ n := by
  refine ⟨?_, decodeSingle_ge (immediate_lt hall hd) hn⟩
  unfold Eip8024.decode
  rw [get?_codeBA hd, immediate_codeBA hall hd]
  have : Eip8024.decodeSingle (tl.headD 0) = some n := hn
  rw [this]; rfl

/-- SWAPN as the checker decodes it is EIP-8024's SWAPN, with `17 ≤ n`. -/
theorem decode_swapn {bs : List Nat} (hall : bs.all (· < 256) = true) {p : Nat} {tl : List Nat}
    (hd : bs.drop p = 0xe7 :: tl) {n : Nat} (hn : Checker.decodeSingle (tl.headD 0) = some n) :
    Eip8024.decode (codeBA bs) p = some (some (.swapn n)) ∧ 17 ≤ n := by
  refine ⟨?_, decodeSingle_ge (immediate_lt hall hd) hn⟩
  unfold Eip8024.decode
  rw [get?_codeBA hd, immediate_codeBA hall hd]
  have : Eip8024.decodeSingle (tl.headD 0) = some n := hn
  rw [this]; rfl

/-! ## Jump destinations -/

theorem mem_D_J_aux (c : ByteArray) (i : Nat) (result : Array UInt256) :
    ∀ x ∈ result, x ∈ D_J_aux c i result := by
  induction i, result using D_J_aux.induct c with
  | case1 i result h =>
    intro x hx
    rw [D_J_aux.eq_def]
    split
    · exact hx
    · rename_i heq; rw [h] at heq; cases heq
  | case2 i result cᵢ h ih =>
    intro x hx
    rw [D_J_aux.eq_def]
    split
    · rename_i heq; rw [h] at heq; cases heq
    · rename_i c' heq
      rw [h] at heq
      cases heq
      apply ih
      split
      · exact Array.mem_push_of_mem _ hx
      · exact hx

/-- Every jump destination of `jumpdests` from `i` is one of EVMLean's from `i`. -/
theorem jumpdests_D_J {bs : List Nat} (hall : bs.all (· < 256) = true) :
    ∀ (f i : Nat) (result : Array UInt256) (t : Nat), t ∈ jumpdests f i (bs.drop i) →
      UInt256.ofNat t ∈ D_J_aux (codeBA bs) i result
  | 0, _, _, _, ht => by simp [jumpdests] at ht
  | f + 1, i, result, t, ht => by
    cases hd : bs.drop i with
    | nil => rw [hd] at ht; simp [jumpdests] at ht
    | cons b tl =>
      rw [hd] at ht
      have hb256 := head_lt hall hd
      have hs := parse_some b hb256
      obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp hs
      have hw := parse_width b hb256
      rw [hop] at hw
      simp only [Option.getD_some] at hw
      have hq : (codeBA bs).get? i >>= parseInstr = some op := by
        rw [get?_codeBA hd]; exact hop
      have htl : bs.drop (i + 1) = tl := by rw [← List.drop_drop, hd]; rfl
      rw [D_J_aux.eq_def]
      split
      · rename_i heq; rw [hq] at heq; cases heq
      · rename_i c' heq
        rw [hq] at heq
        cases heq
        simp only [jumpdests] at ht
        split at ht
        · rename_i hpush
          have hd' : tl.drop (b - 0x5f) = bs.drop (i + 1 + (b - 0x5f)) := by
            rw [← htl, List.drop_drop]
          rw [hd'] at ht
          have hN : N i op = i + 1 + (b - 0x5f) := by rw [N, hw, if_pos hpush]
          rw [hN]
          exact jumpdests_D_J hall f _ _ t ht
        · rename_i hpush
          have hN : N i op = i + 1 := by rw [N, hw, if_neg hpush]
          rw [hN]
          split at ht
          · rename_i h5b
            have hj : op = .JUMPDEST := by
              have := (parse_jumpdest b hb256).mpr h5b
              rw [hop] at this; exact Option.some.inj this
            rw [if_pos hj]
            simp only [List.mem_cons] at ht
            rcases ht with rfl | ht
            · exact mem_D_J_aux _ _ _ _ (Array.mem_push_self ..)
            · rw [← htl] at ht
              exact jumpdests_D_J hall f _ _ t ht
          · rename_i h5b
            have hj : op ≠ .JUMPDEST := fun e =>
              h5b ((parse_jumpdest b hb256).mp (e ▸ hop))
            rw [if_neg hj]
            rw [← htl] at ht
            exact jumpdests_D_J hall f _ _ t ht

/-- A jump destination the checker accepts passes EVMLean's jump check. -/
theorem mem_D_J {bs : List Nat} (hall : bs.all (· < 256) = true) {t : Nat}
    (ht : t ∈ jumpdests codeFuel 0 bs) :
    (D_J (codeBA bs) 0).contains (UInt256.ofNat t) = true := by
  rw [Array.contains_iff_mem]
  exact jumpdests_D_J hall codeFuel 0 #[] t (by simpa using ht)

end Poseidon2.Evm
