import Ethereum.Theory.OpcodeLemmas
import Poseidon2.Checker.Forms
import Poseidon2.Evm.Eip8024

/-!
# EVM steps the opcode simulations need

EVMLean's `Ethereum/Theory/OpcodeLemmas.lean` states `Xstep` for each opcode, with one lemma per
`DUPn` / `SWAPn`. This file adds what the simulations in `Sim.lean` need on top of it:

* `xstep_dup`, `xstep_swap`: `Xstep` of every `DUPn` / `SWAPn` at once (`n` from the operation);
* `xstep_overlay`: `Eip8024.Xstep` is EVMLean's `Xstep` on every instruction EVMLean decodes as
  something other than `INVALID` (so `0xe6` / `0xe7` are the only bytes the overlay changes);
* `xstep_dupn`, `xstep_swapn`: `Eip8024.Xstep` of DUPN / SWAPN;
* the EVMLean word operations as natural numbers, against the checker's `binOp` / `unOp`
  (`binOp_sub`, ...): the checker's word terms evaluate with `binOp`, the EVM computes on
  `UInt256`.
-/

namespace Poseidon2.Evm

open Ethereum Ethereum.EVM Poseidon2.Checker

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ## Words -/

theorem size_eq : UInt256.size = W := rfl

theorem toNat_lt (a : UInt256) : a.toNat < W := a.val.isLt

theorem toNat_inj {a b : UInt256} : a.toNat = b.toNat ↔ a = b := by
  constructor
  · intro h; cases a; cases b; simp only [UInt256.toNat] at h; congr; exact Fin.ext h
  · intro h; rw [h]

theorem toNat_ofNat (n : Nat) : (UInt256.ofNat n).toNat = n % W := rfl

theorem toNat_fromBool (b : Bool) : (UInt256.fromBool b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem one_eq : (⟨1⟩ : UInt256) = UInt256.ofNat 1 := rfl

theorem pc_add_add (p : UInt256) (m n : Nat) :
    p + UInt256.ofNat m + UInt256.ofNat n = p + UInt256.ofNat (m + n) := by
  apply toNat_inj.mp
  show ((p.toNat + m % W) % W + n % W) % W = (p.toNat + (m + n) % W) % W
  simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem binOp_add (a b : UInt256) : binOp 0x01 a.toNat b.toNat = some (UInt256.add a b).toNat :=
  rfl

theorem binOp_mul (a b : UInt256) : binOp 0x02 a.toNat b.toNat = some (UInt256.mul a b).toNat :=
  rfl

theorem binOp_sub (a b : UInt256) : binOp 0x03 a.toNat b.toNat = some (UInt256.sub a b).toNat := by
  show some _ = some (a.val - b.val).val
  rw [Fin.val_sub]
  have := toNat_lt b
  simp only [UInt256.toNat, size_eq] at this ⊢
  congr 2; omega

theorem binOp_div (a b : UInt256) : binOp 0x04 a.toNat b.toNat = some (UInt256.div a b).toNat := by
  show some _ = some (a.val / b.val).val
  rw [Fin.div_val]
  simp only [UInt256.toNat]
  split <;> simp_all

theorem binOp_mod (a b : UInt256) : binOp 0x06 a.toNat b.toNat = some (UInt256.mod a b).toNat := by
  simp only [binOp, UInt256.mod]
  by_cases h : b.toNat = 0
  · have : b.val = 0 := Fin.ext h
    simp [h, this]
  · have : ¬ (b.val == 0) = true := by
      intro h'; apply h; simp [UInt256.toNat, beq_iff_eq.mp h']
    simp only [h, this, if_false, Bool.false_eq_true]
    rfl

theorem binOp_lt (a b : UInt256) : binOp 0x10 a.toNat b.toNat = some (UInt256.lt a b).toNat := by
  simp only [binOp, UInt256.lt, toNat_fromBool]
  congr 1
  by_cases h : a.toNat < b.toNat
  · have : a < b := h
    simp [h, this]
  · have : ¬ a < b := h
    simp [h, this]

theorem binOp_gt (a b : UInt256) : binOp 0x11 a.toNat b.toNat = some (UInt256.gt a b).toNat := by
  simp only [binOp, UInt256.gt, toNat_fromBool]
  congr 1
  by_cases h : a.toNat > b.toNat
  · have : a > b := h
    simp [h, this]
  · have : ¬ a > b := h
    simp [h, this]

theorem binOp_slt (a b : UInt256) : binOp 0x12 a.toNat b.toNat = some (UInt256.slt a b).toNat := by
  simp only [binOp, UInt256.slt, UInt256.sltBool, toNat_fromBool, neg, ge_iff_le]
  congr 1
  have h1 : (a < b) ↔ a.toNat < b.toNat := Iff.rfl
  by_cases ha : 2 ^ 255 ≤ a.toNat <;> by_cases hb : 2 ^ 255 ≤ b.toNat <;>
    by_cases hab : a.toNat < b.toNat <;>
    simp only [ha, hb, hab, h1, if_true, if_false, decide_true, decide_false, Bool.not_true,
      Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false, Bool.true_or,
      beq_self_eq_true, Bool.false_eq_true] <;> rfl

theorem binOp_sgt (a b : UInt256) : binOp 0x13 a.toNat b.toNat = some (UInt256.sgt a b).toNat := by
  simp only [binOp, UInt256.sgt, UInt256.sgtBool, toNat_fromBool, neg, ge_iff_le]
  congr 1
  have h1 : (a > b) ↔ a.toNat > b.toNat := Iff.rfl
  by_cases ha : 2 ^ 255 ≤ a.toNat <;> by_cases hb : 2 ^ 255 ≤ b.toNat <;>
    by_cases hab : a.toNat > b.toNat <;>
    simp only [ha, hb, hab, h1, if_true, if_false, decide_true, decide_false, Bool.not_true,
      Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false, Bool.true_or,
      beq_self_eq_true, Bool.false_eq_true] <;> rfl

theorem binOp_eq (a b : UInt256) : binOp 0x14 a.toNat b.toNat = some (UInt256.eq a b).toNat := by
  simp only [binOp, UInt256.eq, toNat_fromBool]
  congr 1
  by_cases h : a = b
  · simp [h]
  · have : a.toNat ≠ b.toNat := fun h' => h (toNat_inj.mp h')
    simp [h, this]

theorem binOp_and (a b : UInt256) : binOp 0x16 a.toNat b.toNat = some (UInt256.land a b).toNat := by
  show some _ = some ((a.toNat &&& b.toNat) % W)
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left (toNat_lt a))]

theorem binOp_or (a b : UInt256) : binOp 0x17 a.toNat b.toNat = some (UInt256.lor a b).toNat := by
  show some _ = some ((a.toNat ||| b.toNat) % W)
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow (toNat_lt a) (toNat_lt b))]

theorem binOp_xor (a b : UInt256) : binOp 0x18 a.toNat b.toNat = some (UInt256.xor a b).toNat := by
  show some _ = some ((a.toNat ^^^ b.toNat) % W)
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (toNat_lt a) (toNat_lt b))]

/-- `SHL` (EVMLean applies `shiftLeft` to the value and the shift, in that order). -/
theorem binOp_shl (a b : UInt256) :
    binOp 0x1b a.toNat b.toNat = some (UInt256.shiftLeft b a).toNat := by
  simp only [binOp, UInt256.shiftLeft, GE.ge, Fin.le_def]
  congr 1
  by_cases h : a.toNat < 256
  · have : ¬ (256 : Fin UInt256.size).val ≤ a.val.val := by
      show ¬ 256 ≤ a.toNat; omega
    rw [if_neg this, if_pos h]
    rfl
  · have : (256 : Fin UInt256.size).val ≤ a.val.val := by
      show 256 ≤ a.toNat; omega
    rw [if_pos this, if_neg h]
    rfl

theorem binOp_shr (a b : UInt256) :
    binOp 0x1c a.toNat b.toNat = some (UInt256.shiftRight b a).toNat := by
  simp only [binOp, UInt256.shiftRight, GE.ge, Fin.le_def]
  congr 1
  by_cases h : a.toNat < 256
  · have : ¬ (256 : Fin UInt256.size).val ≤ a.val.val := by
      show ¬ 256 ≤ a.toNat; omega
    rw [if_neg this, if_pos h]
    show _ = (b.val >>> a.val).val
    rw [Fin.shiftRight_val]; rfl
  · have : (256 : Fin UInt256.size).val ≤ a.val.val := by
      show 256 ≤ a.toNat; omega
    rw [if_pos this, if_neg h]
    rfl

theorem unOp_iszero (a : UInt256) : unOp 0x15 a.toNat = some (UInt256.isZero a).toNat := by
  simp only [unOp, UInt256.isZero, UInt256.eq0, toNat_fromBool]
  congr 1
  by_cases h : a.toNat = 0
  · have : a = ⟨0⟩ := toNat_inj.mp h
    simp [h, this]
  · have : ¬ (a == ⟨0⟩) = true := by
      intro h'; apply h; have := (beq_iff_eq.mp h'); rw [this]; rfl
    simp [h, this]

theorem toNat_sub (a b : UInt256) : (a - b).toNat = (W - b.toNat + a.toNat) % W := by
  show (a.val - b.val).val = _
  rw [Fin.val_sub]; rfl

theorem unOp_not (a : UInt256) : unOp 0x19 a.toNat = some (UInt256.lnot a).toNat := by
  have ha := toNat_lt a
  have hl : (UInt256.ofNat (UInt256.size - 1)).toNat = W - 1 := by
    show (UInt256.size - 1) % UInt256.size = W - 1
    rw [size_eq]; exact Nat.mod_eq_of_lt (by decide)
  rw [UInt256.lnot, toNat_sub, hl]
  have e : W - a.toNat + (W - 1) = (W - 1 - a.toNat) + W := by omega
  show some (W - 1 - a.toNat % W) = _
  rw [Nat.mod_eq_of_lt ha, e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- `ADDMOD` as natural numbers (`0` for modulus `0`). -/
theorem toNat_addMod (a b c : UInt256) :
    (UInt256.addMod a b c).toNat = if c.toNat = 0 then 0 else (a.toNat + b.toNat) % c.toNat := by
  unfold UInt256.addMod UInt256.eq0
  by_cases h : c.toNat = 0
  · have : c = ⟨0⟩ := toNat_inj.mp h
    simp [h, this]
  · have : ¬ (c == ⟨0⟩) = true := by
      intro h'; apply h; rw [beq_iff_eq.mp h']; rfl
    simp only [this, if_false, Bool.false_eq_true, h, toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by omega)) (toNat_lt c))

/-- `MULMOD` as natural numbers. -/
theorem toNat_mulMod (a b c : UInt256) :
    (UInt256.mulMod a b c).toNat = if c.toNat = 0 then 0 else (a.toNat * b.toNat) % c.toNat := by
  unfold UInt256.mulMod UInt256.eq0
  by_cases h : c.toNat = 0
  · have : c = ⟨0⟩ := toNat_inj.mp h
    simp [h, this]
  · have : ¬ (c == ⟨0⟩) = true := by
      intro h'; apply h; rw [beq_iff_eq.mp h']; rfl
    simp only [this, if_false, Bool.false_eq_true, h, toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by omega)) (toNat_lt c))

/-! ## Stacks -/

theorem take_getLast (l : List UInt256) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ l.length) :
    (l.take n).getLast! = l[n - 1] := by
  rw [List.getLast!_eq_getElem!]
  have : n - 1 < l.length := by omega
  simp only [List.getElem!_eq_getElem?_getD]
  rw [List.length_take, Nat.min_eq_left h2, List.getElem?_take, if_pos (by omega),
    List.getElem?_eq_getElem this]
  rfl

/-- EVMLean's `swap n` as a list operation. -/
def swapList (n : Nat) (l : List UInt256) : List UInt256 :=
  (l.take (n + 1)).getLast! :: (l.take (n + 1)).tail!.dropLast ++ [(l.take (n + 1)).head!] ++
    l.drop (n + 1)

theorem swapList_eq (n : Nat) (l : List UInt256) (h1 : 1 ≤ n) (h2 : n < l.length) :
    swapList n l = (l.set 0 l[n]).set n l[0] := by
  match l, h2 with
  | a :: l', h2 =>
    simp only [List.length_cons] at h2
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hl : ((a :: l').take (m + 1 + 1)).getLast! = l'[m] := by
      rw [take_getLast _ _ (by omega) (by simp; omega)]; simp
    unfold swapList
    rw [hl]
    simp only [List.take_succ_cons, List.tail!_cons, List.head!_cons, List.drop_succ_cons,
      List.set_cons_zero, List.getElem_cons_zero, List.getElem_cons_succ, List.set_cons_succ]
    rw [List.dropLast_eq_take, List.length_take, List.take_take,
      List.set_eq_take_append_cons_drop, if_pos (by omega)]
    simp only [List.cons_append, List.append_assoc]
    congr 2
    congr 1
    omega

/-! ## `Xstep` of DUPn and SWAPn -/

/-- The `n` of `DUPn`. -/
def dupN : Operation.DOp → Nat
  | .DUP1 => 1 | .DUP2 => 2 | .DUP3 => 3 | .DUP4 => 4 | .DUP5 => 5 | .DUP6 => 6 | .DUP7 => 7
  | .DUP8 => 8 | .DUP9 => 9 | .DUP10 => 10 | .DUP11 => 11 | .DUP12 => 12 | .DUP13 => 13
  | .DUP14 => 14 | .DUP15 => 15 | .DUP16 => 16

/-- The `n` of `SWAPn`. -/
def swapN : Operation.ExOp → Nat
  | .SWAP1 => 1 | .SWAP2 => 2 | .SWAP3 => 3 | .SWAP4 => 4 | .SWAP5 => 5 | .SWAP6 => 6
  | .SWAP7 => 7 | .SWAP8 => 8 | .SWAP9 => 9 | .SWAP10 => 10 | .SWAP11 => 11 | .SWAP12 => 12
  | .SWAP13 => 13 | .SWAP14 => 14 | .SWAP15 => 15 | .SWAP16 => 16

theorem mem_dup (s : State) (d : Operation.DOp) : memoryExpansionCost s (.Dup d) = 0 := by
  cases d <;> simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem C_dup (s : State) (d : Operation.DOp) : C' s (.Dup d) = GasConstants.Gverylow := by
  cases d <;> simp [C', InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow,
    InstructionGasGroups.Wverylow.pushInstrsWithoutZero, InstructionGasGroups.Wverylow.dupInstrs,
    InstructionGasGroups.Wverylow.swapInstrs]

theorem mem_swap (s : State) (x : Operation.ExOp) : memoryExpansionCost s (.Exchange x) = 0 := by
  cases x <;> simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem C_swap (s : State) (x : Operation.ExOp) : C' s (.Exchange x) = GasConstants.Gverylow := by
  cases x <;> simp [C', InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow,
    InstructionGasGroups.Wverylow.pushInstrsWithoutZero, InstructionGasGroups.Wverylow.dupInstrs,
    InstructionGasGroups.Wverylow.swapInstrs]

/-- `Xstep` of every `DUPn`. -/
theorem xstep_dup (s : State) (d : Operation.DOp)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Dup d, .none)) :
    Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.stack.length < dupN d then .error .StackUnderflow
      else if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length + 1 > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := (s.machineState.stack.take (dupN d)).getLast! :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Gverylow
        machineState.pc := s.machineState.pc + ⟨1⟩
        machineState.execLength := s.machineState.execLength + 1}, .none) := by
  have hn : 1 ≤ dupN d := by cases d <;> simp [dupN]
  by_cases hu : s.machineState.stack.length < dupN d
  · rw [if_pos hu]
    cases d <;>
    · simp only [dupN] at hu
      have hu2 := hu
      try simp at hu2
      simp [Xstep, Z, δ, hdec, hu, hu2]
  · rw [if_neg hu]
    by_cases hgas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow
    · rw [if_pos hgas]
      cases d <;>
      · simp only [dupN] at hu
        have hu2 := hu
        try simp at hu2
        simp [Xstep, Z, δ, hdec, hu, hu2]
        simp [mem_dup, C_dup, hgas]
    · rw [if_neg hgas]
      by_cases hov : s.machineState.stack.length + 1 > 1024
      · rw [if_pos hov]
        have hov2 : 1024 < s.machineState.stack.length - dupN d + (dupN d + 1) := by omega
        cases d <;>
        · simp only [dupN] at hu hov2
          have hu2 := hu
          try simp at hu2
          simp [Xstep, Z, δ, hdec, hu, hu2]
          simp [mem_dup, C_dup, hgas, α, hov2]
      · rw [if_neg hov]
        have hov2 : ¬ 1024 < s.machineState.stack.length - dupN d + (dupN d + 1) := by omega
        cases d <;>
        · simp only [dupN] at hu hov2 ⊢
          have hu2 := hu
          try simp at hu2
          simp [Xstep, Z, δ, hdec, hu, hu2]
          simp [mem_dup, C_dup, hgas, α, hov2, Operation.isCreate, bind, Except.bind]
          unfold step
          simp [EVM.dup, Ethereum.State.replaceStackAndIncrPC, hu, hu2, Nat.le_of_not_lt hu]
          unfold Ethereum.State.incrPC
          simp [UInt256_ofNat_1, Sat256.subNat_zero]

/-- `Xstep` of every `SWAPn`. -/
theorem xstep_swap (s : State) (x : Operation.ExOp)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Exchange x, .none)) :
    Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.stack.length < swapN x + 1 then .error .StackUnderflow
      else if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else if s.machineState.stack.length > 1024 then .error .StackOverflow
      else .ok ({s with
        machineState.stack := swapList (swapN x) s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Gverylow
        machineState.pc := s.machineState.pc + ⟨1⟩
        machineState.execLength := s.machineState.execLength + 1}, .none) := by
  by_cases hu : s.machineState.stack.length < swapN x + 1
  · rw [if_pos hu]
    cases x <;>
    · simp only [swapN] at hu
      simp [Xstep, Z, δ, hdec, hu]
  · rw [if_neg hu]
    by_cases hgas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow
    · rw [if_pos hgas]
      cases x <;>
      · simp only [swapN] at hu
        simp [Xstep, Z, δ, hdec, hu]
        simp [mem_swap, C_swap, hgas]
    · rw [if_neg hgas]
      by_cases hov : s.machineState.stack.length > 1024
      · rw [if_pos hov]
        have hov2 : 1024 < s.machineState.stack.length - (swapN x + 1) + (swapN x + 1) := by
          omega
        cases x <;>
        · simp only [swapN] at hu hov2
          simp [Xstep, Z, δ, hdec, hu]
          simp [mem_swap, C_swap, hgas, α, hov2]
      · rw [if_neg hov]
        have hov2 : ¬ 1024 < s.machineState.stack.length - (swapN x + 1) + (swapN x + 1) := by
          omega
        cases x <;>
        · simp only [swapN] at hu hov2 ⊢
          simp [Xstep, Z, δ, hdec, hu]
          simp [mem_swap, C_swap, hgas, α, hov2, Operation.isCreate, bind, Except.bind]
          unfold step
          simp [EVM.swap, Ethereum.State.replaceStackAndIncrPC, hu, Nat.le_of_not_lt hu, swapList]
          unfold Ethereum.State.incrPC
          simp [UInt256_ofNat_1, Sat256.subNat_zero]

/-! ## The EIP-8024 overlay -/

theorem parseInstr_e6 : parseInstr 0xe6 = some .INVALID := rfl
theorem parseInstr_e7 : parseInstr 0xe7 = some .INVALID := rfl

/-- On an instruction EVMLean decodes as other than `INVALID`, the overlay is EVMLean. -/
theorem xstep_overlay (vj : Array UInt256) (s : State) (op : Operation)
    (arg : Option (UInt256 × Nat))
    (hdec : decode s.executionEnv.code s.machineState.pc = some (op, arg))
    (hop : op ≠ .INVALID) :
    Eip8024.Xstep vj s = Xstep vj s := by
  have hn : Eip8024.decode s.executionEnv.code s.machineState.pc.toNat = none := by
    unfold Eip8024.decode
    cases hb : s.executionEnv.code.get? s.machineState.pc.toNat with
    | none => rfl
    | some b =>
      by_cases h6 : b = 0xe6
      · subst h6
        simp [decode, hb, parseInstr_e6, bind, Option.bind] at hdec
        exact absurd hdec.1.symm hop
      · by_cases h7 : b = 0xe7
        · subst h7
          simp [decode, hb, parseInstr_e7, bind, Option.bind] at hdec
          exact absurd hdec.1.symm hop
        · split <;> simp_all
  unfold Eip8024.Xstep
  rw [hn]

/-- `Eip8024.Xstep` of DUPN. -/
theorem xstep_dupn (vj : Array UInt256) (s : State) (n : Nat)
    (hdec : Eip8024.decode s.executionEnv.code s.machineState.pc.toNat = some (some (.dupn n))) :
    Eip8024.Xstep vj s =
      if s.machineState.stack.length < n then .error .StackUnderflow
      else if s.machineState.stack.length + 1 > 1024 then .error .StackOverflow
      else if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else .ok ({s with
        machineState.stack := (s.machineState.stack.take n).getLast! :: s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 2
        machineState.execLength := s.machineState.execLength + 1}, .none) := by
  unfold Eip8024.Xstep
  rw [hdec]
  simp only [Eip8024.exec]
  split
  · rfl
  · rename_i hu
    split
    · rfl
    · split
      · rfl
      · simp only [EVM.dup, List.length_take, Nat.min_eq_left (Nat.le_of_not_lt hu), if_true,
          Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, Except.map]
        congr 3
        rw [pc_add_add]

/-- `Eip8024.Xstep` of SWAPN. -/
theorem xstep_swapn (vj : Array UInt256) (s : State) (n : Nat)
    (hdec : Eip8024.decode s.executionEnv.code s.machineState.pc.toNat = some (some (.swapn n))) :
    Eip8024.Xstep vj s =
      if s.machineState.stack.length < n + 1 then .error .StackUnderflow
      else if s.machineState.stack.length + 0 > 1024 then .error .StackOverflow
      else if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
      else .ok ({s with
        machineState.stack := swapList n s.machineState.stack
        machineState.gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Gverylow
        machineState.pc := s.machineState.pc + UInt256.ofNat 2
        machineState.execLength := s.machineState.execLength + 1}, .none) := by
  unfold Eip8024.Xstep
  rw [hdec]
  simp only [Eip8024.exec]
  split
  · rfl
  · rename_i hu
    split
    · rfl
    · split
      · rfl
      · simp only [EVM.swap, List.length_take, Nat.min_eq_left (Nat.le_of_not_lt hu), if_true,
          Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, Except.map, swapList]
        congr 3
        rw [pc_add_add]

end Poseidon2.Evm
