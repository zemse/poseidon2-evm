import Ethereum.Theory.OpcodeLemmas
import Mathlib.Tactic

/-!
# EVMLean's word operations against execution-specs (Cancun)

EVMLean is in the trusted base as a model of the EVM. This file takes its 25 word operations out
of it: for `ADD` .. `SAR` (arithmetic, comparison, bitwise), EVMLean's `UInt256` operation is
the execution-specs one on every input (`*_spec`), and composed with EVMLean's `step_*` lemmas
(`Ethereum/Theory/OpcodeLemmas.lean`), an `Xstep` of the opcode on stack `a :: b :: (c ::) t`
leaves `r :: t` with `r` the execution-specs result in pop order (`x_*`), so the operand order is
proven too (`SHL` / `SHR` swap theirs, `ADDMOD` / `MULMOD` take the modulus third).

`ES.*` transcribes ethereum/execution-specs @ `636b5f1757b1c5eeb5856030ac9a8058cadc4b70`,
`src/ethereum/forks/cancun/vm/instructions/{arithmetic,bitwise,comparison}.py`, with
`U256.to_signed` / `U256.from_signed` / `wrapping_*` / `__invert__` from ethereum/ethereum-types
v0.4.1 (`6111404`) and `get_sign` from `ethereum/utils/numeric.py`. The transcription is
trusted. Arguments are in pop order: the first argument is the top of the stack.
-/

namespace Poseidon2.Evm.WordOps

set_option linter.unnecessarySeqFocus false

namespace ES

def W : Nat := 2 ^ 256

/-- `U256.to_signed`. -/
def toS (x : Nat) : Int := if x < 2 ^ 255 then (x : Int) else (x : Int) - (W : Int)

/-- `U256.from_signed` on its domain `[-2^255, 2^255)`. -/
def fromS (i : Int) : Nat := (i % (W : Int)).toNat

/-- `ethereum.utils.numeric.get_sign`. -/
def getSign (i : Int) : Int := if i < 0 then -1 else if i = 0 then 0 else 1

def add (x y : Nat) : Nat := (x + y) &&& (W - 1)
def sub (x y : Nat) : Nat := (((x : Int) - y) % (W : Int)).toNat   -- `(x - y) & MAX` in Python
def mul (x y : Nat) : Nat := (x * y) &&& (W - 1)
def div (x y : Nat) : Nat := if y = 0 then 0 else x / y
def sdiv (x y : Nat) : Nat :=
  let a := toS x; let b := toS y
  if b = 0 then 0
  else if a = -(2 ^ 255) ∧ b = -1 then fromS (-(2 ^ 255))
  else fromS (getSign (a * b) * ((a.natAbs / b.natAbs : Nat) : Int))
def mod (x y : Nat) : Nat := if y = 0 then 0 else x % y
def smod (x y : Nat) : Nat :=
  let a := toS x; let b := toS y
  if b = 0 then 0 else fromS (getSign a * ((a.natAbs % b.natAbs : Nat) : Int))
def addmod (x y z : Nat) : Nat := if z = 0 then 0 else (x + y) % z
def mulmod (x y z : Nat) : Nat := if z = 0 then 0 else (x * y) % z
def exp (x y : Nat) : Nat := x ^ y % W
/-- `signextend(byte_num, value)`: keep the low `byte_num + 1` bytes, prepend `0xFF` bytes if
their top bit is set. -/
def signextend (b v : Nat) : Nat :=
  if b > 31 then v else
    let n := 8 * (b + 1)
    let low := v % 2 ^ n
    if low >>> (n - 1) = 0 then low else (W - 2 ^ n) + low
def lt (x y : Nat) : Nat := if x < y then 1 else 0
def gt (x y : Nat) : Nat := if x > y then 1 else 0
def slt (x y : Nat) : Nat := if toS x < toS y then 1 else 0
def sgt (x y : Nat) : Nat := if toS x > toS y then 1 else 0
def eq (x y : Nat) : Nat := if x = y then 1 else 0
def iszero (x : Nat) : Nat := if x = 0 then 1 else 0
def and (x y : Nat) : Nat := x &&& y
def or (x y : Nat) : Nat := x ||| y
def xor (x y : Nat) : Nat := x ^^^ y
/-- `~x & MAX` on Python ints, i.e. `MAX - x`. -/
def not (x : Nat) : Nat := W - 1 - x
def byte (i w : Nat) : Nat := if i ≥ 32 then 0 else (w >>> ((31 - i) * 8)) &&& 0xFF
def shl (s v : Nat) : Nat := if s < 256 then (v <<< s) &&& (W - 1) else 0
def shr (s v : Nat) : Nat := if s < 256 then v >>> s else 0
/-- Python `>>` on ints is floor division by `2^s`. -/
def sar (s v : Nat) : Nat :=
  if s < 256 then fromS (Int.fdiv (toS v) (2 ^ s))
  else if toS v ≥ 0 then 0 else W - 1

end ES

open Ethereum
open private powAux from Ethereum.UInt256



local notation "W" => ES.W

theorem size_eq : UInt256.size = W := rfl
theorem lt_W (a : UInt256) : a.toNat < W := a.val.isLt
theorem toNat_mk (x : Fin UInt256.size) : (UInt256.mk x).toNat = x.val := rfl

/-- The `-1` EVMLean writes in `abs` / `sdiv` (its own `OfNat (Fin UInt256.size)` instance). -/
abbrev evmNegOne : Fin UInt256.size :=
  @Neg.neg (Fin UInt256.size) (Fin.neg UInt256.size)
    (@OfNat.ofNat (Fin UInt256.size) 1 (@UInt256.instOfNatFinSize 1))

theorem negOne_val : evmNegOne.val = UInt256.size - 1 := rfl

/-- Rewrite `toNat` instead of unfolding it: the kernel hits deep recursion otherwise. -/
theorem toNat_def (u : UInt256) : u.toNat = u.val.val := rfl

theorem fin_mul_neg_one (x : Fin UInt256.size) : (x * evmNegOne).val = (W - x.val) % W := by
  rw [← size_eq]
  rw [Fin.val_mul, negOne_val]
  have hx := x.isLt
  have hn : 1 ≤ UInt256.size := by decide
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  push_cast [Nat.cast_sub hn, Nat.cast_sub hx.le, ZMod.natCast_self]
  ring

/-! ## ADD MUL SUB DIV MOD ADDMOD MULMOD -/

theorem add_spec (a b : UInt256) : (a + b).toNat = ES.add a.toNat b.toNat := by
  show (a.val + b.val).val = _
  rw [Fin.val_add, ES.add, ES.W, Nat.and_two_pow_sub_one_eq_mod]; rfl

theorem mul_spec (a b : UInt256) : (UInt256.mul a b).toNat = ES.mul a.toNat b.toNat := by
  show (a.val * b.val).val = _
  rw [Fin.val_mul, ES.mul, ES.W, Nat.and_two_pow_sub_one_eq_mod]; rfl

theorem sub_spec (a b : UInt256) : (UInt256.sub a b).toNat = ES.sub a.toNat b.toNat := by
  show (a.val - b.val).val = _
  rw [Fin.sub_def]
  have ha := lt_W a; have hb := lt_W b
  simp only [ES.sub]
  show (UInt256.size - b.toNat + a.toNat) % UInt256.size = _
  rw [size_eq]
  unfold ES.W at *
  omega

theorem div_spec (a b : UInt256) : (UInt256.div a b).toNat = ES.div a.toNat b.toNat := by
  show (a.val / b.val).val = _
  show a.toNat / b.toNat = _
  rw [ES.div]
  split_ifs with h
  · show a.toNat / b.toNat = 0; rw [h, Nat.div_zero]
  · rfl

theorem mod_spec (a b : UInt256) : (UInt256.mod a b).toNat = ES.mod a.toNat b.toNat := by
  unfold UInt256.mod ES.mod
  by_cases h : b.toNat = 0
  · have : (b.val == 0) = true := by
      rw [beq_iff_eq]; exact Fin.ext (by rw [Fin.val_zero]; exact h)
    rw [if_pos this, if_pos h]; rfl
  · have : ¬ (b.val == 0) = true := by
      rw [beq_iff_eq]; intro h'; apply h; show b.val.val = 0; rw [h']; rfl
    rw [if_neg this, if_neg h]
    show (a.val % b.val).val = _
    rw [Fin.val_mod]; rfl

theorem eq0_iff (c : UInt256) : c.eq0 = true ↔ c.toNat = 0 := by
  unfold UInt256.eq0
  constructor
  · intro h; rw [beq_iff_eq.mp h]; rfl
  · intro h; rw [beq_iff_eq]; cases c; congr; exact Fin.ext h

theorem addmod_spec (a b c : UInt256) :
    (UInt256.addMod a b c).toNat = ES.addmod a.toNat b.toNat c.toNat := by
  unfold UInt256.addMod ES.addmod
  by_cases h : c.toNat = 0
  · rw [if_pos ((eq0_iff c).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((eq0_iff c).mp h')), if_neg h]
    show (a.toNat + b.toNat) % c.toNat % UInt256.size = _
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by omega)) (lt_W c))

theorem mulmod_spec (a b c : UInt256) :
    (UInt256.mulMod a b c).toNat = ES.mulmod a.toNat b.toNat c.toNat := by
  unfold UInt256.mulMod ES.mulmod
  by_cases h : c.toNat = 0
  · rw [if_pos ((eq0_iff c).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((eq0_iff c).mp h')), if_neg h]
    show (a.toNat * b.toNat) % c.toNat % UInt256.size = _
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by omega)) (lt_W c))

/-! ## LT GT SLT SGT EQ ISZERO -/

theorem fromBool_toNat (b : Bool) : (UInt256.fromBool b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem lt_spec (a b : UInt256) : (UInt256.lt a b).toNat = ES.lt a.toNat b.toNat := by
  unfold UInt256.lt ES.lt; rw [fromBool_toNat]
  by_cases h : a.toNat < b.toNat
  · rw [if_pos h, if_pos]; exact decide_eq_true (show a.val < b.val from h)
  · rw [if_neg h, if_neg]; intro h'; exact h (of_decide_eq_true h')

theorem gt_spec (a b : UInt256) : (UInt256.gt a b).toNat = ES.gt a.toNat b.toNat := by
  unfold UInt256.gt ES.gt; rw [fromBool_toNat]
  by_cases h : a.toNat > b.toNat
  · rw [if_pos h, if_pos]; exact decide_eq_true (show b.val < a.val from h)
  · rw [if_neg h, if_neg]; intro h'; exact h (of_decide_eq_true h')

theorem toNat_inj {a b : UInt256} : a.toNat = b.toNat ↔ a = b := by
  constructor
  · intro h; cases a; cases b; congr; exact Fin.ext h
  · intro h; rw [h]

theorem eq_spec (a b : UInt256) : (UInt256.eq a b).toNat = ES.eq a.toNat b.toNat := by
  unfold UInt256.eq ES.eq; rw [fromBool_toNat]
  by_cases h : a.toNat = b.toNat
  · rw [if_pos h, if_pos]; exact decide_eq_true (toNat_inj.mp h)
  · rw [if_neg h, if_neg]; intro h'; exact h (toNat_inj.mpr (of_decide_eq_true h'))

theorem iszero_spec (a : UInt256) : (UInt256.isZero a).toNat = ES.iszero a.toNat := by
  unfold UInt256.isZero ES.iszero; rw [fromBool_toNat]
  by_cases h : a.toNat = 0
  · rw [if_pos h, if_pos ((eq0_iff a).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((eq0_iff a).mp h'))]

theorem toS_lt_iff (x y : Nat) (hx : x < W) (hy : y < W) :
    ES.toS x < ES.toS y ↔
      (2 ^ 255 ≤ x ∧ y < 2 ^ 255) ∨ ((2 ^ 255 ≤ x ↔ 2 ^ 255 ≤ y) ∧ x < y) := by
  unfold ES.toS; unfold ES.W at *
  split_ifs <;> omega

theorem sltBool_iff (a b : UInt256) : UInt256.sltBool a b = true ↔ ES.toS a.toNat < ES.toS b.toNat := by
  rw [toS_lt_iff _ _ (lt_W a) (lt_W b)]
  unfold UInt256.sltBool
  have : (a < b) ↔ a.toNat < b.toNat := Iff.rfl
  split_ifs <;> simp_all <;> omega

theorem sgtBool_iff (a b : UInt256) : UInt256.sgtBool a b = true ↔ ES.toS a.toNat > ES.toS b.toNat := by
  rw [gt_iff_lt, toS_lt_iff _ _ (lt_W b) (lt_W a)]
  unfold UInt256.sgtBool
  have : (a > b) ↔ b.toNat < a.toNat := Iff.rfl
  split_ifs <;> simp_all <;> omega

theorem slt_spec (a b : UInt256) : (UInt256.slt a b).toNat = ES.slt a.toNat b.toNat := by
  unfold UInt256.slt ES.slt; rw [fromBool_toNat]
  by_cases h : ES.toS a.toNat < ES.toS b.toNat
  · rw [if_pos h, if_pos ((sltBool_iff a b).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((sltBool_iff a b).mp h'))]

theorem sgt_spec (a b : UInt256) : (UInt256.sgt a b).toNat = ES.sgt a.toNat b.toNat := by
  unfold UInt256.sgt ES.sgt; rw [fromBool_toNat]
  by_cases h : ES.toS a.toNat > ES.toS b.toNat
  · rw [if_pos h, if_pos ((sgtBool_iff a b).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((sgtBool_iff a b).mp h'))]

/-! ## AND OR XOR NOT BYTE SHL SHR -/

theorem and_spec (a b : UInt256) : (UInt256.land a b).toNat = ES.and a.toNat b.toNat := by
  show Nat.land a.toNat b.toNat % UInt256.size = _
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (lt_W b))

theorem or_spec (a b : UInt256) : (UInt256.lor a b).toNat = ES.or a.toNat b.toNat := by
  show Nat.lor a.toNat b.toNat % UInt256.size = _
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (lt_W a) (lt_W b))

theorem xor_spec (a b : UInt256) : (UInt256.xor a b).toNat = ES.xor a.toNat b.toNat := by
  show Nat.xor a.toNat b.toNat % UInt256.size = _
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (lt_W a) (lt_W b))

theorem toNat_sub (a b : UInt256) : (a - b).toNat = (W - b.toNat + a.toNat) % W := by
  show (a.val - b.val).val = _
  rw [Fin.sub_def]; rfl

theorem not_spec (a : UInt256) : (UInt256.lnot a).toNat = ES.not a.toNat := by
  have ha := lt_W a
  have hl : (UInt256.ofNat (UInt256.size - 1)).toNat = W - 1 := Nat.mod_eq_of_lt (by decide)
  rw [UInt256.lnot, toNat_sub, hl]
  unfold ES.not; unfold ES.W at *; omega


theorem shiftRight_toNat (v s : UInt256) :
    (UInt256.shiftRight v s).toNat = if s.toNat < 256 then v.toNat >>> s.toNat else 0 := by
  unfold UInt256.shiftRight
  by_cases h : s.toNat < 256
  · rw [if_neg (show ¬ (256 : Fin UInt256.size) ≤ s.val from fun h' => by
        have : 256 ≤ s.toNat := h'; omega), if_pos h]
    show (v.val >>> s.val).val = _
    rw [Fin.shiftRight_val]; rfl
  · rw [if_pos (show (256 : Fin UInt256.size) ≤ s.val from by
        show 256 ≤ s.toNat; omega), if_neg h]; rfl

theorem shiftLeft_toNat (v s : UInt256) :
    (UInt256.shiftLeft v s).toNat = if s.toNat < 256 then (v.toNat <<< s.toNat) % W else 0 := by
  unfold UInt256.shiftLeft
  by_cases h : s.toNat < 256
  · rw [if_neg (show ¬ (256 : Fin UInt256.size) ≤ s.val from fun h' => by
        have : 256 ≤ s.toNat := h'; omega), if_pos h]
    show (v.val <<< s.val).val = _
    rw [Fin.shiftLeft_val]; rfl
  · rw [if_pos (show (256 : Fin UInt256.size) ≤ s.val from by
        show 256 ≤ s.toNat; omega), if_neg h]; rfl

/-- `SHL`: stack `shift :: value :: t` gives `shiftLeft value shift` (`step_shl`). -/
theorem shl_spec (s v : UInt256) : (UInt256.shiftLeft v s).toNat = ES.shl s.toNat v.toNat := by
  rw [shiftLeft_toNat, ES.shl, ES.W, Nat.and_two_pow_sub_one_eq_mod]

/-- `SHR`: stack `shift :: value :: t` gives `shiftRight value shift` (`step_shr`). -/
theorem shr_spec (s v : UInt256) : (UInt256.shiftRight v s).toNat = ES.shr s.toNat v.toNat := by
  rw [shiftRight_toNat]; rfl

theorem byte_spec (i w : UInt256) : (UInt256.byteAt i w).toNat = ES.byte i.toNat w.toNat := by
  unfold UInt256.byteAt ES.byte
  by_cases h : i.toNat ≥ 32
  · rw [if_pos (show (⟨31⟩ : UInt256) < i from show 31 < i.toNat by omega), if_pos h]; rfl
  · rw [if_neg (show ¬ (⟨31⟩ : UInt256) < i from fun h' => by
        have : 31 < i.toNat := h'; omega), if_neg h]
    show Nat.land (UInt256.shiftRight w _).toNat 255 % UInt256.size = _
    have hs : (UInt256.ofNat ((31 - i.toNat) * 8)).toNat = (31 - i.toNat) * 8 :=
      Nat.mod_eq_of_lt (by unfold UInt256.size; omega)
    have e := shiftRight_toNat w (UInt256.ofNat ((31 - i.toNat) * 8))
    rw [hs, if_pos (by omega)] at e
    rw [e]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right (by unfold UInt256.size; omega))


/-! ## EXP -/

theorem mul_toNat (a b : UInt256) : (a * b).toNat = a.toNat * b.toNat % W := by
  show (a.val * b.val).val = _
  rw [Fin.val_mul]; rfl

theorem modW_of_zmod (x y : Nat) (h : (x : ZMod W) = (y : ZMod W)) : x % W = y % W :=
  (ZMod.natCast_eq_natCast_iff' x y W).mp h

theorem powAux_toNat (n : Nat) : ∀ (a c : UInt256),
    (powAux a c n).toNat = a.toNat * c.toNat ^ n % W := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a c
    rcases n with _ | k
    · rw [powAux]; simp only [pow_zero, mul_one]; exact (Nat.mod_eq_of_lt (lt_W a)).symm
    · rw [powAux]
      have hk : (k + 1) / 2 < k + 1 := Nat.div_lt_self (by omega) (by omega)
      have hsplit : k + 1 = 2 * ((k + 1) / 2) + (k + 1) % 2 := (Nat.div_add_mod _ _).symm
      split_ifs with hodd
      · rw [ih _ hk, mul_toNat, mul_toNat]
        have h1 : (k + 1) % 2 = 1 := by simpa using hodd
        conv => rhs; rw [hsplit, h1, pow_succ, pow_mul]
        apply modW_of_zmod; simp only [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_mod]; ring
      · rw [ih _ hk, mul_toNat]
        have h1 : (k + 1) % 2 = 0 := by simpa using hodd
        conv => rhs; rw [hsplit, h1, Nat.add_zero, pow_mul]
        apply modW_of_zmod; simp only [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_mod]; ring

/-- `EXP`: `0 ^ 0 = 1`, and `x ^ y mod 2^256` for all inputs. -/
theorem exp_spec (a b : UInt256) : (UInt256.exp a b).toNat = ES.exp a.toNat b.toNat := by
  show (powAux ⟨1⟩ a b.val.val).toNat = _
  rw [powAux_toNat]; show 1 % W * _ % W = _; rw [ES.exp]; apply modW_of_zmod; simp only [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_mod, Nat.cast_one, one_mul]; rfl

/-! ## Signed helpers -/

theorem W_pos : (0 : Int) < (W : Int) := by unfold ES.W; positivity

theorem fromS_nat (q : Nat) (h : q < W) : ES.fromS (q : Int) = q := by
  unfold ES.fromS
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h)]; simp

theorem fromS_neg (q : Nat) (h : q ≤ W) : ES.fromS (-(q : Int)) = (W - q) % W := by
  unfold ES.fromS
  by_cases hq : q = 0
  · subst hq; simp
  · have e : -(q : Int) = ((W - q : Nat) : Int) + (W : Int) * (-1) := by
      push_cast [Nat.cast_sub h]; ring
    have hl : W - q < W := by omega
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hl),
      Nat.mod_eq_of_lt hl]
    simp

theorem natAbs_toS (x : Nat) (hx : x < W) :
    (ES.toS x).natAbs = if 2 ^ 255 ≤ x then W - x else x := by
  unfold ES.toS
  split_ifs with h1 h2 h2
  · omega
  · simp
  · have e : (x : Int) - W = -((W - x : Nat) : Int) := by push_cast [Nat.cast_sub hx.le]; ring
    rw [e, Int.natAbs_neg, Int.natAbs_natCast]
  · omega

theorem toS_neg (x : Nat) (h : 2 ^ 255 ≤ x) : ES.toS x = (x : Int) - W := by
  unfold ES.toS; rw [if_neg (by omega)]

theorem toS_pos (x : Nat) (h : ¬ 2 ^ 255 ≤ x) : ES.toS x = x := by
  unfold ES.toS; rw [if_pos (Nat.lt_of_not_le h)]

theorem abs_toNat (a : UInt256) :
    (UInt256.abs a).toNat = if 2 ^ 255 ≤ a.toNat then W - a.toNat else a.toNat := by
  have ha := lt_W a
  unfold UInt256.abs
  split_ifs with h
  · rw [toNat_def, toNat_def, fin_mul_neg_one]; rw [← toNat_def]
    exact Nat.mod_eq_of_lt (Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le _) ha)
      (lt_of_lt_of_le (by positivity) h))
  · rfl

theorem negmk_toNat (x : UInt256) : (UInt256.mk (x.val * evmNegOne)).toNat = (W - x.toNat) % W := by
  rw [toNat_def, toNat_def]; exact fin_mul_neg_one x.val

theorem udiv_toNat (a b : UInt256) : (a / b).toNat = a.toNat / b.toNat := rfl

theorem h255 : (2 : Nat) ^ 255 < W := by unfold ES.W; norm_num
theorem h255' : W = 2 * 2 ^ 255 := by unfold ES.W; norm_num

/-! ## SDIV -/

theorem sdiv_spec (a b : UInt256) : (UInt256.sdiv a b).toNat = ES.sdiv a.toNat b.toNat := by
  have ha := lt_W a; have hb := lt_W b
  have h1 := h255; have h2 := h255'
  have WI : ((W : Nat) : Int) = 2 * 2 ^ 255 := by rw [h2]; push_cast
  unfold UInt256.sdiv ES.sdiv
  simp only
  rw [natAbs_toS _ ha, natAbs_toS _ hb]
  by_cases hxa : 2 ^ 255 ≤ a.toNat <;> by_cases hxb : 2 ^ 255 ≤ b.toNat
  · -- both negative
    simp only [hxa, hxb, if_true, udiv_toNat, abs_toNat, toS_neg _ hxa, toS_neg _ hxb]
    rw [if_neg (by omega)]
    have hq : (W - a.toNat) / (W - b.toNat) < W :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    split_ifs with hs
    · have e1 : a.toNat = 2 ^ 255 := by omega
      have e2 : b.toNat = W - 1 := by omega
      have : -(2 : Int) ^ 255 = -((2 ^ 255 : Nat) : Int) := by push_cast
      rw [e1, e2, this, fromS_neg _ h1.le]
      rw [Nat.mod_eq_of_lt (by omega : W - 2 ^ 255 < W), Nat.sub_sub_self (by omega : 1 ≤ W),
        Nat.div_one]
    · have : (0 : Int) < ((a.toNat : Int) - W) * ((b.toNat : Int) - W) :=
        Int.mul_pos_of_neg_of_neg (by omega) (by omega)
      rw [ES.getSign, if_neg (by omega), if_neg (by omega), one_mul, fromS_nat _ hq]
  · -- dividend negative, divisor non-negative
    simp only [hxa, hxb, if_true, if_false, negmk_toNat, udiv_toNat, abs_toNat, toS_neg _ hxa,
      toS_pos _ hxb]
    by_cases hb0 : b.toNat = 0
    · rw [hb0]; simp
    · rw [if_neg (by omega), if_neg (by omega)]
      have : ((a.toNat : Int) - W) * (b.toNat : Int) < 0 :=
        Int.mul_neg_of_neg_of_pos (by omega) (by omega)
      rw [ES.getSign, if_pos this, neg_one_mul,
        fromS_neg _ (le_trans (Nat.div_le_self _ _) (by omega))]
  · -- dividend non-negative, divisor negative
    simp only [hxa, hxb, if_true, if_false, negmk_toNat, udiv_toNat, abs_toNat, toS_neg _ hxb,
      toS_pos _ hxa]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases ha0 : a.toNat = 0
    · rw [ha0]; simp [ES.getSign, ES.fromS]
    · have : (a.toNat : Int) * ((b.toNat : Int) - W) < 0 :=
        Int.mul_neg_of_pos_of_neg (by omega) (by omega)
      rw [ES.getSign, if_pos this, neg_one_mul,
        fromS_neg _ (le_trans (Nat.div_le_self _ _) (by omega))]
  · -- both non-negative
    simp only [hxa, hxb, if_false, udiv_toNat, toS_pos _ hxa, toS_pos _ hxb]
    by_cases hb0 : b.toNat = 0
    · rw [hb0]; simp
    · rw [if_neg (by omega), if_neg (by omega)]
      have hq : a.toNat / b.toNat < W := lt_of_le_of_lt (Nat.div_le_self _ _) ha
      by_cases ha0 : a.toNat = 0
      · rw [ha0]; simp [ES.getSign, ES.fromS]
      · have : (0 : Int) < (a.toNat : Int) * (b.toNat : Int) :=
          Int.mul_pos (by omega) (by omega)
        rw [ES.getSign, if_neg (by omega), if_neg (by omega), one_mul, fromS_nat _ hq]

/-! ## SMOD -/

theorem toSigned_toNat (i : Int) (h1 : -(W : Int) ≤ i) (h2 : i < W) :
    (UInt256.toSigned i).toNat = ES.fromS i := by
  unfold UInt256.toSigned
  rcases i with n | n
  · have hn : n < W := Int.ofNat_lt.mp h2
    show n % UInt256.size = _
    rw [size_eq, Nat.mod_eq_of_lt hn]; exact (fromS_nat n hn).symm
  · have hn : n + 1 ≤ W := by
      have : Int.negSucc n = -((n + 1 : Nat) : Int) := rfl
      rw [this] at h1; exact_mod_cast (neg_le_neg_iff.mp h1)
    have e : Int.negSucc n = -((n + 1 : Nat) : Int) := rfl
    rw [e, fromS_neg _ hn]
    show (UInt256.size - 1 - n) % UInt256.size = _
    rw [size_eq]; congr 1; omega

theorem sgn_eq (a : UInt256) : UInt256.sgn a = ES.getSign (ES.toS a.toNat) := by
  unfold UInt256.sgn ES.getSign
  have ha := lt_W a
  by_cases h : 2 ^ 255 ≤ a.toNat
  · rw [if_pos h, toS_neg _ h, if_pos (by omega)]
  · rw [if_neg h, toS_pos _ h]
    by_cases h0 : a.toNat = 0
    · rw [if_pos ((eq0_iff a).mpr h0), h0]; simp
    · rw [if_neg (fun h' => h0 ((eq0_iff a).mp h')), if_neg (by omega), if_neg (by omega)]

theorem getSign_cases (i : Int) : ES.getSign i = -1 ∨ ES.getSign i = 0 ∨ ES.getSign i = 1 := by
  unfold ES.getSign; split_ifs <;> simp

theorem smod_spec (a b : UInt256) : (UInt256.smod a b).toNat = ES.smod a.toNat b.toNat := by
  have ha := lt_W a; have hb := lt_W b
  have h1 := h255; have h2 := h255'
  unfold UInt256.smod ES.smod
  simp only
  by_cases hb0 : b.toNat = 0
  · rw [if_pos (by simp [hb0]), hb0]; simp [ES.toS]
  · rw [if_neg (by simp [hb0])]
    have hS : ES.toS b.toNat ≠ 0 := by
      unfold ES.toS; split_ifs <;> omega
    rw [if_neg hS]
    have hab : (UInt256.abs b).toNat ≠ 0 := by
      rw [abs_toNat]; split_ifs <;> omega
    have hm := mod_spec (UInt256.abs a) (UInt256.abs b)
    have hm' : (UInt256.abs a % UInt256.abs b).toNat =
        (UInt256.abs a).toNat % (UInt256.abs b).toNat := by
      rw [show UInt256.abs a % UInt256.abs b = UInt256.mod (UInt256.abs a) (UInt256.abs b) from rfl,
        hm, ES.mod, if_neg hab]
    rw [hm', sgn_eq, abs_toNat, abs_toNat, natAbs_toS _ ha, natAbs_toS _ hb]
    have hr : (if 2 ^ 255 ≤ a.toNat then W - a.toNat else a.toNat) %
        (if 2 ^ 255 ≤ b.toNat then W - b.toNat else b.toNat) < W :=
      lt_of_lt_of_le (Nat.mod_lt _ (by split_ifs <;> omega)) (by split_ifs <;> omega)
    generalize (if 2 ^ 255 ≤ a.toNat then W - a.toNat else a.toNat) %
        (if 2 ^ 255 ≤ b.toNat then W - b.toNat else b.toNat) = r at hr ⊢
    apply toSigned_toNat
    · rcases getSign_cases (ES.toS a.toNat) with h | h | h <;> rw [h] <;> omega
    · rcases getSign_cases (ES.toS a.toNat) with h | h | h <;> rw [h] <;> omega

/-! ## SAR -/

theorem complement_toNat (x : UInt256) : (UInt256.complement x).toNat = W - 1 - x.toNat := by
  have hx := lt_W x
  unfold UInt256.complement
  rw [toNat_def, Fin.sub_def, Fin.val_add]
  show (UInt256.size - (x.toNat + 1 % UInt256.size) % UInt256.size + 0 % UInt256.size) %
    UInt256.size = _
  rw [size_eq]
  unfold ES.W at *
  omega

theorem fdiv_negSucc (m d : Nat) (hd : 0 < d) :
    Int.fdiv (-((m + 1 : Nat) : Int)) (d : Int) = -(((m / d + 1 : Nat)) : Int) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rfl

theorem sar_spec (s v : UInt256) : (UInt256.sar s v).toNat = ES.sar s.toNat v.toNat := by
  have hv := lt_W v
  have h1 := h255; have h2 := h255'
  unfold UInt256.sar ES.sar
  by_cases hneg : 2 ^ 255 ≤ v.toNat
  · have hslt : UInt256.sltBool v ⟨0⟩ = true := by
      rw [sltBool_iff, UInt256.zero_toNat, toS_neg _ hneg, toS_pos 0 (by norm_num)]; omega
    rw [if_pos hslt, complement_toNat]
    have e : (UInt256.complement v >>> s) = UInt256.shiftRight (UInt256.complement v) s := rfl
    rw [e, shiftRight_toNat, complement_toNat]
    by_cases hs : s.toNat < 256
    · rw [if_pos hs, if_pos hs, toS_neg _ hneg]
      have em : (v.toNat : Int) - W = -((W - 1 - v.toNat + 1 : Nat) : Int) := by
        omega
      have hp : (2 : Int) ^ s.toNat = ((2 ^ s.toNat : Nat) : Int) := by push_cast; rfl
      rw [em, hp, fdiv_negSucc _ _ (by positivity), Nat.shiftRight_eq_div_pow]
      have hq : (W - 1 - v.toNat) / 2 ^ s.toNat ≤ W - 1 - v.toNat := Nat.div_le_self _ _
      generalize (W - 1 - v.toNat) / 2 ^ s.toNat = q at hq ⊢
      rw [fromS_neg _ (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [if_neg hs, if_neg hs, toS_neg _ hneg, if_neg (by omega), Nat.sub_zero]
  · have hslt : ¬ UInt256.sltBool v ⟨0⟩ = true := by
      rw [sltBool_iff, UInt256.zero_toNat, toS_pos _ hneg, toS_pos 0 (by norm_num)]; omega
    rw [if_neg hslt]
    have e : (v >>> s) = UInt256.shiftRight v s := rfl
    rw [e, shiftRight_toNat]
    by_cases hs : s.toNat < 256
    · rw [if_pos hs, if_pos hs, toS_pos _ hneg]
      have hp : (2 : Int) ^ s.toNat = ((2 ^ s.toNat : Nat) : Int) := by push_cast; rfl
      rw [hp, Nat.shiftRight_eq_div_pow]
      have : Int.fdiv (v.toNat : Int) ((2 ^ s.toNat : Nat) : Int) =
          ((v.toNat / 2 ^ s.toNat : Nat) : Int) := by
        rw [Int.fdiv_eq_ediv, if_pos (Or.inl (by positivity)), sub_zero, Int.natCast_div]
      rw [this, fromS_nat _ (lt_of_le_of_lt (Nat.div_le_self _ _) hv)]
    · rw [if_neg hs, if_neg hs, toS_pos _ hneg, if_pos (by omega)]

/-! ## SIGNEXTEND -/

theorem and_two_pow_eq (b t : Nat) : b &&& 2 ^ t = if b.testBit t then 2 ^ t else 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  split_ifs with h
  · rw [Nat.testBit_two_pow]; by_cases hi : t = i <;> simp_all
  · simp only [Nat.zero_testBit]; by_cases hi : t = i <;> simp_all

theorem high_mask (m t : Nat) (ht : t ≤ m) : 2 ^ m - 2 ^ t = (2 ^ (m - t) - 1) <<< t := by
  rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel ht]

theorem testBit_high_mask (m t i : Nat) (ht : t ≤ m) :
    (2 ^ m - 2 ^ t).testBit i = (decide (t ≤ i) && decide (i < m)) := by
  rw [high_mask m t ht, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : t ≤ i
  · simp [h]; omega
  · simp [h]

theorem signext_nat (b t : Nat) (hb : b < 2 ^ 256) (ht : t < 256) :
    (if b &&& 2 ^ t ≠ 0 then b ||| (2 ^ 256 - 2 ^ t) else b &&& (2 ^ t - 1)) =
      (if (b % 2 ^ (t + 1)) >>> t = 0 then b % 2 ^ (t + 1)
       else (2 ^ 256 - 2 ^ (t + 1)) + b % 2 ^ (t + 1)) := by
  have hlow : (b % 2 ^ (t + 1)) >>> t = 0 ↔ b.testBit t = false := by
    have hl : b % 2 ^ (t + 1) < 2 ^ (t + 1) := Nat.mod_lt _ (by positivity)
    have h2 : (b % 2 ^ (t + 1)) >>> t < 2 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
      rw [pow_succ] at hl; omega
    have e := Nat.testBit_mod_two_pow b (t + 1) t
    simp only [show t < t + 1 by omega, decide_true, Bool.true_and] at e
    rw [← e, Nat.testBit, Nat.one_and_eq_mod_two]
    constructor
    · intro h; simp [h]
    · intro h; simp at h
      generalize (b % 2 ^ (t + 1)) >>> t = y at h2 h ⊢; omega
  have hhigh : ∀ i, 256 ≤ i → b.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))
  rw [and_two_pow_eq]
  cases hbt : b.testBit t
  · rw [if_neg (by simp), if_pos (hlow.mpr hbt), Nat.and_two_pow_sub_one_eq_mod]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i = t
    · subst hi; simp [hbt]
    · by_cases h' : i < t
      · simp [h', show i < t + 1 by omega]
      · simp [h', show ¬ i < t + 1 by omega]
  · rw [if_pos (by simp), if_neg (fun h => by rw [hlow.mp h] at hbt; cases hbt)]
    have hm : 2 ^ 256 - 2 ^ (t + 1) = (2 ^ (256 - (t + 1)) - 1) <<< (t + 1) :=
      high_mask 256 (t + 1) (by omega)
    rw [hm, Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by positivity)), ← hm]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or, Nat.testBit_or, testBit_high_mask _ _ _ (by omega),
      testBit_high_mask _ _ _ (by omega), Nat.testBit_mod_two_pow]
    by_cases h1 : i < t
    · simp [show ¬ t ≤ i by omega, show ¬ t + 1 ≤ i by omega, show i < t + 1 by omega]
    · by_cases h2 : i = t
      · subst h2; simp [hbt]
      · by_cases h3 : i < 256
        · simp [show t ≤ i by omega, show t + 1 ≤ i by omega, h3, show ¬ i < t + 1 by omega]
        · simp [h3, show ¬ i < t + 1 by omega, hhigh i (by omega)]

theorem lit_toNat (n : Nat) :
    (UInt256.mk (@OfNat.ofNat (Fin UInt256.size) n (@UInt256.instOfNatFinSize n))).toNat =
      n % UInt256.size := rfl

theorem signextend_spec (a b : UInt256) :
    (UInt256.signextend a b).toNat = ES.signextend a.toNat b.toNat := by
  have hb := lt_W b
  unfold UInt256.signextend ES.signextend
  by_cases ha : a.toNat ≤ 31
  · rw [if_pos ha, if_neg (show ¬ a.toNat > 31 by omega)]
    simp only
    have htb : (a * ⟨8⟩ + ⟨7⟩ : UInt256).toNat = 8 * a.toNat + 7 := by
      rw [add_spec, ES.add, ES.W, Nat.and_two_pow_sub_one_eq_mod]
      rw [show (a * ⟨8⟩ : UInt256) = UInt256.mul a ⟨8⟩ from rfl, mul_spec, ES.mul, ES.W,
        Nat.and_two_pow_sub_one_eq_mod, lit_toNat, lit_toNat]
      have e8 : (8 : Nat) % UInt256.size = 8 := rfl
      have e7 : (7 : Nat) % UInt256.size = 7 := rfl
      rw [e8, e7, Nat.mod_eq_of_lt (show a.toNat * 8 < 2 ^ 256 by omega),
        Nat.mod_eq_of_lt (show a.toNat * 8 + 7 < 2 ^ 256 by omega)]
      ring
    have hsb : ((⟨1⟩ : UInt256) <<< (a * ⟨8⟩ + ⟨7⟩)).toNat = 2 ^ (8 * a.toNat + 7) := by
      rw [show ((⟨1⟩ : UInt256) <<< (a * ⟨8⟩ + ⟨7⟩)) =
        UInt256.shiftLeft ⟨1⟩ (a * ⟨8⟩ + ⟨7⟩) from rfl, shiftLeft_toNat, htb,
        if_pos (by omega), lit_toNat, Nat.shiftLeft_eq, size_eq]
      have : 2 ^ (8 * a.toNat + 7) < W := by
        unfold ES.W; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [show 1 % W = 1 from rfl, one_mul, Nat.mod_eq_of_lt this]
    generalize hs : ((⟨1⟩ : UInt256) <<< (a * ⟨8⟩ + ⟨7⟩)) = s at hsb ⊢
    have hpos : 0 < 2 ^ (8 * a.toNat + 7) := by positivity
    have hlt : 2 ^ (8 * a.toNat + 7) < W := by
      unfold ES.W; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hL : (if (b &&& s) ≠ ⟨0⟩ then b ||| (UInt256.size.toUInt256 - s) else b &&& (s - ⟨1⟩)).toNat =
        (if b.toNat &&& 2 ^ (8 * a.toNat + 7) ≠ 0 then
          b.toNat ||| (2 ^ 256 - 2 ^ (8 * a.toNat + 7))
         else b.toNat &&& (2 ^ (8 * a.toNat + 7) - 1)) := by
      have hc : (b &&& s) = ⟨0⟩ ↔ b.toNat &&& 2 ^ (8 * a.toNat + 7) = 0 := by
        rw [← toNat_inj, show (b &&& s) = UInt256.land b s from rfl, and_spec, ES.and, hsb,
          UInt256.zero_toNat]
      by_cases h0 : b.toNat &&& 2 ^ (8 * a.toNat + 7) = 0
      · rw [if_neg (by rw [Ne, hc]; exact not_not.mpr h0), if_neg (not_not.mpr h0)]
        have e1 : (UInt256.mk (@OfNat.ofNat (Fin UInt256.size) 1 (@UInt256.instOfNatFinSize 1))).toNat = 1 := rfl
        rw [show b &&& (s - ⟨1⟩) = UInt256.land b (s - ⟨1⟩) from rfl, and_spec, ES.and,
          toNat_sub, hsb, e1]
        congr 1
        generalize 2 ^ (8 * a.toNat + 7) = p at *
        unfold ES.W at *; omega
      · rw [if_pos (by rw [Ne, hc]; exact h0), if_pos h0]
        rw [show b ||| (UInt256.size.toUInt256 - s) = UInt256.lor b (UInt256.size.toUInt256 - s)
          from rfl, or_spec, ES.or, toNat_sub, hsb]
        have : (UInt256.size.toUInt256).toNat = 0 := by
          show UInt256.size % UInt256.size = 0; exact Nat.mod_self _
        rw [this]
        congr 1
        generalize 2 ^ (8 * a.toNat + 7) = p at *
        unfold ES.W at *; omega
    rw [hL, signext_nat _ _ hb (by omega)]
    rw [show 8 * (a.toNat + 1) = 8 * a.toNat + 7 + 1 by ring, Nat.add_sub_cancel]
    rfl
  · rw [if_neg ha, if_pos (by omega)]

/-! ## Composition with EVMLean's `Xstep` (operand order)

Each theorem: if `Xstep` of the opcode succeeds on stack `a :: b :: (c ::) t`, the new stack is
`r :: t` with `r` the execution-specs result for pop order `(a, b (, c))`. -/

open Ethereum.EVM

set_option hygiene false in
macro "xstep_tac " stepLemma:ident spec:term : tactic =>
  `(tactic| (intro s' o h; rw [$stepLemma:ident s hdec, hs] at h; simp only at h;
             split_ifs at h <;> cases h <;> exact ⟨_, rfl, $spec⟩))

variable (s : State) (a b c : UInt256) (t : List UInt256)

abbrev Code (s : State) := s.executionEnv.code
abbrev Ok2 (s : State) (op : Operation) (a b : UInt256) (t : List UInt256) (v : Nat) : Prop :=
  decode (Code s) s.machineState.pc = some (op, .none) → s.machineState.stack = a :: b :: t →
  ∀ s' o, Xstep (D_J (Code s) 0) s = .ok (s', o) → ∃ r, s'.machineState.stack = r :: t ∧ r.toNat = v
abbrev Ok3 (s : State) (op : Operation) (a b c : UInt256) (t : List UInt256) (v : Nat) :
    Prop :=
  decode (Code s) s.machineState.pc = some (op, .none) → s.machineState.stack = a :: b :: c :: t →
  ∀ s' o, Xstep (D_J (Code s) 0) s = .ok (s', o) → ∃ r, s'.machineState.stack = r :: t ∧ r.toNat = v
abbrev Ok1 (s : State) (op : Operation) (a : UInt256) (t : List UInt256) (v : Nat) : Prop :=
  decode (Code s) s.machineState.pc = some (op, .none) → s.machineState.stack = a :: t →
  ∀ s' o, Xstep (D_J (Code s) 0) s = .ok (s', o) → ∃ r, s'.machineState.stack = r :: t ∧ r.toNat = v

theorem x_add : Ok2 s .ADD a b t (ES.add a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_add (add_spec a b)
theorem x_sdiv : Ok2 s .SDIV a b t (ES.sdiv a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_sdiv (sdiv_spec a b)
theorem x_shl : Ok2 s .SHL a b t (ES.shl a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_shl (shl_spec a b)
theorem x_addmod : Ok3 s .ADDMOD a b c t (ES.addmod a.toNat b.toNat c.toNat) := by
  intro hdec hs; xstep_tac step_addmod (addmod_spec a b c)
theorem x_exp : Ok2 s .EXP a b t (ES.exp a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_exp (exp_spec a b)
theorem x_not : Ok1 s .NOT a t (ES.not a.toNat) := by
  intro hdec hs; xstep_tac step_not (not_spec a)
theorem x_mul : Ok2 s .MUL a b t (ES.mul a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_mul (mul_spec a b)
theorem x_sub : Ok2 s .SUB a b t (ES.sub a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_sub (sub_spec a b)
theorem x_div : Ok2 s .DIV a b t (ES.div a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_div (div_spec a b)
theorem x_mod : Ok2 s .MOD a b t (ES.mod a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_mod (mod_spec a b)
theorem x_smod : Ok2 s .SMOD a b t (ES.smod a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_smod (smod_spec a b)
theorem x_mulmod : Ok3 s .MULMOD a b c t (ES.mulmod a.toNat b.toNat c.toNat) := by
  intro hdec hs; xstep_tac step_mulmod (mulmod_spec a b c)
theorem x_signextend : Ok2 s .SIGNEXTEND a b t (ES.signextend a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_signextend (signextend_spec a b)
theorem x_lt : Ok2 s .LT a b t (ES.lt a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_lt (lt_spec a b)
theorem x_gt : Ok2 s .GT a b t (ES.gt a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_gt (gt_spec a b)
theorem x_slt : Ok2 s .SLT a b t (ES.slt a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_slt (slt_spec a b)
theorem x_sgt : Ok2 s .SGT a b t (ES.sgt a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_sgt (sgt_spec a b)
theorem x_eq : Ok2 s .EQ a b t (ES.eq a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_eq (eq_spec a b)
theorem x_iszero : Ok1 s .ISZERO a t (ES.iszero a.toNat) := by
  intro hdec hs; xstep_tac step_iszero (iszero_spec a)
theorem x_and : Ok2 s .AND a b t (ES.and a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_and (and_spec a b)
theorem x_or : Ok2 s .OR a b t (ES.or a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_or (or_spec a b)
theorem x_xor : Ok2 s .XOR a b t (ES.xor a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_xor (xor_spec a b)
theorem x_byte : Ok2 s .BYTE a b t (ES.byte a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_byte (byte_spec a b)
theorem x_shr : Ok2 s .SHR a b t (ES.shr a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_shr (shr_spec a b)
theorem x_sar : Ok2 s .SAR a b t (ES.sar a.toNat b.toNat) := by
  intro hdec hs; xstep_tac step_sar (sar_spec a b)


end Poseidon2.Evm.WordOps
