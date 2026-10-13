import Poseidon2.Checker.Forms

/-!
# Word terms with value ranges

`mkBin` / `mkUn` build the term of an EVM operation on two (one) words together with an
interval `[lo, hi]` holding its value, given intervals for the operands. Constants fold, and a
few rewrites put equal words into one shape:

* `a + c` with `c ≥ 2^255` is `a - (2^256 - c)`;
* commutative operations keep a constant operand second;
* `and(shl(k, x), 2^256 - 2^s)` with `k ≤ s < 256` is `shl(s, shr(s - k, x))` (both clear the
  low `s` bits of `x · 2^k`).

`Facts` are assumptions on the call (the calldata size, the call value, the selector word):
intervals for given terms, intersected with what the operation gives. A theorem about a
checked run holds for the calls that satisfy its facts.
-/

namespace Poseidon2.Checker

/-- Assumed intervals for terms. -/
abbrev Facts := List (Term × Nat × Nat)

def factOf (t : Term) : Facts → Option (Nat × Nat)
  | [] => none
  | (t', r) :: fs => if t.beq t' then some r else factOf t fs

/-- `r` intersected with the fact on `t`, if any. -/
def withFacts (fs : Facts) (t : Term) (r : Nat × Nat) : Nat × Nat :=
  match factOf t fs with
  | some (lo, hi) => (max lo r.1, min hi r.2)
  | none => r

def full : Nat × Nat := (0, W - 1)

/-- A word known only through its term. -/
structure Word where
  t : Term
  lo : Nat
  hi : Nat
  deriving Inhabited, DecidableEq

def Word.exact (w : Word) : Option Nat := if w.lo = w.hi then some w.lo else none

def Word.const (v : Nat) : Word := ⟨.const v, v, v⟩

/-- Constants print as `Word.const v` (shorter checkpoint literals). -/
instance : Repr Word where
  reprPrec w p :=
    match w.t with
    | .const v => if w.lo = v ∧ w.hi = v then Repr.addAppParen (.text s!"Word.const {v}") p
      else Repr.addAppParen ("Word.mk (" ++ repr w.t ++ s!") {w.lo} {w.hi}") p
    | t => Repr.addAppParen ("Word.mk (" ++ repr t ++ s!") {w.lo} {w.hi}") p

/-- A comparison result: decided, or `[0, 1]`. -/
def decided (yes no : Bool) : Nat × Nat := if yes then (1, 1) else if no then (0, 0) else (0, 1)

/-- The interval of `bin op a b` from the operand intervals. -/
def binRange (op : Nat) (a b : Word) : Nat × Nat :=
  match op with
  | 0x01 => if a.hi + b.hi < W then (a.lo + b.lo, a.hi + b.hi) else full
  | 0x03 =>
    if b.hi ≤ a.lo then (a.lo - b.hi, a.hi - b.lo)
    else if a.hi < b.lo then (a.lo + W - b.hi, a.hi + W - b.lo)
    else full
  | 0x02 => if a.hi * b.hi < W then (a.lo * b.lo, a.hi * b.hi) else full
  | 0x10 => decided (a.hi < b.lo) (b.hi ≤ a.lo)
  | 0x11 => decided (b.hi < a.lo) (a.hi ≤ b.lo)
  | 0x12 => if a.hi < 2 ^ 255 && b.hi < 2 ^ 255 then decided (a.hi < b.lo) (b.hi ≤ a.lo) else (0, 1)
  | 0x13 => if a.hi < 2 ^ 255 && b.hi < 2 ^ 255 then decided (b.hi < a.lo) (a.hi ≤ b.lo) else (0, 1)
  | 0x14 => decided (a.lo = a.hi && b.lo = b.hi && a.lo = b.lo) (a.hi < b.lo || b.hi < a.lo)
  | 0x16 => (0, min a.hi b.hi)
  | 0x1c => if a.lo = a.hi && a.lo < 256 then (b.lo >>> a.lo, b.hi >>> a.lo) else full
  | 0x1b =>
    if a.lo = a.hi && a.lo < 256 && b.hi <<< a.lo < W then (b.lo <<< a.lo, b.hi <<< a.lo)
    else full
  | _ => full

def isConst : Term → Bool
  | .const _ => true
  | _ => false

def commutative (op : Nat) : Bool :=
  op == 0x01 || op == 0x02 || op == 0x14 || op == 0x16 || op == 0x17 || op == 0x18

/-- `some s` if `m = 2^256 - 2^s` (`s < 256`). -/
def lowZeros (m : Nat) : Option Nat :=
  ((List.range 256).find? fun s => m + 2 ^ s = W)

/-- The term of `bin op a b`, normalized (see the module doc). -/
def binTerm (op : Nat) (a b : Term) : Term :=
  match op, a, b with
  | 0x01, x, .const c => if 2 ^ 255 ≤ c ∧ c < W then .bin 0x03 x (.const (W - c)) else .bin op x (.const c)
  | 0x16, .bin 0x1b (.const k) x, .const m =>
    match lowZeros m with
    | some s => if k ≤ s ∧ s < 256 then .bin 0x1b (.const s) (.bin 0x1c (.const (s - k)) x)
      else .bin op a b
    | none => .bin op a b
  | _, _, _ => .bin op a b

/-- `bin op a b` on words: constants fold, else the normalized term and its interval.
`none` for an operation the checker does not support. -/
def mkBin (fs : Facts) (op : Nat) (a b : Word) : Option Word :=
  match a.exact, b.exact with
  | some x, some y => (binOp op x y).map Word.const
  | _, _ =>
    -- a word equals itself
    if op = 0x14 ∧ a.t.beq b.t then some (Word.const 1) else
    match binOp op 0 0 with
    | none => none
    | some _ =>
      -- a constant operand of a commutative operation goes second
      let (a, b) := if commutative op && isConst a.t && !isConst b.t then (b, a) else (a, b)
      let t := binTerm op a.t b.t
      let r := withFacts fs t (binRange op a b)
      some ⟨t, r.1, r.2⟩

/-- `un op a` on words. -/
def mkUn (fs : Facts) (op : Nat) (a : Word) : Option Word :=
  match a.exact with
  | some x => (unOp op x).map Word.const
  | none =>
    match unOp op 0 with
    | none => none
    | some _ =>
      let t := Term.un op a.t
      let r := match op with
        | 0x15 => decided (a.hi = 0) (0 < a.lo)
        | 0x19 => (W - 1 - a.hi, W - 1 - a.lo)
        | _ => full
      let r := withFacts fs t r
      some ⟨t, r.1, r.2⟩

/-- An input word. -/
def mkInput (fs : Facts) (t : Term) (r : Nat × Nat) : Word :=
  match t with
  | .const v => Word.const v
  | t =>
  let r := withFacts fs t r
  ⟨t, r.1, r.2⟩

end Poseidon2.Checker
