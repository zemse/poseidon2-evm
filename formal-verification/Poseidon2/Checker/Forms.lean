import Poseidon2.Spec.Permutation

/-!
# Symbolic values of the checker: terms, linear forms, atoms

* `Term`: an exact 256-bit word built from the call's inputs (`CALLDATALOAD` at a concrete
  offset, `CALLDATASIZE`, `CALLVALUE`) and constants with EVM operations, evaluated exactly
  (`Term.eval`). Terms are built by `Term.mk`, which folds constants and rewrites a few
  shapes into one normal form, so the same word computed two ways gets the same term.
* `Def` / `Tab`: the atoms of the field, numbered in creation order. An atom is either a word
  read in the field (`Def.word t`, the value `Term.eval t mod P`) or the fifth power of a linear
  form over earlier atoms (`Def.pow5 l`). Atoms are looked up by their definition, so two
  computations of the same S-box input get the same atom whatever order they run in.
* `Lin`: a linear form `c + Σ aᵢ·xᵢ` over atoms, in a canonical shape (coefficients in
  `[1, P)`, sorted by atom, constant below `P`).

`linOps` is the spec's `Ops` record over linear forms, with the atom table as the threaded
state: running `permG linOps` on input atoms gives the forms the bytecode must produce.
-/

namespace Poseidon2.Checker

open Poseidon2.Spec

/-- `2^256`. -/
abbrev W : Nat := 2 ^ 256

/-! ## Terms -/

/-- An exact word. `bin op a b` and `un op a` apply the EVM operation with opcode byte `op`
(`a` is the top of the stack). -/
inductive Term where
  | const (v : Nat)
  | cdl (off : Nat)
  | cds
  | cv
  | un (op : Nat) (a : Term)
  | bin (op : Nat) (a b : Term)
  deriving Repr, Inhabited, DecidableEq

/-- Structural equality. -/
def Term.beq : Term → Term → Bool
  | .const a, .const b => a == b
  | .cdl a, .cdl b => a == b
  | .cds, .cds => true
  | .cv, .cv => true
  | .un o a, .un o' a' => o == o' && a.beq a'
  | .bin o a b, .bin o' a' b' => o == o' && a.beq a' && b.beq b'
  | _, _ => false

/-- Two's complement sign of a word. -/
def neg (a : Nat) : Bool := 2 ^ 255 ≤ a

/-- The EVM binary operations on words (`a` on top of the stack), `none` if not supported. -/
def binOp (op a b : Nat) : Option Nat :=
  match op with
  | 0x01 => some ((a + b) % W)
  | 0x02 => some ((a * b) % W)
  | 0x03 => some ((a + W - b) % W)
  | 0x04 => some (if b = 0 then 0 else a / b)
  | 0x06 => some (if b = 0 then 0 else a % b)
  | 0x10 => some (if a < b then 1 else 0)
  | 0x11 => some (if a > b then 1 else 0)
  | 0x12 => some (if (neg a && !neg b) || (neg a == neg b && a < b) then 1 else 0)
  | 0x13 => some (if (!neg a && neg b) || (neg a == neg b && a > b) then 1 else 0)
  | 0x14 => some (if a = b then 1 else 0)
  | 0x16 => some (a &&& b)
  | 0x17 => some (a ||| b)
  | 0x18 => some (a ^^^ b)
  | 0x1b => some (if a < 256 then (b <<< a) % W else 0)
  | 0x1c => some (if a < 256 then b >>> a else 0)
  | _ => none

/-- The EVM unary operations (ISZERO, NOT). -/
def unOp (op a : Nat) : Option Nat :=
  match op with
  | 0x15 => some (if a = 0 then 1 else 0)
  | 0x19 => some (W - 1 - a % W)
  | _ => none

/-- What the checker assumes about the call: the calldata, its size and the call value. -/
structure Env where
  cd : List UInt8
  cv : Nat

/-- `CALLDATALOAD`: 32 bytes big-endian, zero past the end. -/
def cdWord (cd : List UInt8) (off : Nat) : Nat :=
  ((List.range 32).map fun i => (cd.getD (off + i) 0).toNat).foldl (fun acc b => acc * 256 + b) 0

/-- The value of a term. Unsupported operations read as `0` (the checker never builds them). -/
def Term.eval (e : Env) : Term → Nat
  | .const v => v
  | .cdl off => cdWord e.cd off
  | .cds => e.cd.length % W
  | .cv => e.cv % W
  | .un op a => (unOp op (a.eval e)).getD 0
  | .bin op a b => (binOp op (a.eval e) (b.eval e)).getD 0

/-! ## Linear forms -/

/-- `c + Σ a·x` over atoms `x`, terms sorted by atom, coefficients in `[1, P)`. -/
structure Lin where
  c : Nat
  ts : List (Nat × Nat)
  deriving Repr, Inhabited, DecidableEq

def termsBeq : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], [] => true
  | (i, a) :: xs, (j, b) :: ys => i == j && a == b && termsBeq xs ys
  | _, _ => false

def Lin.beq (a b : Lin) : Bool := a.c == b.c && termsBeq a.ts b.ts

/-- Merge two sorted term lists (fuel: the total length; it always suffices, and running out
returns the concatenation, still the right sum). -/
def merge : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, xs, ys => xs ++ ys
  | _, [], ys => ys
  | _, xs, [] => xs
  | f + 1, (i, a) :: xs, (j, b) :: ys =>
    if i < j then (i, a) :: merge f xs ((j, b) :: ys)
    else if j < i then (j, b) :: merge f ((i, a) :: xs) ys
    else
      let c := (a + b) % P
      if c = 0 then merge f xs ys else (i, c) :: merge f xs ys

def Lin.add (a b : Lin) : Lin :=
  ⟨(a.c + b.c) % P, merge (a.ts.length + b.ts.length) a.ts b.ts⟩

def Lin.const (c : Nat) : Lin := ⟨c % P, []⟩

def Lin.scale (a : Lin) (k : Nat) : Lin :=
  let k := k % P
  if k = 0 then ⟨0, []⟩ else ⟨a.c * k % P, a.ts.map fun (i, v) => (i, v * k % P)⟩

/-- The constant of a form without atoms. -/
def Lin.asConst (a : Lin) : Option Nat :=
  match a.ts with
  | [] => some a.c
  | _ => none

/-- `x^5 mod P`. -/
def pow5 (x : Nat) : Nat := let x := x % P; let x2 := x * x % P; x2 * x2 % P * x % P

/-! ## Atoms -/

/-- What an atom stands for. -/
inductive Def where
  /-- the word read in the field -/
  | word (t : Term)
  /-- the fifth power of a form over earlier atoms -/
  | pow5 (l : Lin)
  deriving Repr, Inhabited, DecidableEq

def Def.beq : Def → Def → Bool
  | .word a, .word b => a.beq b
  | .pow5 a, .pow5 b => a.beq b
  | _, _ => false

/-- The atoms, newest first, with the next index (the atom count). -/
structure Tab where
  defs : List (Nat × Def)
  next : Nat
  deriving Repr, Inhabited, DecidableEq

def Tab.empty : Tab := ⟨[], 0⟩

def lookupDef (d : Def) : List (Nat × Def) → Option Nat
  | [] => none
  | (i, d') :: r => if d.beq d' then some i else lookupDef d r

/-- The atom of `d`, created if new, as a form. -/
def Tab.atom (tb : Tab) (d : Def) : Lin × Tab :=
  match lookupDef d tb.defs with
  | some i => (⟨0, [(i, 1)]⟩, tb)
  | none => (⟨0, [(tb.next, 1)]⟩, ⟨(tb.next, d) :: tb.defs, tb.next + 1⟩)

/-- `l^5`: a constant if `l` is one, else the atom `pow5 l`. -/
def Tab.sbox (l : Lin) (tb : Tab) : Lin × Tab :=
  match l.asConst with
  | some c => (Lin.const (pow5 c), tb)
  | none => tb.atom (.pow5 l)

/-- The spec's operations on forms, threading the atom table. -/
def linOps : Ops Lin Tab where
  zero := ⟨0, []⟩
  add := Lin.add
  addC a c := a.add (Lin.const c)
  mulC := Lin.scale
  sbox := Tab.sbox

end Poseidon2.Checker
