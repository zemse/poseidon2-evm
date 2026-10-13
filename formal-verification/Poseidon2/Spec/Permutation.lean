import Mathlib.Data.ZMod.Basic

/-!
# The Poseidon2 permutation

The Poseidon2 permutation of the paper (Grassi, Khovratovich, Schofnegger,
"Poseidon2: A Faster Version of the Poseidon Hash Function",
https://eprint.iacr.org/2023/323), for a state width `t ∈ {2, 3, 4, 8, 12, ...}`
and the S-box `x ↦ x ^ 5`:

* the external linear layer `M_E` before the first round,
* `R_F / 2` full rounds: add a round constant to every element, S-box every element, `M_E`,
* `R_P` partial rounds: add a round constant to element 0, S-box element 0, `M_I`,
* `R_F / 2` full rounds.

`M_E` is `circ(2, 1)` for `t = 2`, `circ(2, 1, 1)` for `t = 3`, `M4` for `t = 4` and
`circ(2·M4, M4, ..., M4)` (blocks of four) for `t = 8, 12, ...`, with the paper's
`M4 = [[5,7,1,3],[4,6,1,1],[1,3,5,7],[1,1,4,6]]`.
`M_I` is `1 + diag(d)`: every row sums the state and adds `d_i · x_i`. The constants record
holds `d` (the "diagonal minus one" of the reference implementations); for `t = 2` and `t = 3`
it is `[1, 2]` and `[1, 1, 2]`, the paper's `[[2,1],[1,3]]` and `[[2,1,1],[1,2,1],[1,1,3]]`.

The definition is written once, over an `Ops` record (zero, addition, adding and multiplying by
a constant, the S-box with a threaded state `σ`), so the same text runs on field elements
(`ringOps`, the spec) and on symbolic values (a later checker). The state is a `List`; the
constants are natural numbers, read in the field by `Nat.cast`.
-/

namespace Poseidon2.Spec

/-- The operations the permutation uses. `σ` is threaded through the S-boxes (unused, `Unit`,
for field elements). -/
structure Ops (α σ : Type) where
  zero : α
  add : α → α → α
  /-- add a constant -/
  addC : α → Nat → α
  /-- multiply by a constant -/
  mulC : α → Nat → α
  /-- `x ↦ x ^ 5` -/
  sbox : α → σ → α × σ

/-- Width, round numbers and constants of one Poseidon2 instance. -/
structure Params where
  t : Nat
  /-- full rounds, half before and half after the partial rounds -/
  roundsF : Nat
  /-- partial rounds -/
  roundsP : Nat
  /-- one row of `t` per full round, in round order -/
  rcExternal : List (List Nat)
  /-- one constant per partial round -/
  rcInternal : List Nat
  /-- `M_I = 1 + diag(diagM1)` -/
  diagM1 : List Nat

namespace Params

/-- The shape the definition assumes: a width Poseidon2 defines, matching table sizes. -/
def WellFormed (c : Params) : Bool :=
  (c.t == 2 || c.t == 3 || (c.t % 4 == 0 && 4 ≤ c.t)) &&
  c.roundsF % 2 == 0 &&
  c.rcExternal.length == c.roundsF && c.rcExternal.all (·.length == c.t) &&
  c.rcInternal.length == c.roundsP &&
  c.diagM1.length == c.t

end Params

section
variable {α σ : Type} (A : Ops α σ)

/-- Row-wise `M4 · (a, b, c, d)`. -/
def m4 (a b c d : α) : List α :=
  [A.add (A.add (A.mulC a 5) (A.mulC b 7)) (A.add (A.mulC c 1) (A.mulC d 3)),
   A.add (A.add (A.mulC a 4) (A.mulC b 6)) (A.add (A.mulC c 1) (A.mulC d 1)),
   A.add (A.add (A.mulC a 1) (A.mulC b 3)) (A.add (A.mulC c 5) (A.mulC d 7)),
   A.add (A.add (A.mulC a 1) (A.mulC b 1)) (A.add (A.mulC c 4) (A.mulC d 6))]

/-- `M4` on every block of four. -/
def m4Blocks : List α → List α
  | a :: b :: c :: d :: r => m4 A a b c d ++ m4Blocks r
  | r => r

/-- The sum of the state. -/
def sum : List α → α
  | [] => A.zero
  | x :: xs => A.add x (sum xs)

/-- The four column sums of a state in blocks of four: element `i` of the result sums the
elements at indices `≡ i (mod 4)`. -/
def colSums : List α → α × α × α × α
  | a :: b :: c :: d :: r =>
    let s := colSums r
    (A.add a s.1, A.add b s.2.1, A.add c s.2.2.1, A.add d s.2.2.2)
  | _ => (A.zero, A.zero, A.zero, A.zero)

/-- Adds column sum `i mod 4` to element `i`. -/
def addColSums (s : α × α × α × α) : List α → List α
  | a :: b :: c :: d :: r =>
    A.add a s.1 :: A.add b s.2.1 :: A.add c s.2.2.1 :: A.add d s.2.2.2 :: addColSums s r
  | r => r

/-- The external matrix `M_E`. For `t ≥ 8`, `circ(2·M4, M4, ..., M4)` applied to `x` is
`M4` on every block plus, on every block, the sum of the `M4` outputs of all blocks. -/
def external (xs : List α) : List α :=
  match xs with
  | [_, _] | [_, _, _] => let s := sum A xs; xs.map (fun x => A.add x s)
  | [a, b, c, d] => m4 A a b c d
  | _ => let ys := m4Blocks A xs; addColSums A (colSums A ys) ys

/-- The internal matrix `M_I = 1 + diag(d)`: `y_i = d_i · x_i + Σ x`. -/
def internal (d : List Nat) (xs : List α) : List α :=
  let s := sum A xs
  List.zipWith (fun x di => A.add (A.mulC x di) s) xs d

/-- The S-box on every element, left to right. -/
def sboxAll : List α → σ → List α × σ
  | [], st => ([], st)
  | x :: xs, st =>
    let r := A.sbox x st
    let rs := sboxAll xs r.2
    (r.1 :: rs.1, rs.2)

/-- Full rounds, one per row of constants. -/
def fullRounds : List (List Nat) → List α → σ → List α × σ
  | [], xs, st => (xs, st)
  | rc :: rcs, xs, st =>
    let r := sboxAll A (List.zipWith A.addC xs rc) st
    fullRounds rcs (external A r.1) r.2

/-- Partial rounds, one per constant. -/
def partialRounds (d : List Nat) : List Nat → List α → σ → List α × σ
  | [], xs, st => (xs, st)
  | _ :: _, [], st => ([], st)
  | rc :: rcs, x :: xs, st =>
    let r := A.sbox (A.addC x rc) st
    partialRounds d rcs (internal A d (r.1 :: xs)) r.2

/-- The permutation over `A`. -/
def permG (c : Params) (xs : List α) (st : σ) : List α × σ :=
  let half := c.roundsF / 2
  let a := fullRounds A (c.rcExternal.take half) (external A xs) st
  let b := partialRounds A c.diagM1 c.rcInternal a.1 a.2
  fullRounds A (c.rcExternal.drop half) b.1 b.2

end

/-- Field (or any commutative semiring) operations. -/
def ringOps (R : Type) [CommSemiring R] : Ops R Unit where
  zero := 0
  add := (· + ·)
  addC x c := x + (c : R)
  mulC x c := (c : R) * x
  sbox x u := (x ^ 5, u)

/-- The permutation over a commutative semiring `R`. -/
def permutation {R : Type} [CommSemiring R] (c : Params) (xs : List R) : List R :=
  (permG (ringOps R) c xs ()).1

/-- The BN254 scalar field prime (the order of the BN254 / alt_bn128 G1 group). -/
abbrev P : Nat := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

/-- The BN254 scalar field `ZMod P`. -/
abbrev F := ZMod P

/-- Every constant is a canonical field element (below `P`). -/
def Params.Canonical (c : Params) : Bool :=
  c.rcExternal.all (·.all (· < P)) && c.rcInternal.all (· < P) && c.diagM1.all (· < P)

/-- The permutation on 256-bit words as the contracts see them: every input word is read
modulo `P` and every output is the canonical representative, below `P`. -/
def permutationWords (c : Params) (ws : List Nat) : List Nat :=
  (permutation c (ws.map (fun w => (w : F)))).map ZMod.val

end Poseidon2.Spec
