import Mathlib.Data.List.GetD
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Poseidon2.Spec.Prime
import Poseidon2.Spec.Diagonal

/-!
# The internal matrix selection criterion, and certificates for it

For `t ≥ 4` the HorizenLabs script
(https://github.com/HorizenLabs/poseidon2/blob/bb476b9ca38198cf5092487283c8b8c5d4317c4e/poseidon2_rust_params.sage,
`generate_matrix_partial`, `check_minpoly_condition`) draws `M = circ(0, 1, .., 1) + diag(r)`
from the Grain stream and redraws while `check_minpoly_condition(M, t)` fails: for
`i = 1 .. 2t` the minimal polynomial of `M ^ i` over `GF(p)` must have degree `t` and be
irreducible. `MinpolyCondition` states that with Mathlib's `minpoly` and `Irreducible`.

This file proves the facts that let a kernel computation decide it for one matrix:

* a draw fails when the polynomial `f` with `f(M) = 0` (the characteristic polynomial) is
  `g · h` with `g`, `h` monic of degree at least 1 (`not_minpolyCondition`): the minimal
  polynomial of `M` divides `f`, so with degree `t` it is `f`, which is reducible;
* a draw passes when `f(M) = 0`, `f` is irreducible and, in `K = GF(p)[x] / f`, no `x ^ i`
  (`1 ≤ i ≤ 2t`) lies in a proper subfield (`minpolyCondition_of_cert`). `f` is irreducible when
  `gcd(f, x ^ (p ^ d) - x) = 1` for `d = 1 .. t / 2` (a Bezout identity each; an irreducible
  factor of degree `d` divides `x ^ (p ^ d) - x`); the subfields of `K` are the `GF(p ^ m)`,
  `m ∣ t`, and `x ^ i` lies in `GF(p ^ m)` when `(x ^ i) ^ (p ^ m) = x ^ i`.

Polynomials are little-endian lists of natural numbers read modulo `P`. The powers
`x ^ (p ^ d) mod f` come from a certificate (the square-and-multiply chain of `x ^ p`, then
composition), checked by the kernel.
-/

namespace Poseidon2.Spec.Minpoly

open Polynomial

/-! ## The criterion -/

/-- `circ(0, 1, .., 1) + diag(r)`: `r_a` on the diagonal, `1` elsewhere. -/
def partialMatrix (t : Nat) (r : List Nat) : Matrix (Fin t) (Fin t) (ZMod P) :=
  Matrix.of fun a b => if a = b then (r.getD a 0 : ZMod P) else 1

/-- The script's `check_minpoly_condition(M, t)`. -/
def MinpolyCondition (t : Nat) (M : Matrix (Fin t) (Fin t) (ZMod P)) : Prop :=
  ∀ i, 1 ≤ i → i ≤ 2 * t →
    (minpoly (ZMod P) (M ^ i)).natDegree = t ∧ Irreducible (minpoly (ZMod P) (M ^ i))

/-- Draw `k` is the first draw whose matrix passes `check_minpoly_condition`: the script keeps
it as its internal matrix. -/
def FirstPass (t rf rp k : Nat) : Prop :=
  (∀ j < k, ∃ r, Grain.drawRow t rf rp j = some r ∧ ¬MinpolyCondition t (partialMatrix t r)) ∧
    ∃ r, Grain.drawRow t rf rp k = some r ∧ MinpolyCondition t (partialMatrix t r)

/-! ## Coefficient lists -/

/-- `l` evaluated at `a`, little-endian. -/
def ev {R : Type*} [Semiring R] : List Nat → R → R
  | [], _ => 0
  | c :: l, a => (c : R) + a * ev l a

def addL : List Nat → List Nat → List Nat
  | [], b => b
  | a :: l, [] => a :: l
  | x :: a, y :: b => (x + y) % P :: addL a b

def smulL (c : Nat) (a : List Nat) : List Nat := a.map fun x => c * x % P

def negL (a : List Nat) : List Nat := a.map fun x => (P - x % P) % P

def subL (a b : List Nat) : List Nat := addL a (negL b)

def mulL (a b : List Nat) : List Nat := a.foldr (fun c acc => addL (smulL c b) (0 :: acc)) []

def allZero (l : List Nat) : Bool := l.all fun x => x % P == 0

section Ev

variable {R : Type*}

@[simp] theorem ev_nil [Semiring R] (a : R) : ev [] a = 0 := rfl
@[simp] theorem ev_cons [Semiring R] (c : Nat) (l : List Nat) (a : R) :
    ev (c :: l) a = (c : R) + a * ev l a := rfl

theorem cast_mod [AddMonoidWithOne R] [CharP R P] (n : Nat) : ((n % P : Nat) : R) = n :=
  (CharP.cast_eq_mod R P n).symm

theorem ev_addL [Semiring R] [CharP R P] :
    ∀ (a b : List Nat) (x : R), ev (addL a b) x = ev a x + ev b x
  | [], b, x => by simp [addL]
  | a :: l, [], x => by simp [addL]
  | c :: a, d :: b, x => by
    simp only [addL, ev_cons, cast_mod, Nat.cast_add, ev_addL a b x]
    noncomm_ring

theorem ev_smulL [Semiring R] [CharP R P] (c : Nat) :
    ∀ (a : List Nat) (x : R), Commute (c : R) x → ev (smulL c a) x = c * ev a x
  | [], x, _ => by simp [smulL]
  | d :: a, x, h => by
    have ih := ev_smulL c a x h
    simp only [smulL, List.map_cons, ev_cons] at ih ⊢
    rw [ih, cast_mod, Nat.cast_mul, mul_add, ← mul_assoc, ← mul_assoc, h.eq]

theorem ev_negL [Ring R] [CharP R P] : ∀ (a : List Nat) (x : R), ev (negL a) x = -ev a x
  | [], x => by simp [negL]
  | d :: a, x => by
    have ih := ev_negL a x
    simp only [negL, List.map_cons, ev_cons] at ih ⊢
    rw [ih, cast_mod, Nat.cast_sub (Nat.mod_lt _ (by decide)).le, CharP.cast_eq_zero, cast_mod]
    noncomm_ring

theorem ev_subL [Ring R] [CharP R P] (a b : List Nat) (x : R) :
    ev (subL a b) x = ev a x - ev b x := by
  rw [subL, ev_addL, ev_negL, sub_eq_add_neg]

theorem ev_mulL [CommSemiring R] [CharP R P] :
    ∀ (a b : List Nat) (x : R), ev (mulL a b) x = ev a x * ev b x
  | [], b, x => by simp [mulL]
  | c :: a, b, x => by
    have ih := ev_mulL a b x
    simp only [mulL, List.foldr_cons] at ih ⊢
    rw [ev_addL, ev_smulL _ _ _ (Commute.all _ _), ev_cons, ih]
    simp only [ev_cons, Nat.cast_zero, zero_add]
    ring

theorem ev_allZero [Semiring R] [CharP R P] :
    ∀ (l : List Nat) (x : R), allZero l = true → ev l x = 0
  | [], _, _ => rfl
  | c :: l, x, h => by
    simp only [allZero, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [ev_cons, ← cast_mod, h.1, ev_allZero l x (by simpa [allZero] using h.2)]
    simp

theorem ev_append [Semiring R] :
    ∀ (a b : List Nat) (x : R), ev (a ++ b) x = ev a x + x ^ a.length * ev b x
  | [], b, x => by simp
  | c :: a, b, x => by
    rw [List.cons_append, ev_cons, ev_cons, ev_append a b x, List.length_cons, pow_succ']
    noncomm_ring

theorem ev_map [Semiring R] {S : Type*} [Semiring S] (φ : R →+* S) :
    ∀ (l : List Nat) (x : R), φ (ev l x) = ev l (φ x)
  | [], _ => by simp
  | c :: l, x => by simp [ev_map φ l x]

theorem length_addL : ∀ a b : List Nat, (addL a b).length = max a.length b.length
  | [], b => by simp [addL]
  | a :: l, [] => by simp [addL]
  | x :: a, y :: b => by simp [addL, length_addL a b]

end Ev

/-! ## Arithmetic modulo a monic `f = fl ++ [1]` (degree `fl.length`) -/

/-- `x · r` modulo `f`, for `r` of length `fl.length`. -/
def mulX (fl r : List Nat) : List Nat :=
  addL (0 :: r.dropLast) (smulL ((P - r.getLastD 0 % P) % P) fl)

/-- `a · b` modulo `f`, for `b` of length `fl.length`. -/
def mulMod (fl a b : List Nat) : List Nat :=
  a.foldr (fun c acc => addL (smulL c b) (mulX fl acc)) (List.replicate fl.length 0)

/-- `g(h)` modulo `f`, for `h` of length `fl.length`. -/
def compMod (fl g h : List Nat) : List Nat :=
  g.foldr (fun c acc => addL [c % P] (mulMod fl acc h)) (List.replicate fl.length 0)

/-- `x` as a reduced polynomial of length `t`. -/
def xL (t : Nat) : List Nat := 0 :: 1 :: List.replicate (t - 2) 0

section Mod

variable {R : Type*} [CommRing R] [CharP R P]

theorem length_mulX (fl r : List Nat) (h : r.length = fl.length) (h1 : 1 ≤ fl.length) :
    (mulX fl r).length = fl.length := by
  simp only [mulX, length_addL, List.length_cons, List.length_dropLast, smulL, List.length_map]
  omega

omit [CharP R P] in
theorem ev_replicate_zero (n : Nat) (x : R) : ev (List.replicate n 0) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem ev_mulX (fl r : List Nat) (x : R) (hr : r.length = fl.length)
    (hf : ev fl x + x ^ fl.length = 0) : ev (mulX fl r) x = x * ev r x := by
  rcases List.eq_nil_or_concat r with h | ⟨r', l, rfl⟩
  · subst h
    have : fl = [] := List.length_eq_zero_iff.mp hr.symm
    subst this
    simp [mulX, smulL, addL]
  · rw [List.concat_eq_append, mulX, ev_addL, ev_smulL _ _ _ (Commute.all _ _), List.dropLast_concat,
      List.getLastD_concat, ev_cons, cast_mod, ev_append]
    simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hr
    have hfl : ev fl x = -x ^ fl.length := eq_neg_of_add_eq_zero_left hf
    rw [Nat.cast_sub (Nat.mod_lt _ (by decide)).le, CharP.cast_eq_zero R P, cast_mod, hfl, ← hr]
    simp only [Nat.cast_zero, zero_add, ev_cons, ev_nil, mul_zero, add_zero]
    ring

theorem length_mulMod (fl a b : List Nat) (hb : b.length = fl.length) (h1 : 1 ≤ fl.length) :
    (mulMod fl a b).length = fl.length := by
  induction a with
  | nil => simp [mulMod]
  | cons c a ih =>
    simp only [mulMod, List.foldr_cons] at ih ⊢
    rw [length_addL, length_mulX _ _ ih h1]
    simp [smulL, hb]

theorem ev_mulMod (fl a b : List Nat) (x : R) (hb : b.length = fl.length) (h1 : 1 ≤ fl.length)
    (hf : ev fl x + x ^ fl.length = 0) : ev (mulMod fl a b) x = ev a x * ev b x := by
  induction a with
  | nil => simp [mulMod, ev_replicate_zero]
  | cons c a ih =>
    have hl := length_mulMod fl a b hb h1
    simp only [mulMod, List.foldr_cons] at ih hl ⊢
    rw [ev_addL, ev_smulL _ _ _ (Commute.all _ _), ev_mulX _ _ _ hl hf, ih, ev_cons]
    ring

theorem length_compMod (fl g h : List Nat) (hh : h.length = fl.length) (h1 : 1 ≤ fl.length) :
    (compMod fl g h).length = fl.length := by
  induction g with
  | nil => simp [compMod]
  | cons c g ih =>
    simp only [compMod, List.foldr_cons] at ih ⊢
    rw [length_addL, length_mulMod _ _ _ hh h1]
    simp; omega

theorem ev_compMod (fl g h : List Nat) (x : R) (hh : h.length = fl.length) (h1 : 1 ≤ fl.length)
    (hf : ev fl x + x ^ fl.length = 0) : ev (compMod fl g h) x = ev g (ev h x) := by
  induction g with
  | nil => simp [compMod, ev_replicate_zero]
  | cons c g ih =>
    simp only [compMod, List.foldr_cons] at ih ⊢
    rw [ev_addL, ev_mulMod _ _ _ _ hh h1 hf, ih]
    simp [cast_mod]
    ring

omit [CharP R P] in
theorem ev_xL (t : Nat) (x : R) : ev (xL t) x = x := by
  simp [xL, ev_replicate_zero]

/-- Frobenius: `(g(y)) ^ P = g(y ^ P)`. -/
theorem ev_pow_P (g : List Nat) (y : R) : ev g y ^ P = ev g (y ^ P) := by
  haveI : ExpChar R P := ExpChar.prime Prime.prime_P
  have := ev_map (frobenius R P) g y
  simpa [frobenius_def] using this

end Mod

/-! ## Certificates for `x ^ (P ^ d)` modulo `f` -/

/-- One square-and-multiply step. -/
def sqStep (fl s : List Nat) (b : Bool) : List Nat :=
  if b then mulMod fl (mulMod fl s s) (xL fl.length) else mulMod fl s s

/-- Square-and-multiply over the bits `bs`, most significant first. -/
def sqRun (fl : List Nat) : List Bool → List Nat → List Nat
  | [], s => s
  | b :: bs, s => sqRun fl bs (sqStep fl s b)

/-- The exponent `sqRun` reaches from `e`. -/
def expOf (e : Nat) : List Bool → Nat
  | [] => e
  | b :: bs => expOf (2 * e + if b then 1 else 0) bs

theorem sqRun_append (fl : List Nat) :
    ∀ (a b : List Bool) (s : List Nat), sqRun fl (a ++ b) s = sqRun fl b (sqRun fl a s)
  | [], _, _ => rfl
  | _ :: a, b, _ => sqRun_append fl a b _

/-- `sqRun` in two parts, the middle state given. -/
theorem sqRun_append_of (fl : List Nat) (a b : List Bool) (s s' s'' : List Nat)
    (ha : sqRun fl a s = s') (hb : sqRun fl b s' = s'') : sqRun fl (a ++ b) s = s'' := by
  rw [sqRun_append, ha, hb]

section Chain

variable {R : Type*} [CommRing R] [CharP R P]

theorem sqRun_sound (fl : List Nat) (h1 : 2 ≤ fl.length) (x : R)
    (hf : ev fl x + x ^ fl.length = 0) :
    ∀ (bs : List Bool) (s : List Nat) (e : Nat), s.length = fl.length → ev s x = x ^ e →
      (sqRun fl bs s).length = fl.length ∧ ev (sqRun fl bs s) x = x ^ expOf e bs
  | [], s, e, hl, he => ⟨hl, he⟩
  | b :: bs, s, e, hl, he => by
    have hxl : (xL fl.length).length = fl.length := by simp [xL]; omega
    have hl' : (sqStep fl s b).length = fl.length := by
      rw [sqStep]; split
      · exact length_mulMod _ _ _ hxl (by omega)
      · exact length_mulMod fl s s hl (by omega)
    have he' : ev (sqStep fl s b) x = x ^ (2 * e + if b then 1 else 0) := by
      rw [sqStep]
      split
      · rw [ev_mulMod _ _ _ _ hxl (by omega) hf, ev_mulMod _ _ _ _ hl (by omega) hf, ev_xL, he]
        ring
      · rw [ev_mulMod _ _ _ _ hl (by omega) hf, he]; ring
    exact sqRun_sound fl h1 x hf bs _ _ hl' he'

/-- The powers `x ^ (P ^ (d + 1))`: `hs[0] = h1`, `hs[d + 1] = hs[d](h1)`. -/
def frobChain (fl h1 : List Nat) : List Nat → List (List Nat) → Bool
  | _, [] => true
  | prev, h :: rest => compMod fl prev h1 == h && frobChain fl h1 h rest

theorem frobChain_cons_of (fl h1 prev h : List Nat) (rest : List (List Nat))
    (hh : compMod fl prev h1 = h) (hr : frobChain fl h1 h rest = true) :
    frobChain fl h1 prev (h :: rest) = true := by
  simp [frobChain, hh, hr]

theorem frobChain_sound (fl h1 : List Nat) (hl1 : 1 ≤ fl.length) (hh1 : h1.length = fl.length)
    (x : R) (hf : ev fl x + x ^ fl.length = 0) (hx : x ^ P = ev h1 x) :
    ∀ (hs : List (List Nat)) (prev : List Nat) (d : Nat), frobChain fl h1 prev hs = true →
      x ^ P ^ d = ev prev x →
      ∀ j < hs.length, x ^ P ^ (d + 1 + j) = ev (hs.getD j []) x
  | [], _, _, _, _, j, hj => by simp at hj
  | h :: rest, prev, d, hc, hp, j, hj => by
    simp only [frobChain, Bool.and_eq_true, beq_iff_eq] at hc
    have hnext : x ^ P ^ (d + 1) = ev h x := by
      rw [← hc.1, ev_compMod _ _ _ _ hh1 hl1 hf, ← hx, ← ev_pow_P, ← hp, ← pow_mul, ← pow_succ]
    cases j with
    | zero => simpa using hnext
    | succ j =>
      have := frobChain_sound fl h1 hl1 hh1 x hf hx rest h (d + 1) hc.2 hnext j
        (by simp at hj; omega)
      rw [show d + 1 + (j + 1) = d + 1 + 1 + j by omega, this]
      simp

end Chain

/-- The certificate for `x ^ (P ^ (j + 1)) mod f = hs[j]`: square-and-multiply over the bits
`bs` of `P` from `x` gives `hs[0]`, then `hs[j + 1] = hs[j](hs[0])`. -/
def frobOk (fl : List Nat) (bs : List Bool) (hs : List (List Nat)) : Prop :=
  2 ≤ fl.length ∧ expOf 1 bs = P ∧
    ∃ h1 rest, hs = h1 :: rest ∧ sqRun fl bs (xL fl.length) = h1 ∧ frobChain fl h1 h1 rest = true

theorem frobOk_sound {R : Type*} [CommRing R] [CharP R P] (fl : List Nat)
    (bs : List Bool) (hs : List (List Nat)) (h : frobOk fl bs hs)
    (x : R) (hf : ev fl x + x ^ fl.length = 0) :
    2 ≤ fl.length ∧ ∀ j < hs.length, x ^ P ^ (j + 1) = ev (hs.getD j []) x := by
  obtain ⟨h2, he, h1, rest, rfl, hrun, hr⟩ := h
  refine ⟨h2, ?_⟩
  have hxl : (xL fl.length).length = fl.length := by simp [xL]; omega
  obtain ⟨hl, hev⟩ := sqRun_sound fl h2 x hf bs _ 1 hxl (by rw [ev_xL, pow_one])
  rw [he, hrun] at hev
  rw [hrun] at hl
  intro j hj
  cases j with
  | zero => simpa using hev.symm
  | succ j =>
    have := frobChain_sound fl _ (by omega) hl x hf hev.symm rest _ 1 hr
      (by simpa using hev.symm) j (by simp at hj; omega)
    rw [show j + 1 + 1 = 1 + 1 + j by omega, this]
    simp

/-! ## Polynomials over `ZMod P` -/

/-- `l` as a polynomial. -/
noncomputable def toPoly (l : List Nat) : (ZMod P)[X] := ev l X

theorem toPoly_cons (c : Nat) (l : List Nat) :
    toPoly (c :: l) = C (c : ZMod P) + X * toPoly l := by
  simp [toPoly]

theorem aeval_toPoly {B : Type*} [Semiring B] [Algebra (ZMod P) B] (l : List Nat) (x : B) :
    aeval x (toPoly l) = ev l x := by
  induction l with
  | nil => simp [toPoly]
  | cons c l ih => rw [toPoly_cons, map_add, map_mul, aeval_C, aeval_X, ih]; simp

theorem coeff_toPoly : ∀ (l : List Nat) (m : Nat), (toPoly l).coeff m = (l.getD m 0 : ZMod P)
  | [], m => by simp [toPoly]
  | c :: l, 0 => by simp [toPoly_cons]
  | c :: l, m + 1 => by
    rw [toPoly_cons, coeff_add, coeff_C, coeff_X_mul, coeff_toPoly l m]
    simp

theorem degree_toPoly_lt (l : List Nat) : (toPoly l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, List.getD_eq_default _ _ hm, Nat.cast_zero]

theorem toPoly_monic (fl : List Nat) :
    toPoly (fl ++ [1]) = X ^ fl.length + toPoly fl := by
  simp only [toPoly, ev_append, ev_cons, ev_nil, Nat.cast_one, mul_zero, add_zero, mul_one]
  ring

theorem monic_toPoly (fl : List Nat) : (toPoly (fl ++ [1])).Monic := by
  rw [toPoly_monic]; exact monic_X_pow_add (degree_toPoly_lt fl)

theorem natDegree_toPoly (fl : List Nat) : (toPoly (fl ++ [1])).natDegree = fl.length := by
  rw [toPoly_monic, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]; exact degree_toPoly_lt fl

theorem ev_root (fl : List Nat) {B : Type*} [Semiring B] [Algebra (ZMod P) B] (x : B)
    (h : aeval x (toPoly (fl ++ [1])) = 0) : ev fl x + x ^ fl.length = 0 := by
  rw [aeval_toPoly, ev_append] at h
  simpa using h

/-- Lists of one length with the same polynomial are equal modulo `P`. -/
theorem map_mod_eq_of_toPoly (a b : List Nat) (hl : a.length = b.length)
    (h : toPoly a = toPoly b) : a.map (· % P) = b.map (· % P) := by
  apply List.ext_getElem (by simpa using hl)
  intro j hja hjb
  have := congrArg (·.coeff j) h
  simp only [coeff_toPoly] at this
  rw [List.getD_eq_getElem _ _ (by simpa using hja), List.getD_eq_getElem _ _ (by simpa [hl] using hja)] at this
  simpa using (ZMod.natCast_eq_natCast_iff' _ _ P).mp this

/-! ## Finite fields -/

/-- An irreducible `g` of degree `d` divides `X ^ (P ^ d) - X`: `GF(P)[X] / g` is a field with
`P ^ d` elements. -/
theorem dvd_X_pow_sub_X {g : (ZMod P)[X]} (hg : Irreducible g) :
    g ∣ X ^ P ^ g.natDegree - X := by
  haveI := Fact.mk hg
  let pb := AdjoinRoot.powerBasis hg.ne_zero
  haveI : Module.Finite (ZMod P) (AdjoinRoot g) := pb.finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod P)
  letI := Fintype.ofFinite (AdjoinRoot g)
  have hcard : Fintype.card (AdjoinRoot g) = P ^ g.natDegree := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod P), Nat.card_zmod,
      pb.finrank, AdjoinRoot.powerBasis_dim]
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard,
    FiniteField.pow_card, sub_self]

theorem pow_pow_mul {K : Type*} [Monoid K] (y : K) (e : Nat) (h : y ^ P ^ e = y) :
    ∀ k, y ^ P ^ (e * k) = y
  | 0 => by simp
  | k + 1 => by rw [Nat.mul_succ, pow_add, pow_mul, pow_pow_mul y e h k, h]

/-- The Bezout identities `u · f + w · (hs[d - 1] - x) = 1`, `d = 1 .. t / 2`. -/
def bezOk (fl : List Nat) (hs : List (List Nat)) (bez : List (List Nat × List Nat)) : Bool :=
  fl.length / 2 ≤ bez.length && fl.length / 2 ≤ hs.length &&
    ((hs.zip bez).take (fl.length / 2)).all fun (h, u, w) =>
      allZero (subL (addL (mulL u (fl ++ [1])) (mulL w (subL h (xL fl.length)))) [1])

theorem irreducible_of_cert (fl : List Nat) (bs : List Bool)
    (hs : List (List Nat)) (bez : List (List Nat × List Nat))
    (hc : frobOk fl bs hs) (hb : bezOk fl hs bez = true) :
    Irreducible (toPoly (fl ++ [1])) := by
  have hmon := monic_toPoly fl
  rw [hmon.irreducible_iff_natDegree']
  refine ⟨fun h1 => ?_, fun g h hg hh hgh hdeg => ?_⟩
  · have := congrArg natDegree h1
    rw [natDegree_toPoly, natDegree_one] at this
    have := hc.1; omega
  · rw [natDegree_toPoly, Finset.mem_Ioc] at hdeg
    -- an irreducible factor `q` of `h`, of degree `d ∈ [1, t / 2]`
    have hhu : ¬IsUnit h := by
      rw [hh.isUnit_iff]; intro e; rw [e, natDegree_one] at hdeg; omega
    obtain ⟨q, hq, hqh⟩ := WfDvdMonoid.exists_irreducible_factor hhu hh.ne_zero
    have hqd : 1 ≤ q.natDegree := hq.natDegree_pos
    have hqle : q.natDegree ≤ h.natDegree := natDegree_le_of_dvd hqh hh.ne_zero
    have hqf : q ∣ toPoly (fl ++ [1]) := hqh.trans (hgh ▸ dvd_mul_left h g)
    -- in `L = GF(P)[X] / q`, the root `β` has `β ^ (P ^ d) = β` and `f(β) = 0`
    haveI := Fact.mk hq
    set L := AdjoinRoot q
    haveI : CharP L P := charP_of_injective_algebraMap (algebraMap (ZMod P) L).injective P
    set β := AdjoinRoot.root q
    have hfβ : aeval β (toPoly (fl ++ [1])) = 0 := by
      obtain ⟨k, hk⟩ := hqf
      rw [hk, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    have hβ : β ^ P ^ q.natDegree = β := by
      have := dvd_X_pow_sub_X hq
      rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at this
      exact this
    obtain ⟨h2, hfr⟩ := frobOk_sound fl bs hs hc β (ev_root fl β hfβ)
    simp only [bezOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hb
    obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hb
    set d := q.natDegree
    have hd : d - 1 < fl.length / 2 := by omega
    have hmem : (hs.getD (d - 1) [], bez.getD (d - 1) ([], [])) ∈
        (hs.zip bez).take (fl.length / 2) := by
      rw [List.mem_iff_getElem]
      refine ⟨d - 1, by simp; omega, ?_⟩
      simp [List.getElem?_eq_getElem (show d - 1 < hs.length by omega),
        List.getElem?_eq_getElem (show d - 1 < bez.length by omega)]
    have hz := ev_allZero _ β (hb3 _ hmem)
    have hF : ev (fl ++ [1]) β = 0 := by rw [← aeval_toPoly]; exact hfβ
    rw [ev_subL, ev_addL, ev_mulL, ev_mulL, ev_subL, ev_xL, ← hfr (d - 1) (by omega),
      show d - 1 + 1 = d by omega, hβ, sub_self, mul_zero, add_zero, hF, mul_zero] at hz
    simp at hz

/-! ## The powers of `x` lie in no proper subfield -/

/-- `w ≠ u` modulo `P` for `n` steps (`w := w · hm`, `u := x · u`, modulo `f`), ending at `w'`. -/
def powsNe (fl hm : List Nat) : Nat → List Nat → List Nat → List Nat → Bool
  | 0, w, _, w' => w == w'
  | n + 1, w, u, w' => w.map (· % P) != u.map (· % P) &&
      powsNe fl hm n (mulMod fl w hm) (mulX fl u) w'

/-- `x ^ n · u` modulo `f`. -/
def mulXs (fl : List Nat) : Nat → List Nat → List Nat
  | 0, u => u
  | n + 1, u => mulXs fl n (mulX fl u)

theorem mulXs_add (fl : List Nat) :
    ∀ (a b : Nat) (u : List Nat), mulXs fl (a + b) u = mulXs fl b (mulXs fl a u)
  | 0, _, _ => by simp [mulXs]
  | a + 1, b, u => by
    rw [show a + 1 + b = (a + b) + 1 by omega, mulXs, mulXs, mulXs_add fl a b]

theorem powsNe_add (fl hm : List Nat) :
    ∀ (a b : Nat) (w u w' w'' : List Nat), powsNe fl hm a w u w' = true →
      powsNe fl hm b w' (mulXs fl a u) w'' = true → powsNe fl hm (a + b) w u w'' = true
  | 0, b, w, u, w', w'', ha, hb => by
    simp only [powsNe, beq_iff_eq] at ha; subst ha; simpa [mulXs] using hb
  | a + 1, b, w, u, w', w'', ha, hb => by
    simp only [powsNe, Bool.and_eq_true] at ha
    rw [show a + 1 + b = (a + b) + 1 by omega, powsNe, ha.1, Bool.true_and]
    exact powsNe_add fl hm a b _ _ w' w'' ha.2 hb

/-- `powsNe` in two parts, `u` written as `x ^ c · u0`. -/
theorem powsNe_seg (fl hm : List Nat) (a b c : Nat) (w u0 w' w'' : List Nat)
    (ha : powsNe fl hm a w (mulXs fl c u0) w' = true)
    (hb : powsNe fl hm b w' (mulXs fl (c + a) u0) w'' = true) :
    powsNe fl hm (a + b) w (mulXs fl c u0) w'' = true :=
  powsNe_add fl hm a b _ _ _ _ ha (by rw [← mulXs_add]; exact hb)

theorem powsNe_sound {R : Type*} [CommRing R] [CharP R P] (fl hm : List Nat)
    (h2 : 2 ≤ fl.length) (hhm : hm.length = fl.length) (x : R)
    (hf : ev fl x + x ^ fl.length = 0) :
    ∀ (n : Nat) (w u w' : List Nat) (k : Nat), powsNe fl hm n w u w' = true →
      w.length = fl.length → u.length = fl.length → ev w x = ev hm x ^ k → ev u x = x ^ k →
      ∀ j < n, ∃ W U : List Nat, W.length = fl.length ∧ U.length = fl.length ∧
        W.map (· % P) ≠ U.map (· % P) ∧ ev W x = ev hm x ^ (k + j) ∧ ev U x = x ^ (k + j)
  | 0, _, _, _, _, _, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, w, u, w', k, h, hw, hu, hwv, huv, j, hj => by
    simp only [powsNe, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    cases j with
    | zero => exact ⟨w, u, hw, hu, h.1, by simpa using hwv, by simpa using huv⟩
    | succ j =>
      obtain ⟨W, U, h⟩ := powsNe_sound fl hm h2 hhm x hf n _ _ w' (k + 1) h.2
        (length_mulMod _ _ _ hhm (by omega)) (length_mulX _ _ hu (by omega))
        (by rw [ev_mulMod _ _ _ _ hhm (by omega) hf, hwv, pow_succ])
        (by rw [ev_mulX _ _ _ hu hf, huv, pow_succ']) j (by omega)
      exact ⟨W, U, by rw [show k + (j + 1) = k + 1 + j by omega]; exact h⟩

/-- Every proper divisor of `t` divides some `m ∈ ms`. -/
def divOk (t : Nat) (ms : List Nat) : Bool :=
  (List.range t).all fun e => e == 0 || t % e != 0 || ms.any fun m => m % e == 0

/-- For each `m ∈ ms`, `hs[m - 1] ^ i ≠ x ^ i` modulo `f` for `i = 1 .. 2t`. -/
def degOk (fl : List Nat) (hs : List (List Nat)) (ms : List Nat) : Prop :=
  divOk fl.length ms = true ∧ ∀ m ∈ ms, 1 ≤ m ∧ m ≤ hs.length ∧
    (hs.getD (m - 1) []).length = fl.length ∧
    ∃ w', powsNe fl (hs.getD (m - 1) []) (2 * fl.length) (hs.getD (m - 1) []) (xL fl.length) w' = true

theorem natDegree_minpoly_of_cert (fl : List Nat) (bs : List Bool)
    (hs : List (List Nat)) (ms : List Nat) (hc : frobOk fl bs hs)
    (hd : degOk fl hs ms) (hirr : Irreducible (toPoly (fl ++ [1])))
    (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ 2 * fl.length) :
    (minpoly (ZMod P) (AdjoinRoot.root (toPoly (fl ++ [1])) ^ i)).natDegree = fl.length := by
  haveI := Fact.mk hirr
  -- named: with these imports, instance search tries `LieAlgebra.toModule` first and fails
  letI : Module (ZMod P) (AdjoinRoot (toPoly (fl ++ [1]))) := Algebra.toModule
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite (ZMod P) (AdjoinRoot (toPoly (fl ++ [1]))) := pb.finite
  haveI : CharP (AdjoinRoot (toPoly (fl ++ [1]))) P :=
    charP_of_injective_algebraMap (algebraMap (ZMod P) _).injective P
  have hfin : Module.finrank (ZMod P) (AdjoinRoot (toPoly (fl ++ [1]))) = fl.length := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_toPoly]
  set α := AdjoinRoot.root (toPoly (fl ++ [1]))
  set γ := α ^ i
  have hint : IsIntegral (ZMod P) γ := IsIntegral.of_finite _ γ
  have hμ : Irreducible (minpoly (ZMod P) γ) := minpoly.irreducible hint
  have he1 : 0 < (minpoly (ZMod P) γ).natDegree := minpoly.natDegree_pos hint
  have hle : (minpoly (ZMod P) γ).natDegree ≤ fl.length := hfin ▸ minpoly.natDegree_le γ
  have hγt : γ ^ P ^ fl.length = γ := by
    haveI : Finite (AdjoinRoot (toPoly (fl ++ [1]))) := Module.finite_of_finite (ZMod P)
    letI := Fintype.ofFinite (AdjoinRoot (toPoly (fl ++ [1])))
    have hcard : Fintype.card (AdjoinRoot (toPoly (fl ++ [1]))) = P ^ fl.length := by
      rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod P),
        Nat.card_zmod, hfin]
    rw [← hcard]; exact FiniteField.pow_card γ
  have hdvd : (minpoly (ZMod P) γ).natDegree ∣ fl.length := by
    apply hμ.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    apply minpoly.dvd
    simp [hγt]
  by_contra hne
  have hlt : (minpoly (ZMod P) γ).natDegree < fl.length := lt_of_le_of_ne hle hne
  set e := (minpoly (ZMod P) γ).natDegree
  obtain ⟨hdiv, hms⟩ := hd
  simp only [divOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true] at hdiv
  obtain ⟨m, hm, hem⟩ : ∃ m ∈ ms, e ∣ m := by
    rcases hdiv e hlt with (h0 | h0) | ⟨m, hm, h⟩
    · omega
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h0
    · exact ⟨m, hm, Nat.dvd_of_mod_eq_zero h⟩
  obtain ⟨hm1, hmhs, hmlen, w2, hpows⟩ := hms m hm
  have hγe : γ ^ P ^ e = γ := by
    obtain ⟨k, hk⟩ := dvd_X_pow_sub_X hμ
    have := congrArg (aeval γ) hk
    rw [map_mul, minpoly.aeval, zero_mul, map_sub, map_pow, aeval_X, sub_eq_zero] at this
    exact this
  obtain ⟨k, hk⟩ := hem
  have hγm : γ ^ P ^ m = γ := hk ▸ pow_pow_mul γ e hγe k
  have hfα : ev fl α + α ^ fl.length = 0 :=
    ev_root fl α (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
  obtain ⟨h2, hfr⟩ := frobOk_sound fl bs hs hc α hfα
  have hαm : α ^ P ^ m = ev (hs.getD (m - 1) []) α := by
    have := hfr (m - 1) (by omega); rwa [show m - 1 + 1 = m by omega] at this
  obtain ⟨W, U, hW, hU, hWU, hWv, hUv⟩ := powsNe_sound fl _ h2 hmlen α hfα _ _ _ _ 1 hpows hmlen
    (by simp [xL]; omega) (by rw [pow_one]) (by rw [ev_xL, pow_one]) (i - 1) (by omega)
  rw [show 1 + (i - 1) = i by omega] at hWv hUv
  have hev : ev W α = ev U α := by
    rw [hWv, hUv, ← hαm, ← pow_mul, mul_comm, pow_mul]
    exact hγm
  rw [← aeval_toPoly, ← aeval_toPoly, AdjoinRoot.aeval_eq, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_eq_mk] at hev
  have hdeg : (toPoly W - toPoly U).natDegree < (toPoly (fl ++ [1])).natDegree := by
    rw [natDegree_toPoly]
    by_cases h0 : toPoly W - toPoly U = 0
    · rw [h0, natDegree_zero]; omega
    · rw [natDegree_lt_iff_degree_lt h0]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · rw [← hW]; exact degree_toPoly_lt W
      · rw [← hU]; exact degree_toPoly_lt U
  exact hWU (map_mod_eq_of_toPoly W U (hW.trans hU.symm)
    (sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hev hdeg)))

/-! ## The matrix on vectors -/

/-- A list as a vector of `ZMod P`. -/
def toVec (t : Nat) (v : List Nat) : Fin t → ZMod P := fun j => (v.getD j 0 : ZMod P)

/-- `partialMatrix t r` times `v`: `r_j · v_j - v_j + Σ v`. -/
def mv (r v : List Nat) : List Nat :=
  (r.zip v).map fun rv => (rv.1 * rv.2 + v.sum % P + (P - rv.2 % P)) % P

/-- `g(M) v` by Horner's rule, `M = partialMatrix t r`. -/
def hornerV (r v : List Nat) : List Nat → List Nat
  | [] => List.replicate v.length 0
  | c :: g => addL (smulL c v) (mv r (hornerV r v g))

/-- The unit vector `e_j` of length `t`. -/
def unitL (t j : Nat) : List Nat := (List.range t).map fun k => if k = j then 1 else 0

/-- `f(M) = 0`, column by column. -/
def matOk (t : Nat) (r fl : List Nat) : Bool :=
  r.length == t && (List.range t).all fun j => allZero (hornerV r (unitL t j) (fl ++ [1]))

theorem getD_addL : ∀ (a b : List Nat) (j : Nat),
    (((addL a b).getD j 0 : Nat) : ZMod P) = (a.getD j 0 : ZMod P) + (b.getD j 0 : ZMod P)
  | [], b, j => by simp only [addL, List.getD_nil, Nat.cast_zero, zero_add]
  | a :: l, [], j => by simp only [addL, List.getD_nil, Nat.cast_zero, add_zero]
  | x :: a, y :: b, 0 => by simp only [addL, List.getD_cons_zero, cast_mod, Nat.cast_add]
  | x :: a, y :: b, j + 1 => by simp only [addL, List.getD_cons_succ]; exact getD_addL a b j

theorem toVec_addL (t : Nat) (a b : List Nat) : toVec t (addL a b) = toVec t a + toVec t b := by
  funext j; simp only [toVec, Pi.add_apply]; exact getD_addL a b j

theorem toVec_smulL (t c : Nat) (a : List Nat) : toVec t (smulL c a) = (c : ZMod P) • toVec t a := by
  funext j
  simp only [toVec, smulL, Pi.smul_apply, smul_eq_mul]
  by_cases h : (j : Nat) < a.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h,
      List.getElem_map, cast_mod, Nat.cast_mul]
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (by omega)]; simp

theorem toVec_replicate (t n : Nat) : toVec t (List.replicate n 0) = 0 := by
  funext j
  simp only [toVec, Pi.zero_apply]
  by_cases hj : (j : Nat) < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate, Nat.cast_zero]
  · rw [List.getD_eq_default _ _ (by simpa using hj), Nat.cast_zero]

theorem length_mv (r v : List Nat) : (mv r v).length = min r.length v.length := by
  simp [mv]

theorem sum_toVec (t : Nat) (v : List Nat) (hv : v.length = t) :
    ∑ k, toVec t v k = (v.sum : ZMod P) := by
  subst hv
  rw [← List.sum_ofFn, Nat.cast_list_sum]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < v.length := by simpa using h1
  simp [toVec, List.getElem?_eq_getElem hj]

theorem mulVec_toVec (t : Nat) (r v : List Nat) (hr : r.length = t) (hv : v.length = t) :
    (partialMatrix t r).mulVec (toVec t v) = toVec t (mv r v) := by
  funext j
  have hj : (j : Nat) < t := j.isLt
  have hsplit : ∀ k : Fin t, partialMatrix t r j k * toVec t v k =
      toVec t v k + (if j = k then ((r.getD j 0 : ZMod P) - 1) * toVec t v j else 0) := by
    intro k
    simp only [partialMatrix, Matrix.of_apply]
    split
    · subst_vars; ring
    · ring
  simp only [Matrix.mulVec, dotProduct, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, sum_toVec t v hv]
  unfold toVec mv
  rw [List.getD_eq_getElem _ _ (show (j : Nat) < ((r.zip v).map _).length by simp; omega),
    List.getElem_map, List.getElem_zip]
  rw [List.getD_eq_getElem r 0 (by omega), List.getD_eq_getElem v 0 (by omega)]
  rw [cast_mod, Nat.cast_add, Nat.cast_add, Nat.cast_mul, cast_mod,
    Nat.cast_sub (Nat.mod_lt _ (by decide)).le, CharP.cast_eq_zero (ZMod P) P, cast_mod]
  ring

theorem hornerV_sound (t : Nat) (r v : List Nat) (hr : r.length = t) (hv : v.length = t) :
    ∀ g : List Nat, (hornerV r v g).length = t ∧
      (ev g (partialMatrix t r)).mulVec (toVec t v) = toVec t (hornerV r v g)
  | [] => by
    refine ⟨by simp [hornerV, hv], ?_⟩
    simp [hornerV, toVec_replicate]
  | c :: g => by
    obtain ⟨hl, ih⟩ := hornerV_sound t r v hr hv g
    refine ⟨?_, ?_⟩
    · simp only [hornerV, length_addL, smulL, List.length_map, length_mv]; omega
    · rw [ev_cons, Matrix.add_mulVec, Matrix.natCast_mulVec, ← Matrix.mulVec_mulVec, ih,
        mulVec_toVec t r _ hr hl, hornerV, toVec_addL, toVec_smulL]

theorem toVec_unitL (t : Nat) (j : Fin t) : toVec t (unitL t j) = Pi.single j 1 := by
  funext k
  simp only [toVec, unitL]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  by_cases h : k = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg (fun e => h (Fin.ext e))]; simp

theorem toVec_allZero (t : Nat) (l : List Nat) (h : allZero l = true) : toVec t l = 0 := by
  funext j
  simp only [toVec, Pi.zero_apply]
  simp only [allZero, List.all_eq_true, beq_iff_eq] at h
  by_cases hj : (j : Nat) < l.length
  · rw [List.getD_eq_getElem _ _ hj, ← cast_mod, h _ (List.getElem_mem hj), Nat.cast_zero]
  · rw [List.getD_eq_default _ _ (by omega), Nat.cast_zero]

theorem aeval_of_matOk (t : Nat) (r fl : List Nat) (h : matOk t r fl = true) :
    aeval (partialMatrix t r) (toPoly (fl ++ [1])) = 0 := by
  simp only [matOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hr, hcols⟩ := h
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [aeval_toPoly, Matrix.zero_mulVec, ← toVec_unitL,
    (hornerV_sound t r _ hr (by simp [unitL]) _).2]
  exact toVec_allZero t _ (hcols j j.isLt)

/-! ## A draw fails, a draw passes -/

/-- If `f(M) = 0` and `f = g · h` with `g`, `h` monic of degree at least 1, the condition fails
already at `i = 1`. -/
theorem not_minpolyCondition (t : Nat) (r fl gl hl : List Nat) (ht : 1 ≤ t) (hfl : fl.length = t)
    (hm : matOk t r fl = true) (hg : 1 ≤ gl.length) (hh : 1 ≤ hl.length)
    (hgh : allZero (subL (mulL (gl ++ [1]) (hl ++ [1])) (fl ++ [1])) = true) :
    ¬MinpolyCondition t (partialMatrix t r) := by
  intro hc
  obtain ⟨hdeg, hirr⟩ := hc 1 le_rfl (by omega)
  rw [pow_one] at hdeg hirr
  have hF := aeval_of_matOk t r fl hm
  have hint : IsIntegral (ZMod P) (partialMatrix t r) := IsIntegral.of_finite _ _
  have hdvd := minpoly.dvd (ZMod P) (partialMatrix t r) hF
  have heq := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monic_toPoly fl) hdvd
    (by rw [natDegree_toPoly, hdeg, hfl])
  rw [← heq] at hirr
  have hprod : toPoly (gl ++ [1]) * toPoly (hl ++ [1]) = toPoly (fl ++ [1]) := by
    have := ev_allZero _ (X : (ZMod P)[X]) hgh
    rw [ev_subL, ev_mulL, sub_eq_zero] at this
    exact this
  rw [← hprod] at hirr
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · rw [(monic_toPoly gl).isUnit_iff] at hu
    have := congrArg natDegree hu; rw [natDegree_toPoly, natDegree_one] at this; omega
  · rw [(monic_toPoly hl).isUnit_iff] at hu
    have := congrArg natDegree hu; rw [natDegree_toPoly, natDegree_one] at this; omega

/-- If `f(M) = 0`, `f` is irreducible and the powers `x ^ i` lie in no proper subfield of
`GF(P)[x] / f`, the condition holds: `M ^ i` and `x ^ i` have the same minimal polynomial. -/
theorem minpolyCondition_of_cert (t : Nat) (r fl : List Nat) (bs : List Bool)
    (hs : List (List Nat)) (bez : List (List Nat × List Nat)) (ms : List Nat)
    (hfl : fl.length = t) (hm : matOk t r fl = true) (hc : frobOk fl bs hs)
    (hb : bezOk fl hs bez = true) (hd : degOk fl hs ms) :
    MinpolyCondition t (partialMatrix t r) := by
  have hirr := irreducible_of_cert fl bs hs bez hc hb
  haveI := Fact.mk hirr
  letI : Module (ZMod P) (AdjoinRoot (toPoly (fl ++ [1]))) := Algebra.toModule
  have ht : 2 ≤ t := hfl ▸ hc.1
  haveI : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  have hF := aeval_of_matOk t r fl hm
  intro i hi1 hi2
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite (ZMod P) (AdjoinRoot (toPoly (fl ++ [1]))) := pb.finite
  have hint : IsIntegral (ZMod P) (AdjoinRoot.root (toPoly (fl ++ [1])) ^ i) :=
    IsIntegral.of_finite _ _
  have hq : Irreducible (minpoly (ZMod P) (AdjoinRoot.root (toPoly (fl ++ [1])) ^ i)) :=
    minpoly.irreducible hint
  have hqM : aeval (partialMatrix t r ^ i)
      (minpoly (ZMod P) (AdjoinRoot.root (toPoly (fl ++ [1])) ^ i)) = 0 := by
    set q := minpoly (ZMod P) (AdjoinRoot.root (toPoly (fl ++ [1])) ^ i)
    have h1 : aeval (AdjoinRoot.root (toPoly (fl ++ [1]))) (q.comp (X ^ i)) = 0 := by
      rw [aeval_comp, aeval_X_pow]; exact minpoly.aeval _ _
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h1
    obtain ⟨k, hk⟩ := h1
    have h2 : aeval (partialMatrix t r) (q.comp (X ^ i)) = 0 := by rw [hk, map_mul, hF, zero_mul]
    rwa [aeval_comp, aeval_X_pow] at h2
  rw [← minpoly.eq_of_irreducible_of_monic hq hqM (minpoly.monic hint)]
  exact ⟨hfl ▸ natDegree_minpoly_of_cert fl bs hs ms hc hd hirr i hi1 (by omega), hq⟩

end Poseidon2.Spec.Minpoly
