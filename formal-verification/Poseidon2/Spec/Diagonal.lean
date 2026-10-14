import Poseidon2.Spec.Grain

/-!
# The diagonal draws

The rows the HorizenLabs script draws for the internal matrix, continuing the Grain generator
of `Grain.lean` after the round constants, and certificates for them.
-/

namespace Poseidon2.Spec.Grain

/-! ## The internal diagonal

For `t ≥ 4` the script's `generate_matrix_partial` draws `M_I = circ(0, 1, .., 1) + diag(r)`
with `r` = `t` values `F(grain_random_bits(n))` (the `n` bits read modulo `p`, no rejection),
continuing the same generator after the round constants, and redraws while
`check_minpoly_condition` fails. The reference implementations store `r - 1` (`diagM1`).
`drawRow t rf rp j` is the `r` of draw `j` (counted from 0), `diagonal` its `r - 1`; which
draw is the first to pass is `Minpoly.FirstPass`. -/

/-- The state after `m` values of `n` bits. -/
def skipBits (n : Nat) : Nat → Nat → Option Nat
  | 0, s => some s
  | m + 1, s =>
    match bits n 0 s with
    | some (_, s') => skipBits n m s'
    | none => none

/-- `t` values of `n` bits, each read modulo `p`. -/
def row (n p : Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some []
  | k + 1, s =>
    match bits n 0 s with
    | some (v, s') => (row n p k s').map (v % p :: ·)
    | none => none

/-- Draw `j` (from 0) of the partial matrix's diagonal `r`, for the BN254 scalar field. -/
def drawRow (t rf rp j : Nat) : Option (List Nat) :=
  (constants 254 P (rf * t + rp) (init 254 t rf rp)).bind fun r =>
    (skipBits 254 (j * t) r.2).bind (row 254 P t)

/-- `diagM1` of draw `j`: its `r - 1`. -/
def diagonal (t rf rp j : Nat) : Option (List Nat) :=
  (drawRow t rf rp j).map (·.map fun v => (v + P - 1) % P)

theorem getLast?_getD_cons (a s : Nat) (l : List Nat) :
    (a :: l).getLast?.getD s = l.getLast?.getD a := by
  cases l <;> simp [List.getLast?_cons]

/-- A certificate for `constants` that also gives the final state. -/
theorem constants_state_of_chain (n p : Nat) :
    ∀ (vs ss : List Nat) (s : Nat), chain n p s vs ss = true →
      constants n p vs.length s = some (vs, ss.getLastD s)
  | [], [], _, _ => rfl
  | v :: vs, s' :: ss, s, h => by
    simp only [chain, Bool.and_eq_true, beq_iff_eq] at h
    have ih := constants_state_of_chain n p vs ss s' h.2
    simp [constants, h.1, ih, getLast?_getD_cons]
  | [], _ :: _, _, h => by simp [chain] at h
  | _ :: _, [], _, h => by simp [chain] at h

/-- A certificate for values of `n` bits: each value and the state after it. -/
def valChain (n : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | s, (v, s') :: rest => bits n 0 s == some (v, s') && valChain n s' rest

/-- The state after the values of a chain. -/
def valLast (s : Nat) (l : List (Nat × Nat)) : Nat := (l.map (·.2)).getLastD s

theorem valLast_cons (s : Nat) (v : Nat × Nat) (l : List (Nat × Nat)) :
    valLast s (v :: l) = valLast v.2 l := by
  simp [valLast, getLast?_getD_cons]

theorem valChain_append (n : Nat) :
    ∀ (a b : List (Nat × Nat)) (s : Nat),
      valChain n s (a ++ b) = (valChain n s a && valChain n (valLast s a) b)
  | [], _, _ => by simp [valChain, valLast]
  | (v, s') :: a, b, s => by
    simp only [List.cons_append, valChain, valChain_append n a b s', Bool.and_assoc,
      valLast_cons]

theorem valChain_append_of (n s s' : Nat) (a b : List (Nat × Nat)) (ha : valChain n s a = true)
    (hs : valLast s a = s') (hb : valChain n s' b = true) : valChain n s (a ++ b) = true := by
  rw [valChain_append, ha, hs, hb]; rfl

theorem skipBits_of_valChain (n : Nat) :
    ∀ (l : List (Nat × Nat)) (s : Nat), valChain n s l = true →
      skipBits n l.length s = some (valLast s l)
  | [], _, _ => rfl
  | (v, s') :: l, s, h => by
    simp only [valChain, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.length_cons, skipBits, h.1, valLast_cons]
    exact skipBits_of_valChain n l s' h.2

theorem row_of_valChain (n p : Nat) :
    ∀ (l : List (Nat × Nat)) (s : Nat), valChain n s l = true →
      row n p l.length s = some (l.map fun vs => vs.1 % p)
  | [], _, _ => rfl
  | (v, s') :: l, s, h => by
    simp only [valChain, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.length_cons, row, h.1]
    simp [row_of_valChain n p l s' h.2]

/-- Draw `j` from certificates: the round-constant chain and the values (with states) of the
draws after it, from the last state of the chain. -/
theorem drawRow_of_vals (t rf rp j : Nat) (vs ss : List Nat) (vals : List (Nat × Nat))
    (hlen : vs.length = rf * t + rp) (hc : chain 254 P (init 254 t rf rp) vs ss = true)
    (hv : valChain 254 (ss.getLastD (init 254 t rf rp)) vals = true)
    (hj : (j + 1) * t ≤ vals.length) :
    drawRow t rf rp j = some (((vals.drop (j * t)).take t).map fun vs => vs.1 % P) := by
  have h1 := constants_state_of_chain 254 P vs ss _ hc
  rw [hlen] at h1
  rw [← List.take_append_drop (j * t) vals, valChain_append, Bool.and_eq_true] at hv
  have h2 := skipBits_of_valChain 254 _ _ hv.1
  rw [List.length_take, min_eq_left (by rw [Nat.succ_mul] at hj; omega)] at h2
  rw [← List.take_append_drop t (vals.drop (j * t)), valChain_append, Bool.and_eq_true] at hv
  have h3 := row_of_valChain 254 P _ _ hv.2.1
  rw [List.length_take, List.length_drop, min_eq_left (by rw [Nat.succ_mul] at hj; omega)] at h3
  simp only [drawRow, h1, Option.bind_some, h2, h3]

end Poseidon2.Spec.Grain
