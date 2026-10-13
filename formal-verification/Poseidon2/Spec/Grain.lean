import Poseidon2.Spec.Permutation

/-!
# Round constants from the Grain LFSR

The round constant generation of the HorizenLabs parameter script
(https://github.com/HorizenLabs/poseidon2/blob/bb476b9ca38198cf5092487283c8b8c5d4317c4e/poseidon2_rust_params.sage,
`init_generator`, `grain_sr_generator`, `grain_random_bits`, `generate_constants`),
written from that script for a prime field with the S-box `x ^ α`:

* an 80-bit LFSR seeded with `field (2 bits) = 1`, `sbox (4) = 0`, `n (12)`, `t (12)`,
  `R_F (10)`, `R_P (10)` and thirty ones, clocked 160 times;
* each clock appends `b62 ⊕ b51 ⊕ b38 ⊕ b23 ⊕ b13 ⊕ b0` and drops `b0`;
* self-shrinking: of each pair of clocked bits the second is output when the first is 1;
* a constant is `n` output bits, most significant first, resampled while `≥ P`;
* Poseidon2 takes `R_F · t + R_P` constants: the first `R_F / 2` full rounds, the partial
  rounds (one each), the last `R_F / 2` full rounds.

Bit `i` of the state number is element `i` of the script's `bit_sequence`.
The internal diagonal is not derived here (the script draws it at random and checks its
minimal polynomials).
-/

namespace Poseidon2.Spec.Grain

/-- The feedback bit. -/
def feedback (s : Nat) : Nat :=
  ((s >>> 62) ^^^ (s >>> 51) ^^^ (s >>> 38) ^^^ (s >>> 23) ^^^ (s >>> 13) ^^^ s) &&& 1

/-- One clock: the new bit and the new state. -/
def clock (s : Nat) : Nat × Nat :=
  let b := feedback s
  (b, (s >>> 1) ||| (b <<< 79))

/-- Clock `k` times, discarding the output. -/
def skip : Nat → Nat → Nat
  | 0, s => s
  | k + 1, s => skip k (clock s).2

/-- Appends `v` as `w` bits, most significant first, to the sequence `(acc, len)` read from
bit 0. -/
def push (acc len v w : Nat) : Nat × Nat := (acc ||| (v <<< len), len + w)

/-- The initial state for `n`-bit field elements, width `t`, `R_F`, `R_P`, after the 160
discarded clocks. -/
def init (n t rf rp : Nat) : Nat :=
  -- bits in script order: bit_sequence[0] is the most significant bit of `field`
  let bits : List (Nat × Nat) := [(1, 2), (0, 4), (n, 12), (t, 12), (rf, 10), (rp, 10)]
  let seq := bits.foldl (fun (acc : Nat × Nat) (vw : Nat × Nat) =>
    -- reverse the `w` bits of `v`, so the most significant lands at the lowest index
    let rev := (List.range vw.2).foldl (fun r i => r ||| (((vw.1 >>> i) &&& 1) <<< (vw.2 - 1 - i))) 0
    push acc.1 acc.2 rev vw.2) (0, 0)
  skip 160 (seq.1 ||| ((2 ^ 30 - 1) <<< seq.2))

/-- The next self-shrunk bit, with `fuel` pairs at most. -/
def nextBit : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, s =>
    let a := clock s
    let b := clock a.2
    if a.1 = 1 then some (b.1, b.2) else nextBit fuel b.2

/-- `k` output bits as a number, most significant first. -/
def bits : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, v, s => some (v, s)
  | k + 1, v, s =>
    match nextBit 1000 s with
    | some (b, s') => bits k (2 * v + b) s'
    | none => none

/-- One constant: `n` bits, resampled while `≥ p` (at most `fuel` tries). -/
def constant (n p : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, s =>
    match bits n 0 s with
    | some (v, s') => if v < p then some (v, s') else constant n p fuel s'
    | none => none

/-- `k` constants. -/
def constants (n p : Nat) : Nat → Nat → Option (List Nat × Nat)
  | 0, s => some ([], s)
  | k + 1, s =>
    match constant n p 1000 s with
    | some (v, s') =>
      match constants n p k s' with
      | some (vs, s'') => some (v :: vs, s'')
      | none => none
    | none => none

/-- The round constants of the script for the BN254 scalar field (254-bit), in its order:
first full rounds, partial rounds, last full rounds. -/
def roundConstants (t rf rp : Nat) : Option (List Nat) :=
  (constants 254 P (rf * t + rp) (init 254 t rf rp)).map (·.1)

end Poseidon2.Spec.Grain

namespace Poseidon2.Spec.Params

/-- The constants of `c` in the script's order: the first `R_F / 2` rows, the partial
round constants, the last `R_F / 2` rows. -/
def roundOrder (c : Params) : List Nat :=
  (c.rcExternal.take (c.roundsF / 2)).flatten ++ c.rcInternal ++
    (c.rcExternal.drop (c.roundsF / 2)).flatten

end Poseidon2.Spec.Params

namespace Poseidon2.Spec.Grain

/-- A certificate for `constants`: `ss` lists the state after each constant, so every
constant is checked from a literal state (kernel evaluation of the plain recursion
re-evaluates the state chain and does not finish for 72 constants). -/
def chain (n p : Nat) : Nat → List Nat → List Nat → Bool
  | _, [], [] => true
  | s, v :: vs, s' :: ss => constant n p 1000 s == some (v, s') && chain n p s' vs ss
  | _, _, _ => false

theorem constants_of_chain (n p : Nat) :
    ∀ (vs ss : List Nat) (s : Nat), chain n p s vs ss = true →
      (constants n p vs.length s).map (·.1) = some vs
  | [], [], _, _ => rfl
  | v :: vs, s' :: ss, s, h => by
    simp only [chain, Bool.and_eq_true, beq_iff_eq] at h
    have ih := constants_of_chain n p vs ss s' h.2
    simp only [List.length_cons, constants, h.1]
    cases hc : constants n p vs.length s' with
    | none => simp [hc] at ih
    | some r => simp_all
  | [], _ :: _, _, h => by simp [chain] at h
  | _ :: _, [], _, h => by simp [chain] at h

/-- `roundConstants` from a certificate. -/
theorem roundConstants_of_chain (t rf rp : Nat) (vs ss : List Nat)
    (hlen : vs.length = rf * t + rp) (h : chain 254 P (init 254 t rf rp) vs ss = true) :
    roundConstants t rf rp = some vs := by
  have := constants_of_chain 254 P vs ss _ h
  rw [hlen] at this
  exact this

/-- The states a certificate needs (computed outside the kernel, checked by `chain`). -/
def certStates (n p k s : Nat) : List Nat :=
  match k with
  | 0 => []
  | k + 1 =>
    match constant n p 1000 s with
    | some (_, s') => s' :: certStates n p k s'
    | none => []

end Poseidon2.Spec.Grain
