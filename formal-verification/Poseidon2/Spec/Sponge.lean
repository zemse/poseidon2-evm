import Poseidon2.Spec.Permutation

/-!
# The hash entries

What the contracts compute, stated on top of `permutation`:

* the permutation entries (every width): `t` words in, `t` words out, `permutationWords`;
* `hash_1` / `hash_2` / `hash_3` of the t = 4 contracts (`IPoseidon2`): the inputs read modulo
  `P`, the state `[x_0, .., x_{n-1}, 0, .., 0, n · 2^64]` permuted once, element 0 returned
  (`hash`, `hashWords`).

`hash` is the single-permutation case of the Barretenberg / Noir Poseidon2 sponge (rate
`t - 1`, capacity 1, initial value `n · 2^64` in the capacity element), which `sponge` states
in general and `sponge_eq_hash_1` / `_2` / `_3` relate for t = 4.
-/

namespace Poseidon2.Spec

/-- The state `hash` permutes for inputs `xs`: the inputs, zeros, and `n · 2^64` last. -/
def spongeState {R : Type} [CommSemiring R] (t : Nat) (xs : List R) : List R :=
  xs ++ List.replicate (t - 1 - xs.length) 0 ++ [((xs.length * 2 ^ 64 : Nat) : R)]

/-- One permutation of `spongeState`, element 0 of the output. For `xs.length ≤ t - 1`. -/
def hash {R : Type} [CommSemiring R] (c : Params) (xs : List R) : R :=
  (permutation c (spongeState c.t xs)).headD 0

/-- `hash` on 256-bit words: inputs read modulo `P`, output below `P`. -/
def hashWords (c : Params) (ws : List Nat) : Nat :=
  (hash c (ws.map (fun w => (w : F)))).val

section Sponge
variable {R : Type} [CommSemiring R] (c : Params)

/-- Barretenberg's `perform_duplex`: add the cache (rate `t - 1`, zero padded) into the state,
then permute. -/
def duplex (state cache : List R) : List R :=
  permutation c (List.zipWith (· + ·) state (cache ++ List.replicate (c.t - cache.length) 0))

/-- Barretenberg's `absorb`, on (state, cache). -/
def absorb (sc : List R × List R) (x : R) : List R × List R :=
  if sc.2.length = c.t - 1 then (duplex c sc.1 sc.2, [x]) else (sc.1, sc.2 ++ [x])

/-- The Barretenberg / Noir Poseidon2 sponge hash (`FieldSponge::hash_internal`,
`Poseidon2::hash`): capacity element `n · 2^64`, absorb every input, squeeze one element. -/
def sponge (xs : List R) : R :=
  let init : List R := List.replicate (c.t - 1) 0 ++ [((xs.length * 2 ^ 64 : Nat) : R)]
  let sc := xs.foldl (absorb c) (init, [])
  (duplex c sc.1 sc.2).headD 0

end Sponge

section T4
variable {R : Type} [CommSemiring R] (c : Params) (h : c.t = 4)
include h

theorem sponge_eq_hash_1 (a : R) : sponge c [a] = hash c [a] := by
  simp [sponge, hash, absorb, duplex, spongeState, h]

theorem sponge_eq_hash_2 (a b : R) : sponge c [a, b] = hash c [a, b] := by
  simp [sponge, hash, absorb, duplex, spongeState, h]

theorem sponge_eq_hash_3 (a b d : R) : sponge c [a, b, d] = hash c [a, b, d] := by
  simp [sponge, hash, absorb, duplex, spongeState, h]

end T4

end Poseidon2.Spec
