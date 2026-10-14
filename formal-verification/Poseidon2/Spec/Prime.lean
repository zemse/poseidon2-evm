import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Tactic.NormNum.Prime
import Poseidon2.Spec.Permutation

/-!
# `P` is prime

A Pratt certificate: Lucas' test (`lucas_primality`) for `P` and for the prime factors of
`P - 1` above `10^6`, recursively, with the factorizations and the witnesses `a` computed
outside the kernel; the factors below `10^6` by `norm_num`. The powers are computed by
`powMod` (square and multiply), checked by kernel evaluation.
-/

namespace Poseidon2.Spec.Prime

/-- `b ^ e % m` by square and multiply, with `k` bits of `e` at most. -/
def pm (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1 % m
  | k + 1, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then pm m k (b * b % m) (e / 2) * b % m
    else pm m k (b * b % m) (e / 2)

theorem pm_eq (m : Nat) : ∀ (k b e : Nat), e < 2 ^ k → pm m k b e = b ^ e % m
  | 0, b, e, h => by
    have : e = 0 := by simpa using h
    subst this; simp [pm]
  | k + 1, b, e, h => by
    have ih := pm_eq m k (b * b % m) (e / 2) (by omega)
    unfold pm
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [if_neg h0, ih]
      have he : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2
      · rw [if_neg (by omega)]
        conv_rhs => rw [he, h2, Nat.add_zero, pow_mul, Nat.pow_mod]
        rw [sq]
      · rw [if_pos h2]
        conv_rhs => rw [he, h2, pow_add, pow_mul, pow_one, Nat.mul_mod, Nat.pow_mod]
        rw [sq, Nat.mul_mod, Nat.mod_mod]

/-- `b ^ e % m` for `e < 2 ^ 256`. -/
def powMod (b e m : Nat) : Nat := pm m 256 b e

theorem zmod_pow (p a e : Nat) (he : e < 2 ^ 256) :
    (a : ZMod p) ^ e = ((powMod a e p : Nat) : ZMod p) := by
  rw [powMod, pm_eq p 256 a e he, ZMod.natCast_mod, Nat.cast_pow]

/-- Lucas' test, with `p - 1 = ∏ q ^ e` over the list `fs` of pairs `(q, e)`. -/
theorem prime_of_lucas (p a : Nat) (fs : List (Nat × Nat)) (hp : 2 ≤ p) (hlt : p < 2 ^ 256)
    (hprod : (fs.map fun qe => qe.1 ^ qe.2).prod = p - 1)
    (hprime : ∀ qe ∈ fs, qe.1.Prime)
    (ha : powMod a (p - 1) p = 1)
    (hq : ∀ qe ∈ fs, powMod a ((p - 1) / qe.1) p ≠ 1) : p.Prime := by
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [zmod_pow p a _ (by omega), ha, Nat.cast_one]
  · intro q hqp hdvd h1
    rw [← hprod] at hdvd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hqp.prime).mp hdvd
    obtain ⟨qe, hqe, rfl⟩ := List.mem_map.mp hx
    have hq' : q = qe.1 :=
      (Nat.prime_dvd_prime_iff_eq hqp (hprime qe hqe)).mp (hqp.dvd_of_dvd_pow hqx)
    subst hq'
    apply hq qe hqe
    rw [zmod_pow p a _ (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))] at h1
    have h2 := congrArg ZMod.val h1
    have : Fact (1 < p) := ⟨by omega⟩
    rwa [ZMod.val_natCast, ZMod.val_one, Nat.mod_eq_of_lt] at h2
    rw [powMod, pm_eq p 256 a _ (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
    exact Nat.mod_lt _ (by omega)

/-- Lucas' test as one kernel computation, given the primes of `fs`. -/
def lucasOk (p a : Nat) (fs : List (Nat × Nat)) : Bool :=
  2 ≤ p && p < 2 ^ 256 && (fs.map fun qe => qe.1 ^ qe.2).prod == p - 1 &&
    powMod a (p - 1) p == 1 && fs.all fun qe => powMod a ((p - 1) / qe.1) p != 1

theorem prime_of_lucasOk (p a : Nat) (fs : List (Nat × Nat)) (h : lucasOk p a fs = true)
    (hprime : ∀ qe ∈ fs, qe.1.Prime) : p.Prime := by
  simp only [lucasOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h2, hlt⟩, hprod⟩, ha⟩, hq⟩ := h
  exact prime_of_lucas p a fs h2 hlt hprod hprime ha hq

theorem prime_12048837557 : Nat.Prime 12048837557 :=
  prime_of_lucasOk _ 2 [(2, 2), (7, 2), (661, 1), (93001, 1)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        norm_num)

theorem prime_5156902474397 : Nat.Prime 5156902474397 :=
  prime_of_lucasOk _ 2 [(2, 2), (107, 1), (12048837557, 1)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, prime_12048837557⟩)

theorem prime_1670836401704629 : Nat.Prime 1670836401704629 :=
  prime_of_lucasOk _ 2 [(2, 2), (3, 4), (5156902474397, 1)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, prime_5156902474397⟩)

theorem prime_405928799 : Nat.Prime 405928799 :=
  prime_of_lucasOk _ 22 [(2, 1), (11, 1), (3691, 1), (4999, 1)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        norm_num)

theorem prime_1593227 : Nat.Prime 1593227 :=
  prime_of_lucasOk _ 2 [(2, 1), (19, 1), (41927, 1)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        norm_num)

theorem prime_639533339 : Nat.Prime 639533339 :=
  prime_of_lucasOk _ 2 [(2, 1), (229, 1), (853, 1), (1637, 1)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        norm_num)

theorem prime_65865678001877903 : Nat.Prime 65865678001877903 :=
  prime_of_lucasOk _ 5 [(2, 1), (83, 1), (379, 1), (1637, 1), (639533339, 1)] (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_639533339⟩)

theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 :=
  prime_of_lucasOk _ 3 [(2, 5), (5, 1), (823, 1), (1593227, 1), (65865678001877903, 1)]
    (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_1593227, prime_65865678001877903⟩)

/-- The BN254 scalar field modulus is prime. -/
theorem prime_P : Nat.Prime P :=
  prime_of_lucasOk P 5 [(2, 28), (3, 2), (13, 1), (29, 1), (983, 1), (11003, 1), (237073, 1),
      (405928799, 1), (1670836401704629, 1), (13818364434197438864469338081, 1)]
    (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
          by norm_num, prime_405928799, prime_1670836401704629,
          prime_13818364434197438864469338081⟩)

instance : Fact (Nat.Prime P) := ⟨prime_P⟩

end Poseidon2.Spec.Prime
