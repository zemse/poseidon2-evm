import Poseidon2.Spec.Minpoly
import Poseidon2.Spec.DiagCheck

/-!
# The internal diagonal for t = 4 is the first draw passing the script's check

Draws 0 .. 3 fail `check_minpoly_condition`: the characteristic polynomial `f` of
their matrix `M` factors (`f = g · h`, both monic of degree at least 1), so the minimal
polynomial of `M ^ 1` is not irreducible of degree 4. Draw 4 passes it: `f` is
irreducible and `x ^ i` (`1 ≤ i ≤ 8`) lies in no proper subfield of `GF(P)[x] / f`.
Certificates written by `scripts/minpoly.mjs`, checked by kernel evaluation.
-/

namespace Poseidon2.Spec.MinpolyCheck.T4

open Minpoly DiagCheck

/-- Draw `j` (`j ≤ 4`), as `DiagCheck.drawRow_t4` gives it. -/
abbrev rowOf (j : Nat) : List Nat := ((diagValsT4.drop (j * 4)).take 4).map fun vs => vs.1 % P

/-- The monic product `g · h` without its leading `1`. -/
def fOf (g h : List Nat) : List Nat := (mulL (g ++ [1]) (h ++ [1])).take 4

/-- Draw 0: `f = g · h`, `g` of degree 2. -/
def g0 : List Nat := [0x17500c7f17af82c78619ec0e97ff70734693cf7af2852c4f502a5105eeadeef0, 0xeb9bef266bbc3b09abb60f4c27502fa15a713a631d8a87cec24da39a10d0053]

def h0 : List Nat := [0x1e36e5dfc421267508b95382f92bc49f42bda27ca944d90c5f0ebf989a86e957, 0x1ed01c593fd33b75eed906e7c2c10fd1737c8c147f1ae092f622cb52231837f6]

theorem fail0 : ¬MinpolyCondition 4 (partialMatrix 4 (rowOf 0)) :=
  not_minpolyCondition 4 _ (fOf g0 h0) g0 h0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 1: `f = g · h`, `g` of degree 2. -/
def g1 : List Nat := [0x3da7c72d087ae8e655ce0cdc10ad1e73be22adf606ead288f501b0ae8af841c, 0x2cc47c12ae71c5111d7aef54f08e76a9da15f7b6c77fab554817070849a62914]

def h1 : List Nat := [0x3eb20d06bb69112e91afcbda3eabf13fccb208fdf0acb976cb20edecb38d678, 0x25883b9468a593863399adce5932a7d236c8380f49f8cc4948e10cf8b50236b8]

theorem fail1 : ¬MinpolyCondition 4 (partialMatrix 4 (rowOf 1)) :=
  not_minpolyCondition 4 _ (fOf g1 h1) g1 h1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 2: `f = g · h`, `g` of degree 1. -/
def g2 : List Nat := [0x24b82ddfcacb39d5771c63482d0c32c0758b88b382a98fb580ba21e7d266cd2]

def h2 : List Nat := [0x172b36fc9b16bf69818e692f4b434d7c55d92eed905d68ee8dd53109e96e614a, 0x907d8580bda85c93f96545cb3cec724290b31f2f71ba4d42919ffd8181954f3, 0x1b8590aef642e752ca2be47d68d9331b83c7b43f1398a7cc969accc425c1f6a4]

theorem fail2 : ¬MinpolyCondition 4 (partialMatrix 4 (rowOf 2)) :=
  not_minpolyCondition 4 _ (fOf g2 h2) g2 h2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 3: `f = g · h`, `g` of degree 2. -/
def g3 : List Nat := [0x19f2588b97232be1c8f8be688f7a555042d4ef02ed20a498b21022b69fcb1761, 0xf22685b7705af29f03d48758b825273d61f1c758627d2e1cf6aab285e3c8749]

def h3 : List Nat := [0x2f87dc7d92c08d2d8695d389864527f58955dfc2103668149cf1dc1cae9f11ee, 0x22fb67f8b0e0eaf8c2d97d546f83cc37788ef0770e52c23689a53c0205b7466f]

theorem fail3 : ¬MinpolyCondition 4 (partialMatrix 4 (rowOf 3)) :=
  not_minpolyCondition 4 _ (fOf g3 h3) g3 h3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Draw 4 -/

/-- The characteristic polynomial of draw 4's matrix, without its leading `1`. -/
def fl : List Nat := [0x2cb1b2929bd625ac9649efb55c2667b9125dadf6e955529b8333100d68bcb912, 0x3825b14da9f5ca9a5a48edc60a5f15fd1e03b5b57810ad0838f0b80ea2d6a9f, 0x87f9b15a6f490f583881cbe240ede1504f2b84efe62d0e03fb21a55dcf457cf, 0x2143cd53c81e700289af101bb1bd7a7ca483c451daed4996a62dc016c9c6e66c]

theorem mat : matOk 4 (rowOf 4) fl = true := by decide +kernel

/-- The bits of `P` after its leading one, most significant first (1 part). -/
def bits0 : List Bool := [true, false, false, false, false, false, true, true, false, false, true, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, true, false, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]

def bits : List Bool := bits0

/-- `x ^ e mod f` after each part of the square-and-multiply. -/
def sq1 : List Nat := [0x1972aacf0cf9fa6b826d6b3bfe27729bd6fde71e575db350ac9157a15e6446ab, 0x361d33579cd0aab476aa136bc4473ea7293e189755ba4c85074bfb6dd7016d0, 0x721313d9b6ad65127b288aa6112728c6fd92fdf4bdbf8e12d87e6d0ba62fdf4, 0x1f028bdadb472b4d2dea78bdc146c387b9087976a38365ab5022ae25be024b63]

theorem run0 : sqRun fl bits0 (xL 4) = sq1 := by decide +kernel

theorem run : sqRun fl bits (xL 4) = sq1 :=
  run0

/-- `x ^ (P ^ d) mod f`, d = 1 .. 2. -/
def H2 : List Nat := [0x12e338de91e680b8ce488bf37147c67a3e5b0e81691b7935dd738458dcfd6d03, 0x2db56a042a9c56bf57f4da398f9cef5ed69fb118740e5d4a1219e8b18ad48427, 0x27be119113dce3da9928017832ae29ddcf59ba79280e7209f0ca980b89cfd2c7, 0x2e9b129212e48609c6390b48aba81eef2e7ca78b6b0d99bda134562e99ef44d3]

def hs : List (List Nat) := [sq1, H2]

theorem comp2 : compMod fl sq1 sq1 = H2 := by decide +kernel

theorem frob : frobOk fl bits hs :=
  ⟨by decide +kernel, by decide +kernel, _, _, rfl, run,
    (frobChain_cons_of _ _ _ _ _ comp2
    rfl)⟩

/-- Bezout identities `u · f + w · (x ^ (P ^ d) - x) = 1`, d = 1 .. 2. -/
def bez : List (List Nat × List Nat) :=
  [([0x22ac204c9adc5ac6c1ac02b2f3818bd81cd28710a92e1ba64a3e522818b2f4f5, 0x18ca45787b7e6b5f72f33855ffac61150bc803e977e5d49b055b10fe7657089b, 0x149eb33582a32c37a5722ac9b75248763a9ca9bac4df3739e05d890933bc28ba], [0x139c769cd3d467a8c68dfe1f718f8a1b345c3a3cd7b5a8ca8d15eb39040819d8, 0x124f936a60596b856ea82d78e2b207a80789073df3b553aa5e42494ba7c05779, 0x2b7d91d8f05dc15a36684afdf426ea67e07205e71e15a95f59ef8585985aff3a, 0x61910b5686bdb1c574c0e8cd703c3efac7630f20d7931ddc5277dc9d92e43f4]),
   ([0x2fef9f28bbff37f214ec2b0bf7fe1565e06b1cef0883dd9a1d18f675d0d39474, 0x1f29a199147a9eb7ccfde74555eb28dd2c9050d7e54d8cf48b0c1f314aaf5585, 0x19da247fe5e94f6b38a2df9418d0a367a9fb0dfa7ede0c61980940fb23c8ec25], [0x2cfb850bc9822bebe0ead5b31e7828461b2768fc371ab3d383c2149f808505e2, 0xa519a24642afbc7d33e095f7f63aa19cf9e2def8ab8cfc1a5e8c6e0000b574f, 0x9e004fde1398d8d0401d1a2f1c8e1df43cbbc41c03959ab67350bb8566fe467, 0x2e8e9ed3effddc27f3d8265bd303d83e5c88e66238d752d77450a976a98c7f22])]

theorem bezout : bezOk fl hs bez = true := by decide +kernel

/-- The maximal proper divisors of 4. -/
def ms : List Nat := [2]

def W2_1 : List Nat := [0x2fc1c58d41f6e3436f120854df51de1e78273aa0ccac21fa4c2741143b58df8f, 0x1be6591a6d5c3390a0b78b769b193b179a641d1af47cc021fdaa80e99430f021, 0x14343a744af4609181a6f2fdb417a6e32fc19e3fb1051b75fc302b5b22b3f65c, 0x14f04798dc027344257eae38642ce13936a3c9f92375c7e116d79f235595c004]

theorem pw2_0 : powsNe fl H2 8 H2 (mulXs fl 0 (xL 4)) W2_1 = true := by
  decide +kernel

theorem pw2 : powsNe fl H2 8 H2 (xL 4) W2_1 = true :=
  pw2_0

theorem degs : degOk fl hs ms :=
  ⟨by decide +kernel, by
    intro m hm
    simp only [ms, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl
    · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, _, pw2⟩⟩

theorem pass : MinpolyCondition 4 (partialMatrix 4 (rowOf 4)) :=
  minpolyCondition_of_cert 4 _ fl bits hs bez ms (by decide +kernel) mat frob bezout degs

/-- Draw 4 is the first draw whose matrix passes the script's check. -/
theorem firstPass : FirstPass 4 8 56 4 :=
  ⟨fun j hj => ⟨_, drawRow_t4 j (by omega), by
    match j, hj with
    | 0, _ => exact fail0
    | 1, _ => exact fail1
    | 2, _ => exact fail2
    | 3, _ => exact fail3
    | _ + 4, h => omega⟩,
   ⟨_, drawRow_t4 4 le_rfl, pass⟩⟩

end Poseidon2.Spec.MinpolyCheck.T4
