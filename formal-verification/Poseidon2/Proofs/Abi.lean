import Poseidon2.Theorems
import Poseidon2.Spec.Abi
import Poseidon2.Proofs.Huff.Amsterdam.T4
import Poseidon2.Proofs.Huff.Osaka.T4
import Poseidon2.Proofs.Yul.OptimizerOff.T4
import Poseidon2.Proofs.Yul.Runs200.T4
import Poseidon2.Proofs.Yul.Runs1000000.T4
import Poseidon2.Proofs.Yul.ViaIrRuns1000000.T4
import Poseidon2.Proofs.Deployed.YulV2
import Poseidon2.Proofs.Deployed.HuffV2

/-!
# The t = 4 hash contracts on ABI calldata

For each of the eight t = 4 hash bytecodes (Huff for Amsterdam and Osaka, `Poseidon2Yul_BN254` at
the three legacy optimizer settings and with via-IR, the deployed Yul v2 and Huff v2), `abi`: a
call with ABI calldata of `hash_1` / `hash_2` / `hash_3` (any 4 selector bytes, then 1 to 3 input
words below `2^256`), with call value 0 for the Yul contracts and any call value for the Huff
ones, returns the Barretenberg / Noir sponge `Poseidon2::hash` (`Spec/Sponge.lean`, `sponge`) of
the inputs read modulo `P`, with exactly the gas listed, and runs out of gas with less.
`abiCancun` is the same of EVMLean's Cancun `Ξ`, for the seven that never run DUPN / SWAPN
(`totalCancun`).

Each is the artifact's `total` (or `totalCancun`) on that calldata, with the case fixed by the
calldata size (`Theorems.huffHash_abi_total`, `huffHashXor_abi_total`, `yulHash_abi_total`,
`hashV2_abi_total`) and `hashWords` read as the sponge (`Spec/Abi.lean`, `hashWords_eq_sponge`).
The theorems are declared in each artifact's namespace, next to its `total`.
-/

namespace Poseidon2.Proofs.Huff.Amsterdam.T4

open Poseidon2.Checker Poseidon2.Spec

/-- `huff/amsterdam/t4` on ABI calldata of 1 to 3 words, any call value: the sponge of the
inputs, with 11837, 11879, 11919 gas for 1, 2, 3 inputs. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
    (v : Nat) (hv : v < W)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Huff.Amsterdam.T4.artifact
      (sel ++ Interface.encodeWords ws) v I) :
    Theorems.ExactGas ([11837, 11879, 11919].getD (ws.length - 1) 0) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.huffHash_abi_total _ gas sel hsel ws hws h1 h3 v g.toNat
    (total _ v hcd hv σ σ₀ g A I hI)
  have hg : gas.getD (2 * ws.length - 1) 0 = [11837, 11879, 11919].getD (ws.length - 1) 0 := by
    rcases (show ws.length = 1 ∨ ws.length = 2 ∨ ws.length = 3 by omega) with hn | hn | hn <;>
      rw [hn] <;> rfl
  rwa [hg, Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Huff.Amsterdam.T4

namespace Poseidon2.Proofs.Huff.Osaka.T4

open Poseidon2.Checker Poseidon2.Spec

/-- `huff/osaka/t4` on ABI calldata of 1 to 3 words, any call value: the sponge of the
inputs, with 11861, 11880, 11943 gas for 1, 2, 3 inputs. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
    (v : Nat) (hv : v < W)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Huff.Osaka.T4.artifact
      (sel ++ Interface.encodeWords ws) v I) :
    Theorems.ExactGas ([11861, 11880, 11943].getD (ws.length - 1) 0) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.huffHashXor_abi_total _ _ _ _ (by decide) gas sel hsel ws hws h1 h3 v
    g.toNat (total _ v hcd hv σ σ₀ g A I hI)
  have hg : gas.getD ([1, 5, 3].getD (ws.length - 1) 0) 0 =
      [11861, 11880, 11943].getD (ws.length - 1) 0 := by
    rcases (show ws.length = 1 ∨ ws.length = 2 ∨ ws.length = 3 by omega) with hn | hn | hn <;>
      rw [hn] <;> rfl
  rwa [hg, Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

/-- `abi` of EVMLean's Cancun `Ξ`. -/
theorem abiCancun (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
    (v : Nat) (hv : v < W)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Huff.Osaka.T4.artifact
      (sel ++ Interface.encodeWords ws) v I) :
    Theorems.ExactGas ([11861, 11880, 11943].getD (ws.length - 1) 0) g.toNat
      (Ethereum.EVM.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.huffHashXor_abi_total _ _ _ _ (by decide) gas sel hsel ws hws h1 h3 v
    g.toNat (totalCancun _ v hcd hv σ σ₀ g A I hI)
  have hg : gas.getD ([1, 5, 3].getD (ws.length - 1) 0) 0 =
      [11861, 11880, 11943].getD (ws.length - 1) 0 := by
    rcases (show ws.length = 1 ∨ ws.length = 2 ∨ ws.length = 3 by omega) with hn | hn | hn <;>
      rw [hn] <;> rfl
  rwa [hg, Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Huff.Osaka.T4

namespace Poseidon2.Proofs.Yul.OptimizerOff.T4

open Poseidon2.Checker Poseidon2.Spec

/-- `yul/optimizeroff/t4` on ABI calldata of 1 to 3 words, call value 0: the sponge of the
inputs, with 15348 gas. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.OptimizerOff.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (15348) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (total _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

/-- `abi` of EVMLean's Cancun `Ξ`. -/
theorem abiCancun (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.OptimizerOff.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (15348) g.toNat
      (Ethereum.EVM.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (totalCancun _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Yul.OptimizerOff.T4

namespace Poseidon2.Proofs.Yul.Runs200.T4

open Poseidon2.Checker Poseidon2.Spec

/-- `yul/runs200/t4` on ABI calldata of 1 to 3 words, call value 0: the sponge of the
inputs, with 15159 gas. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.Runs200.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (15159) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (total _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

/-- `abi` of EVMLean's Cancun `Ξ`. -/
theorem abiCancun (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.Runs200.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (15159) g.toNat
      (Ethereum.EVM.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (totalCancun _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Yul.Runs200.T4

namespace Poseidon2.Proofs.Yul.Runs1000000.T4

open Poseidon2.Checker Poseidon2.Spec

/-- `yul/runs1000000/t4` on ABI calldata of 1 to 3 words, call value 0: the sponge of the
inputs, with 15153 gas. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.Runs1000000.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (15153) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (total _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

/-- `abi` of EVMLean's Cancun `Ξ`. -/
theorem abiCancun (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.Runs1000000.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (15153) g.toNat
      (Ethereum.EVM.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (totalCancun _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Yul.Runs1000000.T4

namespace Poseidon2.Proofs.Yul.ViaIrRuns1000000.T4

open Poseidon2.Checker Poseidon2.Spec

/-- `yul/viairruns1000000/t4` on ABI calldata of 1 to 3 words, call value 0: the sponge of the
inputs, with 13904 gas. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.ViaIrRuns1000000.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (13904) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (total _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

/-- `abi` of EVMLean's Cancun `Ξ`. -/
theorem abiCancun (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Yul.ViaIrRuns1000000.T4.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (13904) g.toNat
      (Ethereum.EVM.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (totalCancun _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Yul.ViaIrRuns1000000.T4

namespace Poseidon2.Proofs.Deployed.YulV2

open Poseidon2.Checker Poseidon2.Spec

/-- `deployed/yulv2` on ABI calldata of 1 to 3 words, call value 0: the sponge of the
inputs, with 19639 gas. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Deployed.YulV2.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (19639) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (total _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

/-- `abi` of EVMLean's Cancun `Ξ`. -/
theorem abiCancun (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
   
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Deployed.YulV2.artifact
      (sel ++ Interface.encodeWords ws) 0 I) :
    Theorems.ExactGas (19639) g.toNat
      (Ethereum.EVM.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.yulHash_abi_total _ rfl gas sel hsel ws hws h1 h3 g.toNat
    (totalCancun _ 0 hcd (by decide) σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Deployed.YulV2

namespace Poseidon2.Proofs.Deployed.HuffV2

open Poseidon2.Checker Poseidon2.Spec

/-- `deployed/huffv2` on ABI calldata of 1 to 3 words, any call value: the sponge of the
inputs, with 14869 gas. -/
theorem abi (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
    (v : Nat) (hv : v < W)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Deployed.HuffV2.artifact
      (sel ++ Interface.encodeWords ws) v I) :
    Theorems.ExactGas (14869) g.toNat
      (Evm.Eip8024.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.hashV2_abi_total _ rfl gas sel hsel ws hws h1 h3 v g.toNat
    (total _ v hcd hv σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

/-- `abi` of EVMLean's Cancun `Ξ`. -/
theorem abiCancun (sel : List UInt8) (hsel : sel.length = 4) (ws : List Nat)
    (hws : ∀ w ∈ ws, w < 2 ^ 256) (h1 : 1 ≤ ws.length) (h3 : ws.length ≤ 3)
    (v : Nat) (hv : v < W)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hI : Theorems.Runs Poseidon2.Bytecode.Deployed.HuffV2.artifact
      (sel ++ Interface.encodeWords ws) v I) :
    Theorems.ExactGas (14869) g.toNat
      (Ethereum.EVM.Ξ σ σ₀ g A I)
      (.ret (Interface.encodeWords
        [(sponge Constants.T4.params (ws.map fun w => (w : F))).val])) := by
  have hcd := Theorems.abi_length_lt sel hsel ws h3
  have h := Theorems.hashV2_abi_total _ rfl gas sel hsel ws hws h1 h3 v g.toNat
    (totalCancun _ v hcd hv σ σ₀ g A I hI)
  rwa [Interface.hashWords_eq_sponge _ rfl ws h1 h3] at h

end Poseidon2.Proofs.Deployed.HuffV2
