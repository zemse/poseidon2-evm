import Poseidon2.Checker.Check
import Poseidon2.Evm.Eip8024
import Poseidon2.Spec.Interface

/-!
# Soundness of the checker: the statement

`CheckerSound` is the proposition that the checker is sound against the EVM semantics
(EVMLean with EIP-8024, `Evm/Eip8024.lean`): if `checkCase` accepts a bytecode for a case, then
every call that satisfies the case's facts, run by `Eip8024.Ξ` with any gas, either runs out of
gas (`OutOfGass`, or EVMLean's step budget `OutOfFuel`, which `Ξ` sets to the gas plus one) or
ends exactly as the case expects: returns the spec's words, or reverts with empty data.

It is **not proven here**. It is a definition, a `Prop`, so nothing in this library assumes
it: `Theorems.lean` states every result as `CheckerSound → ...`. What is proven about it is
listed in `formal-verification/README.md`; the remaining work is a simulation proof of
`Checker.run` against `Eip8024.X` (one lemma per opcode the checker supports).

Partial correctness only: the statement allows running out of gas, and says nothing about the
gas a call uses.
-/

namespace Poseidon2.Soundness

open Ethereum Poseidon2.Spec Poseidon2.Checker Poseidon2.Spec.Interface Poseidon2.Evm

/-- The facts of a case hold for a call. -/
def FactsHold (e : Env) (fs : Facts) : Prop :=
  ∀ f ∈ fs, f.2.1 ≤ f.1.eval e ∧ f.1.eval e ≤ f.2.2

/-- What a case's expectation means for a call: the interface outcome. -/
def outcome (e : Env) : Expect → Outcome
  | .perm c ins => .ret (encodeWords (permutationWords c (ins.map (·.eval e))))
  | .permHead c ins => .ret (encodeWords [(permutationWords c (ins.map (·.eval e))).headD 0])
  | .hash c ins => .ret (encodeWords [hashWords c (ins.map (·.eval e))])
  | .revertEmpty => .revert []

/-- An execution environment running `code` on calldata `cd` with call value `v`. -/
def env (code : ByteArray) (cd : List UInt8) (v : Nat) (I : ExecutionEnv) : Prop :=
  I.code = code ∧ I.calldata.data.toList = cd ∧ I.weiValue = .ofNat v

/-- How an `Eip8024.Ξ` result relates to an interface outcome: out of gas, or that outcome. -/
def Matches : Except EVM.ExecutionException
    (ExecutionResult (AccountMap × UInt256 × Substate)) → Outcome → Prop
  | .error .OutOfGass, _ => True
  | .error .OutOfFuel, _ => True
  | .ok (.success _ o), .ret out => o.data.toList = out
  | .ok (.revert _ o), .revert out => o.data.toList = out
  | _, _ => False

/-- **The soundness proposition** (not proven): an accepted case is the EVM's behaviour. -/
def CheckerSound : Prop :=
  ∀ (bs : List Nat) (cs : Case), bs.all (· < 256) = true → checkCase (Code.ofBytes bs) cs = true →
    ∀ (cd : List UInt8) (v : Nat), cd.length < 2 ^ 64 → v < W → FactsHold ⟨cd, v⟩ cs.facts →
      ∀ (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv),
        env ⟨(bs.map UInt8.ofNat).toArray⟩ cd v I →
        Matches (Eip8024.Ξ σ σ₀ g A I) (outcome ⟨cd, v⟩ cs.expect)

end Poseidon2.Soundness
