import Poseidon2.Checker.Check
import Poseidon2.Checker.Valuation
import Poseidon2.Evm.Eip8024
import Poseidon2.Spec.Interface

/-!
# Soundness of the checker: the statements

`CheckerSound` is the proposition that the checker is sound against the EVM semantics
(EVMLean with EIP-8024, `Evm/Eip8024.lean`): if `checkCase` accepts a bytecode for a case, then
every call that satisfies the case's facts, run by `Eip8024.Ξ` with any gas, either runs out of
gas (`OutOfGass`, or EVMLean's step budget `OutOfFuel`, which `Ξ` sets to the gas plus one) or
ends exactly as the case expects: returns the spec's words, or reverts with empty data.

`CheckerTotal` adds the gas: the checker also computes the gas `G` its run of the case uses
(`checkCaseGas`), and every such call given at least `G` gas ends exactly as the case expects,
with `G` gas used, while every such call given less than `G` runs out of gas. So `G` is the
exact gas of the call, and running out of gas is not a way to satisfy the statement.

Both are proven in `Evm/Final.lean` (`checkerSound`, `checkerTotal`), from the per-opcode
simulations of `Evm/Sim.lean`, `Evm/MemSim.lean`, `Evm/Control.lean`, the run of `Evm/Run.lean`
and the valuation of `Checker/Valuation.lean`. `Theorems.lean` instantiates them for every
contract kind.

The case's input words must be 256-bit words (`t.eval e < 2^256`): the checker reads an input
word pinned by a fact as that constant, which is only the word's value for a value below
`2^256` (every case of `Check.lean` reads calldata words or the capacity word, all below
`2^256`).
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
  | .words ws => .ret (encodeWords (ws.map (· % P)))
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

/-- An `Eip8024.Ξ` result that is exactly the interface outcome, with `gl` gas left: a success
returning the outcome's bytes, or a revert with them. Running out of gas, any other exception, or
other bytes or gas falsify it. -/
def Exact (gl : Nat) : Except EVM.ExecutionException
    (ExecutionResult (AccountMap × UInt256 × Substate)) → Outcome → Prop
  | .ok (.success (_, g, _) o), .ret out => o.data.toList = out ∧ g.toNat = gl
  | .ok (.revert g o), .revert out => o.data.toList = out ∧ g.toNat = gl
  | _, _ => False

theorem Exact.matches {gl : Nat} {r : Except EVM.ExecutionException
    (ExecutionResult (AccountMap × UInt256 × Substate))} {o : Outcome} (h : Exact gl r o) :
    Matches r o := by
  match r, o, h with
  | .ok (.success (_, _, _) _), .ret _, h => exact h.1
  | .ok (.revert _ _), .revert _, h => exact h.1

/-- **The soundness proposition** (proven in `Evm/Final.lean`): an accepted case is the EVM's
behaviour. -/
def CheckerSound : Prop :=
  ∀ (bs : List Nat) (cs : Case), bs.all (· < 256) = true → checkCase (Code.ofBytes bs) cs = true →
    ∀ (cd : List UInt8) (v : Nat), cd.length < 2 ^ 64 → v < W → FactsHold ⟨cd, v⟩ cs.facts →
      (∀ t ∈ cs.expect.inputs, t.eval ⟨cd, v⟩ < W) →
      ∀ (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv),
        env ⟨(bs.map UInt8.ofNat).toArray⟩ cd v I →
        Matches (Eip8024.Ξ σ σ₀ g A I) (outcome ⟨cd, v⟩ cs.expect)

/-- **Total correctness** (proven in `Evm/Final.lean`): a case accepted with gas `G` is the
EVM's behaviour for every call given at least `G` gas, which uses exactly `G`; a call given less
runs out of gas. -/
def CheckerTotal : Prop :=
  ∀ (bs : List Nat) (cs : Case) (G : Nat), bs.all (· < 256) = true →
    checkCaseGas (Code.ofBytes bs) cs G = true →
    ∀ (cd : List UInt8) (v : Nat), cd.length < 2 ^ 64 → v < W → FactsHold ⟨cd, v⟩ cs.facts →
      (∀ t ∈ cs.expect.inputs, t.eval ⟨cd, v⟩ < W) →
      ∀ (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv),
        env ⟨(bs.map UInt8.ofNat).toArray⟩ cd v I →
        (G ≤ g.toNat → Exact (g.toNat - G) (Eip8024.Ξ σ σ₀ g A I) (outcome ⟨cd, v⟩ cs.expect)) ∧
        (g.toNat < G → Eip8024.Ξ σ σ₀ g A I = .error .OutOfGass)

end Poseidon2.Soundness
