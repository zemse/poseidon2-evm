-- Calls every exported bytecode through the EVM semantics the theorems are about
-- (`Evm.Eip8024.Ξ`, EVMLean with EIP-8024), with `#eval` (compiled code, not the kernel, so
-- nothing here is a proof). It shows that the theorems' hypotheses are met by real calls and
-- that their conclusion is not met only by running out of gas: with enough gas each call
-- returns (or reverts) exactly as `Spec/Interface.lean` says, and with 100 gas it runs out.
-- Run from formal-verification/ after `lake build`:
--   lake env lean scripts/Call.lean
-- Optional filter: ONLY=<substring of the artifact name>.
import Poseidon2.Bytecode.All
import Poseidon2.Evm.Eip8024
import Poseidon2.Spec.Interface
import Poseidon2.Spec.Constants.T2
import Poseidon2.Spec.Constants.T3
import Poseidon2.Spec.Constants.T4
import Poseidon2.Spec.Constants.T8
import Poseidon2.Spec.Constants.T12
import Poseidon2.Spec.Constants.T16
import Poseidon2.Spec.Constants.T20
import Poseidon2.Spec.Constants.T24
import Poseidon2.Spec.Constants.T28

open Ethereum Poseidon2.Spec Poseidon2.Spec.Interface Poseidon2.Bytecode Poseidon2.Evm

def paramsOf : Nat → Params
  | 2 => Constants.T2.params
  | 3 => Constants.T3.params
  | 4 => Constants.T4.params
  | 8 => Constants.T8.params
  | 12 => Constants.T12.params
  | 16 => Constants.T16.params
  | 20 => Constants.T20.params
  | 24 => Constants.T24.params
  | _ => Constants.T28.params

/-- The calldata of the call: `n` words (one above `P`), after a selector if `sel`. -/
def calldata (sel : Option Nat) (n : Nat) : List UInt8 :=
  let ws := (List.range n).map fun i => if i = 0 then P + 7 else 1000 * (i + 1)
  (match sel with
   | some s => (Interface.wordBytes s).drop 28
   | none => []) ++ encodeWords ws

/-- The call and what the interface says it returns. -/
def callOf (a : Artifact) : Option (List UInt8 × Nat × Outcome) :=
  let c := paramsOf a.t
  match a.kind with
  | .huffPerm => let cd := calldata none a.t; some (cd, 0, huffPerm c cd)
  | .huffHash => let cd := calldata (some 0) 3; some (cd, 0, huffHash c cd)
  | .yulHash => let cd := calldata (some 0) 3; some (cd, 0, yulHash c cd 0)
  | .yulPerm =>
    let cd := calldata (some (permuteSelector a.t)) a.t
    some (cd, 0, yulPerm c (permuteSelector a.t) cd 0)
  | .hashV2 => let cd := calldata (some 0) 3; some (cd, 0, hashV2 c cd)
  | .huffPart _ _ => none

/-- The call frame `Theorems.Runs a cd v` describes. -/
def frame (a : Artifact) (cd : List UInt8) (v : Nat) : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := a.code, calldata := ⟨cd.toArray⟩, weiValue := .ofNat v }

def describe :
    Except EVM.ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate)) →
    Outcome → String
  | .ok (.success r o), .ret out =>
    s!"{if o.data.toList == out then "returns the spec" else "WRONG OUTPUT"}, \
      {o.size} bytes, gas left {r.2.1.toNat}"
  | .ok (.revert _ o), .revert out =>
    s!"{if o.data.toList == out then "reverts as the spec" else "WRONG REVERT"}"
  | .ok _, _ => "WRONG OUTCOME"
  | .error .OutOfGass, _ => "out of gas"
  | .error .OutOfFuel, _ => "out of fuel"
  | .error _, _ => "OTHER ERROR"

#eval show IO Unit from do
  let only := (← IO.getEnv "ONLY").getD ""
  for a in all do
    unless only.isEmpty || (a.name.splitOn only).length > 1 do continue
    match callOf a with
    | none => continue
    | some (cd, v, out) =>
      let I := frame a cd v
      let big := Eip8024.Ξ default default (.ofNat 30000000) default I
      let small := Eip8024.Ξ default default (.ofNat 100) default I
      IO.println s!"{a.name}: gas 3e7: {describe big out}; gas 100: {describe small out}"
