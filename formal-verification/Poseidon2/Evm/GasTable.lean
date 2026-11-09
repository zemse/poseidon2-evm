import Ethereum.Semantics
import Poseidon2.Evm.ForkData

/-!
# EVMLean's gas on every opcode byte against execution-specs (Cancun)

`Forks.lean` checks the static gas of the opcodes the checker accepts. This file checks EVMLean's
`C'` on all 256 bytes, so no opcode EVMLean defines is missing from its gas groups (which would
make it cost 0): `all_bytes` states that EVMLean decodes a byte as an operation other than
`INVALID` exactly when `spec` defines it, which are Cancun's 148 bytes (`spec_defined`), and
that `C'` charges for it what `spec` says, in `st0`: every stack argument 0, empty access sets
(cold accounts and slots), one empty account and gas 0, so the dynamic parts are fixed (`EXP`
with exponent 0, `KECCAK256` and the copies with size 0, `CALL` with value 0, `SSTORE` writing
the current value). Memory expansion is charged apart from `C'` (`memoryExpansionCost`) and is
not part of `spec`.

`spec` transcribes ethereum/execution-specs @ `636b5f1757b1c5eeb5856030ac9a8058cadc4b70`,
`src/ethereum/forks/cancun/vm/{gas.py,instructions/*.py}`. The transcription is trusted.
-/

namespace Poseidon2.Evm.GasTable

open Ethereum Ethereum.EVM

/-- Cancun's gas for opcode byte `b` in `st0`; `none`: undefined in Cancun. -/
def spec (b : Nat) : Option Nat :=
  if b = 0x00 then some 0
  else if b ∈ [0x01, 0x03] then some 3
  else if b ∈ [0x02, 0x04, 0x05, 0x06, 0x07, 0x0b] then some 5
  else if b ∈ [0x08, 0x09] then some 8
  else if b = 0x0a then some 10           -- EXP, exponent 0
  else if 0x10 ≤ b ∧ b ≤ 0x1d then some 3
  else if b = 0x20 then some 30           -- KECCAK256, size 0
  else if b ∈ [0x30, 0x32, 0x33, 0x34, 0x36, 0x38, 0x3a, 0x3d] then some 2
  else if b ∈ [0x31, 0x3b, 0x3c, 0x3f] then some 2600   -- cold account
  else if b ∈ [0x35, 0x37, 0x39, 0x3e] then some 3
  else if b = 0x40 then some 20
  else if b ∈ [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x48, 0x4a] then some 2
  else if b = 0x47 then some 5
  else if b = 0x49 then some 3
  else if b = 0x50 then some 2
  else if b ∈ [0x51, 0x52, 0x53] then some 3
  else if b = 0x54 then some 2100          -- cold SLOAD
  else if b = 0x55 then some 2200          -- cold slot, writing the current value
  else if b = 0x56 then some 8
  else if b = 0x57 then some 10
  else if b ∈ [0x58, 0x59, 0x5a] then some 2
  else if b = 0x5b then some 1
  else if b ∈ [0x5c, 0x5d] then some 100
  else if b = 0x5e then some 3
  else if b = 0x5f then some 2
  else if 0x60 ≤ b ∧ b ≤ 0x9f then some 3
  else if 0xa0 ≤ b ∧ b ≤ 0xa4 then some (375 + 375 * (b - 0xa0))
  else if b ∈ [0xf0, 0xf5] then some 32000
  else if b ∈ [0xf1, 0xf2, 0xf4, 0xfa] then some 2600   -- cold, gas 0, value 0
  else if b ∈ [0xf3, 0xfd] then some 0
  else if b = 0xff then some 7600          -- 5000 + cold 2600
  else none

/-- Every stack argument 0, empty access sets, one empty account, gas 0. -/
def st0 : State :=
  { (default : State) with
      accountMap := (default : State).accountMap.insert default default
      machineState.stack := List.replicate 7 (UInt256.ofNat 0) }

/-- EVMLean's gas for opcode byte `b` in `st0`; `none`: decoded as `INVALID` or not at all. -/
def lean (b : Nat) : Option Nat :=
  match parseInstr (UInt8.ofNat b) with
  | none => none
  | some .INVALID => none
  | some op => some (C' st0 op)

theorem all_bytes : (List.range 256).all (fun b => spec b == lean b) = true := by decide +kernel

/-- The bytes `spec` defines are the ones `ForkData.lean` transcribes as Cancun's (`cancunDefined`). -/
theorem spec_defined :
    (List.range 256).filter (fun b => (spec b).isSome) = Forks.cancunDefined := by decide +kernel

end Poseidon2.Evm.GasTable
