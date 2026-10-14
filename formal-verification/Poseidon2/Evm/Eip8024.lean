import Ethereum.Semantics

/-!
# EIP-8024 DUPN / SWAPN / EXCHANGE on top of EVMLean

EVMLean (Cancun) decodes `0xe6`, `0xe7` and `0xe8` as `INVALID`. This file adds EIP-8024
(https://eips.ethereum.org/EIPS/eip-8024) without editing EVMLean: `Xstep` runs DUPN, SWAPN and
EXCHANGE itself and hands every other instruction to EVMLean's `EVM.Xstep`; `X` and `Ξ` iterate
it exactly as EVMLean's `EVM.X` and `EVM.Ξ` iterate theirs. The contracts use DUPN and SWAPN
only; EXCHANGE is here so that the overlay is the whole EIP (the checker never runs it).

From the EIP (ethereum/EIPs `9d27a4f`, Last Call) and execution-specs `forks/amsterdam`
(`1689800`, `vm/instructions/stack.py`, `vm/stack.py`):
* the three opcodes take one immediate byte `x = code[pc + 1]` (`0` past the end of the code);
* DUPN / SWAPN: `n = decode_single(x) = (x + 145) mod 256`, `17 ≤ n ≤ 235`; `90 < x < 128` is
  an exceptional halt (so the immediate is never `JUMPDEST` or a `PUSH`);
* EXCHANGE: `(n, m) = decode_pair(x)`, `1 ≤ n < m ≤ 30 - n`; `81 < x < 128` is an exceptional
  halt;
* `DUPN` pushes a copy of the `n`th stack item (1-based), `SWAPN` swaps the top with the
  `n + 1`th item, `EXCHANGE` swaps the `n + 1`th and the `m + 1`th; all cost 3 gas
  (`G_verylow`) and advance `pc` by 2;
* jump destination analysis does not change. EVMLean's `D_J` already steps over `0xe6` .. `0xe8`
  as one-byte `INVALID` instructions and then reads the immediate as an opcode, which the
  immediate ranges keep from being `JUMPDEST` or `PUSH`, so `D_J` is the EIP's.

The EIP charges the gas first, then checks the immediate, then the stack; here an invalid
immediate halts before the gas, and the stack checks come before the gas. Each is an exceptional
halt that EVMLean's callers of `Ξ` treat alike (they match on `.error _`), so only the name of the
exception can differ, and on a run the checker accepts none of them occurs.

The encoding matches `src/bn254/huff/Eip8024.huff` (`DUP17` is `e6 80`, `DUP235` is `e6 5a`)
and revm 43 (`decode_single`, `decode_pair`, `dupn`, `swapn`, `exchange` in `revm-interpreter`),
which the repository's tests run.
-/

namespace Poseidon2.Evm.Eip8024

open Ethereum

/-- EIP-8024 `decode_single`, `none` for the invalid range `90 < x < 128`. -/
def decodeSingle (x : Nat) : Option Nat :=
  if x ≤ 90 ∨ 128 ≤ x then some ((x + 145) % 256) else none

/-- EIP-8024 `decode_pair`, `none` for the invalid range `81 < x < 128`. -/
def decodePair (x : Nat) : Option (Nat × Nat) :=
  if x ≤ 81 ∨ 128 ≤ x then
    let k := x ^^^ 143
    let q := k / 16
    let r := k % 16
    some (if q < r then (q + 1, r + 1) else (r + 1, 29 - q))
  else none

/-- The immediate byte: `code[pc + 1]`, `0` past the end. -/
def immediate (code : ByteArray) (pc : Nat) : Nat :=
  ((code.get? (pc + 1)).getD 0).toNat

/-- The three opcodes. -/
inductive Op where
  | dupn (n : Nat)
  | swapn (n : Nat)
  | exchange (n m : Nat)
  deriving DecidableEq, Repr

/-- `none` when the byte at `pc` is not DUPN / SWAPN / EXCHANGE; `some none` for an invalid
immediate. -/
def decode (code : ByteArray) (pc : Nat) : Option (Option Op) :=
  match code.get? pc with
  | some 0xe6 => some ((decodeSingle (immediate code pc)).map .dupn)
  | some 0xe7 => some ((decodeSingle (immediate code pc)).map .swapn)
  | some 0xe8 => some ((decodePair (immediate code pc)).map fun (n, m) => .exchange n m)
  | _ => none

/-- The stack with its items at (0-based) positions `n` and `m` swapped. -/
def exchangeList (n m : Nat) (l : List UInt256) : List UInt256 :=
  (l.set n (l.getD m default)).set m (l.getD n default)

/-- One DUPN / SWAPN / EXCHANGE: the stack checks, 3 gas, the stack change (EVMLean's `dup` /
`swap`, which take any depth, and `exchangeList`) and `pc + 2`. -/
def exec (op : Op) (s : State) : Except EVM.ExecutionException State :=
  let stk := s.machineState.stack
  let (need, grow) := match op with
    | .dupn n => (n, 1)
    | .swapn n => (n + 1, 0)
    | .exchange _ m => (m + 1, 0)
  if stk.length < need then .error .StackUnderflow
  else if stk.length + grow > 1024 then .error .StackOverflow
  else if s.machineState.gasAvailable.toNat < GasConstants.Gverylow then .error .OutOfGass
  else
    let s := { s with machineState.execLength := s.machineState.execLength + 1
                      machineState.gasAvailable :=
                        s.machineState.gasAvailable.subNat GasConstants.Gverylow }
    let r := match op with
      | .dupn n => EVM.dup n s
      | .swapn n => EVM.swap n s
      | .exchange n m => .ok (s.replaceStackAndIncrPC (exchangeList n m s.machineState.stack))
    r.map (·.incrPC)

/-- EVMLean's `EVM.Xstep` with DUPN / SWAPN / EXCHANGE. -/
def Xstep (validJumps : Array UInt256) (s : State) :
    Except EVM.ExecutionException (State × Option (EVM.HaltCause × ByteArray)) :=
  match decode s.executionEnv.code s.machineState.pc.toNat with
  | none => EVM.Xstep validJumps s
  | some none => .error .InvalidInstruction
  | some (some op) => (exec op s).map fun s' => (s', none)

/-- EVMLean's `EVM.X` over `Xstep`. -/
def X : ℕ → Array UInt256 → State → Except EVM.ExecutionException (ExecutionResult State)
  | 0, _, _ => .error .OutOfFuel
  | f + 1, validJumps, s => do
    let ⟨s', ret⟩ ← Xstep validJumps s
    match ret with
    | none => X f validJumps { s' with executionEnv.depth := s.executionEnv.depth }
    | some ⟨.revert, o⟩ => .ok <| .revert s'.machineState.gasAvailable.toUInt256 o
    | some ⟨.success, o⟩ => .ok <| .success s' o

/-- EVMLean's `EVM.Ξ` (code execution of one call frame) over `X`. -/
def Ξ (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Except EVM.ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate)) := do
  let defState : State := default
  let freshEvmState : State :=
    { defState with
        accountMap := σ
        σ₀ := σ₀
        executionEnv := I
        substate := A
        machineState.gasAvailable := .ofUInt256 g }
  let result ← X (UInt256.toNat g + 1) (EVM.D_J I.code 0) freshEvmState
  match result with
  | .success evmState' o =>
    .ok (ExecutionResult.success
      (evmState'.accountMap, evmState'.machineState.gasAvailable.toUInt256, evmState'.substate) o)
  | .revert g' o => .ok (ExecutionResult.revert g' o)

/-! ## Tests -/

/-- `x ↦ n` at the ends of both valid ranges, and the invalid range. -/
theorem decodeSingle_ends :
    decodeSingle 0x80 = some 17 ∧ decodeSingle 0xff = some 144 ∧ decodeSingle 0x00 = some 145 ∧
    decodeSingle 0x5a = some 235 ∧ decodeSingle 0x5b = none ∧ decodeSingle 0x7f = none := by
  decide

/-- Every macro of `src/bn254/huff/Eip8024.huff`: `DUP<n>` / `SWAP<n>` is the immediate
`(n - 145) mod 256` (`render_eip8024` in generator-rs), which decodes back to `n`. -/
theorem huff_macros_decode :
    (List.range 219).all (fun i => decodeSingle ((i + 17 + 256 - 145) % 256) == some (i + 17)) =
      true := by
  decide

/-- The immediate past the end of the code is `0`, i.e. `n = 145`. -/
theorem immediate_past_end : decode ⟨#[0xe6]⟩ 0 = some (some (.dupn 145)) := by
  decide +kernel

/-- A stack `[1, 2, .., k]` (top first) as words. -/
def stackUpTo (k : Nat) : List UInt256 := (List.range k).map fun i => .ofNat (i + 1)

/-- A state running `code` with `stack` and 100 gas. -/
def testState (code : ByteArray) (stack : List UInt256) : State :=
  let s : State := default
  { s with executionEnv.code := code
           machineState.stack := stack
           machineState.gasAvailable := 100 }

/-- `DUPN 17` (`e6 80`) on 17 items copies item 17 to the top, uses 3 gas, `pc` 0 to 2. -/
theorem dupn17 :
    (match exec (.dupn 17) (testState ⟨#[0xe6, 0x80]⟩ (stackUpTo 17)) with
     | .ok s => s.machineState.stack == UInt256.ofNat 17 :: stackUpTo 17 &&
                s.machineState.pc == .ofNat 2 && s.machineState.gasAvailable.toNat == 97
     | .error _ => false) = true := by
  decide +kernel

/-- `SWAPN 17` (`e7 80`) on 18 items swaps the top with item 18. -/
theorem swapn17 :
    (match exec (.swapn 17) (testState ⟨#[0xe7, 0x80]⟩ (stackUpTo 18)) with
     | .ok s => s.machineState.stack ==
                  (UInt256.ofNat 18 :: (stackUpTo 17).tail ++ [UInt256.ofNat 1]) &&
                s.machineState.pc == .ofNat 2
     | .error _ => false) = true := by
  decide +kernel

/-- `DUPN 17` on 16 items and `SWAPN 17` on 17 items underflow. -/
theorem underflow :
    (match exec (.dupn 17) (testState ⟨#[0xe6, 0x80]⟩ (stackUpTo 16)) with
     | .error .StackUnderflow => true | _ => false) = true ∧
    (match exec (.swapn 17) (testState ⟨#[0xe7, 0x80]⟩ (stackUpTo 17)) with
     | .error .StackUnderflow => true | _ => false) = true := by
  decide +kernel

/-- `Xstep` dispatches `e6 80` to DUPN, an invalid immediate (`e6 5b`) halts, and other bytes
go to EVMLean (`PUSH1 1` here). -/
theorem xstep_dispatch :
    (match Xstep #[] (testState ⟨#[0xe6, 0x80]⟩ (stackUpTo 17)) with
     | .ok (s, none) => s.machineState.stack.length == 18 | _ => false) = true ∧
    (match Xstep #[] (testState ⟨#[0xe6, 0x5b]⟩ (stackUpTo 17)) with
     | .error .InvalidInstruction => true | _ => false) = true ∧
    decode ⟨#[0x60, 0x01]⟩ 0 = none := by
  decide +kernel


/-- `decode_pair` on the EIP's test cases: `e89d` is `EXCHANGE 2 3`, `e82f` is `EXCHANGE 1 19`,
`e850` is `EXCHANGE 14 16`, `e851` is `EXCHANGE 14 15`, `e852` is invalid. -/
theorem decodePair_eip :
    decodePair 0x9d = some (2, 3) ∧ decodePair 0x2f = some (1, 19) ∧
    decodePair 0x50 = some (14, 16) ∧ decodePair 0x51 = some (14, 15) ∧
    decodePair 0x52 = none ∧ decodePair 0x7f = none ∧ decodePair 0x80 ≠ none := by
  decide

/-- Every valid immediate decodes to `1 ≤ n < m ≤ 30 - n`, as the EIP states. -/
theorem decodePair_range :
    (List.range 256).all (fun x => match decodePair x with
      | some (n, m) => 1 ≤ n && n < m && n + m ≤ 30
      | none => true) = true := by
  decide +kernel

/-- Words from numbers. -/
def words (l : List Nat) : List UInt256 := l.map .ofNat

/-- `EXCHANGE 1 2` (`e8 8e`) on `(words [2, 1, 0])` (top first) gives `[2, 0, 1]` (the EIP's
`600060016002e88e`), uses 3 gas and moves `pc` from 0 to 2. -/
theorem exchange12 :
    (match exec (.exchange 1 2) (testState ⟨#[0xe8, 0x8e]⟩ (words [2, 1, 0])) with
     | .ok s => s.machineState.stack == words [2, 0, 1] && s.machineState.pc == .ofNat 2 &&
                s.machineState.gasAvailable.toNat == 97
     | .error _ => false) = true := by
  decide +kernel

/-- `Xstep` dispatches `e8 8e` to EXCHANGE and halts on `e8 52`. -/
theorem xstep_exchange :
    (match Xstep #[] (testState ⟨#[0xe8, 0x8e]⟩ (words [2, 1, 0])) with
     | .ok (s, none) => s.machineState.stack == words [2, 0, 1] | _ => false) = true ∧
    (match Xstep #[] (testState ⟨#[0xe8, 0x52]⟩ (words [2, 1, 0])) with
     | .error .InvalidInstruction => true | _ => false) = true ∧
    (match exec (.exchange 1 2) (testState ⟨#[0xe8, 0x8e]⟩ (words [2, 1])) with
     | .error .StackUnderflow => true | _ => false) = true := by
  decide +kernel

end Poseidon2.Evm.Eip8024
