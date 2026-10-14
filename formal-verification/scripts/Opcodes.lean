-- The opcodes of every exported bytecode, with `#eval` (compiled code, not the kernel, so
-- nothing here is a proof): per artifact, the opcodes its checker runs execute (over all its
-- cases, each opcode by the code byte at the instruction, so `PUSH1` .. `PUSH32` are told apart),
-- and the opcodes of its whole decoded program (`Code.ofBytes`: everything at an instruction
-- boundary, unreachable bytes such as Yul metadata included). The last lines are the union over
-- all artifacts and whether any artifact other than Huff Amsterdam executes or decodes
-- DUPN / SWAPN (`0xe6` / `0xe7`), which only Amsterdam defines. `Evm/Forks.lean` proves the
-- executed set is within the set the checker accepts at all.
-- Run from formal-verification/ after `lake build`:
--   lake env lean --tstack=1000000 scripts/Opcodes.lean
import Poseidon2.Bytecode.All
import Poseidon2.Checker.Check
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

open Poseidon2.Spec Poseidon2.Checker Poseidon2.Bytecode

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

def casesOf (a : Artifact) : List Case :=
  let c := paramsOf a.t
  match a.kind with
  | .huffPerm => huffPermCases c
  | .huffHash => huffHashCases c
  | .yulHash => yulHashCases c
  | .yulPerm => yulPermCases c (Interface.permuteSelector a.t)
  | .hashV2 => hashV2Cases c
  | .huffPart _ _ => []

def opName (b : Nat) : String :=
  if 0x60 ≤ b ∧ b ≤ 0x7f then s!"PUSH{b - 0x5f}"
  else if 0x80 ≤ b ∧ b ≤ 0x8f then s!"DUP{b - 0x7f}"
  else if 0x90 ≤ b ∧ b ≤ 0x9f then s!"SWAP{b - 0x8f}"
  else match b with
  | 0x00 => "STOP" | 0x01 => "ADD" | 0x02 => "MUL" | 0x03 => "SUB" | 0x04 => "DIV"
  | 0x06 => "MOD" | 0x08 => "ADDMOD" | 0x09 => "MULMOD" | 0x10 => "LT" | 0x11 => "GT"
  | 0x12 => "SLT" | 0x13 => "SGT" | 0x14 => "EQ" | 0x15 => "ISZERO" | 0x16 => "AND"
  | 0x17 => "OR" | 0x18 => "XOR" | 0x19 => "NOT" | 0x1b => "SHL" | 0x1c => "SHR"
  | 0x34 => "CALLVALUE" | 0x35 => "CALLDATALOAD" | 0x36 => "CALLDATASIZE"
  | 0x37 => "CALLDATACOPY" | 0x39 => "CODECOPY" | 0x3d => "RETURNDATASIZE" | 0x50 => "POP"
  | 0x51 => "MLOAD" | 0x52 => "MSTORE" | 0x56 => "JUMP" | 0x57 => "JUMPI" | 0x59 => "MSIZE"
  | 0x5b => "JUMPDEST" | 0x5f => "PUSH0" | 0xe6 => "DUPN" | 0xe7 => "SWAPN" | 0xf3 => "RETURN"
  | 0xfd => "REVERT" | 0xfe => "INVALID"
  | b => s!"0x{String.ofList (Nat.toDigits 16 b)}"

/-- The checker's run (`run`), marking the code byte of every instruction it executes. -/
def runMark (fs : Facts) (code : Code) (bs : Array Nat) :
    Nat → List (Nat × Ins) → St → Array Bool → Res × Array Bool
  | 0, _, _, m => (.fail 0 "out of fuel", m)
  | f + 1, is, s, m =>
    let m := match is with
      | (pc, _) :: _ => m.set! (bs.getD pc 0) true
      | [] => m
    match step1 fs code is s with
    | .next is s => runMark fs code bs f is s m
    | .done r => (r, m)

def marked (m : Array Bool) : List Nat := (List.range 256).filter (m.getD · false)

def names (l : List Nat) : String := " ".intercalate (l.map opName)

def isAmsterdamHuff (a : Artifact) : Bool := (a.name.splitOn "huff/amsterdam").length > 1

#eval show IO Unit from do
  let mut allExec := Array.replicate 256 false
  let mut allDec := Array.replicate 256 false
  let mut dupSwapElsewhere : List String := []
  for a in all do
    let code := Code.ofBytes a.bytes
    let bs := a.bytes.toArray
    let mut ex := Array.replicate 256 false
    for cs in casesOf a do
      let (r, m) := runMark cs.facts code bs fuel code.ins St.init ex
      unless resultOk cs.facts cs.expect r do IO.println s!"FAIL {a.name} [{cs.name}]"
      ex := m
    let dec := code.ins.foldl (fun m (pc, _) => m.set! (bs.getD pc 0) true)
      (Array.replicate 256 false)
    for b in marked ex do allExec := allExec.set! b true
    for b in marked dec do allDec := allDec.set! b true
    let ds := [0xe6, 0xe7].filter fun b => ex.getD b false || dec.getD b false
    if !isAmsterdamHuff a && !ds.isEmpty then
      dupSwapElsewhere := dupSwapElsewhere ++ [s!"{a.name} ({names ds})"]
    IO.println s!"{a.name}: executes {(marked ex).length}: {names (marked ex)}"
    let extra := (marked dec).filter fun b => !ex.getD b false
    IO.println s!"  decodes {(marked dec).length}, not executed: {names extra}"
  IO.println s!"union executed {(marked allExec).length}: {names (marked allExec)}"
  IO.println s!"union decoded {(marked allDec).length}: {names (marked allDec)}"
  IO.println s!"DUPN / SWAPN outside Huff Amsterdam: {dupSwapElsewhere}"
