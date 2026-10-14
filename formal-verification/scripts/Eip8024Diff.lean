-- Dev mode, not a proof: runs the corpus of `poseidon2-gen eip8024-corpus` (generator-rs
-- eip8024.rs) through the EIP-8024 overlay (`Evm/Eip8024.lean`, `Eip8024.X` from pc 0 with the
-- line's stack and gas) and compares each result with revm's (Amsterdam), which the corpus
-- line carries. An exceptional halt is one outcome whatever its name (EVMLean's callers of `Ξ`
-- match on `.error _`), so two halts with different names count as a naming difference, not a
-- mismatch. The `pushtrunc` family is EVMLean's known reading of a PUSH cut by the end of the
-- code (unpadded); the checker never runs one. Exit code 1 on any other mismatch.
-- Run from formal-verification/ after `lake build` (scripts/eip8024-diff.sh does both steps):
--   lake env lean --run scripts/Eip8024Diff.lean <corpus file>
import Poseidon2.Evm.Eip8024

open Ethereum Poseidon2.Evm

def nibble (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def parseHex (s : String) : ByteArray :=
  let rec go : List Char → Array UInt8 → Array UInt8
    | a :: b :: rest, acc => go rest (acc.push (UInt8.ofNat (nibble a * 16 + nibble b)))
    | _, acc => acc
  ⟨go s.toList #[]⟩

/-- Runs of consecutive numbers as `a..b`. -/
partial def runs : List Nat → List String
  | [] => []
  | a :: rest =>
    let run := (rest.zip (List.range rest.length)).takeWhile fun (x, i) => x = a + i + 1
    if run.isEmpty then toString a :: runs rest
    else s!"{a}..{a + run.length}" :: runs (rest.drop run.length)

/-- The stack, top first, with runs of consecutive numbers as `a..b` (as eip8024.rs). -/
def renderStack (l : List UInt256) : String :=
  "[" ++ ",".intercalate (runs (l.map (·.toNat))) ++ "]"

def reason : EVM.ExecutionException → String
  | .OutOfGass => "oog"
  | .StackUnderflow => "underflow"
  | .StackOverflow => "overflow"
  | .InvalidInstruction => "invalid"
  | .BadJumpDestination => "badjump"
  | e => reprStr e

/-- The overlay on `code` from pc 0 with the stack `1, 2, .., depth` (1 on top) and `gas`. -/
def runProgram (code : ByteArray) (depth gas : Nat) : String :=
  let s0 : State := default
  let s : State :=
    { s0 with
        executionEnv.code := code
        machineState.stack := (List.range depth).map fun i => UInt256.ofNat (i + 1)
        machineState.gasAvailable := .ofUInt256 (UInt256.ofNat gas) }
  match Eip8024.X (gas + 1) (EVM.D_J code 0) s with
  | .ok (.success s' _) => s!"stop {s'.machineState.gasAvailable.toNat} {renderStack s'.machineState.stack}"
  | .ok (.revert g _) => s!"revert {g.toNat}"
  | .error e => s!"halt {reason e}"

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: Eip8024Diff.lean <corpus file>"; return 2
  let text ← IO.FS.readFile path
  let mut total := 0
  let mut agree := 0
  let mut names : List (String × String) := []
  let mut mismatches : List String := []
  let mut known : List String := []
  for line in text.splitOn "\n" do
    match line.splitOn " " with
    | family :: code :: depth :: gas :: revm =>
      total := total + 1
      let revm := " ".intercalate revm
      let lean := runProgram (parseHex code) depth.toNat! gas.toNat!
      let tag := s!"{family} {code} {depth} {gas}: revm {revm}, lean {lean}"
      if revm == lean then agree := agree + 1
      else if revm.startsWith "halt " && lean.startsWith "halt " then
        names := (s!"revm {revm}, lean {lean}", tag) :: names
      else if family == "pushtrunc" then known := tag :: known
      else mismatches := tag :: mismatches
    | _ => pure ()
  IO.println s!"{total} programs: {agree} equal, {names.length} exceptional halts named differently, {known.length} known EVMLean PUSH deviations, {mismatches.length} mismatches"
  -- the naming differences, one line per pair of names with a count and the first program
  let mut seen : List String := []
  for (pair, t) in names.reverse do
    unless seen.contains pair do
      seen := pair :: seen
      let n := (names.filter (·.1 == pair)).length
      IO.println s!"  name ({n}x): {pair}, first {t}"
  for t in known.reverse do IO.println s!"  known: {t}"
  for t in mismatches.reverse do IO.println s!"  MISMATCH: {t}"
  return if mismatches.isEmpty && 0 < total then 0 else 1
