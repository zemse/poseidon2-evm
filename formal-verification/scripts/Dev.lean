-- Development mode of the checker: runs it with `#eval` (compiled code, not the kernel, so
-- nothing here is a proof) on every exported bytecode and prints one line per case.
-- Run from formal-verification/ after `lake build`:
--   lake env lean scripts/Dev.lean
-- Optional filter: ONLY=<substring of the artifact name>.
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

def describe : Res → String
  | .ret ws tb => s!"return {ws.length} words, {tb.next} atoms"
  | .revert n => s!"revert {n} bytes"
  | .stop => "stop"
  | .fail pc msg => s!"FAIL at pc {pc}: {msg}"

#eval show IO Unit from do
  let only := (← IO.getEnv "ONLY").getD ""
  for a in all do
    unless only.isEmpty || (a.name.splitOn only).length > 1 do continue
    let code := Code.ofBytes a.bytes
    for cs in casesOf a do
      let t0 ← IO.monoMsNow
      let r := runCase code cs
      let ok := resultOk cs.facts cs.expect r
      let t1 ← IO.monoMsNow
      IO.println s!"{if ok then "pass" else "FAIL"} {a.name} [{cs.name}]: {describe r} ({t1 - t0} ms)"
