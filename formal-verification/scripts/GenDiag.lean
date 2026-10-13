-- Writes the DiagCheck.lean certificate sections (one T<t>.part file per width into $OUT):
-- the LFSR state after every skipped value of the diagonal draws, in chunks of 96, and the
-- theorems that check them. Run from formal-verification/ after `lake build`:
--   OUT=/some/dir lake env lean scripts/GenDiag.lean
-- `#eval` only computes the certificate; the kernel checks it when DiagCheck.lean builds.
import Poseidon2.Spec.GrainCheck
open Poseidon2.Spec Poseidon2.Spec.Grain Poseidon2.Spec.GrainCheck Poseidon2.Spec.Constants

def statesAfter (n : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | m + 1, s => match bits n 0 s with
    | some (_, s') => s' :: statesAfter n m s'
    | none => []

def hex (v : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 v)

partial def chunks (k : Nat) : List Nat → List (List Nat)
  | [] => []
  | l => l.take k :: chunks k (l.drop k)

def gen (t rf rp k : Nat) (ss : List Nat) : IO Unit := do
  let s0 := ss.getLast!
  let ds := statesAfter 254 (k * t) s0
  let cs := chunks 96 ds
  let out ← IO.FS.Handle.mk s!"{(← IO.getEnv "OUT").get!}/T{t}.part" .write
  let p := fun (s : String) => out.putStrLn s
  p s!"/-! ### t = {t}: draw {k}, {ds.length} skipped values -/\n"
  p s!"/-- The LFSR state after the round constants for t = {t} (the last of `statesT{t}`). -/"
  p s!"def diagStartT{t} : Nat := {hex s0}\n"
  let mut start := s0
  let mut i := 0
  for c in cs do
    p s!"/-- Certificate states, values {96 * i} .. {96 * i + c.length - 1} of the skipped draws for t = {t}. -/"
    p s!"def diagStatesT{t}_{i} : List Nat :=\n  [{", ".intercalate (c.map hex)}]\n"
    p s!"theorem steps_t{t}_{i} : Grain.stepsChain 254 {hex start} diagStatesT{t}_{i} = true := by\n  decide +kernel\n"
    start := c.getLast!
    i := i + 1
  -- right-nested append and its proof
  let n := cs.length
  let names := (List.range n).map fun j => s!"diagStatesT{t}_{j}"
  if n = 0 then
    p s!"/-- The skipped states for t = {t} (none). -/\ndef diagStatesT{t} : List Nat := []\n"
    p s!"theorem steps_t{t} : Grain.stepsChain 254 diagStartT{t} diagStatesT{t} = true := rfl\n"
  else
    p s!"/-- The skipped states for t = {t}. -/\ndef diagStatesT{t} : List Nat :=\n  {" ++ ".intercalate names}\n"
    -- proof: stepsChain_append_of nested
    let rec proof (j : Nat) (fuel : Nat) : String :=
      match fuel with
      | 0 => ""
      | f + 1 =>
        if j + 1 = n then s!"steps_t{t}_{j}"
        else s!"(Grain.stepsChain_append_of _ _ _ _ _ steps_t{t}_{j} (by decide +kernel)\n    {proof (j + 1) f})"
    p s!"theorem steps_t{t} : Grain.stepsChain 254 diagStartT{t} diagStatesT{t} = true :=\n  {proof 0 (n + 1)}\n"
  p s!"theorem diagonal_t{t} : Grain.diagonal {t} {rf} {rp} {k} = some T{t}.params.diagM1 :=\n  Grain.diagonal_of_chain {t} {rf} {rp} {k} _ statesT{t} diagStatesT{t} _ (by decide +kernel) chain_t{t}\n    (by decide +kernel) steps_t{t} (by decide +kernel)\n"
  out.flush

#eval do
  gen 4 8 56 4 statesT4
  gen 8 8 57 30 statesT8
  gen 12 8 57 6 statesT12
  gen 16 8 57 6 statesT16
  gen 20 8 57 42 statesT20
  gen 24 8 57 2 statesT24
  gen 28 8 59 34 statesT28
