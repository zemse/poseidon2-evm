import Lean

/-!
# Axiom audit

`#assert_standard_axioms Poseidon2` fails unless every theorem whose name starts with
`Poseidon2` depends only on `propext`, `Classical.choice` and `Quot.sound`. That excludes
`sorryAx` (any `sorry`) and `Lean.ofReduceBool` / `Lean.trustCompiler` (any `native_decide`).
-/

namespace Poseidon2.AxiomCheck

open Lean Elab Command

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_standard_axioms " pre:ident : command => do
  let env ← getEnv
  let pre := pre.getId
  let mut n := 0
  for (name, info) in env.constants.toList do
    unless pre.isPrefixOf name do continue
    unless info matches .thmInfo _ do continue
    n := n + 1
    let axs ← liftCoreM <| collectAxioms name
    let bad := axs.filter (fun a => !standard.contains a)
    unless bad.isEmpty do
      throwError "{name} depends on non-standard axioms {bad.toList}"
  logInfo m!"{n} theorems under {pre} use only standard axioms"

end Poseidon2.AxiomCheck
