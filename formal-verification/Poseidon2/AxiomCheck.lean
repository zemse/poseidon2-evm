import Lean

/-!
# Axiom audit

`#assert_standard_axioms Poseidon2 "Poseidon2"` fails the build unless

* every `.lean` file under the directory `Poseidon2/` is a module of the environment (imported,
  directly or not, by the file running the command), so no file escapes the audit;
* no constant defined in a module whose name starts with `Poseidon2` is an `axiom`;
* every constant defined in such a module (theorems, definitions, instances, opaque constants,
  inductive types, private names and auxiliary declarations alike) depends only on `propext`,
  `Classical.choice` and `Quot.sound`. That excludes `sorryAx` (any `sorry`) and the auxiliary
  axioms `native_decide` adds (`<name>._native.native_decide.ax_*` in Lean 4.29).

Constants are selected by their defining module, not by name, so private declarations
(`_private.<module>.0.<name>`) and names outside the `Poseidon2` namespace are covered.
-/

namespace Poseidon2.AxiomCheck

open Lean Elab Command

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Module names of the `.lean` files below `dir`, which is relative to the package root. -/
partial def modulesIn (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← modulesIn e.path (pre.str e.fileName))
    else if e.fileName.endsWith ".lean" then
      if let some stem := e.path.fileStem then out := out.push (pre.str stem)
  return out

elab "#assert_standard_axioms " pre:ident dir:str : command => do
  let env ← getEnv
  let pre := pre.getId
  let mods := env.header.moduleNames
  -- every file under `dir` is in the environment, except the module running the audit
  let here := env.header.mainModule
  let files ← modulesIn dir.getString pre
  for m in files do
    unless m == here || mods.contains m do
      throwError "{m} is not imported by the audit, so it is neither built nor checked"
  -- constants defined in our modules, of every kind
  let mut ours : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := mods[idx.toNat]? | continue
    unless pre.isPrefixOf m do continue
    if info matches .axiomInfo _ then
      throwError "{privateToUserName name} is an axiom declared in {m}"
    ours := ours.push name
  -- one traversal with a shared visited set, then per constant only if something is wrong
  let (_, s) := ((ours.forM CollectAxioms.collect).run env).run {}
  let bad := s.axioms.filter (fun a => !standard.contains a)
  unless bad.isEmpty do
    for name in ours do
      let axs ← liftCoreM <| collectAxioms name
      let b := axs.filter (fun a => !standard.contains a)
      unless b.isEmpty do
        throwError "{privateToUserName name} depends on non-standard axioms {b.toList}"
    throwError "non-standard axioms {bad.toList} reached"
  logInfo m!"{ours.size} constants of {files.size} {pre} modules use only standard axioms"

end Poseidon2.AxiomCheck
