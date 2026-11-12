-- Checks that the pieces of `scripts/replay.sh` together replay every module of the import
-- closure of the given roots: a module is covered when a `fresh:M` piece has it in M's closure
-- (`leanchecker --fresh M` replays all of that closure) or a module piece names a prefix of it
-- (`leanchecker M` replays every module whose name starts with M on top of its imports). A
-- module that declares no constant has nothing to replay. Reads the import lists from the .olean
-- files, so run it after the build, from formal-verification/ (scripts/replay.sh does):
--   lake env lean --run scripts/ReplayCoverage.lean <root>... -- <piece>...
import Lean

open Lean

def importsOf (m : Name) : IO (Array Name) := do
  let (d, _) ← readModuleData (← findOLean m)
  return d.imports.map (·.module)

/-- Constants of `m`, read from its most private .olean part, as `leanchecker` does. -/
def constCount (m : Name) : IO Nat := do
  let f ← findOLean m
  let mut file := f
  let s := OLeanLevel.server.adjustFileName f
  if ← s.pathExists then
    file := s
    let p := OLeanLevel.private.adjustFileName f
    if ← p.pathExists then file := p
  let (d, _) ← readModuleData file
  return d.constNames.size

partial def closure (roots : List Name) : IO (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots
  while true do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      seen := seen.insert m
      todo := (← importsOf m).toList ++ todo
  return seen

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let roots := (args.takeWhile (· != "--")).map String.toName
  let pieces := (args.dropWhile (· != "--")).drop 1
  let all ← closure roots
  let mut covered : Std.HashSet Name := {}
  for p in pieces do
    let n := if p.startsWith "fresh:" then (p.drop 6).toString else p
    if n.any Char.isWhitespace || n.toName.isAnonymous then
      IO.eprintln s!"not a module name: {repr p}"
      return 2
    if p.startsWith "fresh:" then
      let c ← closure [n.toName]
      IO.println s!"{p}: {c.size} modules"
      covered := covered.insertMany c
    else
      let t := n.toName
      let sel := all.toList.filter t.isPrefixOf
      if sel.isEmpty then
        IO.eprintln s!"{p} names no module of the closure"
        return 2
      IO.println s!"{p}: {sel.length} modules"
      covered := covered.insertMany sel
  let mut empty := #[]
  let mut missing := #[]
  for m in all.toList do
    if covered.contains m then continue
    if (← constCount m) == 0 then empty := empty.push m else missing := missing.push m
  IO.println s!"{all.size} modules in the closure of {roots}; declaring no constant and not \
    replayed: {empty.qsort (·.toString < ·.toString)}"
  if missing.isEmpty then
    IO.println "every other module is replayed by a piece"
    return 0
  IO.eprintln s!"not replayed by any piece: {missing.qsort (·.toString < ·.toString)}"
  return 1
