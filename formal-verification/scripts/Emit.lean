-- Writes the kernel check of one exported bytecode to <OUT>/<Artifact>.lean (OUT defaults to
-- Poseidon2/Proofs; the module prefix follows it): every case of its interface run in segments of
-- SEG instructions, with the checker state at each boundary written out as a literal, and the
-- spec side of a permutation case (`SpecSegments.lean`) in segments of SPEC rounds. `#eval` only
-- computes those states; the kernel re-checks each segment from its literal start state when the
-- written file builds. Each case is also checked to use the gas `gas` lists for it. With more
-- than PER kernel checks the declarations are cut into <OUT>/<Artifact>/Part<i>.lean, each
-- importing the one before, so no Lean process holds more than PER of them. scripts/proof.sh
-- runs this with the settings of each artifact.
-- Run from formal-verification/ after `lake build`:
--   OUT=Poseidon2/Proofs/Generated ART=huff/amsterdam/t28 SEG=1000 SPEC=10 PER=3 \
--     lake env lean --tstack=1000000 scripts/Emit.lean
import Poseidon2.Bytecode.All
import Poseidon2.Checker.Check
import Poseidon2.Checker.Segments
import Poseidon2.Checker.SpecSegments
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

/-- `huff/amsterdam/t4` as `Huff.Amsterdam.T4`. -/
def moduleOf (name : String) : String :=
  ".".intercalate ((name.splitOn "/").map fun p =>
    if p == "runs1000000" then "Runs1000000" else if p == "runs200" then "Runs200"
    else if p == "optimizeroff" then "OptimizerOff" else if p == "huffv2" then "HuffV2"
    else if p == "yulv2" then "YulV2" else p.capitalize)

/-- The Lean expression of an artifact's cases. -/
def casesExpr (a : Artifact) : String :=
  let c := s!"Constants.T{a.t}.params"
  match a.kind with
  | .huffPerm => s!"huffPermCases {c}"
  | .huffHash => s!"huffHashCases {c}"
  | .yulHash => s!"yulHashCases {c}"
  | .yulPerm => s!"yulPermCases {c} (Interface.permuteSelector {a.t})"
  | .hashV2 => s!"hashV2Cases {c}"
  | .huffPart _ _ => "[]"

def casesOf (a : Artifact) (c : Params) : List Case :=
  match a.kind with
  | .huffPerm => huffPermCases c
  | .huffHash => huffHashCases c
  | .yulHash => yulHashCases c
  | .yulPerm => yulPermCases c (Interface.permuteSelector a.t)
  | .hashV2 => hashV2Cases c
  | .huffPart _ _ => []

def renderAny {α : Type} [Repr α] (x : α) : String :=
  ((Std.Format.pretty (repr x) 1000000000).replace "Poseidon2.Checker." "")

def render (s : St) : String := renderAny s

/-- The input words of a permutation case, as the case list builds them. -/
def insExpr (a : Artifact) : String :=
  match a.kind with
  | .yulPerm => s!"cdlWords 4 Constants.T{a.t}.params.t"
  | _ => s!"cdlWords 0 Constants.T{a.t}.params.t"

/-- The rounds in segments of `n` (at least one). -/
partial def roundChunks (n : Nat) (rs : List Round) : List (List Round) :=
  if rs.isEmpty then [] else rs.take (max n 1) :: roundChunks n (rs.drop (max n 1))

def pcExpr (p : Option Nat) : String :=
  match p with
  | some pc => s!"(some {pc})"
  | none => "none"

/-- The segments of one case: the boundary pcs and states. -/
partial def segments (fs : Facts) (code : Code) (k : Nat) (is : List (Nat × Ins)) (s : St)
    (acc : Array (Option Nat × St)) : Array (Option Nat × St) :=
  match runN fs code k is s with
  | .next is' s' =>
    -- stop when the next segment would end the run anyway
    match runN fs code k is' s' with
    | .done _ => acc.push (pcOf is', s')
    | .next _ _ => segments fs code k is' s' (acc.push (pcOf is', s'))
  | .done _ => acc

def emit (a : Artifact) (c : Params) (k sb per : Nat) (root : String) : IO Unit := do
  let code := Code.ofBytes a.bytes
  let mod := moduleOf a.name
  let ns := ".".intercalate (root.splitOn "/") ++ "." ++ mod
  let modPath := "/".intercalate (mod.splitOn ".")
  -- the declarations go to a buffer; `heavy` marks the end of a kernel check, where a long file
  -- may be cut into parts
  let buf ← IO.mkRef (#[] : Array String)
  let cuts ← IO.mkRef (#[] : Array Nat)
  let p := fun (x : String) => buf.modify (·.push x)
  let heavy : IO Unit := do cuts.modify (·.push (← buf.get).size)
  p s!"def code : Code := Code.ofBytes Poseidon2.Bytecode.{mod}.artifact.bytes"
  p ""
  p s!"def cases : List Case := {casesExpr a}"
  p ""
  p "theorem code_wf : code.WF := Code.ofBytes_wf _"
  p ""
  let cases := casesOf a c
  let gases := cases.map fun cs => (runCase code cs).gas
  for (cs, j) in cases.zip (List.range cases.length) do
    let segs := segments cs.facts code k code.ins St.init #[]
    let G := (runCase code cs).gas
    p s!"/-! ### Case {j}: {cs.name} ({segs.size} boundaries) -/"
    p ""
    let mut prevPc := "(some 0)"
    let mut prevS := "St.init"
    for ((pc, s), i) in segs.toList.zip (List.range segs.size) do
      p s!"def s{j}_{i + 1} : St :=\n  {render s}\n"
      p s!"theorem seg{j}_{i} : (runN (cases.getD {j} default).facts code {k} (code.at {prevPc}) {prevS}).pcSt ="
      p s!"    some ({pcExpr pc}, s{j}_{i + 1}) := by\n  decide +kernel\n"
      heavy
      prevPc := pcExpr pc
      prevS := s!"s{j}_{i + 1}"
    let rest := fuel - k * segs.size
    let (lastP, lastSt) := segs.back?.getD (some 0, St.init)
    let F := s!"(cases.getD {j} default).facts"
    let runE := s!"run {F} code {rest} (code.at {prevPc}) {prevS}"
    -- a permutation case whose spec run needs more than one segment: checked in segments of
    -- rounds (`SpecSegments.lean`), else in one declaration with the end of the run
    let specSegs := match cs.expect with
      | .perm c ins =>
        match run cs.facts code rest (code.at lastP) lastSt with
        | .ret ws tb _ =>
          let (ys, t0) := inputForms cs.facts ins tb
          let chunks := roundChunks sb (rounds c)
          if chunks.length ≤ 1 then none else some (c, ws, tb, ys, t0, chunks)
        | _ => none
      | _ => none
    match specSegs with
    | none =>
      p s!"theorem end{j} : resultOkGas {F} (cases.getD {j} default).expect {G}"
      p s!"    ({runE}) = true := by\n  decide +kernel\n"
      heavy
    | some (c, ws, tb, ys, t0, chunks) =>
      let cE := s!"Constants.T{a.t}.params"
      let insE := insExpr a
      let tabE := fun (t : Tab) (name : String) =>
        if t == tb then (s!"tf{j}", none) else (name, some t)
      p s!"/-! The spec side of case {j}, in {chunks.length} segments of rounds. -/\n"
      p s!"def r{j} : List SV :=\n  {renderAny ws}\n"
      if tb == lastSt.tab && 0 < segs.size then p s!"def tf{j} : Tab := {prevS}.tab\n"
      else p s!"def tf{j} : Tab :=\n  {renderAny tb}\n"
      p s!"theorem fin{j} : {runE} = .ret r{j} tf{j} {G} := by\n  decide +kernel\n"
      heavy
      p s!"theorem exp{j} : (cases.getD {j} default).expect = .perm {cE} ({insE}) := rfl\n"
      p s!"def y{j} : List Lin :=\n  {renderAny ys}\n"
      let (t0E, t0D) := tabE t0 s!"t{j}_0"
      if let some t := t0D then p s!"def {t0E} : Tab :=\n  {renderAny t}\n"
      p s!"theorem in{j} : inputForms {F} ({insE}) tf{j} = (y{j}, {t0E}) := by\n  decide +kernel\n"
      heavy
      let x0 := external linOps ys
      p s!"def x{j}_0 : List Lin :=\n  {renderAny x0}\n"
      p s!"theorem ext{j} : external linOps y{j} = x{j}_0 := by\n  decide +kernel\n"
      heavy
      let mut xs := x0
      let mut tE := t0E
      let mut tCur := t0
      let mut listE := s!"(rounds {cE})"
      for (ch, i) in chunks.zip (List.range chunks.length) do
        let (xs', t') := roundsRun linOps c.diagM1 ch xs tCur
        let last := i + 1 == chunks.length
        p s!"def x{j}_{i + 1} : List Lin :=\n  {renderAny xs'}\n"
        let (tE', tD) := tabE t' s!"t{j}_{i + 1}"
        if let some t := tD then p s!"def {tE'} : Tab :=\n  {renderAny t}\n"
        let l := if last then listE else s!"({listE}.take {ch.length})"
        p s!"theorem sp{j}_{i} : roundsRun linOps {cE}.diagM1 {l} x{j}_{i} {tE} ="
        p s!"    (x{j}_{i + 1}, {tE'}) := by\n  decide +kernel\n"
        heavy
        listE := s!"({listE}.drop {ch.length})"
        xs := xs'; tE := tE'; tCur := t'
      p s!"theorem out{j} : outputsMatch r{j} x{j}_{chunks.length} = true := by\n  decide +kernel\n"
      heavy
      p s!"theorem spec{j} : roundsRun linOps {cE}.diagM1 (rounds {cE})"
      p s!"    (external linOps (inputForms {F} ({insE}) tf{j}).1)"
      p s!"    (inputForms {F} ({insE}) tf{j}).2 = (x{j}_{chunks.length}, {tE}) := by"
      p s!"  rw [in{j}]"
      p s!"  dsimp only"
      p s!"  rw [ext{j}]"
      for i in List.range (chunks.length - 1) do
        p s!"  rw [rounds_seg _ _ _ _ _ _ _ _ sp{j}_{i}]"
      p s!"  exact sp{j}_{chunks.length - 1}\n"
      p s!"theorem end{j} : resultOkGas {F} (cases.getD {j} default).expect {G}"
      p s!"    ({runE}) = true := by"
      p s!"  rw [fin{j}, exp{j}]"
      p s!"  exact resultOkGas_perm spec{j} out{j}\n"
    p s!"theorem case{j} : checkCaseGas code (cases.getD {j} default) {G} = true := by"
    let sum := (List.replicate segs.size (toString k)).foldr (fun x acc => s!"{x} + ({acc})") (toString rest)
    p s!"  have e : fuel = {sum} := by decide"
    p s!"  unfold checkCaseGas runCase"
    p s!"  rw [e, ← Code.at_zero]"
    for i in List.range segs.size do
      p s!"  rw [seg_run _ _ code_wf _ _ _ _ _ _ seg{j}_{i}]"
    p s!"  exact end{j}\n"
  let mainStart := (← buf.get).size
  p "/-- The gas of each case's run, in the order of `cases`: a call in case `j` given at least"
  p "`gas[j]` gas uses exactly that much, and with less runs out of gas (`total`). -/"
  p s!"def gas : List Nat := {gases}"
  p ""
  p s!"theorem checkG : CheckedGas code cases gas :="
  p s!"  ⟨by decide, fun j hj => by"
  p s!"    have hl : cases.length = {cases.length} := by decide"
  p s!"    rw [hl] at hj"
  p s!"    match j, hj with"
  for j in List.range cases.length do
    p s!"    | {j}, _ => exact case{j}"
  p s!"    | n + {cases.length}, h => exact absurd h (by omega)⟩"
  p ""
  p s!"theorem check : cases.all (checkCase code) = true := checkG.check"
  p ""
  -- the contract-level statements, from the checker's soundness (`Soundness.checkerSound`,
  -- `Soundness.checkerTotal`)
  let art := s!"Poseidon2.Bytecode.{mod}.artifact"
  let c := s!"Constants.T{a.t}.params"
  let (iface, thm, extraHyp, extraArg, args) := match a.kind with
    | .huffPerm => (s!"Interface.huffPerm {c} cd", "huffPerm", "", "", "")
    | .huffHash => (s!"Interface.huffHash {c} cd", "huffHash", "", "", "")
    | .yulHash => (s!"Interface.yulHash {c} cd v", "yulHash", "", "", "")
    | .yulPerm => (s!"Interface.yulPerm {c} (Interface.permuteSelector {a.t}) cd v",
        "yulPerm", "", "", s!"(Interface.permuteSelector {a.t}) (by decide) (by decide) ")
    | .hashV2 => (s!"Interface.hashV2 {c} cd", "hashV2", " (h4 : 4 ≤ cd.length)", " h4", "")
    | .huffPart _ _ => ("", "", "", "", "")
  let hyps := fun (hg : String) => [
    s!"    (hcd : cd.length < 2 ^ 64){extraHyp} (hv : v < W) (σ σ₀ : Ethereum.AccountMap)",
    s!"    (g : Ethereum.UInt256) (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)",
    s!"    (hI : Theorems.Runs {art} cd v I){hg} :"]
  unless thm.isEmpty do
    p "/-- The contract statement: every call of the bytecode by the EVM (`Evm.Eip8024.Ξ`) either"
    p "runs out of gas or ends as the interface says (`Theorems.lean`, `Soundness.checkerSound`). -/"
    p s!"theorem correct (cd : List UInt8) (v : Nat)"
    for l in hyps "" do p l
    p s!"    Soundness.Matches (Evm.Eip8024.Ξ σ σ₀ g A I) ({iface}) :="
    p s!"  Theorems.{thm}_correct {art} {c} {args}check cd v hcd{extraArg} hv σ σ₀ g A I hI"
    p ""
    p "/-- Total correctness: every call is in some case `j` of `cases`; given at least `gas[j]`"
    p "gas it ends exactly as the interface says with `gas[j]` used, given less it runs out of gas"
    p "(`Theorems.Total`, `Soundness.checkerTotal`). -/"
    p s!"theorem total (cd : List UInt8) (v : Nat)"
    for l in hyps "" do p l
    p s!"    Theorems.Total cases gas ⟨cd, v⟩ g.toNat (Evm.Eip8024.Ξ σ σ₀ g A I) ({iface}) :="
    p s!"  Theorems.{thm}_total {art} {c} {args}gas checkG cd v hcd{extraArg} hv σ σ₀ g A I hI"
    p ""
    p s!"/-- With at least {maxGas gases} gas (the most of any case) every call ends exactly as the"
    p "interface says, using at most that much. -/"
    p s!"theorem enough (cd : List UInt8) (v : Nat)"
    for l in hyps s!" (hg : {maxGas gases} ≤ g.toNat)" do p l
    p s!"    ∃ G, G ≤ {maxGas gases} ∧ Soundness.Exact (g.toNat - G) (Evm.Eip8024.Ξ σ σ₀ g A I)"
    p s!"      ({iface}) :="
    p s!"  (total cd v hcd{extraArg} hv σ σ₀ g A I hI).exact"
    p s!"    (le_trans (le_of_eq (show maxGas gas = {maxGas gases} by decide)) hg)"
    p ""
  let lines ← buf.get
  let cuts ← cuts.get
  let imports := ["Poseidon2.Checker.Check", "Poseidon2.Checker.Segments",
    "Poseidon2.Checker.SpecSegments", "Poseidon2.Spec.Interface", "Poseidon2.AxiomCheck",
    "Poseidon2.Theorems",
    s!"Poseidon2.Bytecode.{mod}", s!"Poseidon2.Spec.Constants.T{a.t}"]
  let writeFile := fun (path : String) (imps : List String) (doc : List String)
      (body : List String) => do
    let h ← IO.FS.Handle.mk path .write
    let p := fun (x : String) => h.putStrLn x
    p "-- Generated by scripts/Emit.lean. Do not edit."
    for i in imps do p s!"import {i}"
    p ""
    p "/-!"
    for l in doc do p l
    p "-/"
    p ""
    p s!"namespace {ns}"
    p ""
    p "open Poseidon2.Checker Poseidon2.Spec"
    p ""
    p "set_option maxRecDepth 100000"
    p "set_option maxHeartbeats 0"
    p ""
    for l in body do p l
    p s!"end {ns}"
    h.flush
  let doc := [
    s!"The checker accepts `{a.name}` on every case of its interface, by kernel evaluation in",
    s!"segments of at most {k} instructions and {sb} rounds of the spec; the checker state at each",
    "segment boundary is written out below (computed outside the kernel, checked by it). The",
    s!"gas of each case's run is `gas` ({gases}); `correct` is partial correctness, `total`",
    "total correctness with that gas."]
  let main := (lines.extract mainStart lines.size).toList
  let path := s!"{root}/{modPath}.lean"
  let dir := s!"{root}/{modPath}"
  if ← System.FilePath.pathExists dir then IO.FS.removeDirAll dir
  -- the kernel checks in parts of `per`, each part importing the one before, so that no Lean
  -- process holds more than `per` of them (memory grows with the checks a file holds)
  let ends := (cuts.toList.zip (List.range cuts.size)).filterMap fun (n, i) =>
    if (i + 1) % per == 0 && i + 1 < cuts.size then some n else none
  if ends.isEmpty then
    writeFile path imports doc ((lines.extract 0 mainStart).toList ++ main ++
      ["#assert_standard_axioms_here", ""])
  else
    IO.FS.createDirAll dir
    let bounds := 0 :: ends ++ [mainStart]
    let parts := (bounds.zip bounds.tail).zip (List.range (bounds.length - 1))
    for ((b, e), i) in parts do
      -- the parts only run the checker; the EVM proofs `Theorems` brings in are left to the
      -- main file, so the processes doing the kernel checks load fewer modules
      let imps := if i == 0 then imports.filter (· != "Poseidon2.Theorems")
        else [s!"{ns}.Part{i - 1}"]
      writeFile s!"{dir}/Part{i}.lean" imps
        [s!"Part {i} of the kernel check of `{a.name}`; `{modPath}.lean` puts the parts together."]
        (lines.extract b e).toList
    writeFile path (imports ++ [s!"{ns}.Part{parts.length - 1}"]) doc (main ++
      [s!"#assert_standard_axioms {ns} \"{dir}\"", "#assert_standard_axioms_here", ""])
  IO.println s!"wrote {path} ({if ends.isEmpty then 0 else ends.length + 1} parts)"
  IO.println s!"module {ns}"

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

#eval show IO Unit from do
  let art := (← IO.getEnv "ART").getD ""
  let k := ((← IO.getEnv "SEG").getD "4000").toNat!
  let sb := ((← IO.getEnv "SPEC").getD "100").toNat!
  let per := ((← IO.getEnv "PER").getD "1000").toNat!
  for a in all do
    unless a.name == art do continue
    let root := (← IO.getEnv "OUT").getD "Poseidon2/Proofs"
    IO.FS.createDirAll ((System.FilePath.mk s!"{root}/{"/".intercalate ((moduleOf a.name).splitOn ".")}").parent.get!)
    emit a (paramsOf a.t) k sb per root
