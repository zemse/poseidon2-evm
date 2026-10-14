import Poseidon2.Checker.SymExec
import Poseidon2.Spec.Sponge
import Poseidon2.Spec.Interface
import Poseidon2.Bytecode.Artifact

/-!
# The check

For an artifact and one case of the call (a set of `Facts` and the outcome
`Spec/Interface.lean` gives for it), `checkCase` runs the bytecode symbolically and compares:

* a permutation case with `permG linOps` run on the input atoms over the atom table the
  bytecode built: every returned word must have a raw bound below `P` and the form the spec
  gives, so spec and checker share one definition (`permG`, `hashG`);
* a case of fixed words (`words`) the same way, the spec's forms being constants;
* a revert case with an empty `REVERT`.

`cases` lists the cases of every contract kind; together they cover every call with calldata
shorter than `2^64` bytes. `check` is the conjunction over them.
-/

namespace Poseidon2.Checker

open Poseidon2.Spec Poseidon2.Bytecode

/-- What a case must end in. -/
inductive Expect where
  /-- return `permG` of the input words (read in the field) -/
  | perm (c : Params) (inputs : List Term)
  /-- return element 0 of `permG` of the input words -/
  | permHead (c : Params) (inputs : List Term)
  /-- return `hashG` of the input words -/
  | hash (c : Params) (inputs : List Term)
  /-- return the words `ws` (read in the field), whatever the calldata -/
  | words (ws : List Nat)
  /-- revert with empty data -/
  | revertEmpty

/-- One case of a call. -/
structure Case where
  name : String
  facts : Facts
  expect : Expect

instance : Inhabited Case := ⟨⟨"", [], .revertEmpty⟩⟩

/-- The atoms of the input words, as forms. -/
def inputForms (fs : Facts) : List Term → Tab → List Lin × Tab
  | [], tb => ([], tb)
  | t :: ts, tb =>
    -- as `toLin` reads an input word: a constant if the facts fix it, else its atom
    let w := mkInput fs t full
    let (x, tb) := match w.exact with
      | some v => (Lin.const v, tb)
      | none => tb.atom (.word t)
    let (xs, tb) := inputForms fs ts tb
    (x :: xs, tb)

/-- The forms the spec returns, over the table the bytecode built. -/
def specForms (fs : Facts) (e : Expect) (tb : Tab) : List Lin :=
  match e with
  | .perm c ins => let (xs, tb) := inputForms fs ins tb; (permG linOps c xs tb).1
  | .permHead c ins => let (xs, tb) := inputForms fs ins tb; [(permG linOps c xs tb).1.headD linOps.zero]
  | .hash c ins => let (xs, tb) := inputForms fs ins tb; [(hashG linOps c xs tb).1]
  | .words ws => ws.map Lin.const
  | .revertEmpty => []

/-- Every returned word is canonical (below `P`) with the spec's form. -/
def outputsMatch : List SV → List Lin → Bool
  | [], [] => true
  | .lin l b :: ws, f :: fs => b < P && l.beq f && outputsMatch ws fs
  | .word w :: ws, f :: fs =>
    match w.exact with
    | some v => v < P && (Lin.const v).beq f && outputsMatch ws fs
    | none => false
  | _, _ => false

/-- The instruction budget of a run. -/
def fuel : Nat := 1000000

/-- The run of one case. -/
def runCase (code : Code) (cs : Case) : Res :=
  run cs.facts code fuel code.ins St.init

/-- Whether the run ends as the case expects. -/
def resultOk (fs : Facts) (e : Expect) : Res → Bool
  | .ret ws tb _ =>
    match e with
    | .revertEmpty => false
    | e => outputsMatch ws (specForms fs e tb)
  | .revert n _ => match e with
    | .revertEmpty => n == 0
    | _ => false
  | _ => false

def checkCase (code : Code) (cs : Case) : Bool := resultOk cs.facts cs.expect (runCase code cs)

/-- Whether the run ends as the case expects, having used `G` gas. -/
def resultOkGas (fs : Facts) (e : Expect) (G : Nat) : Res → Bool
  | .ret ws tb g => g == G && resultOk fs e (.ret ws tb g)
  | .revert n g => g == G && resultOk fs e (.revert n g)
  | _ => false

/-- The case is accepted and its run uses `G` gas. -/
def checkCaseGas (code : Code) (cs : Case) (G : Nat) : Bool :=
  resultOkGas cs.facts cs.expect G (runCase code cs)

theorem resultOkGas_eq {fs : Facts} {e : Expect} {G : Nat} {r : Res}
    (h : resultOkGas fs e G r = true) : resultOk fs e r = true ∧ r.gas = G := by
  cases r with
  | ret ws tb g =>
    simp only [resultOkGas, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.2, h.1⟩
  | revert n g =>
    simp only [resultOkGas, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.2, h.1⟩
  | stop => simp [resultOkGas] at h
  | fail _ _ => simp [resultOkGas] at h

theorem checkCaseGas_eq {code : Code} {cs : Case} {G : Nat} (h : checkCaseGas code cs G = true) :
    checkCase code cs = true ∧ (runCase code cs).gas = G :=
  resultOkGas_eq h

/-- Every case of `cases` is accepted, the one at index `j` using `gas[j]` gas. -/
def CheckedGas (code : Code) (cases : List Case) (gas : List Nat) : Prop :=
  gas.length = cases.length ∧
    ∀ j, j < cases.length → checkCaseGas code (cases.getD j default) (gas.getD j 0) = true

/-- The most gas of a list. -/
def maxGas (gas : List Nat) : Nat := gas.foldr max 0

theorem le_maxGas : ∀ (gas : List Nat) (j : Nat), gas.getD j 0 ≤ maxGas gas
  | [], _ => by simp [maxGas]
  | g :: gas, 0 => by simp [maxGas]
  | g :: gas, j + 1 => by
    have := le_maxGas gas j
    simp only [maxGas, List.foldr_cons, List.getD_cons_succ] at this ⊢
    omega

theorem CheckedGas.mem {code : Code} {cases : List Case} {gas : List Nat}
    (h : CheckedGas code cases gas) {cs : Case} (hcs : cs ∈ cases) :
    ∃ G, G ≤ maxGas gas ∧ checkCaseGas code cs G = true := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcs
  refine ⟨gas.getD j 0, le_maxGas gas j, ?_⟩
  have := h.2 j hj
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this

theorem CheckedGas.check {code : Code} {cases : List Case} {gas : List Nat}
    (h : CheckedGas code cases gas) : cases.all (checkCase code) = true :=
  List.all_eq_true.mpr fun _ hcs => by
    obtain ⟨_, -, hg⟩ := h.mem hcs
    exact (checkCaseGas_eq hg).1

/-! ## The cases of each contract kind -/

def cdlWords (off n : Nat) : List Term := (List.range n).map fun i => .cdl (off + 32 * i)

/-- Calldata shorter than `2^64` bytes. -/
def cdsMax : Nat := 2 ^ 64 - 1

/-- The selector word `shr(224, calldataload(0))`. -/
def selTerm : Term := .bin 0x1c (.const 224) (.cdl 0)

/-- The capacity word of `Poseidon2Yul_BN254`, `shl(64, shr(5, sub(calldatasize(), 4)))`, as
the checker normalizes it. -/
def capTerm (fs : Facts) : Term :=
  let w := (do
    let s ← mkBin fs 0x03 (mkInput fs .cds full) (Word.const 4)
    let s ← mkBin fs 0x1c (Word.const 5) s
    mkBin fs 0x1b (Word.const 64) s).getD default
  w.t

/-- `huffPerm`: one case, any calldata. -/
def huffPermCases (c : Params) : List Case :=
  [⟨"any calldata", [], .perm c (cdlWords 0 c.t)⟩]

/-- `huffHash`: the three arities. -/
def huffHashCases (c : Params) : List Case :=
  [⟨"hash_1 (size < 0x44)", [(.cds, 0, 0x43)], .hash c (cdlWords 4 1)⟩,
   ⟨"hash_2 (size = 0x44)", [(.cds, 0x44, 0x44)], .hash c (cdlWords 4 2)⟩,
   ⟨"hash_3 (size > 0x44)", [(.cds, 0x45, cdsMax)], .hash c (cdlWords 4 3)⟩]

/-- Calldata of `n < 4` bytes: the three argument words are zero. -/
def shortFacts (n : Nat) : Facts := [(.cds, n, n), (.cdl 4, 0, 0), (.cdl 0x24, 0, 0), (.cdl 0x44, 0, 0)]

/-- The permutation of three words and the capacity, for calldata below 4 bytes and from 4 on
(`yulHash` without the call value check). -/
def hashCapCases (cv : Facts) (c : Params) : List Case :=
  let long : Facts := [(.cds, 4, cdsMax)] ++ cv
  ([0, 1, 2, 3].map fun n =>
    let short := shortFacts n ++ cv
    (⟨s!"size {n}", short, .permHead c (cdlWords 4 3 ++ [capTerm short])⟩ : Case)) ++
  [⟨"size >= 4", long, .permHead c (cdlWords 4 3 ++ [capTerm long])⟩]

/-- `yulHash`: a call value reverts, else `hashCapCases`. -/
def yulHashCases (c : Params) : List Case :=
  ⟨"call value", [(.cds, 0, cdsMax), (.cv, 1, W - 1)], .revertEmpty⟩ :: hashCapCases [(.cv, 0, 0)] c

/-- `hashV2`: below 4 bytes the fixed word `hashV2Short`, from 4 bytes on `hashCapCases` with any
call value. -/
def hashV2Cases (c : Params) : List Case :=
  ([0, 1, 2, 3].map fun n =>
    (⟨s!"size {n}", shortFacts n, .words [Interface.hashV2Short]⟩ : Case)) ++
  (hashCapCases [] c).drop 4

/-- `yulPerm` with selector `sel`: every reverting class, and the call. -/
def yulPermCases (c : Params) (sel : Nat) : List Case :=
  let low : List Case :=
    if sel = 0 then [] else
    [⟨"selector below, no value", [(.cds, 4, cdsMax), (selTerm, 0, sel - 1), (.cv, 0, 0)], .revertEmpty⟩,
     ⟨"selector below, value", [(.cds, 4, cdsMax), (selTerm, 0, sel - 1), (.cv, 1, W - 1)],
      .revertEmpty⟩]
  [⟨"size < 4, no value", [(.cds, 0, 3), (.cv, 0, 0)], .revertEmpty⟩,
   ⟨"size < 4, value", [(.cds, 0, 3), (.cv, 1, W - 1)], .revertEmpty⟩] ++ low ++
  [⟨"selector above, no value", [(.cds, 4, cdsMax), (selTerm, sel + 1, 2 ^ 32 - 1), (.cv, 0, 0)],
    .revertEmpty⟩,
   ⟨"selector above, value", [(.cds, 4, cdsMax), (selTerm, sel + 1, 2 ^ 32 - 1), (.cv, 1, W - 1)],
    .revertEmpty⟩,
   ⟨"call value", [(.cds, 4, cdsMax), (selTerm, sel, sel), (.cv, 1, W - 1)], .revertEmpty⟩,
   ⟨"short arguments", [(.cds, 4, 4 + 32 * c.t - 1), (selTerm, sel, sel), (.cv, 0, 0)], .revertEmpty⟩,
   ⟨"call", [(.cds, 4 + 32 * c.t, cdsMax), (selTerm, sel, sel), (.cv, 0, 0)], .perm c (cdlWords 4 c.t)⟩]

end Poseidon2.Checker

namespace Poseidon2.Checker

/-- Every element passes if every index does (for the per-case kernel theorems). -/
theorem all_of_getD {α : Type} [Inhabited α] (f : α → Bool) :
    ∀ (l : List α), (∀ j, j < l.length → f (l.getD j default) = true) → l.all f = true
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true]
    refine ⟨h 0 (by simp), all_of_getD f l fun j hj => ?_⟩
    simpa using h (j + 1) (by simp; omega)

end Poseidon2.Checker
