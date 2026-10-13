import Poseidon2.Checker.Bounds

/-!
# Symbolic execution of runtime bytecode

The checker runs the bytecode once per case of the call (a set of `Facts`), with:

* concrete control flow: `JUMP` / `JUMPI` targets must be exact and valid jump destinations
  (EVMLean's `D_J`), a `JUMPI` condition must be decided by its interval;
* concrete memory: addresses exact, words keyed by address, overlapping unequal accesses
  rejected, `MSIZE` tracked;
* symbolic values `SV`: an exact word term, a linear form with an upper bound on the raw
  value, or `c · l^k` for an S-box in progress. Every raw `ADD` / `MUL` on field values is
  checked to stay below `2^256`; `ADDMOD` / `MULMOD` / `MOD` by `P` move between them;
* `CODECOPY` from the code bytes, `CALLDATALOAD` / `CALLDATACOPY` at exact offsets;
* DUPN / SWAPN (EIP-8024) decoded as `Evm/Eip8024.lean` does.

Anything else (an unsupported opcode, a symbolic address or jump, an undecided branch, a
possible overflow, an exceptional halt such as `INVALID` or a stack overflow) makes the run
fail: the checker never accepts a path it cannot follow exactly.
-/

namespace Poseidon2.Checker

open Poseidon2.Spec

/-- A symbolic stack or memory value. -/
inductive SV where
  /-- an exact word -/
  | word (w : Word)
  /-- a value `≤ b` that is `≡ l (mod P)` -/
  | lin (l : Lin) (b : Nat)
  /-- the value `c · l^k mod P`, `2 ≤ k ≤ 4` -/
  | pw (c : Nat) (l : Lin) (k : Nat)
  deriving Repr, Inhabited

def SV.const (v : Nat) : SV := .word (Word.const v)

def SV.exact : SV → Option Nat
  | .word w => w.exact
  | _ => none

/-! ## Decoding -/

/-- An instruction. -/
inductive Ins where
  | op (b : Nat)
  | push (v : Nat)
  | dupn (n : Nat)
  | swapn (n : Nat)
  /-- an EIP-8024 immediate out of range, or PUSH data cut by the end of the code -/
  | bad (b : Nat)
  deriving Repr, Inhabited

/-- `n` bytes big-endian, `none` if the code ends first. -/
def takeBytes : Nat → List Nat → Nat → Option (Nat × List Nat)
  | 0, bs, acc => some (acc, bs)
  | n + 1, b :: bs, acc => takeBytes n bs (acc * 256 + b)
  | _ + 1, [], _ => none

/-- EIP-8024 `decode_single`. -/
def decodeSingle (x : Nat) : Option Nat :=
  if x ≤ 90 ∨ 128 ≤ x then some ((x + 145) % 256) else none

/-- The instructions with their `pc` (fuel: the byte count). -/
def decode : Nat → Nat → List Nat → List (Nat × Ins)
  | 0, _, _ => []
  | _, _, [] => []
  | f + 1, pc, b :: bs =>
    if 0x60 ≤ b ∧ b ≤ 0x7f then
      match takeBytes (b - 0x5f) bs 0 with
      | some (v, rest) => (pc, .push v) :: decode f (pc + 1 + (b - 0x5f)) rest
      | none => [(pc, .bad b)]
    else if b = 0x5f then (pc, .push 0) :: decode f (pc + 1) bs
    else if b = 0xe6 ∨ b = 0xe7 then
      let x := bs.headD 0
      match decodeSingle x with
      | some n => (pc, if b = 0xe6 then .dupn n else .swapn n) :: decode f (pc + 2) bs.tail
      | none => [(pc, .bad b)]
    else (pc, .op b) :: decode f (pc + 1) bs

/-- The valid jump destinations, as EVMLean's `D_J` finds them: every `0x5b` byte that is not
PUSH data (DUPN / SWAPN count as one-byte instructions there). -/
def jumpdests : Nat → Nat → List Nat → List Nat
  | 0, _, _ => []
  | _, _, [] => []
  | f + 1, pc, b :: bs =>
    if 0x60 ≤ b ∧ b ≤ 0x7f then jumpdests f (pc + 1 + (b - 0x5f)) (bs.drop (b - 0x5f))
    else if b = 0x5b then pc :: jumpdests f (pc + 1) bs
    else jumpdests f (pc + 1) bs

/-- For every valid jump destination, the instructions from it on. -/
def destSuffixes (dj : List Nat) : List (Nat × Ins) → List (Nat × List (Nat × Ins))
  | [] => []
  | (pc, i) :: rest =>
    let tail := destSuffixes dj rest
    match i with
    | .op 0x5b => if dj.contains pc then (pc, (pc, i) :: rest) :: tail else tail
    | _ => tail

def findDest (pc : Nat) : List (Nat × List (Nat × Ins)) → Option (List (Nat × Ins))
  | [] => none
  | (p, s) :: r => if p = pc then some s else findDest pc r

/-- The decoded code. -/
structure Code where
  bytes : List Nat
  ins : List (Nat × Ins)
  dests : List (Nat × List (Nat × Ins))

def Code.ofBytes (bs : List Nat) : Code :=
  let ins := decode bs.length 0 bs
  ⟨bs, ins, destSuffixes (jumpdests bs.length 0 bs) ins⟩

/-- The word of the code at `off`, zero past the end (`CODECOPY`). -/
def codeWord (bs : List Nat) (off : Nat) : Nat :=
  ((bs.drop off).take 32 ++ List.replicate (32 - ((bs.drop off).take 32).length) 0).foldl
    (fun acc b => acc * 256 + b) 0

/-! ## State and steps -/

structure St where
  stk : List SV
  mem : List (Nat × SV)
  /-- active memory in bytes, a multiple of 32 -/
  msize : Nat
  tab : Tab
  deriving Inhabited

def St.init : St := ⟨[], [], 0, Tab.empty⟩

abbrev M := Except String

def push (s : St) (v : SV) : M St :=
  if s.stk.length < 1024 then .ok { s with stk := v :: s.stk } else .error "stack overflow"

def pop1 (s : St) : M (SV × St) :=
  match s.stk with
  | a :: r => .ok (a, { s with stk := r })
  | [] => .error "stack underflow"

def pop2 (s : St) : M (SV × SV × St) :=
  match s.stk with
  | a :: b :: r => .ok (a, b, { s with stk := r })
  | _ => .error "stack underflow"

def pop3 (s : St) : M (SV × SV × SV × St) :=
  match s.stk with
  | a :: b :: c :: r => .ok (a, b, c, { s with stk := r })
  | _ => .error "stack underflow"

def exactOf (what : String) (v : SV) : M Nat :=
  match v.exact with
  | some x => .ok x
  | none => .error s!"{what} is not exact"

/-- The memory size after touching `[a, a + n)` (no change for `n = 0`). -/
def touch (msize a n : Nat) : Nat :=
  if n = 0 then msize else max msize ((a + n + 31) / 32 * 32)

/-- Reads the word at `a`: the stored word, zero if nothing overlaps, else fail. -/
def readMem (a : Nat) : List (Nat × SV) → M SV
  | [] => .ok (SV.const 0)
  | (k, v) :: r =>
    if k = a then .ok v
    else if k + 32 ≤ a ∨ a + 32 ≤ k then readMem a r
    else .error s!"unaligned memory read at {a}"

/-- Writes the word at `a`; fails on a partial overlap. -/
def writeMem (a : Nat) (v : SV) : List (Nat × SV) → M (List (Nat × SV))
  | [] => .ok [(a, v)]
  | (k, w) :: r =>
    if k = a then .ok ((a, v) :: r)
    else if k + 32 ≤ a ∨ a + 32 ≤ k then ((k, w) :: ·) <$> writeMem a v r
    else .error s!"unaligned memory write at {a}"

def mstore (s : St) (a : Nat) (v : SV) : M St := do
  let mem ← writeMem a v s.mem
  .ok { s with mem := mem, msize := touch s.msize a 32 }

/-- `n` words from `a`. -/
def readWords (mem : List (Nat × SV)) : Nat → Nat → M (List SV)
  | 0, _ => .ok []
  | n + 1, a => do
    let v ← readMem a mem
    let vs ← readWords mem n (a + 32)
    .ok (v :: vs)

/-- The field view of a value: a form and a bound on the raw value. -/
def toLin (v : SV) (tb : Tab) : M (Lin × Nat × Tab) :=
  match v with
  | .word w =>
    match w.exact with
    | some x => .ok (Lin.const x, x, tb)
    | none => let (l, tb) := tb.atom (.word w.t); .ok (l, w.hi, tb)
  | .lin l b => .ok (l, b, tb)
  | .pw _ _ _ => .error "power used linearly"

/-- `c · l^k` view. -/
def toPow (v : SV) (tb : Tab) : M (Nat × Lin × Nat × Tab) :=
  match v with
  | .pw c l k => .ok (c, l, k, tb)
  | v => do let (l, _, tb) ← toLin v tb; .ok (1, l, 1, tb)

/-- The constant of a value read in the field, if it is one. -/
def fieldConst (v : SV) : Option Nat :=
  match v with
  | .word w => w.exact
  | .lin l _ => l.asConst
  | .pw _ _ _ => none

/-- `v · c mod P`. -/
def scaleMod (v : SV) (c : Nat) (tb : Tab) : M (SV × Tab) :=
  if c % P = 0 then .ok (SV.const 0, tb) else
  match v with
  | .pw c' l k => .ok (.pw (c' * c % P) l k, tb)
  | v => do let (l, _, tb) ← toLin v tb; .ok (.lin (l.scale c) (P - 1), tb)

/-- `MULMOD a b P` on non-constant values. -/
def mulModP (a b : SV) (tb : Tab) : M (SV × Tab) :=
  match fieldConst a, fieldConst b with
  | some x, some y => .ok (SV.const (x * y % P), tb)
  | some x, none => scaleMod b x tb
  | none, some y => scaleMod a y tb
  | none, none => do
    let (ca, la, ka, tb) ← toPow a tb
    let (cb, lb, kb, tb) ← toPow b tb
    if !la.beq lb then .error "MULMOD of two different forms" else
    let k := ka + kb
    let c := ca * cb % P
    if k < 5 then .ok (.pw c la k, tb)
    else if k = 5 then
      let (x, tb) := tb.sbox la
      .ok (.lin (x.scale c) (P - 1), tb)
    else .error "power above 5"

/-- A word operand, or fail. -/
def wordOf (v : SV) : M Word :=
  match v with
  | .word w => .ok w
  | _ => .error "field value used as a word"

/-- Binary operations other than the field ones. -/
def wordBin (fs : Facts) (op : Nat) (a b : SV) : M SV := do
  let wa ← wordOf a
  let wb ← wordOf b
  match mkBin fs op wa wb with
  | some w => .ok (.word w)
  | none => .error s!"unsupported operation {op}"

/-- `ADD` / `MUL`: on words exactly, else in the field with the raw bound checked. -/
def addMul (fs : Facts) (op : Nat) (a b : SV) (tb : Tab) : M (SV × Tab) :=
  -- two words stay exact terms when one is a constant (addresses, sizes); two input words
  -- are added in the field, so the sum is not a new atom
  let exactWords := match a, b with
    | .word x, .word y => x.exact.isSome || y.exact.isSome
    | _, _ => false
  if exactWords then do let v ← wordBin fs op a b; .ok (v, tb) else
    if op = 0x01 then do
      let (la, ba, tb) ← toLin a tb
      let (lb, bb, tb) ← toLin b tb
      if ba + bb < W then .ok (.lin (la.add lb) (ba + bb), tb)
      else .error "ADD may overflow"
    else
      match a.exact, b.exact with
      | some c, _ => do
        let (l, bnd, tb) ← toLin b tb
        if bnd * c < W then .ok (.lin (l.scale c) (bnd * c), tb) else .error "MUL may overflow"
      | _, some c => do
        let (l, bnd, tb) ← toLin a tb
        if bnd * c < W then .ok (.lin (l.scale c) (bnd * c), tb) else .error "MUL may overflow"
      | _, _ => .error "MUL of two field values"

/-- Writes `n` words from the code at `src` to memory at `dst`. -/
def codeCopy (bs : List Nat) (s : St) : Nat → Nat → Nat → M St
  | 0, _, _ => .ok s
  | n + 1, dst, src => do
    let s ← mstore s dst (SV.const (codeWord bs src))
    codeCopy bs s n (dst + 32) (src + 32)

/-- Writes `n` calldata words from `src` to memory at `dst`. -/
def cdCopy (fs : Facts) (s : St) : Nat → Nat → Nat → M St
  | 0, _, _ => .ok s
  | n + 1, dst, src => do
    let s ← mstore s dst (.word (mkInput fs (.cdl src) full))
    cdCopy fs s n (dst + 32) (src + 32)

/-- Writes `n` zero words to memory at `dst`. -/
def zeroFill (s : St) : Nat → Nat → M St
  | 0, _ => .ok s
  | n + 1, dst => do
    let s ← mstore s dst (SV.const 0)
    zeroFill s n (dst + 32)

/-- One instruction that does not change control flow. -/
def step (fs : Facts) (code : Code) (i : Ins) (s : St) : M St :=
  match i with
  | .push v => push s (SV.const v)
  | .dupn n =>
    match s.stk[n - 1]? with
    | some v => push s v
    | none => .error "stack underflow"
  | .swapn n =>
    match s.stk, s.stk[n]? with
    | a :: _, some b => .ok { s with stk := (s.stk.set 0 b).set n a }
    | _, _ => .error "stack underflow"
  | .bad b => .error s!"invalid instruction {b}"
  | .op b =>
    if 0x80 ≤ b ∧ b ≤ 0x8f then
      match s.stk[b - 0x80]? with
      | some v => push s v
      | none => .error "stack underflow"
    else if 0x90 ≤ b ∧ b ≤ 0x9f then
      let n := b - 0x8f
      match s.stk, s.stk[n]? with
      | a :: _, some c => .ok { s with stk := (s.stk.set 0 c).set n a }
      | _, _ => .error "stack underflow"
    else match b with
    | 0x01 | 0x02 => do
      let (x, y, s) ← pop2 s
      let (v, tb) ← addMul fs b x y s.tab
      push { s with tab := tb } v
    | 0x1b => do
      let (x, y, s) ← pop2 s
      match x.exact, y with
      -- `shl(k, v)` of a field value: `v · 2^k`, the raw bound checked
      | some k, .lin l bnd =>
        if k < 256 ∧ bnd * 2 ^ k < W then push s (.lin (l.scale (2 ^ k)) (bnd * 2 ^ k))
        else .error "SHL may overflow"
      | _, _ => push s (← wordBin fs b x y)
    | 0x03 | 0x04 | 0x10 | 0x11 | 0x12 | 0x13 | 0x14 | 0x16 | 0x17 | 0x18 | 0x1c => do
      let (x, y, s) ← pop2 s
      push s (← wordBin fs b x y)
    | 0x15 | 0x19 => do
      let (x, s) ← pop1 s
      let w ← wordOf x
      match mkUn fs b w with
      | some w => push s (.word w)
      | none => .error "unsupported unary operation"
    | 0x06 => do
      let (x, n, s) ← pop2 s
      let n ← exactOf "MOD modulus" n
      match x.exact with
      | some v => push s (SV.const (if n = 0 then 0 else v % n))
      | none =>
        if n ≠ P then .error "MOD by a symbolic value other than P" else
        match x with
        | .pw c l k => push s (.pw c l k)
        | x => do
          let (l, bnd, tb) ← toLin x s.tab
          push { s with tab := tb } (.lin l (min bnd (P - 1)))
    | 0x08 => do
      let (x, y, n, s) ← pop3 s
      let n ← exactOf "ADDMOD modulus" n
      match x.exact, y.exact with
      | some a, some c => push s (SV.const (if n = 0 then 0 else (a + c) % n))
      | _, _ =>
        if n ≠ P then .error "ADDMOD by other than P" else do
        let (la, _, tb) ← toLin x s.tab
        let (lb, _, tb) ← toLin y tb
        push { s with tab := tb } (.lin (la.add lb) (P - 1))
    | 0x09 => do
      let (x, y, n, s) ← pop3 s
      let n ← exactOf "MULMOD modulus" n
      match x.exact, y.exact with
      | some a, some c => push s (SV.const (if n = 0 then 0 else a * c % n))
      | _, _ =>
        if n ≠ P then .error "MULMOD by other than P" else do
        let (v, tb) ← mulModP x y s.tab
        push { s with tab := tb } v
    | 0x34 => push s (.word (mkInput fs .cv full))
    | 0x35 => do
      let (a, s) ← pop1 s
      let off ← exactOf "CALLDATALOAD offset" a
      push s (.word (mkInput fs (.cdl off) full))
    | 0x36 => push s (.word (mkInput fs .cds full))
    | 0x3d => push s (SV.const 0)
    | 0x37 => do
      let (d, sr, n, s) ← pop3 s
      let d ← exactOf "CALLDATACOPY destination" d
      let n ← exactOf "CALLDATACOPY size" n
      if n % 32 ≠ 0 then .error "CALLDATACOPY size not a multiple of 32" else
      match sr with
      -- from `calldatasize()`: past the end, zeros (solc's memory zeroing idiom)
      | .word ⟨.cds, _, _⟩ => zeroFill s (n / 32) d
      | sr => do
        let sr ← exactOf "CALLDATACOPY source" sr
        cdCopy fs s (n / 32) d sr
    | 0x39 => do
      let (d, sr, n, s) ← pop3 s
      let d ← exactOf "CODECOPY destination" d
      let sr ← exactOf "CODECOPY source" sr
      let n ← exactOf "CODECOPY size" n
      if n % 32 ≠ 0 then .error "CODECOPY size not a multiple of 32" else
      codeCopy code.bytes s (n / 32) d sr
    | 0x50 => do let (_, s) ← pop1 s; .ok s
    | 0x51 => do
      let (a, s) ← pop1 s
      let a ← exactOf "MLOAD address" a
      let v ← readMem a s.mem
      push { s with msize := touch s.msize a 32 } v
    | 0x52 => do
      let (a, v, s) ← pop2 s
      let a ← exactOf "MSTORE address" a
      mstore s a v
    | 0x59 => push s (SV.const s.msize)
    | 0x5b => .ok s
    | _ => .error s!"unsupported opcode {b}"

/-- How a run ends. -/
inductive Res where
  /-- `RETURN` of these words -/
  | ret (ws : List SV) (tab : Tab)
  /-- `REVERT` of this many bytes -/
  | revert (size : Nat)
  /-- `STOP` or the end of the code -/
  | stop
  | fail (pc : Nat) (msg : String)
  deriving Inhabited

/-- Runs from the instruction list `is` (fuel: the instruction budget). -/
def run (fs : Facts) (code : Code) : Nat → List (Nat × Ins) → St → Res
  | 0, _, _ => .fail 0 "out of fuel"
  | _, [], _ => .stop
  | f + 1, (pc, i) :: rest, s =>
    let jump (target : SV) (s : St) : Res :=
      match target.exact with
      | none => .fail pc "symbolic jump target"
      | some t =>
        match findDest t code.dests with
        | some is => run fs code f is s
        | none => .fail pc s!"invalid jump destination {t}"
    match i with
    | .op 0x00 => .stop
    | .op 0x56 =>
      match pop1 s with
      | .ok (t, s) => jump t s
      | .error e => .fail pc e
    | .op 0x57 =>
      match pop2 s with
      | .ok (t, c, s) =>
        match c with
        | .word w =>
          if 0 < w.lo then jump t s
          else if w.hi = 0 then run fs code f rest s
          else .fail pc "undecided JUMPI"
        | _ => .fail pc "JUMPI on a field value"
      | .error e => .fail pc e
    | .op 0xf3 =>
      match pop2 s with
      | .ok (off, sz, s) =>
        match off.exact, sz.exact with
        | some o, some n =>
          if n % 32 ≠ 0 then .fail pc "RETURN size not a multiple of 32" else
          match readWords s.mem (n / 32) o with
          | .ok ws => .ret ws s.tab
          | .error e => .fail pc e
        | _, _ => .fail pc "symbolic RETURN range"
      | .error e => .fail pc e
    | .op 0xfd =>
      match pop2 s with
      | .ok (_, sz, _) =>
        match sz.exact with
        | some n => .revert n
        | none => .fail pc "symbolic REVERT size"
      | .error e => .fail pc e
    | i =>
      match step fs code i s with
      | .ok s => run fs code f rest s
      | .error e => .fail pc e

end Poseidon2.Checker
