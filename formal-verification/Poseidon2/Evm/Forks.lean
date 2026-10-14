import Poseidon2.Evm.ForkData
import Poseidon2.Evm.Decode
import Poseidon2.Bytecode.All

/-!
# The forks the contracts target against EVMLean's Cancun

The theorems are about EVMLean, which models Cancun, with the EIP-8024 overlay
(`Eip8024.lean`); the contracts target Osaka (Huff `Osaka/`, the Yul builds, the deployed v2)
and Amsterdam (Huff `Amsterdam/`). This file checks, against the fork tables `ForkData.lean`
transcribes from ethereum/execution-specs (`scripts/forks.sh`), what the theorems need of those
forks:

* `ctl_rejects`: the checker runs no opcode outside `accepted`, so the theorems rest on these
  opcodes only;
* `parse_defined`: EVMLean defines exactly the opcodes Cancun defines; Prague defines the same,
  Osaka adds `CLZ` (`0x1e`), Amsterdam adds `SLOTNUM` (`0x4b`), DUPN, SWAPN and EXCHANGE
  (`0xe6` .. `0xe8`) (`defined_*`). Of these only DUPN and SWAPN are in `accepted`;
* `staticGas_fork`: the checker's `staticGas`, which the simulations prove is what EVMLean
  charges (`Sim.lean`, `MemSim.lean`, `Control.lean`, `Final.lean`), is the static gas of all
  four forks on every accepted opcode the fork defines; `memCost_fork`: `memCost` is every fork's
  `calculate_memory_gas_cost`;
* `osaka_scan`: no artifact other than the Huff Amsterdam ones can reach `0xe6` / `0xe7` (on the
  raw bytes; the proven form is `cancun` in each Osaka target's proof, `Cancun.lean`).

So on these contracts the forks and the overlay differ in nothing the runs execute: a run of
the overlay executes only `accepted` opcodes, which every fork runs as Cancun does (the
execution-specs diffs of their functions show no change in semantics either; README, Forks),
and the Osaka targets never reach DUPN / SWAPN, which Osaka lacks. Here that last step is argued:
`scan` follows every instruction that falls through from `pc = 0` or from a `JUMPDEST`
byte (every element of `D_J`), stopping at instructions that halt in Osaka and in the overlay
(`STOP`, `JUMP`, `RETURN`, `REVERT`, `INVALID`, `SELFDESTRUCT`, bytes Osaka does not define), so
every `pc` a run in either semantics reaches before its first DUPN / SWAPN is one it visits. It is
proven for the runs the theorems are about by `Cancun.lean` (`ovFree`, `xi_cancun`) and each
Osaka target's `cancun` theorem (`Proofs/`): those runs are the same under EVMLean's own `Ξ`, so
`scan` is a cross-check on the raw bytes. The fork tables are transcribed, not derived: they
are part of the trusted base.
-/

namespace Poseidon2.Evm.Forks

open Ethereum Ethereum.EVM Poseidon2.Checker Poseidon2.Bytecode

/-! ## The opcodes the checker runs -/

/-- The first bytes of the instructions the checker runs: the `.op` bytes `ctl` and `step`
accept, `PUSH1` .. `PUSH32`, `DUP1` .. `DUP16`, `SWAP1` .. `SWAP16` and DUPN / SWAPN. -/
def accepted : List Nat :=
  [0x00, 0x01, 0x02, 0x03, 0x04, 0x06, 0x08, 0x09, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,
    0x17, 0x18, 0x19, 0x1b, 0x1c, 0x34, 0x35, 0x36, 0x37, 0x39, 0x3d, 0x50, 0x51, 0x52, 0x56,
    0x57, 0x59, 0x5b, 0x5f] ++ (List.range 64).map (0x60 + ·) ++ [0xe6, 0xe7, 0xf3, 0xfd]

/-- Every other `.op` makes the run fail. -/
theorem ctl_rejects (b : Nat) (hb : b ∉ accepted) (fs : Facts) (code : Code) (pc : Nat) (s : St) :
    ∃ e, ctl fs code pc (.op b) s = .stop (.fail pc e) := by
  simp only [accepted, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, not_or, not_exists, not_and] at hb
  obtain ⟨⟨⟨h00, h01, h02, h03, h04, h06, h08, h09, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h1b, h1c, h34, h35, h36, h37, h39, h3d, h50, h51, h52, h56, h57, h59, h5b, h5f, -⟩,
    hr⟩, he6, he7, hf3, hfd, -⟩ := hb
  have h80 : ¬(0x80 ≤ b ∧ b ≤ 0x8f) := fun h => hr (b - 0x60) (by omega) (by omega)
  have h90 : ¬(0x90 ≤ b ∧ b ≤ 0x9f) := fun h => hr (b - 0x60) (by omega) (by omega)
  have hs : Checker.step fs code (.op b) s = .error s!"unsupported opcode {b}" := by
    simp only [Checker.step, if_neg h80, if_neg h90]
  refine ⟨s!"unsupported opcode {b}", ?_⟩
  unfold ctl
  split <;> simp_all

/-- An instruction the decoder could not read makes the run fail. -/
theorem ctl_bad (b : Nat) (fs : Facts) (code : Code) (pc : Nat) (s : St) :
    ∃ e, ctl fs code pc (.bad b) s = .stop (.fail pc e) :=
  ⟨_, rfl⟩

/-! ## The opcodes each fork defines -/

/-- Whether EVMLean reads the byte as `INVALID` (undefined, or `0xfe`). -/
def isInvalid : Option Operation → Bool
  | some .INVALID => true
  | _ => false

/-- EVMLean defines exactly what Cancun defines (`INVALID` aside, which execution-specs does
not list). -/
theorem parse_defined :
    (List.range 256).filter (fun n => !isInvalid (parseInstr (UInt8.ofNat n))) = cancunDefined := by
  decide +kernel

/-- The opcodes a fork defines that Cancun does not. -/
def added (l : List Nat) : List Nat := l.filter (fun b => !cancunDefined.contains b)

theorem defined_prague : pragueDefined = cancunDefined := by decide

theorem defined_osaka :
    added osakaDefined = [0x1e] ∧ cancunDefined.all osakaDefined.contains := by
  decide

theorem defined_amsterdam :
    added amsterdamDefined = [0x1e, 0x4b, 0xe6, 0xe7, 0xe8] ∧
      cancunDefined.all amsterdamDefined.contains := by
  decide

/-- Cancun defines every accepted opcode but DUPN / SWAPN, Amsterdam all of them; `CLZ`,
`SLOTNUM` and `EXCHANGE` are not accepted. -/
theorem accepted_defined :
    accepted.filter (fun b => !cancunDefined.contains b) = [0xe6, 0xe7] ∧
      accepted.all amsterdamDefined.contains ∧
      [0x1e, 0x4b, 0xe8].all (fun b => !accepted.contains b) := by
  decide

/-! ## Static gas and memory expansion -/

/-- The checker's instruction for an opcode byte (the immediate does not change the gas). -/
def insOf (b : Nat) : Ins :=
  if 0x60 ≤ b ∧ b ≤ 0x7f then .push 0
  else if b = 0xe6 then .dupn 17
  else if b = 0xe7 then .swapn 17
  else .op b

/-- The words a copy writes, as `staticGas` reads its size from the stack. -/
def copyWords (s : St) : Nat := (((s.stk[2]?).bind SV.exact).getD 0 + 31) / 32

/-- A table entry agrees with `staticGas`: the copies cost `3 + 3 · words` (`staticGas_copy`),
everything else the constant `gas` (checked on the initial state; `staticGas_const` shows the
state does not matter). -/
def Cost.ok (c : Cost) : Bool :=
  if c.op = 0x37 ∨ c.op = 0x39 then c.gas == 3 && c.perWord == 3
  else c.perWord == 0 && staticGas (insOf c.op) St.init == c.gas

theorem staticGas_const (b : Nat) (h37 : b ≠ 0x37) (h39 : b ≠ 0x39) (s s' : St) :
    staticGas (.op b) s = staticGas (.op b) s' := by
  simp only [staticGas]
  split_ifs
  · rfl
  · split <;> simp_all

theorem staticGas_copy (s : St) :
    staticGas (.op 0x37) s = 3 + 3 * copyWords s ∧ staticGas (.op 0x39) s = 3 + 3 * copyWords s :=
  ⟨rfl, rfl⟩

theorem Cost.ok_spec (c : Cost) (h : c.ok = true) (s : St) :
    staticGas (insOf c.op) s = c.gas + c.perWord * copyWords s := by
  unfold Cost.ok at h
  by_cases hc : c.op = 0x37 ∨ c.op = 0x39
  · simp only [hc, if_true, Bool.and_eq_true, beq_iff_eq] at h
    have hi : insOf c.op = .op c.op := by rcases hc with hc | hc <;> simp [insOf, hc]
    rw [hi, h.1, h.2]
    rcases hc with hc | hc <;> rw [hc]
    exacts [(staticGas_copy s).1, (staticGas_copy s).2]
  · simp only [hc, if_false, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hw, hg⟩ := h
    rw [hw, Nat.zero_mul, Nat.add_zero, ← hg]
    unfold insOf
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact staticGas_const _ (by omega) (by omega) _ _

theorem cancunGas_ok : cancunGas.all Cost.ok = true := by decide +kernel
theorem pragueGas_ok : pragueGas.all Cost.ok = true := by decide +kernel
theorem osakaGas_ok : osakaGas.all Cost.ok = true := by decide +kernel
theorem amsterdamGas_ok : amsterdamGas.all Cost.ok = true := by decide +kernel

/-- Every accepted opcode a fork defines has an entry. -/
theorem gas_covers :
    (accepted.filter cancunDefined.contains).all (fun b => cancunGas.any (·.op == b)) ∧
      (accepted.filter pragueDefined.contains).all (fun b => pragueGas.any (·.op == b)) ∧
      (accepted.filter osakaDefined.contains).all (fun b => osakaGas.any (·.op == b)) ∧
      accepted.all (fun b => amsterdamGas.any (·.op == b)) := by
  decide +kernel

/-- `staticGas` is each fork's static gas on every accepted opcode the fork defines. -/
theorem staticGas_fork (t : List Cost)
    (ht : t = cancunGas ∨ t = pragueGas ∨ t = osakaGas ∨ t = amsterdamGas) :
    ∀ c ∈ t, ∀ s, staticGas (insOf c.op) s = c.gas + c.perWord * copyWords s := by
  intro c hc s
  have hok : t.all Cost.ok = true := by
    rcases ht with rfl | rfl | rfl | rfl
    exacts [cancunGas_ok, pragueGas_ok, osakaGas_ok, amsterdamGas_ok]
  exact Cost.ok_spec c (List.all_eq_true.mp hok c hc) s

/-- `memCost` (of a size in bytes that is a multiple of 32, as `msize` always is) is every fork's
`calculate_memory_gas_cost`: `MEMORY_PER_WORD` per word plus the words squared over the divisor. -/
theorem memCost_fork (p : Nat × Nat)
    (hp : p = cancunMem ∨ p = pragueMem ∨ p = osakaMem ∨ p = amsterdamMem) (m : Nat) :
    memCost m = p.1 * (m / 32) + m / 32 * (m / 32) / p.2 := by
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

/-! ## DUPN / SWAPN in the Osaka targets -/

/-- A set of bytes as a number (bit `b` set for `b` in the list). -/
def mask : List Nat → Nat
  | [] => 0
  | b :: bs => 2 ^ b + mask bs

/-- `mask osakaDefined` as a literal, so the kernel does not recompute it for every byte. -/
def osakaMask : Nat := 0xa43f0000000000000000001fffffffffffffffffffff07ffffff00017fff0fff

theorem osakaMask_eq : mask osakaDefined = osakaMask := by decide +kernel

/-- Whether the instruction `b` stops falling through in Osaka and in the overlay: `STOP`,
`JUMP`, `RETURN`, `REVERT`, `INVALID`, `SELFDESTRUCT`, or a byte Osaka does not define (which
Cancun does not define either; `0xe6` / `0xe7` never get here). -/
def halts (m b : Nat) : Bool :=
  b == 0x00 || b == 0x56 || b == 0xf3 || b == 0xfd || b == 0xfe || b == 0xff || (m >>> b) % 2 == 0

/-- `false` if a DUPN / SWAPN byte can be reached: decoding as `D_J` does, `live` is whether the
instruction can be reached by falling through from `pc = 0` or from a `JUMPDEST` byte. The
liveness is matched on at every step so the kernel never holds a long chain of it. -/
def scan (m : Nat) : Nat → Bool → List Nat → Bool
  | 0, _, _ => true
  | _, _, [] => true
  | f + 1, live, b :: bs =>
    match live || b == 0x5b with
    | true =>
      if 0x60 ≤ b ∧ b ≤ 0x7f then scan m f true (bs.drop (b - 0x5f))
      else if b = 0xe6 ∨ b = 0xe7 then false
      else scan m f (!halts m b) bs
    | false =>
      if 0x60 ≤ b ∧ b ≤ 0x7f then scan m f false (bs.drop (b - 0x5f))
      else scan m f false bs

/-- The artifacts that target Osaka (or earlier): the Huff contracts generated for Osaka, the Yul
builds (solc's `evm_version` is at most Osaka) and the deployed v2 contracts. -/
def osakaTargets : List Artifact := [
  Huff.Osaka.T2.artifact, Huff.Osaka.T3.artifact, Huff.Osaka.T4.artifact, Huff.Osaka.T8.artifact,
  Huff.Osaka.T12.artifact, Huff.Osaka.T16.artifact, Huff.Osaka.T20.artifact,
  Huff.Osaka.T24.artifact, Huff.Osaka.T28.artifact,
  Yul.Runs1000000.T2.artifact, Yul.Runs1000000.T3.artifact, Yul.Runs1000000.T4.artifact,
  Yul.Runs1000000.T8.artifact, Yul.Runs1000000.T12.artifact,
  Yul.Runs200.T2.artifact, Yul.Runs200.T3.artifact, Yul.Runs200.T4.artifact,
  Yul.Runs200.T8.artifact, Yul.Runs200.T12.artifact,
  Yul.OptimizerOff.T2.artifact, Yul.OptimizerOff.T3.artifact, Yul.OptimizerOff.T4.artifact,
  Yul.OptimizerOff.T8.artifact, Yul.OptimizerOff.T12.artifact,
  Deployed.HuffV2.artifact, Deployed.YulV2.artifact]

/-- Every exported artifact is a Huff Amsterdam one or an Osaka target. -/
theorem osakaTargets_all :
    (all.map (·.name)).filter (fun n => !osakaTargets.any (·.name == n)) =
      ["huff/amsterdam/t2", "huff/amsterdam/t3", "huff/amsterdam/t4", "huff/amsterdam/t8",
        "huff/amsterdam/t12", "huff/amsterdam/t16", "huff/amsterdam/t20", "huff/amsterdam/t24",
        "huff/amsterdam/t28"] := by
  decide +kernel

/-! One kernel check per Osaka target (one for all of them holds 20 GB). -/
theorem scan_huffOsakaT2 :
    scan osakaMask codeFuel true Huff.Osaka.T2.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT3 :
    scan osakaMask codeFuel true Huff.Osaka.T3.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT4 :
    scan osakaMask codeFuel true Huff.Osaka.T4.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT8 :
    scan osakaMask codeFuel true Huff.Osaka.T8.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT12 :
    scan osakaMask codeFuel true Huff.Osaka.T12.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT16 :
    scan osakaMask codeFuel true Huff.Osaka.T16.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT20 :
    scan osakaMask codeFuel true Huff.Osaka.T20.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT24 :
    scan osakaMask codeFuel true Huff.Osaka.T24.artifact.bytes := by decide +kernel

theorem scan_huffOsakaT28 :
    scan osakaMask codeFuel true Huff.Osaka.T28.artifact.bytes := by decide +kernel

theorem scan_yulRuns1000000T2 :
    scan osakaMask codeFuel true Yul.Runs1000000.T2.artifact.bytes := by decide +kernel

theorem scan_yulRuns1000000T3 :
    scan osakaMask codeFuel true Yul.Runs1000000.T3.artifact.bytes := by decide +kernel

theorem scan_yulRuns1000000T4 :
    scan osakaMask codeFuel true Yul.Runs1000000.T4.artifact.bytes := by decide +kernel

theorem scan_yulRuns1000000T8 :
    scan osakaMask codeFuel true Yul.Runs1000000.T8.artifact.bytes := by decide +kernel

theorem scan_yulRuns1000000T12 :
    scan osakaMask codeFuel true Yul.Runs1000000.T12.artifact.bytes := by decide +kernel

theorem scan_yulRuns200T2 :
    scan osakaMask codeFuel true Yul.Runs200.T2.artifact.bytes := by decide +kernel

theorem scan_yulRuns200T3 :
    scan osakaMask codeFuel true Yul.Runs200.T3.artifact.bytes := by decide +kernel

theorem scan_yulRuns200T4 :
    scan osakaMask codeFuel true Yul.Runs200.T4.artifact.bytes := by decide +kernel

theorem scan_yulRuns200T8 :
    scan osakaMask codeFuel true Yul.Runs200.T8.artifact.bytes := by decide +kernel

theorem scan_yulRuns200T12 :
    scan osakaMask codeFuel true Yul.Runs200.T12.artifact.bytes := by decide +kernel

theorem scan_yulOptimizerOffT2 :
    scan osakaMask codeFuel true Yul.OptimizerOff.T2.artifact.bytes := by decide +kernel

theorem scan_yulOptimizerOffT3 :
    scan osakaMask codeFuel true Yul.OptimizerOff.T3.artifact.bytes := by decide +kernel

theorem scan_yulOptimizerOffT4 :
    scan osakaMask codeFuel true Yul.OptimizerOff.T4.artifact.bytes := by decide +kernel

theorem scan_yulOptimizerOffT8 :
    scan osakaMask codeFuel true Yul.OptimizerOff.T8.artifact.bytes := by decide +kernel

theorem scan_yulOptimizerOffT12 :
    scan osakaMask codeFuel true Yul.OptimizerOff.T12.artifact.bytes := by decide +kernel

theorem scan_deployedHuffV2 :
    scan osakaMask codeFuel true Deployed.HuffV2.artifact.bytes := by decide +kernel

theorem scan_deployedYulV2 :
    scan osakaMask codeFuel true Deployed.YulV2.artifact.bytes := by decide +kernel

theorem osaka_scan :
    osakaTargets.all (fun a => scan osakaMask codeFuel true a.bytes) = true := by
  simp only [osakaTargets, List.all_cons, List.all_nil, scan_huffOsakaT2, scan_huffOsakaT3,
    scan_huffOsakaT4, scan_huffOsakaT8, scan_huffOsakaT12, scan_huffOsakaT16, scan_huffOsakaT20,
    scan_huffOsakaT24, scan_huffOsakaT28, scan_yulRuns1000000T2, scan_yulRuns1000000T3,
    scan_yulRuns1000000T4, scan_yulRuns1000000T8, scan_yulRuns1000000T12, scan_yulRuns200T2,
    scan_yulRuns200T3, scan_yulRuns200T4, scan_yulRuns200T8, scan_yulRuns200T12,
    scan_yulOptimizerOffT2, scan_yulOptimizerOffT3, scan_yulOptimizerOffT4, scan_yulOptimizerOffT8,
    scan_yulOptimizerOffT12, scan_deployedHuffV2, scan_deployedYulV2, Bool.and_true]

/-- The scan is not vacuous: it finds DUPN / SWAPN in Huff Amsterdam t = 2 and t = 28. -/
theorem amsterdam_scan :
    [Huff.Amsterdam.T2.artifact, Huff.Amsterdam.T28.artifact].all
      (fun a => !scan osakaMask codeFuel true a.bytes) = true := by
  decide +kernel

end Poseidon2.Evm.Forks
