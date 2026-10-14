# Formal verification (Lean 4)

The goal of this directory is a kernel-checked proof that the generated runtime bytecode of the contracts (Huff t = 2, 3, 4, 8, 12, 16, 20, 24, 28; Yul t = 2, 3, 4, 8, 12 under legacy solc) returns the Poseidon2 output over BN254 for every input. The proofs are about the raw runtime bytes, so huff-neo, solc and the generators stay outside the trusted base.

**Status: the contract theorems, partial and total correctness, are proven without hypotheses about the checker, but this is not yet a "formally verified" claim** (see "Not yet claimed" below). What is proven, kernel-checked and free of `sorry`, axioms of ours and `native_decide`:

- the Poseidon2 specification, its constants (round constants and internal diagonals derived from the Grain LFSR of the HorizenLabs script), 73 known-answer tests against other implementations, and the calldata interface of every contract;
- that a symbolic checker accepts every exported bytecode on every calldata class of its interface (all 35: the 17 small ones committed in `Poseidon2/Proofs/`, the 18 large ones written by `scripts/proof.sh` and checked in CI, see below);
- that the checker's symbolic run of the spec evaluates to the spec (`Checker/Bridge.lean`), that its word terms and intervals (`Checker/BoundsSound.lean`) and its field values (`Checker/FieldSound.lean`) describe what the EVM operations compute, and that checking a run in segments loses nothing (`Checker/Segments.lean`);
- that every instruction the checker's `step` accepts is one EVM step (`Evm/Sim.lean`, `Evm/MemSim.lean`, against EVMLean's `Xstep` with the EIP-8024 overlay): the EVM runs out of gas, which it does only with less gas than the step costs, or pays exactly the gas the checker computes for the instruction (`insGas`: the opcode's static gas, 3 per word copied, and the growth of `memCost`, the memory expansion EVMLean charges), moves `pc` by the instruction's length, changes nothing but the stack, the memory and the active words, and the checker's new state describes the EVM's (`StRel`: the stack, the word memory against the byte memory, `msize` against the active words, and the gas bound `Cₘ(activeWords) + gas < 2^256`, which every step keeps and which keeps the memory size from wrapping). Covered: `PUSH0` .. `PUSH32`, `DUP1` .. `DUP16` and `SWAP1` .. `SWAP16` (one lemma each), DUPN, SWAPN, `POP`, `JUMPDEST`, `ADD`, `MUL`, `SUB`, `DIV`, `MOD`, `ADDMOD`, `MULMOD`, `LT`, `GT`, `SLT`, `SGT`, `EQ`, `ISZERO`, `AND`, `OR`, `XOR`, `NOT`, `SHL`, `SHR`, `CALLVALUE`, `CALLDATASIZE`, `RETURNDATASIZE`, each in every form the checker accepts (exact words with any modulus, field values, `P`), which keep the memory (`Evm/Memory.lean`: `step_mem`, `sim_lift`); and `MLOAD`, `MSTORE`, `MSIZE`, `CALLDATALOAD`, `CALLDATACOPY` (from an offset or from `CALLDATASIZE`), `CODECOPY`, in the forms the checker accepts (exact addresses and offsets, whole words);
- that EVMLean's byte arrays behave as functions of the index (`Evm/Bytes.lean`): `ByteArray.write` changes exactly the bytes it writes, `readWithPadding` and `readBytes` read zeros past the end, and 32 big-endian bytes are the spec's `wordBytes` of their value (for the returned words);
- that the checker's decoder agrees with EVMLean's at every `pc` its run reaches (`Evm/Decode.lean`): those `pc`s stay below `33 · 2^20` and advance by the instruction's length (`Dec`), EVMLean decodes there the opcode the checker saw, the `PUSH` value it pushed (the checker rejects a `PUSH` cut by the end of the code, so EVMLean's unpadded reading of one never matters), DUPN / SWAPN with `17 ≤ n`, and every jump destination the checker finds is in EVMLean's `D_J` (unchanged by EIP-8024);
- that `JUMP` and `JUMPI` (both ways) are EVM steps that set `pc` (`Evm/Control.lean`; `STOP` halts with empty output);
- that the checker's whole run is the EVM's (`Evm/Run.lean`): every instruction the run accepts is one EVM step costing the gas the checker adds to its state (`St.gas`, at least 1), the stack stays at most 1024 items and the atom table only grows along the run, and, iterating `Eip8024.X` with the fuel `Ξ` gives (gas + 1), for every case the checker accepts the EVM's run of the call runs out of gas, the call's gas being below the checker's gas up to there, or reaches a state related to the checker's at its final `RETURN` or `REVERT` having paid exactly that gas (`reaches_final`). The segmented kernel checks of `Proofs/` prove `checkCaseGas` (`checkCase` and the gas of the run), whose first half is what `reaches_final` takes (`seg_run` composes the segments), so they need nothing more;
- that the last instruction is the EVM's (`Evm/Final.lean`): the checker's `RETURN` is the EVM halting with output `encodeWords` of the values its returned words describe, having paid the memory expansion the checker adds to the run's gas, or running out of gas with less than that (`final_return`); its empty `REVERT` is the EVM reverting with empty output, which costs nothing (`final_revert`);
- that a valuation of the atoms exists (`Checker/Valuation.lean`): every `pow5` atom is a form over older atoms (`Tab.WF`), because every form the checker holds names only atoms its table has (`St.Inv`, kept by every step, `step_inv` / `runN_inv'`) and the spec's symbolic run keeps that too (`permG_inv`); then `defsVal` values the atoms from the oldest on (`Tab.WF.valid`), and under it the spec's forms are the case's words (`spec_sound`);
- that the checker runs only the 102 opcodes of `accepted`, that on them the static gas and the memory expansion of Cancun, Prague, Osaka and Amsterdam, as transcribed from execution-specs, are the checker's, that EVMLean defines exactly Cancun's opcodes, and that no Osaka target can reach DUPN / SWAPN by falling through from an entry on the raw bytes (`Evm/Forks.lean`, see Forks);
- that on the Osaka targets the overlay is EVMLean itself (`Evm/Cancun.lean`): if the checker accepts a case on a code that passes `ovFree` (from `pc = 0` and from every jump destination, no DUPN / SWAPN among the instructions the run can fall through to), then every call in that case gets the same result from `Eip8024.Ξ` as from EVMLean's Cancun `EVM.Ξ` (`xi_cancun`: along the run every EVM step is at an instruction of a checked segment, where the overlay's step is EVMLean's). All 26 Osaka targets prove `ovFree` by kernel evaluation and state it as `cancun : Eip8024.Ξ σ σ₀ g A I = Ethereum.EVM.Ξ σ σ₀ g A I` for every call, and `totalCancun`, `total` of `EVM.Ξ` (per kind: `huffPerm_cancun`, `huffHash_cancun`, `yulPerm_cancun`, `yulHash_cancun`, `hashV2_cancun`), so their theorems hold of EVMLean without the overlay;
- **`CheckerSound`** (`Soundness.lean`), proven as `Soundness.checkerSound` (`Evm/Final.lean`): if the checker accepts a bytecode on a case, then every call that meets the case's facts, run by `Eip8024.Ξ` with any gas, runs out of gas or ends exactly as the case expects. It asks one thing of the case: its input words are below `2^256`. Without that it is false for contrived cases (a fact can pin a term whose value is above `2^256 - 1` to `2^256 - 1`, and the checker reads the pinned constant); every case of `Check.lean` reads calldata words and the capacity word, which `Theorems.lean` shows are below `2^256`;
- **`CheckerTotal`** (`Soundness.lean`), proven as `Soundness.checkerTotal`: if the checker accepts a bytecode on a case with gas `G` (`checkCaseGas`), then every such call given at least `G` gas ends exactly as the case expects with `G` gas used (`Exact (g - G)`: a success or revert with exactly the expected bytes and `g - G` gas left; running out of gas or any other exception falsifies it), and every such call given less than `G` runs out of gas. Both come from `checker_core` (from `reaches_final`, `Xi_eq`, `spec_sound`, `outputsMatch_sound` and the gas carried along the run), so `G` is exactly the gas of the call, not a bound;
- the contract theorems (`Theorems.lean`, and each artifact's `correct`, `total` and `enough` in `Proofs/`), without hypotheses about the checker. Each contract kind has one dispatch over its cases (`huffPerm_of`, `huffHash_of`, `yulPerm_of`, `hashCap_of`, `yulHash_of`, `hashV2_of`) that turns what each case gives into the interface's outcome, and it gives both statements. For the Huff permutation entries, partial correctness:

  ```lean
  theorem huffPerm_correct (a : Artifact) (c : Params)
      (hc : (huffPermCases c).all (checkCase (Code.ofBytes a.bytes)) = true)
      (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
      (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
      Matches (Eip8024.Ξ σ σ₀ g A I) (huffPerm c cd)
  ```

  and total correctness:

  ```lean
  theorem huffPerm_total (a : Artifact) (c : Params) (gas : List Nat)
      (hc : CheckedGas (Code.ofBytes a.bytes) (huffPermCases c) gas)
      (cd : List UInt8) (v : Nat) (hcd : cd.length < 2 ^ 64) (hv : v < W)
      (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) (hI : Runs a cd v I) :
      Total (huffPermCases c) gas ⟨cd, v⟩ g.toNat (Eip8024.Ξ σ σ₀ g A I) (huffPerm c cd)

  def Total (cases : List Case) (gas : List Nat) (e : Env) (g : Nat) (r : ...) (o : Outcome) :=
    ∃ j, j < cases.length ∧ FactsHold e (cases.getD j default).facts ∧
      (gas.getD j 0 ≤ g → Exact (g - gas.getD j 0) r o) ∧
      (g < gas.getD j 0 → r = .error .OutOfGass)
  ```

  `Proofs/Huff/Amsterdam/T2.lean` instantiates them with its kernel checks as `correct` and `total`: there `gas` is the literal `[5912]` and `checkG : CheckedGas code cases gas` is kernel-checked, so a call of the t = 2 permutation given at least 5,912 gas returns exactly `encodeWords (permutationWords c (calldataWords cd 0 c.t))` and leaves `g - 5912`, and given less runs out of gas. Every artifact's file has its `gas` list (one entry per case, in the order of its `cases`), and `enough` states the simpler corollary: with at least the most gas of any case, every call ends exactly as the interface says. `Runs a cd v I` fixes only the call frame's code, calldata and call value (`runs_exists`: every artifact, calldata and value has such a frame); the accounts, substate, gas and the rest of the frame are arbitrary. `Matches` holds for an out-of-gas (or out-of-fuel) error, for a success whose output bytes are exactly the interface's, and for nothing else: any other exceptional halt, a revert, or other bytes falsify it.

What the theorems do not say, and why this is not yet called formally verified:

- **The semantics.** EVMLean models Cancun; the contracts target Osaka and Amsterdam. Every opcode the checker runs has the same static gas and memory expansion in Cancun, Prague, Osaka and Amsterdam (`Evm/Forks.lean`, against tables transcribed from execution-specs), the Osaka targets' theorems hold of EVMLean's own `Ξ` (`cancun`, they never run DUPN / SWAPN), and the forks add no opcode the checker runs besides those two (Forks, below). That the forks also run these opcodes as Cancun does is read off the execution-specs sources, not proven, and Amsterdam is not final. The EIP-8024 overlay, which only the Huff Amsterdam theorems need, is checked against the EIP text, execution-specs and revm (EIP-8024 overlay, below), not proven against a model of Amsterdam.
- **The frame, not the transaction.** `Ξ` is the execution of the call frame. A transaction calling the contract also pays the intrinsic 21,000 and the calldata (Gas, below); a contract calling it pays the `CALL` and the account access. Neither is part of the theorems.
- **The olean trust** (`leanchecker` over the import closure, C9), the spec items listed under Constant provenance (C10, C11), the correspondence of `Bytecode/` with deployments (D13), and an independent review of the statements (E15) are still open.

## Layout

| Path | Contents |
| ---- | -------- |
| `Poseidon2/Spec/Permutation.lean` | The permutation, written once over an `Ops` record (zero, add, add and multiply by a constant, S-box with a threaded state), its `ZMod P` instance, `permutationWords` (inputs read modulo `P`, outputs below `P`) |
| `Poseidon2/Spec/Sponge.lean` | `hashG` / `hash` / `hashWords` (the t = 4 `hash_1` / `hash_2` / `hash_3`: `[x.., 0.., n · 2^64]` permuted once, element 0), over any `Ops`; the Barretenberg / Noir sponge and proofs that the two agree for 1, 2 and 3 inputs |
| `Poseidon2/Spec/Interface.lean` | Calldata to returndata of every contract kind: `huffPerm`, `huffHash`, `yulHash`, `yulPerm`, `hashV2` (the deployed v2 Huff) |
| `Poseidon2/Spec/Constants/T<t>.lean` | Round numbers, round constants and internal diagonal per width, with their source in the file header |
| `Poseidon2/Spec/Vectors.lean` | 73 known-answer tests from other implementations and 3 agreement checks with this repository's reference (t = 20, 24, 28), all by `decide +kernel` |
| `Poseidon2/Spec/Grain.lean`, `GrainCheck.lean`, `DiagCheck.lean` | The HorizenLabs Grain LFSR in Lean, and proofs that every width's round constants and internal diagonal are its output |
| `Poseidon2/Evm/Eip8024.lean` | DUPN / SWAPN / EXCHANGE (EIP-8024) on top of EVMLean, with tests; `Steps.lean`: `Xstep` of every `DUPn` / `SWAPn` and of DUPN / SWAPN, the overlay agreeing with EVMLean elsewhere, EVMLean's word operations as natural numbers; `Sim.lean`: the per-opcode simulation lemmas (stack and arithmetic); `Bytes.lean`: byte arrays as functions of the index, big-endian words; `Memory.lean`: the word memory against the byte memory (`MemRel`, `StRel`), `SimulatesM`, the lift of `Sim.lean`'s lemmas; `MemSim.lean`: the memory and data opcodes; `Decode.lean`: the checker's decoder and jump destinations against EVMLean's `decode` and `D_J`; `Control.lean`: `JUMP`, `JUMPI`, `STOP`; `Run.lean`: every accepted instruction as an EVM step, the run iterated with gas up to the final `RETURN` / `REVERT`; `Final.lean`: `RETURN`, `REVERT` and the proof of `CheckerSound` (`checkerSound`); `Cancun.lean`: the overlay is EVMLean on runs that never reach DUPN / SWAPN (`ovFree`, `xi_cancun`); `Forks.lean`: the opcodes the checker runs, their gas and the opcode sets in Cancun, Prague, Osaka and Amsterdam, the DUPN / SWAPN scan of the Osaka targets; `ForkData.lean`: the fork tables, written by `scripts/forks.sh`; `Smoke.lean` shows EVMLean is wired in |
| `Poseidon2/Bytecode/` | The runtime bytecode of 35 artifacts, written by `poseidon2-gen lean-export` (generator-rs), with byte count and keccak256 |
| `Poseidon2/Checker/` | The symbolic checker (`Forms`, `Bounds`, `SymExec`, `Check`), segmented checking (`Segments` for the bytecode run, `SpecSegments` for the spec side), its soundness (`Bridge`: the spec run; `BoundsSound`: word terms; `FieldSound`: field values; `Valuation`: the atom table's shape and a valuation of it), mutation tests (`Mutations`) |
| `Poseidon2/Soundness.lean` | `CheckerSound` and `CheckerTotal`, the soundness propositions, and `Exact` (both proven in `Evm/Final.lean`) |
| `Poseidon2/Theorems.lean` | For every contract kind: check accepted implies the interface behaviour (`*_correct`, through `checkerSound`), and check accepted with its gas implies the exact interface behaviour with that gas (`*_total`, `Total`, through `checkerTotal`) |
| `Poseidon2/Proofs/` | Library `Poseidon2Proofs`: per artifact, the kernel check with the gas of each case (`gas`, `checkG`) and the contract theorems (`correct`, `total`, `enough`), written by `scripts/Emit.lean`; the 17 small artifacts are committed, the 18 large ones go to `Proofs/Generated/` (not committed) as a chain of parts |
| `Poseidon2/AxiomCheck.lean`, `Audit.lean`, `Proofs/Audit.lean` | The audits (below) |
| `scripts/` | Generators of the data files (node, Lean), `Dev.lean` (the checker by `#eval` on every artifact, with the gas of each case), `Call.lean` (every artifact called through `Eip8024.Ξ` by `#eval`, again with exactly the gas it used and one less), `Opcodes.lean` (the opcodes each artifact's runs execute and decode, by `#eval`), `Eip8024Diff.lean` and `eip8024-diff.sh` (the overlay against revm on a corpus of programs, by `#eval`), `forks.sh` (writes `Evm/ForkData.lean` from execution-specs), `Emit.lean` (writes `Proofs/`), `proof.sh` (writes and builds the proof of an artifact), `export.sh` (rewrites `Bytecode/`) |

## Building

```sh
cd formal-verification
export LEAN_NUM_THREADS=1     # one Lean process at a time, see below
lake exe cache get            # Mathlib oleans
lake build                    # spec, checker, theorems, audit
lake build Poseidon2.Proofs.Audit                 # kernel checks of the 17 committed artifacts
scripts/proof.sh $(scripts/proof.sh --list large) # write and kernel-check the other 18
scripts/export.sh             # rewrite Bytecode/ from the sources (forge, cargo)
```

The toolchain is `leanprover/lean4:v4.29.0` (`lean-toolchain`), the one EVMLean pins. Dependencies (`lakefile.toml`, pinned in `lake-manifest.json`):

- Mathlib `v4.29.0` (`8a17838`), the revision EVMLean's manifest pins.
- EVMLean, https://github.com/lefterislazar/EVMLean at `fd4f5e6` (the commit EquiVM pins). Only its Lean modules are built. Its lakefile also declares an `extern_lib` (C code for sha256 / keccak cloned from GitHub and compiled with `cc`, plus `git submodule update` for the Ethereum tests), but Lake links extern libraries only into executables and precompiled modules, and this package builds neither, so a plain `lake build` runs no C compiler and clones nothing. Some precompiles (BN_ADD, SNARKV, ...) shell out to `python3` when executed; that is runtime only and never happens in a proof, and none of our `#eval`s reaches a precompile. Logically those precompiles return `default` (`totallySafePerformIO`); the Poseidon2 contracts call none.

`Poseidon2Proofs` is not a default target. Lake has no job limit; it runs as many Lean processes as `LEAN_NUM_THREADS` (default: one per core), and each uses that many threads. With `LEAN_NUM_THREADS=1` every step below fits a 16 GB machine. Do not run `lake build Poseidon2Proofs` with `Proofs/Generated/` present: its globs then build all 18 large artifacts too.

Measured on an Apple M2 Max with 96 GB, `/usr/bin/time -l`, one at a time:

- `lake exe cache get` on a clean clone: 92 s (Mathlib cache already in `~/.cache/mathlib`, so no download), `.lake` 7.3 GB.
- `lake build Poseidon2 Poseidon2.Proofs.Audit` on that clone (EVMLean, then everything of ours): 1,600 s at 11.1 GB with `LEAN_NUM_THREADS=1`, `.lake` 7.6 GB afterwards. The peak is `GrainCheck.lean` (383 s, 11.1 GB); then `DiagCheck.lean` (743 s, 6.4 GB), which imports it. With `LEAN_NUM_THREADS=2` the same build takes 1,170 s but two processes reach 14.5 GB together. `Evm/Forks.lean`, added since, takes 87 s at 5.4 GB (its 26 scans, 1 to 6 s each; one kernel check for all of them held 20 GB). `Evm/Cancun.lean` takes 2 s; each Osaka target's `ovFree` kernel check adds a few seconds to its proof (all 35 proofs rebuilt: at most 7.6 GB, Huff Osaka t = 28 448 s at 5.6 GB).
- The 17 committed artifacts (`scripts/proof.sh`, writing included): 573 s for all 17, at most 5.4 GB.
- The 18 large ones (`scripts/proof.sh`, writing included): 83 to 446 s and 3.6 to 7.6 GB each, in the table below.

## How the bytecode is checked

1. `poseidon2-gen lean-export` writes each runtime bytecode as a Lean literal (`Bytecode/`).
2. The checker (`Checker/`) runs it symbolically once per calldata class of its interface (`Check.lean`: `huffPermCases`, `huffHashCases`, `yulHashCases`, `yulPermCases`, `hashV2Cases`). Values are exact word terms with intervals, linear forms over atoms in `F_p` with an upper bound on the raw word, or partial S-box powers. Atoms are input words read in the field and fifth powers of earlier forms, looked up by definition, not by creation order. Control flow, jump destinations (EVMLean's `D_J`) and memory addresses must be concrete; every raw `ADD` / `MUL` / `SHL` on field values is bounded below `2^256`; a branch must be decided by its interval. Anything else fails. The checker also adds up the gas of its run (Gas, below).
3. The returned forms are compared with `permG linOps` / `hashG linOps` run on the input atoms over the bytecode's own atom table: the same definition the spec uses, so the spec and the checker cannot drift.
4. In the kernel (`Proofs/`), long runs are checked in segments between literal checker states, so no declaration holds the whole run; `Segments.lean` proves that segments compose (`seg_run`). The spec side of a permutation case is checked the same way, in segments of rounds (`SpecSegments.lean`: `permG_eq_roundsRun`, `rounds_seg`, `resultOk_perm`, `resultOkGas_perm`). Each case is checked together with its gas (`checkCaseGas`), which the file states as a literal.

Checker results (`scripts/Dev.lean`, `#eval`): every case of the 33 artifacts built from the current sources passes (148 cases), the deployed Yul v2 passes its 6, the deployed Huff v2 passes from 4 bytes of calldata on. Below 4 bytes the deployed Huff v2 adds its capacity word, which wrapped below zero, to another word unreduced; for empty calldata it returns `0x0fcc8f62…82d5` (anvil returns the same), where the deployed Yul v2 returns the permutation of its capacity word. `Mutations.lean` checks that one-byte mutations are rejected.

Kernel checks (`decide +kernel`), all 35 artifacts, one at a time, without error. The 17 small ones (Huff t = 2, 3, 4 on both forks; Yul t = 2, 3, 4 at all three optimizer settings; both deployed v2 contracts) need no checkpoint (segments of 8,000 instructions, the spec side in one declaration); their files are a few KB, committed, and audited together by `Proofs/Audit.lean`. The 18 large ones are written by `scripts/proof.sh` with segments of 1,000 instructions and 10 rounds and three kernel checks per part file; their files are 1.3 to 9.9 MB each (80 MB in all), so they are not committed. `Emit.lean` is deterministic (two runs give the same bytes), so the committed tree and the scripts regenerate them, and CI checks every one (below). Each generated file ends with `#assert_standard_axioms_here`, and the last file of an artifact also audits its parts.

| Artifact | Parts | Bytecode segments | Files | Wall | Peak RSS |
| -------- | ----- | ----------------- | ----- | ---- | -------- |
| Huff t = 8, Amsterdam / Osaka | 6 / 6 | 6 / 6 | 4.9 / 4.9 MB | 164 / 167 s | 5.8 / 5.8 GB |
| Huff t = 12 | 7 / 7 | 8 / 9 | 9.3 / 2.2 MB | 345 / 112 s | 7.6 / 4.4 GB |
| Huff t = 16 | 8 / 8 | 11 / 12 | 2.8 / 3.0 MB | 164 / 151 s | 5.4 / 4.6 GB |
| Huff t = 20 | 9 / 9 | 14 / 16 | 4.4 / 4.7 MB | 239 / 225 s | 6.0 / 5.0 GB |
| Huff t = 24 | 10 / 11 | 17 / 20 | 5.8 / 6.7 MB | 338 / 299 s | 7.5 / 5.4 GB |
| Huff t = 28 | 11 / 12 | 20 / 25 | 8.5 / 9.9 MB | 446 / 432 s | 7.4 / 5.6 GB |
| Yul t = 8, optimizer 1,000,000 / 200 / off | 9 / 10 / 10 | 8 / 9 / 10 | 1.3 / 1.4 / 1.4 MB | 83 / 95 / 92 s | 3.6 / 3.8 / 3.7 GB |
| Yul t = 12 | 11 / 11 / 12 | 14 / 14 / 15 | 2.3 / 2.5 / 2.4 MB | 150 / 165 / 163 s | 4.2 / 4.5 / 4.4 GB |

Every permutation case has 7 spec segments. All 35 were measured again after the checker came to compute the gas (the checkpoint states carry it and every case is checked with its gas): the large ones took at most 15 s longer than before and no more memory (`/usr/bin/time -l` gives Huff Amsterdam t = 12 7.81 GB, t = 28 7.61 GB, t = 8 5.98 GB), the 17 small ones 573 s instead of 372 s. The parts of a large artifact do not import `Theorems.lean` (only its last file does); with it they took up to 8.0 GB (t = 12). Wall and peak are of `scripts/proof.sh <artifact>` with `LEAN_NUM_THREADS=1` (writing the files, about 10 to 15 s, included; peak is the largest Lean process, sampled every second). Before this layout, with segments of 3,000 instructions, the spec side in one declaration and one file per artifact, Huff t = 28 took 19.7 GB, for two reasons found by checking single declarations: the spec run of t = 28 alone took 12.7 GB, and a `CODECOPY` of 27 words near the end of the 64 KB code took 13 GB because each word walked the code list from its start (now it is walked once). A monolithic check (no segments) overflows the kernel's stack at 38.8 GB. Memory also grows with the number of kernel checks one Lean process holds, hence the parts.

## Gas

The checker adds up the gas of its run as EVMLean charges it (Cancun, and on these opcodes also Prague, Osaka and Amsterdam, see Forks): each instruction's static gas (`staticGas`: 0 for `STOP`, `RETURN`, `REVERT`; 1 for `JUMPDEST`; 2 for `PUSH0`, `POP`, `CALLVALUE`, `CALLDATASIZE`, `RETURNDATASIZE`, `MSIZE`; 5 for `MUL`, `DIV`, `MOD`; 8 for `ADDMOD`, `MULMOD`, `JUMP`; 10 for `JUMPI`; 3 for the rest it accepts, DUPN and SWAPN included; `CALLDATACOPY` and `CODECOPY` 3 plus 3 per word), plus the memory expansion, which over a run is `memCost` (EVMLean's `Cₘ`, 3 per word and words squared over 512) of the memory the run ends with, the `RETURN`'s range included. The path is concrete, so this is one number per case, `G`. The per-artifact files list it per case (`gas`), and the kernel checks it with the run (`checkCaseGas`). `CheckerTotal` makes it the exact gas of the call: with at least `G` the call ends as the interface says and `g - G` is left, with less it runs out of gas.

`G` is execution gas: what `Ξ` consumes, the gas of the contract's own call frame. That is the number `poseidon2-gen verify` reports as call gas (revm's gas spent by the outermost frame) and the number in brackets in a forge or cast trace. A transaction calling the contract directly uses 21,000 + 4 per zero byte and 16 per non-zero byte of calldata + `G` (the EIP-7623 floor of 10 per zero and 40 per non-zero byte is lower for every returning call below, and can be higher for a reverting one, whose `G` is small); for example the deployed Huff v2 on three words of calldata (one of them `P + 7`; 66 zero and 34 non-zero bytes) used 36,677 = 21,000 + 808 + 14,869 on anvil (Osaka). On Amsterdam the 21,000 becomes 15,000 for a call without value (EIP-2780: 12,000 for the sender, 3,000 for the recipient) and the floor 15,000 + 64 per calldata byte (EIP-7976), still lower for every returning call below with calldata of just its input words (that needs `G` above 60 per calldata byte; the least is Huff t = 3, 7,653 for 96 bytes, about 80). A contract calling it pays the `CALL` and the account access on top.

Every `G` of a returning case equals the measured call-frame gas, on both forks for Huff and at every solc setting for Yul. Huff, `poseidon2-gen verify --hardfork <fork> 2 3 4 8 12 16 20 24 28` (revm on the fork's rules), `G` / measured:

| t | Amsterdam | Osaka |
| - | --------- | ----- |
| 2 | 5,912 / 5,912 | 5,912 / 5,912 |
| 3 | 7,653 / 7,653 | 7,653 / 7,653 |
| 4, `hash_1` / `hash_2` / `hash_3` | 11,895, 11,902, 11,975 / the same | 11,895, 11,902, 11,975 / the same |
| 8 | 23,933 / 23,933 | 24,499 / 24,499 |
| 12 | 34,288 / 34,288 | 35,696 / 35,696 |
| 16 | 44,966 / 44,966 | 48,635 / 48,635 |
| 20 | 55,763 / 55,763 | 63,188 / 63,188 |
| 24 | 66,431 / 66,431 | 77,045 / 77,045 |
| 28 | 79,032 / 79,032 | 94,502 / 94,502 |

Yul, `forge test -vvvv` of `test/Poseidon2Yul*.t.sol` (`permute`) and `test/Poseidon2.t.sol` (`hash_1`, `hash_2`, `hash_3` of `Poseidon2Yul_BN254`, the same gas for all three and for calldata below 4 bytes) built as `scripts/export.sh` builds them, on forge's Amsterdam EVM, `G` / measured:

| t | optimizer 1,000,000 runs | 200 runs | off |
| - | ------------------------ | -------- | --- |
| 2 | 9,019 / 9,019 | 9,019 / 9,019 | 10,200 / 10,200 |
| 3 | 10,992 / 10,992 | 10,992 / 10,992 | 12,913 / 12,913 |
| 4 | 15,152 / 15,152 | 15,158 / 15,158 | 15,320 / 15,320 |
| 8 | 31,450 / 31,450 | 34,756 / 34,756 | 35,175 / 35,175 |
| 12 | 48,991 / 48,991 | 51,021 / 51,021 | 54,184 / 54,184 |

The deployed v2 contracts, `cast call --trace` on anvil (Osaka) with the runtime code of `deployed-artifacts/`: Huff 14,869 / 14,869 (calldata of 4 bytes or more), Yul 19,639 / 19,639. `scripts/Call.lean` gets the same numbers from EVMLean itself, and shows that each call returns with exactly that gas (0 left) and runs out of gas with one less. The reverting cases (the Yul wrappers: 43 gas with a call value, 68 below 4 bytes, 101 for another selector, 157, or 193 with the optimizer off, for short arguments; `Poseidon2Yul_BN254` and the deployed Yul v2: 43 with a call value) are kernel-checked like the others but were not measured.

## Forks

The theorems are about EVMLean (Cancun) with the EIP-8024 overlay. The Huff contracts are generated for Amsterdam (DUPN / SWAPN, code up to 64 KB) and for Osaka, the Yul builds are compiled for Osaka (solc knows no later fork, `foundry.toml`) and run in tests on forge's Amsterdam EVM, the deployed Yul v2 was compiled for Cancun. `Evm/Forks.lean` checks what carrying the theorems to Prague, Osaka and Amsterdam needs, against `Evm/ForkData.lean`, which `scripts/forks.sh` writes from ethereum/execution-specs (Cancun, Prague, Osaka at `a6c4bcf`, Amsterdam at `1689800` on `forks/amsterdam`, 2026-10-06), checking for every entry the byte of the mnemonic and that the function the fork runs for it charges the named constant:

- **The opcodes.** The checker runs no opcode outside `accepted`, 102 first bytes (`ctl_rejects`): `STOP`, `ADD`, `MUL`, `SUB`, `DIV`, `MOD`, `ADDMOD`, `MULMOD`, `LT`, `GT`, `SLT`, `SGT`, `EQ`, `ISZERO`, `AND`, `OR`, `XOR`, `NOT`, `SHL`, `SHR`, `CALLVALUE`, `CALLDATALOAD`, `CALLDATASIZE`, `CALLDATACOPY`, `CODECOPY`, `RETURNDATASIZE`, `POP`, `MLOAD`, `MSTORE`, `JUMP`, `JUMPI`, `MSIZE`, `JUMPDEST`, `PUSH0` .. `PUSH32`, `DUP1` .. `DUP16`, `SWAP1` .. `SWAP16`, DUPN, SWAPN, `RETURN`, `REVERT`. The 35 artifacts' runs execute 71 of them (`scripts/Opcodes.lean`): not `DIV`, `SGT`, `XOR`, `RETURNDATASIZE`, `STOP`, and of the `PUSH`es only `PUSH0`, 1, 2, 4, 8, 31 and 32. DUPN / SWAPN are executed by Huff Amsterdam only (DUPN by t = 2, 4, 8 .. 28, SWAPN by t = 16 .. 28; t = 3 needs neither).
- **The opcode sets.** EVMLean defines exactly Cancun's opcodes (`parse_defined`, over all 256 bytes). Prague defines the same, Osaka adds `CLZ` (EIP-7939), Amsterdam `SLOTNUM` (EIP-7843) and DUPN, SWAPN, EXCHANGE (EIP-8024) (`defined_*`). Of these only DUPN and SWAPN are accepted; `CLZ` and `SLOTNUM` are `INVALID` in the overlay, `EXCHANGE` is modelled by the overlay (so that it is the whole EIP), and none of the three ever runs.
- **Static gas.** On every accepted opcode it defines, each of the four forks charges the checker's `staticGas` (`staticGas_fork`): 0 `STOP` / `RETURN` / `REVERT`, 1 `JUMPDEST`, 2 `PUSH0` / `POP` / `CALLVALUE` / `CALLDATASIZE` / `RETURNDATASIZE` / `MSIZE`, 5 `MUL` / `DIV` / `MOD`, 8 `ADDMOD` / `MULMOD` / `JUMP`, 10 `JUMPI`, 3 plus 3 per word for the copies, 3 for the rest, DUPN / SWAPN included (Amsterdam). EVMLean charges `staticGas` (the simulations), so its Cancun gas is each fork's. EIP-7904, once a repricing of `DIV`, `MOD`, `ADDMOD`, `MULMOD` and others, is now Informational and changes nothing.
- **Memory expansion.** `calculate_memory_gas_cost` is 3 per word plus words squared over 512 in all four (`memCost_fork`), and `calculate_gas_extend_memory` differs only in type annotations.
- **Semantics.** From Cancun to Amsterdam the execution-specs functions of the accepted opcodes, the jump destination analysis (`get_valid_jump_destinations`, unchanged by EIP-8024), the 1024 stack limit and the exceptional halt (the frame loses all its gas; Amsterdam also refills the state gas reservoir, which these contracts never draw on) change only in type annotations and field names (`evm.message.data` to `evm.call_data`). This is read from the diffs, not machine-checked.
- **DUPN / SWAPN in the Osaka targets.** Osaka lacks them (`0xe6` / `0xe7` halt), the overlay runs them. No Osaka target (Huff Osaka, the 15 Yul builds, both deployed v2) runs either, and this is proven: each one's `ovFree` (kernel) and `cancun` state that every call is the same under EVMLean's Cancun `Ξ` as under the overlay (`Evm/Cancun.lean`), so their theorems, `totalCancun` included, need neither the overlay nor an argument about it. Their decoded bytes do hold some (Huff Osaka t = 12 .. 28 and Yul 200 runs t = 8, in data and metadata), which is why `ovFree` follows control flow: from `pc = 0` and from every jump destination it walks the decoded instructions the run can fall through to and stops at one it cannot (`JUMP`, `RETURN`, `REVERT`, `STOP`, anything the checker rejects). Huff Amsterdam t = 2 and t = 28 fail it, t = 3 passes (it needs neither opcode). `osaka_scan` (`Forks.lean`) is the earlier check of the same on the raw bytes, decoding as `D_J` does; it is now a cross-check.
- **Code size.** A deployment limit, not part of `Ξ`. Up to Osaka it is 24,576 bytes (EIP-170), which every Osaka target meets (at most 24,370); Amsterdam raises it to 65,536 (EIP-7954), which Huff Amsterdam t = 8 .. 28 need (25,124 to 64,615 bytes) and meet.
- **Outside the frame.** Osaka's transaction gas cap (EIP-7825, 16,777,216), Amsterdam's intrinsic gas and calldata floor (EIP-2780, EIP-7976, Gas above), state gas (EIP-8037) and state access costs (EIP-8038, no opcode here touches an account or storage), and the log a call with value emits (EIP-7708, before the code runs) are not part of `Ξ` and charge nothing the contracts' code pays.

So no opcode the runs execute differs between EVMLean with the overlay and Prague, Osaka or Amsterdam, in gas or (by the diffs) in semantics, and `G` is the same on all four. revm agrees: `poseidon2-gen verify` (revm 43.0.3) measures the Huff `G` of the Gas table on Amsterdam and Osaka again (2026-10-14).

Amsterdam is not final: its meta EIP (EIP-7773) is in Review and its EIPs (EIP-8024 and EIP-7954 included) in Last Call; it is active on Sepolia since 2026-10-06, and mainnet has no date. A change before mainnet needs `scripts/forks.sh` and the build again. Chains other than Ethereum's (the deployed v2 is also on L2 testnets) are not covered.

## EIP-8024 overlay

`Evm/Eip8024.lean` adds DUPN, SWAPN and EXCHANGE to EVMLean (which reads `0xe6` .. `0xe8` as `INVALID`). Only the Huff Amsterdam theorems depend on it (the Osaka targets' also hold without it, `cancun`). It was compared line by line with the EIP (ethereum/EIPs `9d27a4f`, Last Call until 2026-11-01) and with execution-specs `forks/amsterdam` (`1689800`, `dupn`, `swapn`, `exchange`, `decode_single`, `decode_pair`, `buffer_read`), and agrees on: the immediate `code[pc + 1]`, `0` past the end of the code; the invalid ranges (`90 < x < 128`, for EXCHANGE `81 < x < 128`), an exceptional halt; `n = (x + 145) mod 256` and `decode_pair` (`decodePair_eip`, `decodePair_range`, and `generator-rs` checks it inverts the EIP's encoders); DUPN copies the `n`th item, SWAPN swaps the top with the `n + 1`th, EXCHANGE the `n + 1`th with the `m + 1`th; underflow when the stack has fewer than `n`, `n + 1`, `m + 1` items, overflow when DUPN finds 1024; 3 gas; `pc + 2`; jump destination analysis unchanged (EVMLean's `D_J` reads the immediate as an instruction, which a valid immediate never makes `JUMPDEST` or a `PUSH`, so it skips nothing and keeps `e6 5b`'s `JUMPDEST`; `mem_D_J` proves the checker's destinations are `D_J`'s). One difference, not in what a call does: the EIP charges the gas before it checks the immediate and the stack, the overlay checks them first. Every one of these is an exceptional halt, which EVMLean's callers of `Ξ` treat alike (`.error _`), so only the exception's name differs, and on the checker's runs none of them happens.

`scripts/eip8024-diff.sh` runs a corpus of 3,581 programs through the overlay (`Eip8024.X`, `#eval`) and through revm 43.0.3 at Amsterdam (`poseidon2-gen eip8024-corpus`, `generator-rs/src/eip8024.rs`): every immediate byte of the three opcodes at the stack depths around underflow and overflow, the immediate past the end of the code, the gas boundary, the EIP's execution tests, jumps onto the opcode, its immediate and the byte after, and sequences, plus three `PUSH`es cut by the end of the code. Every program ends the same in both (stack, gas left, or an exceptional halt). 446 halts are named differently: 440 because revm names a DUPN underflow `StackOverflow` (its `dup` has one failure for both), 6 because of the order of checks above (an invalid immediate or a short stack with under 3 gas: revm `OutOfGas`, the overlay `InvalidInstruction` or `StackUnderflow`). The three cut `PUSH`es show EVMLean's known unpadded reading (Trusted base). The run takes about 3 s; it is development mode (`#eval`), not a proof. The same corpus through EVMLean patched with DUPN / SWAPN / EXCHANGE and padded `PUSH`es (two patches prepared for upstream, not submitted) leaves only revm's 440 names.

## Continuous integration

`.github/workflows/formal-verification.yml` runs on pushes to `main` and on pull requests that touch `formal-verification/`, `src/`, `test/`, `generator-rs/`, `deployed-artifacts/` or `foundry.toml`, on GitHub-hosted runners (4 vCPU, 16 GB, 14 GB of disk guaranteed), all with `LEAN_NUM_THREADS=1`:

| Job | What it runs | Measured here (M2 Max) |
| --- | ------------ | ---------------------- |
| Lean build | `leanprover/lean-action@v1`: elan, `lake exe cache get`, `lake build Poseidon2 Poseidon2.Proofs.Audit`, `.lake` cached for the jobs below; then `scripts/proof.sh` on the 17 small artifacts and `git diff --exit-code Poseidon2/Proofs` | 1,600 s at 11.1 GB on a clean clone; the proof check 87 s at 1.9 GB (it only rewrites the files, the build is cached) |
| Exported bytecode is current | `scripts/export.sh` (forge `v1.8.5` with the submodules, the Rust exporter with huff-neo), then `git diff --exit-code Poseidon2/Bytecode`, so the proofs cover the bytecode the sources compile to | 181 s on a clean clone (the exporter's release build and the Osaka regeneration included), 0.3 GB; the files it writes are identical on two checkouts at different paths |
| Kernel check, one per large artifact (18) | restores the build, `scripts/proof.sh <artifact>` | 83 to 446 s at 3.6 to 7.6 GB (table above) |

The Yul builds of `export.sh` name their remappings: forge's detected ones carry the absolute path of the checkout into the solc metadata, whose hash ends the code, so the bytes depended on where the repository was checked out. The committed Yul bytecode was exported again that way; only the 53 metadata bytes at the end of each changed (checked by comparing the code before them), and the 15 Yul artifacts were kernel-checked again.

Disk: `.lake` is 7.6 GB after the build and the toolchain 2.5 GB, so with the cache archive the jobs come close to the 14 GB; the Lean jobs first delete the runner's Android SDK, .NET and GHC (the `df` before and after is in the log). The cache is keyed on the toolchain, the manifest and the commit, like `lean-action`'s own, and holds all of `.lake`.

Not yet run on GitHub (nothing here was pushed): the workflow file was checked by parsing it and by running each job's commands locally on a clean clone (`git clone`, `lake exe cache get`, the build, the 17-artifact check, `scripts/proof.sh huff/osaka/t28` in 425 s at 5.9 GB, `scripts/export.sh` and its diff). Untested until the first push: the actions themselves (`lean-action` restoring the cache in the matrix jobs without a rebuild, the matrix from the `artifacts` job), the runner's speed (expect a few times slower than here; every job is far below the 6 h limit) and its free disk.

## Trusted base

- The Lean 4 kernel and the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), enforced by the audits.
- The Mathlib and EVMLean `.olean` files. `lake exe cache get` downloads prebuilt Mathlib oleans, and the kernel does not re-check imported declarations. To discharge this, rebuild Mathlib from source instead of using the cache, or replay the whole import closure with the `leanchecker` that ships with the toolchain (`lake env leanchecker --fresh Poseidon2.Audit`; not run here, it re-checks all of Mathlib's imported part and takes hours).
- The specification in `Spec/` (`Permutation.lean`, `Sponge.lean`, `Interface.lean`, the constants): that it states the Poseidon2 of the paper (https://eprint.iacr.org/2023/323) and what the contracts are meant to compute. The known-answer tests are the evidence that it matches other implementations.
- For the contract theorems: EVMLean's semantics plus `Evm/Eip8024.lean`, whose fork is Cancun while the contracts target Osaka and Amsterdam. Carrying the theorems to those forks (Forks, above) trusts the tables `scripts/forks.sh` transcribes from execution-specs into `Evm/ForkData.lean`, the reading of the execution-specs diffs that the forks run the checker's opcodes as Cancun does, and, for the Huff Amsterdam contracts only, `Evm/Eip8024.lean` as a model of EIP-8024 (EIP-8024 overlay, above); the Osaka targets' theorems also hold of EVMLean's own `Ξ` (`cancun`). There is no Lean model of Osaka or Amsterdam. One deviation of EVMLean from the EVM is known: it reads a `PUSH` immediate cut short by the end of the code as the bytes that are there, where the EVM pads them on the right with zeros (`0x61 0xab` at the end pushes `0xab00`); the checker rejects such a `PUSH`, so no proof relies on it (`decode_push` takes all the immediate bytes). A fix for it, and DUPN / SWAPN / EXCHANGE in EVMLean itself, are prepared as patches for upstream but not submitted.
- The correspondence between the Lean literals in `Bytecode/` and deployed code: each file records the keccak256 of its code (the account's `codehash`); the kernel does not recompute it. The deployed v2 artifacts' initcode hashes equal the ones in `deployed-artifacts/*/v2/README.md`.

Not trusted: huff-neo, solc, the generators, the checker (`CheckerSound` is proven), the checkpoint states (re-checked by the kernel), the Lean compiler (no `native_decide`).

## Sorry and axiom list

No `sorry`, no `axiom` declared here, no `native_decide`. `Audit.lean` checks every constant of every module under `Poseidon2/` (selected by defining module, so private and auxiliary declarations are included) and fails on any file under `Poseidon2/` it does not import; `Proofs/Audit.lean` does the same for the committed files of `Poseidon2/Proofs/`, and every generated file under `Proofs/Generated/` audits its own constants (`#assert_standard_axioms_here`, checked to reject `sorry`, `native_decide` and an `axiom`) and, in an artifact's last file, those of its parts. `CheckerSound` and `CheckerTotal` are theorems (`checkerSound`, `checkerTotal`), not axioms or hypotheses.

## Constant provenance

| t | Rf / Rp | Round constants and diagonal | Cross-checked against | Test vectors |
| - | ------- | ---------------------------- | --------------------- | ------------ |
| 2 | 8 / 56 | TaceoLabs co-snarks `poseidon2_bn254_t2.rs` | noir-poseidon (round constants) | noir-poseidon (11) |
| 3 | 8 / 56 | TaceoLabs co-snarks `poseidon2_bn254_t3.rs` | noir-poseidon (round constants) | noir-poseidon (10), HorizenLabs |
| 4 | 8 / 56 | TaceoLabs co-snarks `poseidon2_bn254_t4.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11), Barretenberg, co-snarks (inputs above P), noir-lang `hash_1` / `hash_2` / `hash_3`, Barretenberg sponge |
| 8 | 8 / 57 | TaceoLabs co-snarks `poseidon2_bn254_t8.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11) |
| 12 | 8 / 57 | LeastAuthority TaceoLabs-nullifier-oracle-service `bn254_t12.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11) |
| 16 | 8 / 57 | TaceoLabs co-snarks `poseidon2_bn254_t16.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11) |
| 20 | 8 / 57 | **this repository's generator** (`generator-rs` at `93ee033`) | Grain LFSR in Lean (round constants and diagonal) | none external; agreement with `generator-rs/src/reference.rs` only |
| 24 | 8 / 57 | **this repository's generator** | as t = 20 | as t = 20 |
| 28 | 8 / 59 | **this repository's generator** | as t = 20 | as t = 20 |

- Exact URLs and commits are in each file header and next to each test.
- Every round constant of every width is the Grain LFSR output of the HorizenLabs script for its t, Rf and Rp (`GrainCheck.lean`). Every internal diagonal for t ≥ 4 is `r - 1` for the script's diagonal draw number k = 4, 30, 6, 6, 42, 2, 34 (t = 4 .. 28) after the round constants (`DiagCheck.lean`). For t = 2 and 3 the diagonal is `[1, 2]` and `[1, 1, 2]` (the paper's fixed internal matrices).
- **Still trusted:** that draw k is the first one passing the script's minimal-polynomial check (a security selection, not part of the function), and the round numbers. `scripts/rounds.mjs` recomputes Rf / Rp from the script's security inequalities (8/56 for t ≤ 4, 8/57 for t = 8 to 24, 8/59 for t = 28); that is a node check, not a proof.
- **t = 28 has no reference implementation of its linear layers**: HorizenLabs and TaceoLabs stop at t = 24; t = 28 follows the script's generic `t % 4 == 0` matrix, which the spec states for every t ≥ 8.
- The repository's generator reproduces every table for t ≤ 16 value for value, which was checked when the t ≥ 20 files were written.

## Scripts

`scripts/` holds what wrote the data files, so they can be regenerated and reviewed: `transcribe.mjs` (constants for t ≤ 16, from the fetched upstream files named in it), `vectors.mjs` and `genvectors.mjs` (`Vectors.lean`), `dump-params.rs` and `genwide.mjs` (t = 20, 24, 28), `rounds.mjs` (Rf / Rp), `GenDiag.lean` (the `DiagCheck.lean` certificates), `Dev.lean` (the checker in development mode, with the gas of each case), `Call.lean` (the calls through `Eip8024.Ξ`, development mode, with the gas they used), `Eip8024Diff.lean` with `eip8024-diff.sh` (the EIP-8024 overlay against revm on the corpus `poseidon2-gen eip8024-corpus` writes, development mode), `Emit.lean` (`Proofs/`), `proof.sh` (runs `Emit.lean` with each artifact's settings and builds the result) and `export.sh` (runs the exporter on fresh forge builds). The node scripts read upstream files fetched by hand into the working directory; their URLs and commits are in the scripts.

## Conventions

- The state is a `List`; constants are natural numbers read in the field by `Nat.cast`.
- Contract inputs are raw 256-bit words. The spec reads each modulo `P` (`permutationWords`, `hashWords`) and returns canonical outputs (`ZMod.val`, below `P`).
- Kernel evaluation only: every computational check is `decide +kernel`. `#eval` appears only in `scripts/`, to compute certificates the kernel then checks and as development checks (`Dev.lean`, `Call.lean`), never as evidence for a theorem.
