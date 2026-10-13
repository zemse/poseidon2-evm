# Formal verification (Lean 4)

The goal of this directory is a kernel-checked proof that the generated runtime bytecode of the contracts (Huff t = 2, 3, 4, 8, 12, 16, 20, 24, 28; Yul t = 2, 3, 4, 8, 12 under legacy solc) returns the Poseidon2 output over BN254 for every input. The proofs are about the raw runtime bytes, so huff-neo, solc and the generators stay outside the trusted base.

**Status: not formally verified.** What is proven, kernel-checked and free of `sorry`, axioms of ours and `native_decide`:

- the Poseidon2 specification, its constants (round constants and internal diagonals derived from the Grain LFSR of the HorizenLabs script), 73 known-answer tests against other implementations, and the calldata interface of every contract;
- that a symbolic checker accepts every exported bytecode on every calldata class of its interface (17 artifacts in `Poseidon2/Proofs/`; the 18 larger ones were kernel-checked the same way here, but their files are not committed, see below);
- that the checker's symbolic run of the spec evaluates to the spec (`Checker/Bridge.lean`), that its word terms and intervals (`Checker/BoundsSound.lean`) and its field values (`Checker/FieldSound.lean`) describe what the EVM operations compute, that checking a run in segments loses nothing (`Checker/Segments.lean`), and the contract-level statements that follow from the check *if* the checker is sound (`Theorems.lean`).

What is **not** proven: that the checker is sound against the EVM semantics. That proposition, `CheckerSound` in `Soundness.lean`, is a definition, not an axiom, and every contract theorem takes it as a hypothesis. Until it is proven, nothing here is "formally verified"; the contract theorems are conditional. What remains for it is the EVM half of the simulation: one lemma per supported opcode relating the checker's step to EVMLean's `Xstep` (EVMLean's own `Ethereum/Theory/OpcodeLemmas.lean` gives the `Xstep` side; `Evm/Sim.lean` has the first ones: `MULMOD`, `ADDMOD`, field `ADD`, `POP`, `DUP1`), the word memory model against EVMLean's byte memory, our decoder and jump destinations against EVMLean's `decode` and `D_J`, the iteration of `X` with gas, and the returned bytes; then their composition into `CheckerSound`.

## Layout

| Path | Contents |
| ---- | -------- |
| `Poseidon2/Spec/Permutation.lean` | The permutation, written once over an `Ops` record (zero, add, add and multiply by a constant, S-box with a threaded state), its `ZMod P` instance, `permutationWords` (inputs read modulo `P`, outputs below `P`) |
| `Poseidon2/Spec/Sponge.lean` | `hashG` / `hash` / `hashWords` (the t = 4 `hash_1` / `hash_2` / `hash_3`: `[x.., 0.., n · 2^64]` permuted once, element 0), over any `Ops`; the Barretenberg / Noir sponge and proofs that the two agree for 1, 2 and 3 inputs |
| `Poseidon2/Spec/Interface.lean` | Calldata to returndata of every contract kind: `huffPerm`, `huffHash`, `yulHash`, `yulPerm`, `hashV2` (the deployed v2 Huff) |
| `Poseidon2/Spec/Constants/T<t>.lean` | Round numbers, round constants and internal diagonal per width, with their source in the file header |
| `Poseidon2/Spec/Vectors.lean` | 73 known-answer tests from other implementations and 3 agreement checks with this repository's reference (t = 20, 24, 28), all by `decide +kernel` |
| `Poseidon2/Spec/Grain.lean`, `GrainCheck.lean`, `DiagCheck.lean` | The HorizenLabs Grain LFSR in Lean, and proofs that every width's round constants and internal diagonal are its output |
| `Poseidon2/Evm/Eip8024.lean` | DUPN / SWAPN (EIP-8024) on top of EVMLean, with tests; `Sim.lean`: the first per-opcode simulation lemmas against EVMLean; `Smoke.lean` shows EVMLean is wired in |
| `Poseidon2/Bytecode/` | The runtime bytecode of 35 artifacts, written by `poseidon2-gen lean-export` (generator-rs), with byte count and keccak256 |
| `Poseidon2/Checker/` | The symbolic checker (`Forms`, `Bounds`, `SymExec`, `Check`), segmented checking (`Segments`), its soundness so far (`Bridge`: the spec run; `BoundsSound`: word terms; `FieldSound`: field values), mutation tests (`Mutations`) |
| `Poseidon2/Soundness.lean` | `CheckerSound`, the soundness proposition (not proven) |
| `Poseidon2/Theorems.lean` | For every contract kind: check accepted and `CheckerSound` imply the interface behaviour |
| `Poseidon2/Proofs/` | Library `Poseidon2Proofs`: one file per artifact, the kernel check and the contract theorem; written by `scripts/Emit.lean` |
| `Poseidon2/AxiomCheck.lean`, `Audit.lean`, `Proofs/Audit.lean` | The audits (below) |
| `scripts/` | Generators of the data files (node, Lean), `Dev.lean` (the checker by `#eval` on every artifact) and `Emit.lean` (writes `Proofs/`) |

## Building

```sh
cd formal-verification
lake exe cache get   # Mathlib oleans
lake build                                   # spec, checker, theorems, audit
LEAN_NUM_THREADS=2 lake build Poseidon2Proofs   # the per-artifact kernel checks
```

The toolchain is `leanprover/lean4:v4.29.0` (`lean-toolchain`), the one EVMLean pins. Dependencies (`lakefile.toml`, pinned in `lake-manifest.json`):

- Mathlib `v4.29.0` (`8a17838`), the revision EVMLean's manifest pins.
- EVMLean, https://github.com/lefterislazar/EVMLean at `fd4f5e6` (the commit EquiVM pins). Only its Lean modules are built. Its lakefile also declares an `extern_lib` (C code for sha256 / keccak cloned from GitHub and compiled with `cc`, plus `git submodule update` for the Ethereum tests), but Lake links extern libraries only into executables and precompiled modules, and this package builds neither, so a plain `lake build` runs no C compiler and clones nothing. Some precompiles (BN_ADD, SNARKV, ...) shell out to `python3` when executed; that is runtime only and never happens in a proof, and none of our `#eval`s reaches a precompile. Logically those precompiles return `default` (`totallySafePerformIO`); the Poseidon2 contracts call none.

`Poseidon2Proofs` is not a default target. Lake has no job limit and runs one Lean process per core; `LEAN_NUM_THREADS=2` keeps it to two (17 files: 169 to 189 s, at most 7.8 GB in total).

Measured on an Apple M2 Max with 96 GB, after the Mathlib cache and EVMLean are built: `GrainCheck.lean` 384 s at 11.2 GB and `DiagCheck.lean` 752 s at 6.3 GB, one after the other; `Vectors.lean` 10 s at 4.6 GB. A clean `lake build` takes about 20 minutes.

## How the bytecode is checked

1. `poseidon2-gen lean-export` writes each runtime bytecode as a Lean literal (`Bytecode/`).
2. The checker (`Checker/`) runs it symbolically once per calldata class of its interface (`Check.lean`: `huffPermCases`, `huffHashCases`, `yulHashCases`, `yulPermCases`, `hashV2Cases`). Values are exact word terms with intervals, linear forms over atoms in `F_p` with an upper bound on the raw word, or partial S-box powers. Atoms are input words read in the field and fifth powers of earlier forms, looked up by definition, not by creation order. Control flow, jump destinations (EVMLean's `D_J`) and memory addresses must be concrete; every raw `ADD` / `MUL` / `SHL` on field values is bounded below `2^256`; a branch must be decided by its interval. Anything else fails.
3. The returned forms are compared with `permG linOps` / `hashG linOps` run on the input atoms over the bytecode's own atom table: the same definition the spec uses, so the spec and the checker cannot drift.
4. In the kernel (`Proofs/`), long runs are checked in segments between literal checker states, so no declaration holds the whole run; `Segments.lean` proves that segments compose (`seg_run`).

Checker results (`scripts/Dev.lean`, `#eval`): every case of the 33 artifacts built from the current sources passes (148 cases), the deployed Yul v2 passes its 6, the deployed Huff v2 passes from 4 bytes of calldata on. Below 4 bytes the deployed Huff v2 adds its capacity word, which wrapped below zero, to another word unreduced; for empty calldata it returns `0x0fcc8f62…82d5` (anvil returns the same), where the deployed Yul v2 returns the permutation of its capacity word. `Mutations.lean` checks that one-byte mutations are rejected.

Kernel checks (`decide +kernel`): committed for 17 artifacts (Huff t = 2, 3, 4 on both forks; Yul t = 2, 3, 4 at all three optimizer settings; both deployed v2 contracts), 6 to 35 s and at most 4.8 GB each. The other 18 need checkpoint states that make their files 0.2 to 2.8 MB each (23 MB in all), so their files are not committed; `scripts/Emit.lean` writes them (`OUT=dir ART=<name> SEG=3000 lake env lean --tstack=1000000 scripts/Emit.lean`, then `lake env lean --tstack=4000000 <file>`). Each was checked that way, one at a time, without error:

| Artifact | Proof file | Wall | Peak RSS |
| -------- | ---------- | ---- | -------- |
| Huff t = 8, Amsterdam / Osaka | 2.2 / 2.1 MB | 68 / 69 s | 6.6 / 6.5 GB |
| Huff t = 12 | 1.9 / 0.7 MB | 84 / 81 s | 9.0 / 8.3 GB |
| Huff t = 16 | 0.5 / 0.9 MB | 86 / 118 s | 10.5 / 10.1 GB |
| Huff t = 20 | 1.0 / 1.4 MB | 125 / 150 s | 12.8 / 10.9 GB |
| Huff t = 24 | 1.5 / 1.6 MB | 230 / 183 s | 17.7 / 13.7 GB |
| Huff t = 28 | 2.0 / 2.8 MB | 316 / 256 s | 19.7 / 16.3 GB |
| Yul t = 8, optimizer 1,000,000 / 200 / off | 0.2 / 0.4 / 0.4 MB | 40 / 45 / 43 s | 6.5 / 5.5 / 5.5 GB |
| Yul t = 12 | 0.6 / 0.6 / 0.8 MB | 72 / 79 / 82 s | 7.9 / 8.4 / 7.8 GB |

A monolithic check of Huff t = 28 (no segments) overflows the kernel's stack at 38.8 GB.

## Trusted base

- The Lean 4 kernel and the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), enforced by the audits.
- The Mathlib and EVMLean `.olean` files. `lake exe cache get` downloads prebuilt Mathlib oleans, and the kernel does not re-check imported declarations. To discharge this, rebuild Mathlib from source instead of using the cache, or replay the whole import closure with the `leanchecker` that ships with the toolchain (`lake env leanchecker --fresh Poseidon2.Audit`; not run here, it re-checks all of Mathlib's imported part and takes hours).
- The specification in `Spec/` (`Permutation.lean`, `Sponge.lean`, `Interface.lean`, the constants): that it states the Poseidon2 of the paper (https://eprint.iacr.org/2023/323) and what the contracts are meant to compute. The known-answer tests are the evidence that it matches other implementations.
- For the contract theorems: EVMLean's semantics plus `Evm/Eip8024.lean`, and `CheckerSound` (see Status).
- The correspondence between the Lean literals in `Bytecode/` and deployed code: each file records the keccak256 of its code (the account's `codehash`); the kernel does not recompute it. The deployed v2 artifacts' initcode hashes equal the ones in `deployed-artifacts/*/v2/README.md`.

Not trusted: huff-neo, solc, the generators, the checker (once `CheckerSound` is proven), the checkpoint states (re-checked by the kernel), the Lean compiler (no `native_decide`).

## Sorry and axiom list

No `sorry`, no `axiom` declared here, no `native_decide`. `Audit.lean` checks every constant of every module under `Poseidon2/` (selected by defining module, so private and auxiliary declarations are included) and fails on any file under `Poseidon2/` it does not import; `Proofs/Audit.lean` does the same for `Poseidon2/Proofs/`. `CheckerSound` is a hypothesis, not an axiom.

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

`scripts/` holds what wrote the data files, so they can be regenerated and reviewed: `transcribe.mjs` (constants for t ≤ 16, from the fetched upstream files named in it), `vectors.mjs` and `genvectors.mjs` (`Vectors.lean`), `dump-params.rs` and `genwide.mjs` (t = 20, 24, 28), `rounds.mjs` (Rf / Rp), `GenDiag.lean` (the `DiagCheck.lean` certificates), `Dev.lean` (the checker in development mode) and `Emit.lean` (`Proofs/`). The node scripts read upstream files fetched by hand into the working directory; their URLs and commits are in the scripts.

## Conventions

- The state is a `List`; constants are natural numbers read in the field by `Nat.cast`.
- Contract inputs are raw 256-bit words. The spec reads each modulo `P` (`permutationWords`, `hashWords`) and returns canonical outputs (`ZMod.val`, below `P`).
- Kernel evaluation only: every computational check is `decide +kernel`. `#eval` appears only in `scripts/`, to compute certificates the kernel then checks, never as evidence.
