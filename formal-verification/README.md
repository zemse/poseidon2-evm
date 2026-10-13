# Formal verification (Lean 4)

The goal of this directory is a kernel-checked proof that the generated runtime bytecode of the contracts (Huff t = 2, 3, 4, 8, 12, 16, 20, 24, 28; Yul t = 2, 3, 4, 8, 12 under legacy solc) returns the Poseidon2 output over BN254 for every input. The proofs are about the raw runtime bytes, so huff-neo, solc and the generators stay outside the trusted base.

**Status: not formally verified.** What is proven, kernel-checked and free of `sorry`, axioms of ours and `native_decide`:

- the Poseidon2 specification, its constants (round constants and internal diagonals derived from the Grain LFSR of the HorizenLabs script), 73 known-answer tests against other implementations, and the calldata interface of every contract;
- that a symbolic checker accepts every exported bytecode on every calldata class of its interface (all 35: the 17 small ones committed in `Poseidon2/Proofs/`, the 18 large ones written by `scripts/proof.sh` and checked in CI, see below);
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
| `Poseidon2/Checker/` | The symbolic checker (`Forms`, `Bounds`, `SymExec`, `Check`), segmented checking (`Segments` for the bytecode run, `SpecSegments` for the spec side), its soundness so far (`Bridge`: the spec run; `BoundsSound`: word terms; `FieldSound`: field values), mutation tests (`Mutations`) |
| `Poseidon2/Soundness.lean` | `CheckerSound`, the soundness proposition (not proven) |
| `Poseidon2/Theorems.lean` | For every contract kind: check accepted and `CheckerSound` imply the interface behaviour |
| `Poseidon2/Proofs/` | Library `Poseidon2Proofs`: per artifact, the kernel check and the contract theorem, written by `scripts/Emit.lean`; the 17 small artifacts are committed, the 18 large ones go to `Proofs/Generated/` (not committed) as a chain of parts |
| `Poseidon2/AxiomCheck.lean`, `Audit.lean`, `Proofs/Audit.lean` | The audits (below) |
| `scripts/` | Generators of the data files (node, Lean), `Dev.lean` (the checker by `#eval` on every artifact), `Emit.lean` (writes `Proofs/`), `proof.sh` (writes and builds the proof of an artifact), `export.sh` (rewrites `Bytecode/`) |

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
- `lake build Poseidon2 Poseidon2.Proofs.Audit` on that clone (EVMLean, then everything of ours): 1,600 s at 11.1 GB with `LEAN_NUM_THREADS=1`, `.lake` 7.6 GB afterwards. The peak is `GrainCheck.lean` (383 s, 11.1 GB); then `DiagCheck.lean` (743 s, 6.4 GB), which imports it. With `LEAN_NUM_THREADS=2` the same build takes 1,170 s but two processes reach 14.5 GB together.
- The 17 committed artifacts (`scripts/proof.sh`, writing included): 10 to 44 s and 3.0 to 5.1 GB each.
- The 18 large ones (`scripts/proof.sh`, writing included): 81 to 436 s and 3.8 to 8.0 GB each, in the table below.

## How the bytecode is checked

1. `poseidon2-gen lean-export` writes each runtime bytecode as a Lean literal (`Bytecode/`).
2. The checker (`Checker/`) runs it symbolically once per calldata class of its interface (`Check.lean`: `huffPermCases`, `huffHashCases`, `yulHashCases`, `yulPermCases`, `hashV2Cases`). Values are exact word terms with intervals, linear forms over atoms in `F_p` with an upper bound on the raw word, or partial S-box powers. Atoms are input words read in the field and fifth powers of earlier forms, looked up by definition, not by creation order. Control flow, jump destinations (EVMLean's `D_J`) and memory addresses must be concrete; every raw `ADD` / `MUL` / `SHL` on field values is bounded below `2^256`; a branch must be decided by its interval. Anything else fails.
3. The returned forms are compared with `permG linOps` / `hashG linOps` run on the input atoms over the bytecode's own atom table: the same definition the spec uses, so the spec and the checker cannot drift.
4. In the kernel (`Proofs/`), long runs are checked in segments between literal checker states, so no declaration holds the whole run; `Segments.lean` proves that segments compose (`seg_run`). The spec side of a permutation case is checked the same way, in segments of rounds (`SpecSegments.lean`: `permG_eq_roundsRun`, `rounds_seg`, `resultOk_perm`).

Checker results (`scripts/Dev.lean`, `#eval`): every case of the 33 artifacts built from the current sources passes (148 cases), the deployed Yul v2 passes its 6, the deployed Huff v2 passes from 4 bytes of calldata on. Below 4 bytes the deployed Huff v2 adds its capacity word, which wrapped below zero, to another word unreduced; for empty calldata it returns `0x0fcc8f62…82d5` (anvil returns the same), where the deployed Yul v2 returns the permutation of its capacity word. `Mutations.lean` checks that one-byte mutations are rejected.

Kernel checks (`decide +kernel`), all 35 artifacts, one at a time, without error. The 17 small ones (Huff t = 2, 3, 4 on both forks; Yul t = 2, 3, 4 at all three optimizer settings; both deployed v2 contracts) need no checkpoint (segments of 8,000 instructions, the spec side in one declaration); their files are a few KB, committed, and audited together by `Proofs/Audit.lean`. The 18 large ones are written by `scripts/proof.sh` with segments of 1,000 instructions and 10 rounds and three kernel checks per part file; their files are 1.3 to 9.9 MB each (80 MB in all), so they are not committed. `Emit.lean` is deterministic (two runs give the same bytes), so the committed tree and the scripts regenerate them, and CI checks every one (below). Each generated file ends with `#assert_standard_axioms_here`, and the last file of an artifact also audits its parts.

| Artifact | Parts | Bytecode segments | Files | Wall | Peak RSS |
| -------- | ----- | ----------------- | ----- | ---- | -------- |
| Huff t = 8, Amsterdam / Osaka | 6 / 6 | 6 / 6 | 4.9 / 4.9 MB | 165 / 169 s | 6.0 / 5.9 GB |
| Huff t = 12 | 7 / 7 | 8 / 9 | 9.2 / 2.2 MB | 349 / 109 s | 8.0 / 4.6 GB |
| Huff t = 16 | 8 / 8 | 11 / 12 | 2.8 / 3.0 MB | 159 / 148 s | 5.6 / 4.8 GB |
| Huff t = 20 | 9 / 9 | 14 / 16 | 4.4 / 4.7 MB | 237 / 222 s | 6.3 / 5.1 GB |
| Huff t = 24 | 10 / 11 | 17 / 20 | 5.8 / 6.7 MB | 334 / 293 s | 7.7 / 5.6 GB |
| Huff t = 28 | 11 / 12 | 20 / 25 | 8.5 / 9.9 MB | 436 / 427 s | 7.8 / 5.8 GB |
| Yul t = 8, optimizer 1,000,000 / 200 / off | 9 / 10 / 10 | 8 / 9 / 10 | 1.3 / 1.4 / 1.4 MB | 81 / 91 / 89 s | 3.8 / 4.1 / 4.0 GB |
| Yul t = 12 | 11 / 11 / 12 | 14 / 14 / 15 | 2.3 / 2.5 / 2.4 MB | 148 / 164 / 161 s | 4.5 / 4.8 / 4.6 GB |

Every permutation case has 7 spec segments. Wall and peak are of `scripts/proof.sh <artifact>` with `LEAN_NUM_THREADS=1` (writing the files, about 10 to 15 s, included; peak is the largest Lean process). Before this layout, with segments of 3,000 instructions, the spec side in one declaration and one file per artifact, Huff t = 28 took 19.7 GB, for two reasons found by checking single declarations: the spec run of t = 28 alone took 12.7 GB, and a `CODECOPY` of 27 words near the end of the 64 KB code took 13 GB because each word walked the code list from its start (now it is walked once). A monolithic check (no segments) overflows the kernel's stack at 38.8 GB. Memory also grows with the number of kernel checks one Lean process holds, hence the parts.

## Continuous integration

`.github/workflows/formal-verification.yml` runs on pushes to `main` and on pull requests that touch `formal-verification/`, `src/`, `test/`, `generator-rs/`, `deployed-artifacts/` or `foundry.toml`, on GitHub-hosted runners (4 vCPU, 16 GB, 14 GB of disk guaranteed), all with `LEAN_NUM_THREADS=1`:

| Job | What it runs | Measured here (M2 Max) |
| --- | ------------ | ---------------------- |
| Lean build | `leanprover/lean-action@v1`: elan, `lake exe cache get`, `lake build Poseidon2 Poseidon2.Proofs.Audit`, `.lake` cached for the jobs below; then `scripts/proof.sh` on the 17 small artifacts and `git diff --exit-code Poseidon2/Proofs` | 1,600 s at 11.1 GB on a clean clone; the proof check 87 s at 1.9 GB (it only rewrites the files, the build is cached) |
| Exported bytecode is current | `scripts/export.sh` (forge `v1.8.5` with the submodules, the Rust exporter with huff-neo), then `git diff --exit-code Poseidon2/Bytecode`, so the proofs cover the bytecode the sources compile to | 181 s on a clean clone (the exporter's release build and the Osaka regeneration included), 0.3 GB; the files it writes are identical on two checkouts at different paths |
| Kernel check, one per large artifact (18) | restores the build, `scripts/proof.sh <artifact>` | 81 to 436 s at 3.8 to 8.0 GB (table above) |

The Yul builds of `export.sh` name their remappings: forge's detected ones carry the absolute path of the checkout into the solc metadata, whose hash ends the code, so the bytes depended on where the repository was checked out. The committed Yul bytecode was exported again that way; only the 53 metadata bytes at the end of each changed (checked by comparing the code before them), and the 15 Yul artifacts were kernel-checked again.

Disk: `.lake` is 7.6 GB after the build and the toolchain 2.5 GB, so with the cache archive the jobs come close to the 14 GB; the Lean jobs first delete the runner's Android SDK, .NET and GHC (the `df` before and after is in the log). The cache is keyed on the toolchain, the manifest and the commit, like `lean-action`'s own, and holds all of `.lake`.

Not yet run on GitHub (nothing here was pushed): the workflow file was checked by parsing it and by running each job's commands locally on a clean clone (`git clone`, `lake exe cache get`, the build, the 17-artifact check, `scripts/proof.sh huff/osaka/t28` in 425 s at 5.9 GB, `scripts/export.sh` and its diff). Untested until the first push: the actions themselves (`lean-action` restoring the cache in the matrix jobs without a rebuild, the matrix from the `artifacts` job), the runner's speed (expect a few times slower than here; every job is far below the 6 h limit) and its free disk.

## Trusted base

- The Lean 4 kernel and the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), enforced by the audits.
- The Mathlib and EVMLean `.olean` files. `lake exe cache get` downloads prebuilt Mathlib oleans, and the kernel does not re-check imported declarations. To discharge this, rebuild Mathlib from source instead of using the cache, or replay the whole import closure with the `leanchecker` that ships with the toolchain (`lake env leanchecker --fresh Poseidon2.Audit`; not run here, it re-checks all of Mathlib's imported part and takes hours).
- The specification in `Spec/` (`Permutation.lean`, `Sponge.lean`, `Interface.lean`, the constants): that it states the Poseidon2 of the paper (https://eprint.iacr.org/2023/323) and what the contracts are meant to compute. The known-answer tests are the evidence that it matches other implementations.
- For the contract theorems: EVMLean's semantics plus `Evm/Eip8024.lean`, and `CheckerSound` (see Status).
- The correspondence between the Lean literals in `Bytecode/` and deployed code: each file records the keccak256 of its code (the account's `codehash`); the kernel does not recompute it. The deployed v2 artifacts' initcode hashes equal the ones in `deployed-artifacts/*/v2/README.md`.

Not trusted: huff-neo, solc, the generators, the checker (once `CheckerSound` is proven), the checkpoint states (re-checked by the kernel), the Lean compiler (no `native_decide`).

## Sorry and axiom list

No `sorry`, no `axiom` declared here, no `native_decide`. `Audit.lean` checks every constant of every module under `Poseidon2/` (selected by defining module, so private and auxiliary declarations are included) and fails on any file under `Poseidon2/` it does not import; `Proofs/Audit.lean` does the same for the committed files of `Poseidon2/Proofs/`, and every generated file under `Proofs/Generated/` audits its own constants (`#assert_standard_axioms_here`, checked to reject `sorry`, `native_decide` and an `axiom`) and, in an artifact's last file, those of its parts. `CheckerSound` is a hypothesis, not an axiom.

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

`scripts/` holds what wrote the data files, so they can be regenerated and reviewed: `transcribe.mjs` (constants for t ≤ 16, from the fetched upstream files named in it), `vectors.mjs` and `genvectors.mjs` (`Vectors.lean`), `dump-params.rs` and `genwide.mjs` (t = 20, 24, 28), `rounds.mjs` (Rf / Rp), `GenDiag.lean` (the `DiagCheck.lean` certificates), `Dev.lean` (the checker in development mode), `Emit.lean` (`Proofs/`), `proof.sh` (runs `Emit.lean` with each artifact's settings and builds the result) and `export.sh` (runs the exporter on fresh forge builds). The node scripts read upstream files fetched by hand into the working directory; their URLs and commits are in the scripts.

## Conventions

- The state is a `List`; constants are natural numbers read in the field by `Nat.cast`.
- Contract inputs are raw 256-bit words. The spec reads each modulo `P` (`permutationWords`, `hashWords`) and returns canonical outputs (`ZMod.val`, below `P`).
- Kernel evaluation only: every computational check is `decide +kernel`. `#eval` appears only in `scripts/`, to compute certificates the kernel then checks, never as evidence.
