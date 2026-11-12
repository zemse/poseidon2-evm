# Tasks

Goal: fastest Poseidon2 EVM code theoretically possible, with a proof of optimality in a stated model. Lean reproving cost accepted for any saving, however small. EVMMAX out of scope.

## Huff, open directions

- [x] 4x4 block program search over alternative M4 DAGs (lane 5, LANE5-EXTERNAL.md): no 11-op M4 DAG over nonnegative forms (126.8M sets exhausted), 12 ops with 4 reductions is least; kept block none below 344 (TAKE=1 w8/w9, TAKE=2 w8), exit / exit0 none below 152 / 155. No gain.
- [ ] Two kept blocks interleaved: bound 341 at window 10, at most 3 gas a kept block (~147 at t28). Needs a two-block search.
- [ ] M4 DAGs with MULMOD by negative or fractional constants: an 11-op DAG would cost 98 against 104 a block. Not searched.
- [ ] t2/t3/t4 re-search with restrictions lifted (window, live-only DUP filter, fixed DAG, whitelist). Relaxation floor gaps t2 339, t3 504, t4 672: upper bound, real gain unknown.
- [x] t4 hash arity dispatch by computed jump (e9bc320): `calldatasize 0x9 shl jump`, a copy of the rounds per arity, 64,257 bytes. hash 11,880 / 11,887 / 11,960 to 11,841 / 11,882 / 11,922; other calldata sizes fail.
- [ ] t4 hash: fuse round-0 forms with ROUND4. hash_1 done (cc13782, -1); hash_2 (f 246 vs 252) and hash_3 (f 277 vs 292) searches stopped unfinished.
- [ ] First consuming round costs 8 more than steady (lazier exit-layer bounds force an extra ADDMOD). 8 gas per width t >= 8.
- [x] Deferred-sum internal state (421b4e2): t20 / t24 / t28 -67 / -56 / -522. Relaxed `defercycle` mean 28.5 against our 30 a round (STRICT 29.5): up to ~4.5 gas a round at t20-28 if the PRIME carrier moves are realizable.
- [x] t24/t28 diag constants on the stack on Amsterdam, no shared body (b9f1a4a): -300 / -376.
- [ ] Osaka t8: `primeEarly` impossible within DUP16 reach (24,217 stays).
- [x] Lane-copy steady internal rounds (c9b0314): -339 to -351 at t8 to t28.
- [x] Lazy t8 column sums, in-place takes, six-reduction final block (4ea72b3): -146 t8 to -148 t28.
- [x] t2/t3/t4 last rounds in place (572c52a) and chained external rounds (f5f2e63): t2 -18, t3 -18, t4 -3 per arity.
- [ ] t4 hash junctions of consecutive ROUND4s (rounds 1-3, 60-62): relaxed (PRIME copies free) 6 gas a junction; no exact search with PRIME placement finished (LANE6-SMALL.md).
- [x] t3 junction of rounds 2 and 3 at window 8: none below 186 (closed). t2 rounds 60-63 as one chain (fe9e427): -3.
- [x] t3 finite-horizon bound policy and guarded lazy seam: 7,626 to 7,586 on Amsterdam/Osaka, five runtime bytes less; exact-bound, split/fallback, public/private-entry and full-word compiled checks pass.
- [ ] Steady internal round t8 290 against floor B 266: at most one of the n + 1 moves shown not inherent beyond t = 4.
- [x] External blocks: `sblock` take searches finished with the 24-byte arena: none below 344 (kept), 152 / 155 (exit / exit0).
- [ ] Osaka t24/t28 shared body: with laneCopy the body period is free (any length, free mid entry); trade body length against call overhead.
- [x] t >= 8 entries store each final block's outputs as made (0aa5ea6): -14 / -21 / -28 / -35 / -42 / -49 at t8..t28.
- [x] firstSum, the first internal sum from the exit layer's column sums (733f7d4): -3 / -12 / -52 / -73 / -113 / -145 at t8..t28.
- [x] t4 hash row 0 in place (ad802b5): -3 per arity.
- [ ] t4 hash_1: a rounds macro per dead-slot count (Amsterdam, one copy per arity) drops its PUSH0: -2.
- [ ] firstSum: K - s0 takes two SWAPs (6 gas at t12..t28) and the seam carrier 3.
- [ ] Clippy `manual_is_multiple_of` at `generator-rs/src/huff/schedule.rs` `column_cap`.
- [x] `src/bn254/README.md` figures re-measured (2cd5769): Osaka t2 code size, streamed blocks 365 / 377 / 359; 231 to 867 and 24 to 51 kept as recorded when they landed. Tables hand-aligned; `prettier --check` not run (not installed).

## Yul, open directions

- [ ] t12 via-IR: one function and 8-round chunks exceed 40 GB; 2-round chunks too deep. Memory-held state est. a net loss.
- [x] t2/t3/t4/t8 tuned for via-IR 1M (999f493, d7fd8be): t2 7,560, t3 9,505, t4 13,904, t8 29,321.
- [x] t12 all diag constants as PUSH32 and tree sum (4ac47ed, 870682a, fcb1904): 46,272 to 43,682 at legacy 1M.
- [x] t8 via-IR compiles with a rounds function (aa12830).
- [x] Bound-planned Yul interval sums: 57 fewer reductions at t8/t12, -456 gas at all legacy settings; t8 via-IR 1M 29,321 to 28,391. Full-word compiled reference checks and consumer compiler controls pass.
- [ ] t2/t3 legacy: ~10-15 gas/round of stack moves left; needs a simulator of solc's CodeTransform + CSE to search shapes. Est. 300-600.
- [ ] `Poseidon2Yul_BN254` fallback dispatch to hash_1/2/3 by calldatasize: ~-60/-20/+15.

## Lean

- [x] Refresh proofs for every Huff/Yul bytecode changed since b4afc03 (5b2903a, aa1e499).
- [x] Prove the via-IR 1M builds of t2/t3/t4/t8 (04f2d61, 75518ae); 39 targets proven.
- [x] Refresh proofs for the bytecode of the four gas lanes (cfd38de, 6feaeaa), with the t4 Huff hash failing outside the 36 / 68 / 100 byte calldata sizes.
- [x] Refresh proofs for the bytecode of lanes 5 to 7 (23735b4, 6e05cd6): t2, the t4 hash, t8..t28 on Amsterdam (SUB in firstSum), t2 and t4 on Osaka.
- [x] Refresh all seven Yul ordered-sum bytecodes and their generated proofs: t8/t12 legacy 1M, 200 and off, t8 via-IR 1M; kernel builds and independent replay pass.
- [x] Refresh t3 bytecode and proofs on Amsterdam/Osaka for the finite-horizon policy: exact gas 7,586, fresh kernel builds and independent replay pass.

## Code quality review

Source review, 2026-10-31. Findings are not a completed security or soundness audit. High = artifact safety or misleading success/provenance; Medium = robustness, coverage or maintainability. First batch: structured JSON parsing, build/verify/publish separation, emitter exit status and strict corpus parsing. Preserve gas unless a runtime change is explicitly chosen; change generators rather than generated files.

### Rust generator

- [ ] High: structured JSON parsing in `generator-rs/src/lean_export.rs`, replacing substring searches. Fall back to initcode only when deployed bytecode is absent, not malformed. Test whitespace, reordered keys, missing fields and invalid hex.
- [ ] High: separate build, verify and publish in `main.rs`, `huff/mod.rs` and `yul/mod.rs`. Validate every width before writing; `huff --verify` must publish only verified output. Inject verification and later-width failures and assert existing files stay unchanged; define and test publication-failure handling.
- [ ] Medium: validate supported widths at the shared parameter boundary, not only the CLI. Grain encodes width in 12 bits. Reject unsupported widths, including 4096, before expensive derivation; test CLI and library calls.
- [ ] Medium: validate Lean export labels as module components and reject separators, invalid identifiers and duplicate final paths before writing. Test capitalization collisions (`foo` / `Foo`), repeated labels, forks and widths.
- [ ] Medium: manifest generator-owned Huff outputs and remove obsolete alternatives on split/unsplit transitions. Test both directions in temporary roots; preserve unrelated files.
- [ ] Low: preserve I/O error causes and attach operation/path context at filesystem boundaries (`error.rs`, Huff/Yul writers and export). Inject write/removal failures and check diagnostics; keep expected search rejection cheap.

### Lean and verification tooling

- [ ] High: preserve the Lean emitter exit status in `formal-verification/scripts/proof.sh`; the pipeline currently observes `sed`'s status. Require exactly one valid module name. Test an emitter that prints a module then fails, missing/duplicate module lines, and no build after failure.
- [ ] Medium: fail closed on malformed differential corpus records in `scripts/Eip8024Diff.lean`. Reject invalid/odd-length hex and malformed nonblank records with line numbers; check expected coverage. Corrupt one record among valid ones and require failure.
- [ ] Medium: add targeted CI model-conformance checks using `scripts/eip8024-diff.sh` and canonical fork-table regeneration from `scripts/forks.sh`. Test that wrong overlay behavior and changed gas tables fail independently of local proofs. Label these checks as conformance tests, not proofs.
- [ ] Medium: make every `scripts/export.sh` compiler configuration complete and independent of ambient `FOUNDRY_*` settings. Validate compiler, optimizer, runs, EVM target and via-IR against the export label; record via-IR in `lean_export.rs`. Test conflicting environment settings and mislabeled metadata.
- [ ] Medium: replace positional whitelist dispatch in `Poseidon2/Evm/Run.lean` with named opcode cases. Reordering `stepOps` should not require corresponding simulation-proof edits. Rebuild/replay affected modules and preserve artifact acceptance, gas and proof performance.
- [ ] Optional: expose successful call-frame account-map/substate preservation as a public corollary alongside output/gas correctness (`Soundness.lean`, `Evm/Sim.lean`). Prove downstream use without reopening opcode simulations; exclude transaction-level value transfer. Not evidence of a current state-changing bug.

Keep segmented reflection, kernel checks, axiom audits and replay coverage. Do not mechanically rewrite every `simp` or replace generated bytecode proofs with handwritten ones.

### Huff/Yul interfaces and tests

- [ ] Medium: define malformed-calldata behavior for the Yul fallback and Huff t4 entry. Their arity dispatch differs outside canonical ABI lengths (e.g. 69 bytes); the Amsterdam Huff entry now fails on any size but 36 / 68 / 100. Test short payloads, partial/trailing words and wrong selectors. Document supported calls before choosing gas-costly rejection checks; update `Poseidon2Yul.sol` and the Huff entry renderer.
- [ ] Medium: extend existing hash fuzzing beyond inputs bounded below PRIME. Test unchecked modulo equivalence and checked helper rejection at PRIME - 1, PRIME, PRIME + 1 and maximum uint256; assert the expected custom error. Preserve the deployed contracts' modulo semantics.
- [ ] Medium: supplement generated Yul-versus-Huff permutation fuzzing with bounded randomized reference comparisons across supported widths and arbitrary uint256 inputs. Retain independently sourced fixed vectors; document shared constants/assumptions rather than treating agreement as full independence.

### CI and tooling

- [ ] Medium: detect untracked generator-owned outputs in freshness checks (`.github/workflows/test.yml`); `git diff --exit-code` alone misses them. Use a scoped manifest or status check. Test a newly generated untracked file and a synchronized checkout.
- [ ] Medium: add bounded `generator-rs/stacksearch` Rust and Node accounting tests to CI, plus formatting and Clippy checks for both crates. Baseline: both format checks and main-generator strict Clippy pass; stacksearch strict Clippy has style findings; gas-floor Node tests pass.
- [ ] Low: add `--locked` to generator Cargo invocations in `package.json` and `formal-verification/scripts/export.sh`. Verify generation/export commands do not change Cargo.lock and fail when resolution would require an update.

Guidance: [Rust API/error handling](https://rust-lang.github.io/api-guidelines/interoperability.html), [Serde JSON](https://serde.rs/json.html), [mathlib style](https://leanprover-community.github.io/contribute/style.html), [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), [Yul semantics](https://docs.soliditylang.org/en/latest/yul.html), [Solidity ABI](https://docs.soliditylang.org/en/latest/abi-spec.html), [Huff docs](https://github.com/huff-language/huff-docs), [Foundry testing](https://www.getfoundry.sh/forge/testing).

## Optimality proof roadmap

Unrestricted "no faster EVM program exists" is out of reach: it is a circuit lower bound for an explicit function, beyond known techniques. Provable: optimality inside a stated model, layered.

- [ ] Model statement: straight-line EVM programs computing the Poseidon2 round DAG over GF(p), with allowed rewrites (reassociation, lazy reduction under 2^256 bounds, constant folding, seam fusion) and opcode set (ADD, MUL, ADDMOD, MULMOD, MOD, PUSH, DUP/DUPN, SWAP/SWAPN, EXCHANGE, MLOAD/MSTORE).
- [ ] L1 arithmetic floor: S-box x^5 needs 3 multiplications (addition chain); each diag product needs one MULMOD with a generic constant; count of irreducible ops per round. Lean.
- [ ] L2 reduction floor: minimal ADDMOD/MOD count given 256-bit bounds, as ILP/DP; Lean-checked dual certificate.
- [ ] L3 stack floor: minimal DUP/SWAP/PUSH gas per segment for fixed boundary layouts; exact search with checkable certificate.
- [ ] Composition: min-plus DP over boundary layouts across rounds, so per-round bounds sum to a whole-permutation bound.
- [ ] Gap report: proven floor vs shipped gas per width; zero gap = optimal in the model.
- [ ] First: prove floor B (arith gas + 3 per net consumed slot, `gas-floor.mjs`) in Lean for every width. Current gaps 7-10%, ~9.5% at t8-t20, mostly SWAP gas in internal consuming rounds.
- [ ] Certificate pipeline: SAT/PB encoding of "segment gas <= C-1", LRAT (Lean core checker) or VeriPB (pb-catcher) refutation; verified encoder is ours to write.
- [ ] Normal-form lemma for cutting at round boundaries; recent cross-seam savings may falsify a strict one.
- [ ] Research: `evm-gas-optimality-proofs/evm-gas-optimality-proofs.md`.

Prior art: ebso (Nagele, Schett, LOPSTR 2019, SMT superoptimizer for loop-free EVM code), SYRUP (Albert, Gordillo, Rubio, Schett, CAV 2020 Max-SMT; TOSEM 2022 "Super-optimization of Smart Contracts").
