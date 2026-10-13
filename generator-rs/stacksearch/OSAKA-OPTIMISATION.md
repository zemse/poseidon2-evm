# Osaka optimisation lanes

The Python probes and replays this record names (`*.py`) were removed after the lanes; their outputs stay in `results/` and the measurements below.

## Lane 1: t = 4 internal boundaries

Baseline b7d7125, 2026-10-10. Serial work in branch `bhai/8cf2de96-fdd6bb`. No production generator changes, no speedup. Both historical searches stopped at their RSS guard before the heuristic correction below. Neither exhausted, and their heuristic was not admissible. The finite incumbent-renaming family has no win once both boundaries are charged; that result is independent of the search heuristic.

### Baseline and final execution

Compiled huff-neo/revm verification was run in this worktree before the experiments, for Osaka and Amsterdam. Osaka was repeated before the heuristic correction; production source remains unchanged. All model differences were zero; initial and final Osaka gas are identical.

| Fork      | t=2 raw | t=3 raw | t=4 raw | t=4 hash_1 | hash_2 | hash_3 |
| --------- | ------: | ------: | ------: | ---------: | -----: | -----: |
| Osaka     |   6,066 |   7,768 |  12,087 |     11,910 | 11,932 | 12,005 |
| Amsterdam |   6,027 |   7,768 |  12,087 |     11,910 | 11,932 | 12,005 |

Each fork verified 24 calls at t=2, 24 at t=3 and 96 at t=4. These are call-frame execution gas, not transaction/deployment gas or host CPU timing. The generator checks pinned external answers and shared vectors, and the verifier checks deterministic full-word random inputs against the reference.

The t=4 internal segment remains 9,296 = 56 \* 166 gas. The [baseline accounting](OSAKA-BASELINE.md) gives a fixed-arithmetic, free-placement relaxation of 154 per round, not an attainable schedule or unrestricted minimum. The old search's root heuristic 157 is a historical value, not a certified floor. The corrected root value is 154.

### Search and replay changes

- `internal` accepts distinct-output `O` goal slots and `UNORDERED=1`, which permits any permutation of the required outputs and PRIME copies. Every lane must occur once in the live prefix and meet its own output bound. The garbage limit still applies below that prefix.
- `UB=<gas>` drops successors with f >= gas before storing them. `MAXF` is also checked before insertion. The queue revisits lower f buckets because the conservative heuristic need not be consistent.
- Initial layouts require every lane once, and input/output bounds must have the configured lane count and lie in 1..5. Lane 0 is at most 4P, so adding a round constant below P cannot overflow its initial ADD.
- `REPLAY` emits portable cost/layout/DSL records and rejects a non-goal endpoint. `bench.py` dispatches the `internal` binary to its own checker, records the search environment and accepts progress without a queue count.
- `internal_check.py` independently replays numeric operands on 64 deterministic trials, including bound endpoints and maximal round constants, with arbitrary deterministic diagonal constants. It checks complete/distinct goals, lane names, bounds lengths, reach, depth, modulus operands, ADD overflow, output bounds and gas. This is numeric evidence, not a symbolic proof over all inputs.

The arithmetic class whitelist, strict DUP generation rule, S-box macro and one-round starting layout were not widened. These generation restrictions are not proved complete. The three-lane mode of `internal` remains the general-diagonal analogue of t=4, not Poseidon2's actual t=3 diagonal.

### Heuristic correction

Two coordinator-supplied allowed-state/completion counterexamples are retained unchanged as Rust regressions, with strict DUP enabled:

1. Fixed goal `[out0,P,out1,out2,out3]`, bounds 2, garbage 2. From top-first `[part(1,1),P,out(1,2),out(2,2),out(3,2),part(2,2),out(0,2)]`, SWAP6 reaches the exact goal for 3 gas. The old heuristic charged 4 because it required a dead entry above an output to be POPped. The corrected value is 0.
2. Fixed goal `[out1,out0,P,out2,out3]`, bounds 3, garbage 0. From `[part(3,1),part(12,1),PROD,PROD+1,part(15,1),P,out(2,2),out(3,2)]`, ADD ADD SWAP2 ADD reaches the exact clean goal for 12 gas. The old heuristic charged 16. Partial sums classified dead can be recombined and consumed by pending outputs, so merely removing the above-output POP charge is insufficient. The corrected value is 6.

All completion moves are accepted by `apply`. Tests also check the bound at each suffix, goal value zero, small product/output completions and every suffix of the 166-gas incumbent. No reachability certificate from a normal initial layout was run for the two witnesses. They disprove the old bound over permitted states/completions, not prove that a particular historical search discarded its optimum.

The corrected general bound charges only operations that create a missing required class: one final ADD per missing output and one MULMOD per missing product. It charges the greater of net stack supply and mandatory diagonal-plus-PRIME supply, not their sum. Distinct missing diagonal constants and consumed/retained PRIME copies must be supplied by PUSH/DUP; other arithmetic and POPs only consume more slots. Output reductions, sum formation, S-box work, per-class copies, feasibility rejection, garbage and placement are omitted at arbitrary states.

At the raw five-slot t=4 boundary with one PRIME and all input/output bounds 2, the fixed class graph requires seven ADDs and eight mod operations (85 gas, 23 net consumed slots). The full sum's bound 7 requires at least one ADDMOD. Equal initial/required-final heights then require at least 23 supplied slots, giving 85 + 3 \* 23 = 154. This special root relaxation is not applied to partial/computed states. `NO_SUM_WASTE` is now a compatibility toggle with no effect.

This is a conservative lower bound for the permitted class operations and configured goals, not an unrestricted EVM minimum or a certificate that the generation filters cover all useful programs. No post-correction expensive search or optimality claim is made.

### Historical experiments

| Hypothesis                                                                | Result                              | Scope                                                                                           |
| ------------------------------------------------------------------------- | ----------------------------------- | ----------------------------------------------------------------------------------------------- |
| Sub-166 round with output order relaxed, PRIME fixed below outputs        | No candidate before RSS stop        | Old heuristic, `UB=166`, goal `O,O,O,O,P`, garbage 1, depth 16, bounds 2                        |
| Sub-166 round with the entire live endpoint unordered                     | No candidate before RSS stop        | Old heuristic, `UB=166 UNORDERED=1`, four outputs plus one PRIME, same start and limits         |
| Permute inactive lanes of the incumbent, compose cycles and all 56 rounds | No saving within this finite family | Six renamed bodies, shortest SWAP-only adapters on five live prefix slots, canonical boundaries |

First search: 282.1091195 seconds, sampled peak RSS 8,811,577,344 bytes, stopped by the 8 GiB guard. Last progress was 14,000,000 expansions / 112,516,342 states at f=157.

Unordered search: 105.53246691700001 seconds, sampled peak RSS 8,844,787,712 bytes, stopped by the 8 GiB guard. Last progress was 6,000,000 expansions / 51,035,987 states at f=157. These are last reported counters, not final totals. Both process groups received SIGTERM (return code -15). The 0.25-second RSS sampler is not a hard allocation cap; sampled peaks can exceed the threshold.

These cutoffs describe pre-correction code. Running the same arguments with corrected code does not reproduce that heuristic or frontier. No fixed-endpoint sub-166 search or previously rejected generic/GC/memory-diagonal option was repeated in this lane.

### Charged finite composition

`internal_layouts.py` reads `INTERNAL4` relative to its own repository root, not the original checkout. It renames s1/s2/s3 and their matching diagonal constants in all six ways. Each body is independently replayed at 166 gas and preserves its renamed layout, with one dead value below it.

Adapter BFS exhausts the 120 permutations of the five live prefix slots using SWAP1..4, without touching garbage. A dynamic program composes two or 56 bodies with entry, inter-round and final adapters charged. The probe numerically replays every ordered pair of body layouts and each selected minimum path, retaining accumulated garbage between rounds. Each replay uses 64 trials.

| Modelled internal gas                          | Result | Against incumbent |
| ---------------------------------------------- | -----: | ----------------: |
| Best two rounds, canonical boundaries          |    332 |                 0 |
| Best two rounds visiting a noncanonical layout |    350 |               +18 |
| Cheapest distinct two-layout closed cycle      |    350 |               +18 |
| Best 56 rounds, canonical boundaries           |  9,296 |                 0 |
| Best 56 rounds visiting a noncanonical layout  |  9,314 |               +18 |

A transposition of inactive lanes needs three top-based SWAPs (9 gas); a three-cycle needs four (12). Keeping the canonical layout costs no adapter. The finite-family minimum is still 166 per round. This is opcode-model gas with numeric replay, not a newly compiled production candidate.

The result does not cover fused adapters, naturally changing endpoints, different PRIME positions, extra retained live values, changed bounds/arithmetic, transformed representations, or jointly synthesised rounds. It does not exhaust cross-round EVM schedules.

### Commands and verification

```sh
ROOT=/Users/sohamzemse/workspace/opensource/personal/poseidon2-evm/.bhai/worktrees/8cf2de96-fdd6bb
SEARCH="$ROOT/generator-rs/stacksearch"

cargo fmt --manifest-path "$SEARCH/Cargo.toml" -- --check
cargo test --release --locked --offline --manifest-path "$SEARCH/Cargo.toml" --bin internal
cargo build --release --locked --offline --manifest-path "$SEARCH/Cargo.toml" --bin internal

# Historical invocations, not reproduction of the old frontier on corrected code.

# Compiled baseline checks already run; not repeated after the heuristic correction.
cargo run --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- verify --hardfork osaka 2 3 4
cargo run --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- verify --hardfork amsterdam 2 3 4
```

The corrected harness has eleven Rust tests and fourteen Python tests. Tests cover both heuristic witnesses and valid suffixes, malformed/truncated/duplicate goals, invalid names/bounds, wrong cost/output/modulus, overflow/reach failures, unordered PRIME position, shortest adapters, whole composition, and runner dispatch without queue telemetry. The 166-gas program is replayed through the rebuilt Rust binary's `REPLAY` mode and the independent Python checker.

Rust uses `cargo fmt`; Markdown and JSON use the existing installed Prettier. No dependencies or lockfiles changed. Production TS/Rust, generated src and tests are unchanged. Coordinator both-fork verification and serial generation parity remain independent integration gates.

Portable artifacts: [incumbent](results/t4-internal-incumbent.txt), [historical cutoffs and finite-family summary](results/lane1-internal.json). Transient artifacts:

- `/tmp/poseidon2-lane1-baseline-osaka.log`, `/tmp/poseidon2-lane1-baseline-amsterdam.log`, `/tmp/poseidon2-lane1-final-osaka.log`.
- `/tmp/poseidon2-lane1-any-end/{result.json,stdout.txt,stderr.txt}` and `/tmp/poseidon2-lane1-unordered/{result.json,stdout.txt,stderr.txt}`.
- `/tmp/poseidon2-lane1-incumbent-final.txt` and `/tmp/poseidon2-lane1-layouts.json` (before the heuristic correction).
- `/tmp/poseidon2-lane1-incumbent-corrected.txt` and `/tmp/poseidon2-lane1-layouts-corrected.json`.

### Handoff to lane 2

Keep 166 as the verified incumbent, not a proved minimum. Do not use historical f=157 cutoffs as exhaustion or a certified floor. The corrected conservative bound is weaker away from the root; a compact macro/preplacement graph or productive restriction is preferable to an uncontrolled larger-memory search.

A naturally layout-changing body, changed retained values or joint-round synthesis is still untested. Charge the external exit, every internal transition and external re-entry before accepting it. The finite renaming probe supplies adapters and whole-chain replay, not new bodies. Any production candidate still needs symbolic overflow/shared-vector checks, compiled full-word Osaka verification, both-fork TS/Rust parity and the independent coordinator gate.

## Lane 2: t = 2 reduction placement

Baseline ab0df8a, 2026-10-10, measured again in branch `bhai/8cf2de96-85c43b`. The first generic internal bridge is unchanged. The other 55 rounds replace `(3b+x) mod P` with `(3b mod P)+x`, moving x's DUP after MULMOD without adding a SWAP. TS and Rust use the same policy, with the existing PRIME refresh and output construction.

| Fork      | t=2 before | t=2 after | Saving | t=3 raw | t=4 raw |
| --------- | ---------: | --------: | -----: | ------: | ------: |
| Osaka     |      6,066 |     5,956 |    110 |   7,768 |  12,087 |
| Amsterdam |      6,027 |     5,917 |    110 |   7,768 |  12,087 |

These are compiled huff-neo/revm call-frame gas, not host timing. Both baseline and candidate verified 24 calls at t=2, 24 at t=3 and 96 at t=4 per fork, including shared vectors and deterministic full-word inputs. Every model difference is zero. The t=4 hash entrypoints remain 11,910 / 11,932 / 12,005. Runtime size is unchanged: t=2 is 3,918 bytes on Osaka, 4,007 on Amsterdam.

For reduced x, the new inactive output is below 2P. The bridge gives active/inactive bounds (2,1); subsequent rounds have active output `2x+b < 4P` and inactive output below 2P. The active output plus its next constant is below 5P < 2^256. The inclusive guard `3*(P-1)+bound(b) <= UINT256_MAX` admits b below 2P but not the initial b below 3P. Final bounds (4,2) permit external re-entry. MULMOD itself cannot overflow.

### Recalibrated accounting

The internal segment changes 4,987 -> 4,877 gas. The first round remains 105; steady rounds change 88 -> 86, with the same fourteen three-gas PRIME refreshes on Osaka. The 110-gas saving is arithmetic, not recovered placement overhead. Initial/external/wrapper costs remain 27 / 1,000 / 52.

The new fixed-mix core relaxation is `2,997 + 3*815 = 5,442`, and the same-wrapper relaxation is 5,494. The measured 5,956 still has a 462-gas gap: 57 in SWAPs and 405 in surplus supply. The internal relaxation is 4,496, gap 381. These floors hold the new arithmetic and live-slot model fixed; neither the old nor new floor is an unrestricted optimum.

### Verification and artifacts

- `cargo test --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml"`: eight library, four generator and four compiled verifier tests. The strict Amsterdam t=2 snapshot is updated to the independently measured 5,917; large-width snapshots are unchanged.
- `node --test "$ROOT/generator-rs/stacksearch/gas-floor.test.mjs" "$ROOT/generator-rs/stacksearch/reduction-policy.test.mjs"`: seven tests. Focused TS/Rust regressions cover inactive bounds P/2P/3P, maximal constants, the first bridge, all 56 rounds and external re-entry. Rust also checks exact inclusive bounds and the last round with or without a retained PRIME.
- Both-fork serial parity compares generated Huff, tests and stdout for t=2/3/4 byte-for-byte. The checked-in t=2 permutation is regenerated using the existing Amsterdam convention; generated wrapper and vectors are unchanged.
- Rust uses cargo fmt; TS/tests/Markdown use the installed Prettier. Scoped generated diff and whitespace checks are run before committing. No dependencies or lockfiles changed.

Transient evidence: `/tmp/poseidon2-lane2-{baseline,t2}-{osaka,amsterdam}.log`, `/tmp/poseidon2-lane2-{baseline,t2}-floor.json`, and `/tmp/poseidon2-serial-parity.HgfZUw`. The commands use this lane's absolute worktree root and its freshly built `generator-rs/target/release/poseidon2-gen`, not an installed binary. No broad search, transformed representation or improved first bridge was attempted. t=3 is a separate follow-up.

## Lane 2: t = 3 periodic reduction

The coordinator supplied four concrete templates, independently numerically replayed before this implementation. TS and Rust now dispatch them by inclusive tracked bounds rather than a round-number cycle. The two previous templates remain fallbacks for unexpected bounds or layouts. All four use the same live boundary `[s0,P,s2,s1]`, preserve it as `[s0',P,s2',s1']` and add one dead old s1 per round. No adapter or expensive synthesis is needed.

| Fork      | t=3 before | t=3 after | Saving | Runtime bytes before | After |
| --------- | ---------: | --------: | -----: | -------------------: | ----: |
| Osaka     |      7,768 |     7,656 |    112 |                6,733 | 6,719 |
| Amsterdam |      7,768 |     7,656 |    112 |                6,733 | 6,719 |

Both forks compile and execute t=2/3/4 against the reference again, with 24 / 24 / 96 verified calls and zero model differences. The committed t=2 costs remain 5,956 / 5,917; t=4 raw and all hash costs remain unchanged. Parameters, pinned external known answers and shared vectors are unchanged. The tracked t=3 permutation is regenerated using Amsterdam; its wrapper and vectors do not change.

### Policy and bounds

Let x be the normalized S-box result, b=s1, c=s2 and L=P-1. Form `q=x+b` with ADD, then `s=(q+c) mod P` and `a'=s+x`. Dispatch only when b's bound is at most 4L and c's at most 5L:

- Reset when b's bound exceeds 3L: reduce b'=s+b and d=2c, then c'=s+d. This also handles the initial (4,4) bridge.
- Otherwise high when c's bound exceeds 2L: leave b'=s+b lazy, reduce d=2c and leave c'=s+d lazy.
- Otherwise low: leave b'=s+b, d=2c and c'=s+d lazy. At the final internal round or a part boundary, use the final variant to reduce c' instead.

The ordinary cycle is (1,2) -> (2,5) -> (3,2) -> (4,5) -> (1,2), in multiples of L for exact generator bounds. q is at most 5L < 2^256 even when c is lazy at 5L; x+c would not be safe in that phase. Active output is at most 2L, low c' at most 5L, high/reset c' at most 2L. The final low-phase reduction gives (2,4,1); high/reset final outputs are also safe for external constants. All ADDs remain emitter-checked. The corrected common prefix uses DUP5 for x, not the rejected prototype's DUP4.

### Recalibrated accounting and verification

Internal model and compiled execution agree at 6,000 instead of 6,112: 27 low rounds at 101, 14 high at 109, 14 reset at 117 and one final at 109. Linear arithmetic is 237 ADD / 99 ADDMOD instead of 223 / 113. The saving is 70 arithmetic gas plus 42 from fourteen fewer net consumed slots, not recovered placement overhead. The new internal fixed-mix floor is `56*48 + 2,808 = 5,496`; its placement/supply gap remains 504. Initial/external/wrapper costs remain 42 / 1,539 / 75. The new core relaxation is `3,813 + 3*1,043 = 6,942`, same-wrapper 7,017; the 639-gas total gap is unchanged (444 SWAP, 195 surplus supply). These are scoped new-arithmetic floors, not unrestricted minima.

- Full Rust suite: nine library, four generator and five compiled verifier tests. Both forks now have strict small-width gas assertions, alongside the unchanged t=16/24/28 snapshots.
- Nine Node tests check accounting, both t=2 policies and both t=3 policies. Rust checks the first bridge, all phases, exact inclusive bounds and threshold-plus-one fallbacks, maximal constants, retained garbage/layout, and final entry with either next-round flag. TS checks the full generated arithmetic counts and external re-entry against the reference.
- Both-fork serial TS/Rust parity passes for t=2/3/4 sources, tests and stdout. Cargo fmt, Prettier, scoped generated diffs and whitespace checks are run before committing.

No A\* sweep, transformed representation, t=4 search, dependency or lockfile change was needed. An additional `forge test --offline --match-contract 'Poseidon2T[23]Test'` did not reach execution: source-only submodules triggered unsuccessful dependency discovery, and the nested stringutils source was missing. No dependency installation succeeded. `/tmp/poseidon2-lane2-foundry.log` records this environment failure; compiled huff-neo/revm verification and the full Rust suite pass independently.

Transient evidence: `/tmp/poseidon2-lane2-t3-{osaka,amsterdam}.log`, `/tmp/poseidon2-lane2-t3-floor.json` and `/tmp/poseidon2-serial-parity.IQUskN`. No claim of global optimality or further placement recovery is made. The independent integration checks below pass. An improved first bridge or joint placement policy remains a separate investigation.

### Independent integration checks

The coordinator rebuilt and passed 18 Rust tests, nine Node tests and the
64-chain production-DSL replay. Separate compiled runs verify 144 calls per
fork at 5,956 / 7,656 / 12,087 on Osaka and 5,917 / 7,656 / 12,087 on Amsterdam.
All model differences are zero. Serial TS/Rust source, test and stdout parity
passes on both forks. Fresh opcode accounting reproduces the revised floors
and unchanged gaps above.

Foundry also passes all 18 t=2/t=3 tests, including input sanitization, in a
source snapshot of commit 95dcf5b with the existing main dependency tree.
This avoids worktree dependency discovery; no download or installation was
needed. The command is `forge test --offline --match-contract 'Poseidon2T[23]Test' --threads 1`.
The log is `/tmp/poseidon2-lane2-independent-foundry.log`.

## Lane 3: finite SHL and standalone MOD probes

Baseline a3f442e, 2026-10-10, measured in branch `bhai/8cf2de96-16957d` before the probes. No production arithmetic, templates, wrappers, parameters or generated outputs change. The test-only verifier hook compiles portable candidate DSL with the existing huff-neo/revm dependencies. No default speedup was found.

### Baseline and final execution

Both the initial compiled CLI runs and final full Rust suite reproduce these call-frame costs, excluding transaction, deployment and caller overhead:

| Fork      | t=2 raw | t=3 raw | t=4 raw | t=4 hash_1 | hash_2 | hash_3 |
| --------- | ------: | ------: | ------: | ---------: | -----: | -----: |
| Osaka     |   5,956 |   7,656 |  12,087 |     11,910 | 11,932 | 12,005 |
| Amsterdam |   5,917 |   7,656 |  12,087 |     11,910 | 11,932 | 12,005 |

Each baseline/final fork verifies 24 / 24 / 96 calls against the reference, with zero model differences. Pinned external known answers, shared vectors and deterministic full-word inputs are unchanged. Gas is deterministic, not CPU timing. The same-wrapper fixed-mix floors remain 5,494 / 7,017 / 11,226, with gaps 462 / 639 / 861. The t=4 final external round remains 352 against the scoped 328 relaxation.

### Finite family and bound checks

`linear_probe.py` reads the incumbent final-round and `LINEAR_FINAL4` TS templates. Production template replay and the external A\* search moves do not support SHL or standalone MOD; neither is extended here. The emitter already uses MOD for input reduction. The family contains 13 final-round and 12 linear-only programs:

- Incumbent and four t0/t1 shift masks, including the unchanged mask. For each selected sum, ADD becomes ADDMOD with immediate `P swap2` supply. Its product PRIME supply is removed and MULMOD by four becomes ordered SHL by two. Existing arithmetic order, slot lifetimes and projected stack layouts are held fixed. DUP depths are remapped; each projected SWAP uses shortest top-based SWAP-only transport, treating equal values as interchangeable. This is not joint arithmetic/placement synthesis.
- Six individual ADDMOD-to-ADD+MOD controls and one all-six control per boundary. Every exposed sum has an inclusive uint256 bound before MOD. Adjacent replacement preserves arithmetic and net consumed slots, so these are tie controls, not a claimed new policy.
- One final-round raw-sharing candidate: retain the unreduced s1 sum for s0's ADDMOD, then MOD s1 and restore the canonical output prefix. All three new SWAPs are charged. This is an actual shared intermediate, but only one delayed-reduction schedule.

Each program has independent inclusive-bound replay and 64 deterministic numeric trials, including zero, one, P-1, maximal input bounds and maximal round constants. Final-round inputs are at most 4(P-1), linear-only inputs at most P-1; S-box constant additions are at most 5(P-1). An early-reduced sum is at most P-1, so shifting it gives at most 4(P-1) < 2^256. Shifting the unreduced sum can reach 8(P-1) > UINT256_MAX and is rejected even on a zero-valued numeric trial. Final consumers already use ADDMOD, so the lazy shifted products do not need another reduction in these programs. This does not justify the substitution in regular rounds.

MOD takes the value before the modulus; SHL takes the shift before the value. Focused regressions reject reversed operands, wrong modulus, unsafe ADD/SHL, invalid input/constant bounds, excessive reach and unsupported operations. Small five-slot BFS independently checks the SWAP transport helper with distinct and repeated values. These checks certify the interval conditions and replayed family, not completeness of a larger search space.

### Compiled candidate results

Every program is compiled and executed on both forks. For each of the 13 full-round programs, only round 63 of the generated raw t=4 permutation is replaced in memory. Its actual input/output wrappers and the other rounds remain unchanged. Each candidate checks all four permutation outputs on the existing eight shared vectors and sixteen deterministic full-word inputs. The hash programs are not replaced by these probes; their unchanged gas is checked separately by the full suite.

| Final-round program                     | Segment model | Compiled raw call, both forks | Against incumbent |
| --------------------------------------- | ------------: | ----------------------------: | ----------------: |
| Incumbent / unchanged shift mask        |           352 |                        12,087 |                 0 |
| Early t0 reduction, then SHL            |           355 |                        12,090 |                +3 |
| Early t1 reduction, then SHL            |           355 |                        12,090 |                +3 |
| Both early reductions and SHLs          |           358 |                        12,093 |                +6 |
| Share raw s1, delay its MOD             |           361 |                        12,096 |                +9 |
| Six individual / all-six ADD+MOD splits |           352 |                        12,087 |                 0 |

All candidate model differences are zero. Shift replacements preserve the 184 arithmetic gas and 48 net consumed slots, but this immediate-supply policy adds one SWAP per replacement. Raw sharing preserves the same inventory and adds three SWAPs. These compiled regressions reject these exact programs, not alternative factorizations, arithmetic orders, PRIME preplacement or fused boundaries.

Each linear-only program is separately compiled behind the same fixed four-input reduction/output wrapper and compared with the reference M4 on 24 full-word inputs per fork. The wrapper costs 95 gas: 55 input, 23 stores, 5 return and 12 memory expansion, including three PUSH0s. It is an isolated linear-layer harness, not the default permutation or an actual fallback option path.

| Linear-only program                          | Segment model | Compiled isolated call, both forks |
| -------------------------------------------- | ------------: | ---------------------------------: |
| Incumbent                                    |           163 |                                258 |
| Unchanged shift mask, redundant SWAP removed |           160 |                                255 |
| Either single shift                          |           163 |                                258 |
| Both shifts                                  |           166 |                                261 |
| Individual / all-six ADD+MOD splits          |           163 |                                258 |

The unchanged mask removes exactly `swap1` from `P P swap1 swap6` in `LINEAR_FINAL4`; exchanging identical PRIME copies is redundant. A regression compares its complete stack and bounds with the incumbent. This is a tested unused-path lead, not an applied production improvement or a three-gas default t=4 saving. Relative to the no-op-free control, each shift again adds three gas.

In total, the compiled probe checks 600 calls per fork (25 programs times 24), separately from baseline/final verification. The Python probe checks 1,600 numeric replays. The JSON reports model evidence; the Rust gate provides the separate compiled measurements above.

### Reproduction and verification

```sh
ROOT=/absolute/path/to/this/worktree
SEARCH="$ROOT/generator-rs/stacksearch"

cargo run --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- verify --hardfork osaka 2 3 4
cargo run --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- verify --hardfork amsterdam 2 3 4
cargo test --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" finite_linear_arithmetic_candidates -- --test-threads=1 --nocapture
cargo test --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- --test-threads=1
node --test "$SEARCH/gas-floor.test.mjs" "$SEARCH/reduction-policy.test.mjs"
cargo fmt --manifest-path "$ROOT/generator-rs/Cargo.toml" -- --check
```

All 19 Rust tests, nine Node tests, seven Python regressions and the 64-chain production t=3 replay pass. The Python regressions regenerate and compare both portable corpora, preventing stale DSL/model records. The full Rust suite includes both-fork small-width verification and unchanged t=16/24/28 snapshots, plus checked-in generator-output equality. The first test-only build attempted to use transitive serde_json, then switched to a tab-separated corpus without adding a dependency. The isolated wrapper's initial 98-gas estimate was corrected to 95 after observing its three PUSH0s; its source was not changed to obtain the correction.

Rust uses cargo fmt; JSON/Markdown use the existing Prettier. No production generator changes require regeneration or new TS/Rust parity. No dependency, lockfile, search heuristic or opcode-accounting guard changes. No broad search, installation, Foundry invocation, merge or push was performed.

Portable evidence: [model and DSL records](results/lane3-linear.json), [compiled corpus](results/lane3-linear.program), `linear_probe.py`, `linear_probe_test.py` and test-only `linear_probe.rs`. Transient logs: `/tmp/poseidon2-lane3-baseline-{osaka,amsterdam}.log`, `/tmp/poseidon2-lane3-rust.log`, `/tmp/poseidon2-lane3-t3-periodic.json`.

### Handoff to lane 4

No incumbent gas or placement gap was recovered. Avoid repeating adjacent ADD+MOD replacements or this immediate-supply transport family. Free PRIME preplacement, different arithmetic order, fused boundaries, other raw shared values and SHL+MOD or MUL+MOD product schedules remain untested. The redundant fallback SWAP is safe locally, but any production patch should first show a benefit on an actual selected option path. Ordinary external-round shifts need their own downstream bound/reduction accounting.

Lane 4's transformed inactive coordinates remain a separate investigation. Keep the incumbent controls, charge entry/exit and all 56 rounds, and distinguish inventory filters from compiled measurements. [EIP-145](https://eips.ethereum.org/EIPS/eip-145) is the operand-order and three-gas SHL prior art; revm compilation/execution supplies the independent checks here.

## Lane 4: bounded inactive-coordinate probe

Baseline ecdb664, 2026-10-10, independently rebuilt in branch `bhai/8cf2de96-db0dff`. Both compiled fork checks reproduce Osaka 5,956 / 7,656 / 12,087 and Amsterdam 5,917 / 7,656 / 12,087, with 24 / 24 / 96 calls per fork and zero model differences. Runtime bytes are 3,918 / 6,719 / 15,644 on Osaka and 4,007 / 6,719 / 13,629 on Amsterdam. The unchanged t=4 hash entrypoints cost 11,910 / 11,932 / 12,005. No coordinate representation is applied to production.

### t = 3 finite family and shear

`inactive_probe.py` checks all 104 integer 2x2 transforms with entries in -2..2 and determinant +/-1, including identity. It computes the exact inverse, `T B T^-1`, forcing `T [1,1]` and active observation `[1,1] T^-1`. Absolute coefficient sums are filters only, not arithmetic costs or scheduled gas. The discriminant of `x^2-5x+5` is 5, and its Legendre symbol is P-1 for the pinned scalar field. This excludes triangular/diagonal base-field similarity, not coupled bases.

For `u=b+c, v=c`, the transformed inactive matrix is `[[3,1],[1,2]]`, forcing `[2,1]`, active row `[1,0]`. The probe uses the six-addition DAG `q=z+u; s=q+v; a'=q+z; v'=s+v; h=s+q; u'=h+u`. A finite dynamic program considers all 64 ADD/ADDMOD masks per round, charges 6/14 funded gas respectively, and carries inclusive multiples of L=P-1 through all 56 rounds. ADD requires a bound at most UINT256_MAX, and each active output is at most 4L so the next constant ADD fits. This is a fixed-DAG policy minimum, not a schedule minimum.

Entry reduces u with ADDMOD from b,c <=4L and keeps v=c, giving a funded allowance of 14. Exit uses `b=(u+(kP-v)) mod P`, c=v, with k equal to v's final bound in multiples of L. Requiring k<=4 ensures both a nonnegative subtraction and `kP <= UINT256_MAX`, and permits external constant additions. SUB plus ADDMOD adds 20 funded gas. These allowances exclude placement and extra stock.

| Evidence for this specific shear/DAG                      |   Gas |
| --------------------------------------------------------- | ----: |
| Minimum 56-round linear funded inventory                  | 2,840 |
| S-boxes plus that inventory and entry/exit allowances     | 5,562 |
| Incumbent internal fixed-inventory floor                  | 5,496 |
| Incumbent scheduled internal chain                        | 6,000 |
| One clean-boundary scheduled model, including conversions | 8,592 |

The scheduled control uses fixed DAG order, last-use consumption, locally shortest commutative top-based SWAP transport with a stable tail, and clean `[a,P,u,v]` boundaries. Entry and exit use the production `[a,P,c,b]=[a,P,v,b]` order. Their costs are 32/41, with every literal PRIME, DUP and SWAP charged. The original probe used `[a,P,b,c]` and undercharged six adapter gas in total; this correction does not change the 5,562 funded relaxation. The complete portable DSL is numerically replayed on 64 chains, including inclusive input endpoints and maximal constants. The replay also propagates independent intervals and checks ADD overflow, SUB order/nonnegativity, exact PRIME operands, reach, output parity and safe external re-entry. There is no compiled coordinate candidate. The 8,592 model rejects only this deliberately bounded transport policy; the 5,562 relaxation leaves 438 gas of possible placement allowance below the incumbent, so the basis itself is not rejected. No larger schedule search follows in this lane.

### t = 4 observable basis

The probe derives the actual diagonal-minus-one constants with the TS generator after its pinned Barretenberg assertion. For inactive `B=D+J`, rows `1^T, 1^T B, 1^T B^2` have determinant equal modulo P to the Vandermonde product of diagonal differences, here nonzero. It checks the characteristic coefficients and recurrence on 64 trials and records all constants in the portable JSON.

The direct recurrence has coefficients `d0+1, c1, c2, -q0, -q1, -q2`, all nonzero and outside +/-5 modulo P. Here `c1=sum(d)+9`, `c2=sum(d^2)+6sum(d)+27`, `q2=-sum(d)-3`, `q1=sum_pairs(d)+2sum(d)` and `q0=-product(d)-sum_pairs(d)`. Its six independent generic MULMODs, one small product by three and six additions have optimistic funded linear inventory 128, or 176 with the S-box. This already exceeds the incumbent scheduled 166 before conversion, extra reductions or placement. Only that naive unfactored DAG is rejected; generic coefficients do not prove that shared products or other factorizations cannot help. No new transform, opcode or parameter infrastructure is added to either production generator.

### Reproduction and verification

```sh
ROOT=/absolute/path/to/this/worktree
SEARCH="$ROOT/generator-rs/stacksearch"
```

Seven Python regressions regenerate [the portable evidence](results/lane4-inactive.json), check all finite inverses and policies, charged full-chain totals, unsafe entry ADD and reversed SUB rejection, and the scoped t=4 inventory. The boundary regression ties both original-coordinate endpoints to all four production INTERNAL3_PERIODIC layouts and a matching next external template. Python uses the installed standard library and existing Node, with no dependency or lockfile changes. The [Poseidon2 paper](https://eprint.iacr.org/2023/323) supplies the linear-layer prior art; the actual constants and arithmetic are checked locally, not inferred from search snippets. The t=2 PRIME backing-copy follow-up is recorded below.

## Lane 4: t = 2 optional PRIME backing

Production baseline ecdb664, remeasured after the boundary correction in branch `bhai/8cf2de96-db0dff`. Only optional backing copies change. The actual MULMOD modulus and next-S-box PRIME copies remain. Arithmetic, parameters, wrappers, bounds and output semantics are unchanged. No new option, memory cache or opcode support is needed.

### Compiled variants and selected policy

Each prototype generates the full t=2 permutation, compiles with huff-neo and verifies 24 shared-vector/full-word calls per fork in revm. These are measured call-frame gas and runtime bytes, not deployment/transaction/caller costs. Every model difference is zero.

| Prototype                                       | Osaka call gas | Runtime bytes | Amsterdam call gas | Runtime bytes |
| ----------------------------------------------- | -------------: | ------------: | -----------------: | ------------: |
| Retained floated baseline                       |          5,956 |         3,918 |              5,917 |         4,007 |
| Omit only specialized `else pushPrime`          |          5,917 |         7,201 |              5,917 |         4,008 |
| Omit entire specialized optional backing stanza |          5,914 |         7,424 |              5,914 |         4,014 |

The partial omission selects `floatPrimeInternal=false`, but still supplies an optional backing copy in the first generic bridge. Removing the entire specialized stanza permits the floated generic bridge, avoiding that extra three gas. These experiments remove copies; they are not the older rejected experiment that supplied a fresh backing copy every round.

The final TS/Rust policy keeps `floatPrimeInternal=true` unchanged as the compact candidate. With `internalMul3` and `floatPrimeInternal=false`, specialized t=2 rounds omit optional backing, and a non-collecting generic t=2 bridge also omits it. This reaches the complete-omission cost without removing the compact option. Other widths and garbage-collecting paths retain their previous policy. `pushPrime` still emits a reachable DUP or literal PUSH32 at the same three gas, with no bound or reach bypass.

| Final default | Before gas | After gas | Saving | Before bytes | After bytes | Growth |
| ------------- | ---------: | --------: | -----: | -----------: | ----------: | -----: |
| Osaka         |      5,956 |     5,914 |     42 |        3,918 |       7,424 |  3,506 |
| Amsterdam     |      5,917 |     5,914 |      3 |        4,007 |       4,014 |      7 |

The Osaka bytecode increase alone adds **701,200 code-deposit gas** at 200 gas/byte. This excludes all other deployment costs and is not a measured full-deployment gas figure. The Amsterdam runtime increase is seven bytes. Both defaults remain within their runtime limits (24,576 / 65,536 bytes), and the compiled tests also enforce the corresponding initcode limits. This is a small execution saving with a large Osaka deployment tradeoff, not a free win.

### Tight-budget compact fallback

The TS regression and compiled Rust regression both call `buildBest` with the old compact core-byte budget. The full wrapper is 51 bytes and 52 call gas. Selection restores `floatPrimeInternal=true` with the same arithmetic and floated-copy path as before; no new knob is introduced.

| Fork      | Tight core `maxBytes` | Selected core bytes | Core gas | Compiled runtime bytes | Compiled call gas |
| --------- | --------------------: | ------------------: | -------: | ---------------------: | ----------------: |
| Osaka     |                 3,867 |               3,867 |    5,904 |                  3,918 |             5,956 |
| Amsterdam |                 3,956 |               3,956 |    5,865 |                  4,007 |             5,917 |

At the ordinary budget, both select the literal-capable candidate at 5,862 core gas, with 7,373 / 3,963 core bytes. The Rust gate compiles both selected budgets and checks all 24 reference inputs per case, giving 48 additional calls per fork. It asserts the chosen option, exact gas/bytes, maximum DUP reach, stack depth, runtime size and initcode size. The compact result is a verified budget fallback, not merely a manually forced option.

### Accounting, safety and verification

Fresh Osaka accounting gives internal gas 4,877 -> 4,835: one generic bridge at 105 and 55 rounds at 86, removing the fourteen backing-copy surcharges. The internal fixed-inventory floor remains 4,496; its surplus-supply gap falls 381 -> 339. Initial/external/wrapper costs remain 27 / 1,000 / 52. The same-wrapper floor remains 5,494, with total gap 462 -> 420 (57 SWAP gas plus 363 surplus supply). This recovers supply headroom, unlike lane 2's arithmetic saving. These remain fixed-inventory, fixed-boundary relaxations, not unrestricted EVM minima.

All arithmetic still passes the emitter's inclusive overflow checks. The existing t=2 bounds/first-bridge/external-re-entry regressions now exercise both backing policies, inactive bounds below P/2P/3P, maximal constants, all 56 rounds, and in Rust both final next-PRIME flags. The specialized MULMOD policy still produces inactive output at most 2(P-1), and its active-output safety guard is unchanged. Final live stock includes PRIME under the reduced outputs in both schedules.

- Both-fork CLI verification: 24 / 24 / 96 calls at 5,914 / 7,656 / 12,087, all model differences zero. t=3 runtime remains 6,719 bytes; t=4 remains 15,644 / 13,629 bytes. The t=4 hash entrypoints remain 11,910 / 11,932 / 12,005.
- Full Rust suite: 20 tests (11 library, four generator, five compiled integration). Both small-width gas snapshots now assert 5,914 for t=2. t=16/24/28 snapshots and checked-in generator equality pass unchanged. The finite lane 3 compiled corpus also passes.
- Eleven Node tests pass, including both t=2 backing policies and both ordinary/tight-budget selections. Fourteen Python regressions pass: seven linear probes and all seven corrected inactive-coordinate probes. The t=3 production DSL still replays 64 complete chains at 6,000 internal gas.
- Serial TS/Rust parity passes on Osaka and Amsterdam for t=2/3/4 sources, tests and stdout. Only the intended tracked Amsterdam t=2 `Permutation.huff` changes after regeneration; its wrapper and test vectors are unchanged.
- Cargo fmt, the existing Prettier and scoped whitespace checks pass. No dependency, lockfile, installation, Foundry invocation, merge or push. The parent owns final README reconciliation and independent Foundry verification in a committed non-Git snapshot.

```sh
ROOT=/absolute/path/to/this/worktree
SEARCH="$ROOT/generator-rs/stacksearch"
cargo run --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- verify --hardfork osaka 2 3 4
cargo run --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- verify --hardfork amsterdam 2 3 4
cargo test --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" t2_omitted_backing_and_compact_budget -- --test-threads=1 --nocapture
cargo test --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- --test-threads=1
node --test "$SEARCH/gas-floor.test.mjs" "$SEARCH/reduction-policy.test.mjs"
node "$SEARCH/gas-floor.mjs"
```

Transient evidence: `/tmp/poseidon2-lane4-t2-{partial,entire}-{osaka,amsterdam}.log`, `/tmp/poseidon2-lane4-final-rust.log`, `/tmp/poseidon2-lane4-final-floor.json`, `/tmp/poseidon2-lane4-final-t3-periodic.json` and `/tmp/poseidon2-serial-parity.NkRYib`. The portable regressions and generated source preserve the selected policy and compact fallback; the unselected partial prototype is documented evidence only. No further investigation follows in this lane.

## Final accounting

Original baseline b7d7125 versus integrated production 5d2d521, 2026-10-10. Measured gas below is call-frame execution gas, excluding transaction intrinsic gas, deployment and caller overhead. Gas is deterministic; host timing and warm medians are not the metric. The pinned parameters and reference outputs are unchanged.

| Fork      | Width | Before |  After | Saving | Runtime bytes before |  After |
| --------- | ----: | -----: | -----: | -----: | -------------------: | -----: |
| Osaka     |     2 |  6,066 |  5,914 |    152 |                3,918 |  7,424 |
| Osaka     |     3 |  7,768 |  7,656 |    112 |                6,733 |  6,719 |
| Osaka     |     4 | 12,087 | 12,087 |      0 |               15,644 | 15,644 |
| Amsterdam |     2 |  6,027 |  5,914 |    113 |                4,007 |  4,014 |
| Amsterdam |     3 |  7,768 |  7,656 |    112 |                6,733 |  6,719 |
| Amsterdam |     4 | 12,087 | 12,087 |      0 |               13,629 | 13,629 |

The t=4 rows measure the raw permutation, not a hash entrypoint. Hash gas remains 11,910 / 11,932 / 12,005. The Osaka t=2 default minimizes execution gas, not total deployment-plus-use cost. Compared with the retained compact schedule, its extra code deposit alone takes 16,696 calls saving 42 gas to recover; other deployment costs are excluded. The compiled compact fallback retains the lane-2 improvement at 5,956 gas and 3,918 runtime bytes.

### What the lower bound means

No unrestricted theoretical minimum was established. The [fixed-mix relaxation](OSAKA-BASELINE.md#fixed-mix-relaxation) fixes arithmetic counts, live boundary stock, three-gas PUSH/DUP supply and the existing wrapper. It makes placement free. With `B = ADD + MUL + 2*ADDMOD + 2*MULMOD`, the core floor is arithmetic gas plus `3*B`. Changing the arithmetic, representation, stock or supply model requires recalibration.

| Width | Arithmetic gas | Slots B | Same-wrapper floor | Actual call | Gap | SWAP gas | Surplus supply |
| ----- | -------------: | ------: | -----------------: | ----------: | --: | -------: | -------------: |
| 2     |          2,997 |     815 |              5,494 |       5,914 | 420 |       57 |            363 |
| 3     |          3,813 |   1,043 |              7,017 |       7,656 | 639 |      444 |            195 |
| 4     |          6,148 |   1,660 |             11,226 |      12,087 | 861 |      612 |            249 |

These are scoped lower bounds, not attainable schedules or promised savings. Removing a DUP can require a SWAP, so the two gap columns cannot be harvested independently. Lane 2 lowers the arithmetic/inventory floors by the same 110/112 gas as the calls; only lane 4's omitted backing copies close the t=2 placement/supply gap, by 42 gas on Osaka.

### Segment attribution

The following accounts for the entire Osaka call. Every initial/external/wrapper segment is unchanged; all realized savings are internal. Wrapper floors are held equal to the current wrapper cost, not proved optimal. Boundary sharing may move credits between segments.

| Width | Segment               | Before | After | Current floor | Gap |
| ----- | --------------------- | -----: | ----: | ------------: | --: |
| 2     | Initial linear        |     27 |    27 |            18 |   9 |
| 2     | Eight external rounds |  1,000 | 1,000 |           928 |  72 |
| 2     | 56 internal rounds    |  4,987 | 4,835 |         4,496 | 339 |
| 2     | Wrapper               |     52 |    52 |            52 |   0 |
| 3     | Initial linear        |     42 |    42 |            30 |  12 |
| 3     | Eight external rounds |  1,539 | 1,539 |         1,416 | 123 |
| 3     | 56 internal rounds    |  6,112 | 6,000 |         5,496 | 504 |
| 3     | Wrapper               |     75 |    75 |            75 |   0 |
| 4     | Initial linear        |    122 |   122 |           104 |  18 |
| 4     | Eight external rounds |  2,571 | 2,571 |         2,400 | 171 |
| 4     | 56 internal rounds    |  9,296 | 9,296 |         8,624 | 672 |
| 4     | Wrapper               |     98 |    98 |            98 |   0 |

Rank by absolute remaining headroom: t=4 internal 672 (504 SWAP + 168 surplus), t=3 internal 504 (336 + 168), then t=2 internal 339 (all surplus). The next segment is t=4 external at 171. Arithmetic and stack transport dominate; these cores have no EVM memory operations or calls.

### Rejections and next targets

- Renaming the existing t=4 bodies cannot improve their finite composition once adapters are charged. Visiting a different layout costs at least 9,314 for 56 rounds versus 9,296. The two larger opcode searches stopped at their memory guards with the old heuristic; neither is an exhaustion or optimality result.
- The compiled t=4 final-round SHL variants add 3/6 gas, and raw-s1 reuse adds 9. Adjacent ADD+MOD controls tie. These reject the tested immediate-supply/order family only. A three-gas redundant SWAP in an unselected linear fallback remains unapplied and is not a default t=4 saving.
- The t=3 shear has a 5,562 fixed-DAG funded relaxation, but the tested clean-boundary transport costs 8,592 with the real entry/exit order. A schedule that permits retained dead values or different operation ordering remains open; it has a 438-gas placement allowance to match the incumbent 6,000.
- The t=4 observable-coordinate recurrence's naive unfactored DAG already needs 176 funded gas per round versus the scheduled incumbent 166. Other factorizations or shared products were not excluded.

The next serious scheduling experiment should target a short joint t=4 window with naturally changing layouts or fused transitions, not repeat the renamed-body control or increase the old search's memory limit. Charge both external boundaries and every transition. For t=3, compare a productive original-basis schedule with a non-clean-boundary shear schedule. At t=2, consuming old inputs at their last use is the remaining transport lead, but the already rejected generic shared-sum implementation is not a new candidate. None of these leads is an implemented saving.

### Independent integration gates

Before fast-forward integration, the coordinator rebuilt the candidate and independently passed:

- 20 generator Rust tests, including the compiled default/compact t=2 gate, the lane-3 compiled corpus and unchanged t=16/24/28 integrations; 11 additional Rust search tests.
- 11 Node accounting/reduction/budget tests, all 28 Python search/linear/coordinate regressions, and the 64-chain t=3 production-DSL replay.
- Compiled Osaka and Amsterdam reference checks at t=2/3/4: 24/24/96 calls per fork, exact model equality. The separate default/compact t=2 run checks 48 calls per fork.
- Serial TS/Rust generation parity for both forks: byte-identical source, tests and stdout. Rust/TS formatting, scoped diffs, signed noreply commits and clean candidate status.
- 29 Foundry tests across `Poseidon2Test`, `Poseidon2T2Test` and `Poseidon2T3Test`. These run from a non-Git archive of committed 5d2d521 with a symlink to the existing main `lib`, using `forge test --offline --match-contract '^Poseidon2(T[23])?Test$' --threads 1`. No dependency installation or lockfile change was needed.

Fresh accounting is reproducible with `node generator-rs/stacksearch/gas-floor.mjs`. Coordinator artifacts are `/tmp/poseidon2-final-candidate-{rust,node,python,osaka,amsterdam,compact}.log`, `/tmp/poseidon2-final-search-rust.log`, `/tmp/poseidon2-final-floor.json`, `/tmp/poseidon2-final-t3-periodic.json`, `/tmp/poseidon2-serial-parity.RuK1gT` and `/tmp/poseidon2-final-foundry.log`. The committed non-Git Foundry snapshot is `/tmp/poseidon2-final-foundry.4CBwgQ`. These logs are transient; the tests, probes, corpus and generated code are committed.

After integration, the main checkout independently passes the same 20 Rust, 11 Node and 28 Python tests, both-fork compiled verification and serial TS/Rust parity again. Its regenerated accounting is byte-identical to the reviewed candidate's JSON. The final main logs use `/tmp/poseidon2-final-main-{rust,node,python,osaka,amsterdam}.log`; parity artifacts are `/tmp/poseidon2-serial-parity.r2ncRg`. Subsequent source edits only correct scheduler comments; no generated opcode or parameter changes accompany the final documentation.


## Wide widths: state elements held in memory

Baseline 3a4db26, 2026-10-11. From t = 16 the `DUP16` reach cannot hold the state, so the consuming internal round keeps reach - 4 = 12 elements on the stack and the rest in memory, and the external rounds shadow their out-of-reach values. Per steady internal round (static opcode gas of the generated body), Osaka paid t = 16 637, t = 28 1,201 against Amsterdam's 555 and 935. Of the t = 28 gap of 266: 15 memory elements at 12 gas each (`PUSH MLOAD`, `PUSH MSTORE` beyond what a stack element pays) is 180, the sum chain's reductions 112 against 72 (a `MOD` of the partial sum before the `ADD` once the PRIME copies under the operands ran out of reach, two elements per reduction), and `s0^5` through memory 18.

### Changes

- 2b3db1e: every reduction of the sum chain is an `ADDMOD`. The copy goes under its operand where the later `DUP`s keep their reach; copies under elements loaded from memory cost none, so they are counted per step from the top instead of from the deepest slot. Otherwise the copy is `DUP`ed on top and `SWAP2`ed under the partial sum: the same 11 gas as the `MOD`, but it absorbs an element (three per reduction).
- 91aa2b8: `consumeSlots`. With shadow, the option search also tries 13 and 14 stack elements for the `primeStack` + `sharedBody` schedules. Each element more saves its loads and store and takes a slot from the sum chain's PRIME copies. t = 16 takes 14, t = 20 and t = 28 13, t = 24 stays at 12. The Osaka search does about twice the builds (Rust `verify` of t = 16 to 28: 578 to 1,025 CPU s; the TS Osaka generation of `parity.sh` takes 64 min).

| Fork  | Width |  Before | After (2b3db1e) | After (91aa2b8) | Saving | Runtime bytes after |
| ----- | ----: | ------: | --------------: | --------------: | -----: | ------------------: |
| Osaka |    12 |  35,718 |          35,696 |          35,696 |     22 |              21,009 |
| Osaka |    16 |  53,927 |          53,066 |          51,792 |  2,135 |              24,420 |
| Osaka |    20 |  69,398 |          69,387 |          67,175 |  2,223 |              24,453 |
| Osaka |    24 |  85,043 |          82,342 |          82,342 |  2,701 |              24,337 |
| Osaka |    28 | 105,773 |         102,480 |         102,130 |  3,643 |     23,020 + 23,126 |

t = 28 is the cold-hop call (warm 103,273 to 99,630). t = 2, 3, 4, 8 and every Amsterdam width are byte-identical. The steady internal round is now t = 16 600, t = 28 1,144; 168 of the remaining 209 at t = 28 is the 14 memory elements' loads and stores.

### Rejected or left open (estimates, not built)

- Accumulating the memory elements' outputs into the next round's sum as they are stored (`DUP1` before the store, `ADD` after) saves 3 gas per element, but the running sum needs a stack slot (12 gas per round as a memory element, or a store and a load): at most 27 gas a round at t = 28, nothing at t = 16 and t = 20.
- Updating a memory element every second round (`d^2 s + d S_j + S_(j+1)`) halves its loads and stores but the next round's sum still needs `d s`, so it takes three `MULMOD`s per two rounds instead of two: dearer.
- Keeping `s0^5` on the stack instead of the 18-gas round trip takes a slot, which a memory element pays 12 to 15 for: about even.
- t = 28 as one contract: 105,019 (period 3, diag constants in memory, which alone cost about 3 gas per use per round). The external rounds are 2,364 bytes each; running them through a shared body would free about 16 KB but costs about 200 gas a round (`CODECOPY` of 28 constants, `MLOAD` per lane, the jumps), for an estimated net 1.6K below the split.
- External rounds: Osaka pays 348 (t = 16) to 648 (t = 28) gas a round over Amsterdam, almost all memory: every S-box output is shadowed (`DUP1 PUSH MSTORE`, 9) and replaced in place (`SWAPn POP`, 5), then loaded again for the column sums and the blocks. A block-wise schedule that consumes each block in place and shadows only what the reach loses is estimated at about 240 gas a round at t = 28 and 100 at t = 16 (2K and 0.8K a call).

## Wide widths: streamed external rounds

Baseline 463ba0e, 2026-10-11. With shadow every S-box output of an external round was stored (`DUP1 <off> MSTORE`, 9 gas) and swapped into the slot of its input (`SWAPn POP`, 5), then loaded again for the column sums and the blocks: a steady round cost t = 16 1,924 and t = 28 3,423 gas of static opcodes against Amsterdam's 1,576 and 2,775, and the `SWAPn POP` were the 119 to 121 POPs a call of t = 16 to 28 executed.

### Change

`externalStream`, taken by every shadow schedule with `externalD` and `externalTemplate` (with shadow and no `gcExternal`, which it makes moot). A layer runs block by block: the column sums `S` (reduced, `chainSumInPlace`) load the S-box outputs `x` from their memory slots, each block computes `u = x + S` on top and its M4 (the `block` template), and each output of the M4 goes straight into the S-box of the next round over a PRIME copy `DUP`ed and swapped under it, whose result is stored to a slot (`<off> MSTORE`, 6). The next layer loads it twice (6 each). The outputs of the last two blocks stay on the stack, so the next layer takes those blocks first. The S-boxes after the internal rounds store their outputs the same way (an input is `DUP`ed or loaded, its slot left dead), the layer before the internal rounds stays `externalMatrix`, and the last round's reduced outputs go straight to their words of `[0, 32t)` instead of `DUP` and `MSTORE` after the round.

A steady round now costs t = 16 1,693 (16 lanes: 4 blocks of 125 for the M4, 57 a stored lane and 51 to 54 a kept one, 140 for the sums), t = 20 2,127 and t = 28 3,036. The code is smaller, so the internal body takes longer periods, and t = 28 fits one contract. POPs a call: 1.

| Fork  | Width |              Before |        After | Saving | Runtime bytes before | after  |
| ----- | ----: | ------------------: | -----------: | -----: | -------------------: | -----: |
| Osaka |    16 |              51,792 |       49,550 |  2,242 |               24,420 | 23,931 |
| Osaka |    20 |              67,175 |       64,405 |  2,770 |               24,453 | 24,557 |
| Osaka |    24 |              82,342 |       79,583 |  2,759 |               24,337 | 24,053 |
| Osaka |    28 | 102,130 / 99,630 (2 parts) | 97,714 (1 part) | 4,416 / 1,916 | 23,020 + 23,126 | 24,239 |

t = 28 before is the cold / warm hop. t = 2 to 12 and every Amsterdam width are byte-identical (no shadow schedule). The Rust `verify` of every Osaka width took 989 CPU s (the shadow search is smaller: the non-streamed variants of those candidates are gone).

### Rejected (measured, Osaka verify)

- Blocks kept on the stack: 0, 1, 2, 3. t = 16 50,207 / 50,043 / 49,752 / 50,252 (before the streamed last round); t = 20 and t = 24 with 1, 2, 3 (also before it): 64,897 / 64,672 / 65,002 and 80,075 / 79,910 / 80,168; t = 28 with 1, 2, 3: 97,939 / 97,714 / 97,936. Three blocks leave the S-box work out of reach.
- A kept lane's input `DUP`ed over a PRIME copy instead of swapped up (3 gas less a lane, a dead value left under the block): t = 16 49,763 (+213, 374 bytes more), the dead values cost reach.
- A PRIME copy before the layer that leads into the internal rounds (no `PUSH32` there): t = 16 +3 gas, -63 bytes; not kept.
- The stream without shadow (t = 8, t = 12): the search keeps the stack-only schedules (24,499, 35,696). With every block kept on the stack (now a candidate, taken on Amsterdam from t = 8) still the same on Osaka.

### Left open (estimates, not built)

- A searched program for a block's M4 run into its four S-boxes and stores: done, see the streamed block programs below (0.7K to 1.2K a call, more than estimated: the search also drops some of the template's own SWAPs).
- One shared body for the streamed layers (as the internal rounds have): a t = 28 layer is about 1.8 KB, 0.9 KB of it round constants, so six calls would free about 5 KB, enough for an internal body period of 3 or 4 instead of 2 (about 29 calls of 50 gas and the sub-chain swaps). But each call pays `CODECOPY` of 28 words and an `MLOAD` per constant (about 170 gas), the kept blocks alternate with period 2, and the slots must match between calls: about even at t = 28, a loss below.
- The internal rounds are now most of the gap to Amsterdam: t = 28 1,171 a steady round against 935 (the 14 memory elements and the period-2 body's calls).

## Wide widths: steady internal rounds

Baseline b999f70, 2026-10-11. A steady internal round of the body cost t = 16 597, t = 20 780, t = 24 970 to 985 and t = 28 1,171 gas of static opcodes against Amsterdam's 555, 687, 811 and 935. At t = 28: 14 memory elements at 18 gas of loads and stores each (load for the sum chain, load for the MULMOD, store), `s0^5` through memory 18, the round constant `MLOAD` 3 and the call overhead 69 a call of 2 rounds, of which 15 is the mid exit every full call passes.

### Changes

- Fused sums (`FUSE_MIN` = 6 memory elements, t = 24 and 28): a consuming round with another after it updates its memory elements first, over the PRIME copy the sum chain leaves under the sum, stores each output with `DUP1 <off> MSTORE` into the slot its input's load freed and adds it to a running sum (reduced by `ADDMOD` with a copy `DUP`ed and `SWAP2`ed under it), stored to one slot. The next sum chain takes that slot as one term instead of loading every element: 3 gas an element for 12 (the sum's store and load) and a `SWAP` per reduction. The first internal round, whose outputs go to memory out of order, sums them from their slots after the round (191 gas once at t = 28); the last, which only takes the sum, costs 137 less.
- `s0^5` at word 0: the hand-off region `[0, 32t)` holds nothing before the last round, so a consuming round with elements in memory stores `s0^5` there: its 3 accesses a round take `PUSH0` (2 gas, 1 byte) instead of `PUSH2`.
- Mid entry: a remainder call of r rounds runs the body's last r rounds instead of its first. It comes before the last full call, `SWAP`s the stack into the layout those rounds start from (each sub-chain rotated by the rounds it skips: at t = 28 six transpositions, 18 `SWAP`s) and jumps to a `JUMPDEST` the full calls pass for 1 gas, instead of every full call paying 15 for a mid exit that jumps to the next instruction. Taken when 3 gas a `SWAP` is below 14 a full call plus the 9 of the exit's setup; a build that fails after it (t = 12, where the rounds after the body start from another rotation and leave reach) is retried with the mid exit.

| Fork  | Width | Before | Fused sums + PUSH0 | Mid entry | Saving | Runtime bytes after |
| ----- | ----: | -----: | -----------------: | --------: | -----: | ------------------: |
| Osaka |    16 | 49,550 |             49,379 |    49,364 |    186 |              24,539 |
| Osaka |    20 | 64,405 |             64,234 |    64,166 |    239 |              24,370 |
| Osaka |    24 | 79,583 |             78,431 |    78,276 |  1,307 |              24,538 |
| Osaka |    28 | 97,714 |             96,472 |    96,137 |  1,577 |              24,513 |

Call gas measured by `verify`. t = 2 to 12 and every Amsterdam width are byte-identical. A steady body round now costs t = 24 952 to 967 and t = 28 1,153 (static, `PUSH0` counted as 3); t = 24 also drops `primeInMemory` (the code is smaller) and takes 14 elements on the stack.

### Rejected (measured)

- Fused sums at t = 20 (5 memory elements, and 6 or 7 with 13 or 12 on the stack): 63,852 code gas against 63,846, so `FUSE_MIN` is 6 and t = 20 keeps loading its elements.
- Fused sums for a single memory element (t = 16): stores the output twice; 49,588 against 49,099 code gas.
- Fused sums without slot reuse (a fresh slot for each output): the slots rotate between calls and the body's replay check fails at every period.

### Left open

- The rest of the t = 28 gap (1,153 against 935): 14 elements at 12 gas of load and store (168), the fused sum's store and load (12), `s0^5` (15), the round constant `MLOAD` (3) and about 27 a round of call overhead. A searched program for the stack part of the round (memory operations as fixed leaves) was not run.

## Wide widths: streamed block programs

Baseline d8a8bac, 2026-10-11. Each block of a streamed layer ran `u = x + S`, the `block` template and then per output `DUP` PRIME, `SWAP1`, the constant, the S-box and the store (a kept lane also a swap up): 389 gas a stored block with its inputs on the stack, 401 with them loaded, 386 a kept one.

### Changes

- `sblock` (stacksearch) searches a whole block from `[S0, S1, S2, S3, P]` and the inputs, with the M4 DAG of the template fixed and the lane (constant, S-box, store) as one move from `[s_i', P]`. Best: stored 365 (none below within a working stack of 10), loaded 377, kept 359 (none below within 10). RESULTS.md has the growth curve (peak 7.1 GB, 621 s).
- `stream_blocks` (templates.rs / templates.ts) holds the programs: two stored ones (the inputs deep or shallow on the stack, or loaded) and two kept ones (inputs loaded 359, on the stack 347, the first layer only); the first whose DUPs reach the stack as it is runs, else the template. `P` DUPs the nearest PRIME copy, so one program serves every floor.

| Fork  | Width | Before | After  | Saving | Runtime bytes after |
| ----- | ----: | -----: | -----: | -----: | ------------------: |
| Osaka |    16 | 49,364 | 48,659 |    705 | 24,306 (24,539)     |
| Osaka |    20 | 64,166 | 63,221 |    945 | 24,033 (24,370)     |
| Osaka |    24 | 78,276 | 77,151 |  1,125 | 24,287 (24,538)     |
| Osaka |    28 | 96,137 | 94,934 |  1,203 | 24,112 (24,513)     |

Call gas measured by `verify`. t = 2 to 12 and every Amsterdam width are byte-identical. A steady round costs t = 16 1,591 (1,693 before) and t = 28 2,862 (3,036).

### Left open

- Blocks across each other: the next block's `u` among this block's S-boxes (the search stops at the block's end with an empty working stack).
- The freed bytes (233 to 401) are not yet spent: a longer internal body period at t = 28 needs more than that.

## Wide widths: body period, inline rounds and raw inputs

Baseline 74c5b9a, 2026-10-12.

### Changes

- Inline rounds: `bodyInline` was rounded down to leave no partial call, a rule from before the mid entry. Now the largest count that fits is kept when it costs less than the rounded one. Amsterdam t = 24 keeps 24 steady rounds inline instead of 9 (a round inline saves 6 gas, the partial call with its mid exit costs 18 more), t = 28 11 instead of 3. Osaka keeps its counts.
- Body period: the search took the sub-chains of the longest period that fits, then spent the bytes left on diag constants as `PUSH32` and inline rounds. Now it also tries shorter periods, stopping at the first that costs no less than the one before. Osaka t = 28 takes a period of 3 with 25 diag constants as `PUSH32` and PRIME from memory instead of a period of 2 with all of them as `PUSH32` (the longest that fits, 4, leaves too few as `PUSH32`): 297 gas. Osaka verify takes about 50% longer.
- Raw inputs: the first part's entry loaded, reduced and stored every shadowed input (23 gas a word). The inputs beyond the entry's own reach (s16 and up) now stay in calldata with a `PUSH0` in their place, and each use loads and reduces one (`[PRIME] <off> CALLDATALOAD MOD`, 14 gas against 6): 5 gas a word, used twice. A build that fails with them retries with the stores.

| Fork      | Width | Before | After  | Saving | Runtime bytes before / after |
| --------- | ----: | -----: | -----: | -----: | ---------------------------: |
| Amsterdam |    24 | 66,605 | 66,539 |     66 | 49,146 / 64,654              |
| Amsterdam |    28 | 79,182 | 79,158 |     24 | 54,923 / 64,616              |
| Osaka     |    24 | 77,151 | 77,087 |     64 | 24,287 / 24,223              |
| Osaka     |    28 | 94,934 | 94,553 |    381 | 24,112 / 24,383              |

Call gas measured by `verify`. Osaka t = 28 is 297 from the period and 84 from the raw inputs. Every other width is byte-identical on both forks.

### Rejected

- Scratch inside `[0, 32t)` on Amsterdam t = 24 / t = 28: the body scratch is the period plus two return slots (25 / 29 words). Dropping the mid-exit slot fits only where there is no partial call (24 words at t = 24), which saves about 4 gas (one word of memory, the return size from `MSIZE`), against the 66 of the inline rounds above, which need it. The output stores start at word 0 below the scratch, so `MSIZE` offsets save nothing either.
- Only the longest and the next shorter period: misses t = 28's period 3, two below the longest.
- Every shadowed input raw (also s8 to s15 at t = 28): 77,062 / 94,528 with the zeros, 77,027 / 94,485 without them (a shallower stack, so a second probe), but inputs within reach at entry lose their 3-gas `DUP`s and t = 16 / t = 20 then fail as one contract or cost more (t = 16 48,775 against 48,659). Not kept; 25 to 70 gas at t = 24 / t = 28 are left there.
- Mid entry for a partial call when there is only one full call (Amsterdam t = 24 / t = 28 after the change above): the rotation of a single chain of 23 / 27 elements takes about as many `SWAP`s, more than the 15 gas of the mid exit.

## Wide widths: ordered block programs and the interleaving bound

Baseline ac591e5, 2026-10-12. The layer before the internal rounds and the last linear layer still ran `u = x + S` and the `block` / `exit` / `final` templates, whose outputs end on top in order (161, 164 and 193 gas a block replayed in `sblock`).

### Changes

- `sblock` goals `exit` (outputs `[o0, o1, o2, o3]` on top), `exit0` (`[o0, P, o1, o2, o3]`, block 0 before the internal rounds) and `final` (the reduced M4). Best: exit 152 (none below within a working stack of 10), exit0 155 (none below within 9), final 184 (none below within 11). RESULTS.md has the growth curves.
- `ordered_blocks` (templates.rs / templates.ts) holds the three programs; `ordered_block` runs the first whose DUPs reach the stack, else the template, in schedules with streamed rounds only (Osaka t = 8 costs 323 gas more with them: 24,822).

| Fork      | Width | Before | After  | Saving | Runtime bytes before / after |
| --------- | ----: | -----: | -----: | -----: | ---------------------------: |
| Amsterdam |     8 | 23,969 | 23,933 |     36 | 25,134 / 25,124              |
| Amsterdam |    12 | 34,342 | 34,288 |     54 | 36,681 / 36,676              |
| Amsterdam |    16 | 45,038 | 44,966 |     72 | 49,150 / 49,123              |
| Amsterdam |    20 | 55,853 | 55,763 |     90 | 61,177 / 61,144              |
| Amsterdam |    24 | 66,539 | 66,431 |    108 | 64,654 / 64,615              |
| Amsterdam |    28 | 79,158 | 79,032 |    126 | 64,616 / 64,571              |
| Osaka     |    16 | 48,659 | 48,635 |     24 | 24,306 / 24,302              |
| Osaka     |    20 | 63,221 | 63,188 |     33 | 24,033 / 24,026              |
| Osaka     |    24 | 77,087 | 77,045 |     42 | 24,223 / 24,213              |
| Osaka     |    28 | 94,553 | 94,502 |     51 | 24,383 / 24,370              |

Call gas measured by `verify`. t = 2 to 4 and Osaka t = 8 / t = 12 are byte-identical. Amsterdam saves 18 gas a block (9 in each layer); on Osaka only the last layer takes its program.

### Rejected

- Osaka exit layer with a pushed PRIME (`[PRIME]` or its memory slot) where no copy is within `DUP16` reach: t = 16 48,617 (+58 bytes), t = 20 63,194 (+6 gas), t = 24 and t = 28 12 gas less. Not uniform, not kept.
- Dead values left on the stack (Amsterdam, `GARBAGE=1`: a `DUP` may leave a spare copy, nothing is popped) for the 347 kept block: none below 347 within a working stack of 8 (102M states, 699 s, 14.7 GB); 9 would pass 30 GB.
- Interleaving adjacent blocks (the next block's `u` among this block's S-boxes): a lower bound first (`sblock` `ROLL=1`, RESULTS.md), 341 within a working stack of 10 against 347, so at most 6 gas a block and only if every one of its six rolls is a `SWAP` the neighbouring block needs as well. Not worth a two-block search, whose states would be far beyond the memory cap.

### Left open

- The S-boxes after the internal rounds (51 gas a lane: a PRIME copy and a `DUP` of the input over the 45 of the lane) could run in the last internal round's output loop, where each output is on top over a PRIME copy: about 3 gas a lane (45 at t = 16, 81 at t = 28 on Amsterdam), at the price of a hook in every internal round emitter, the shared body included.
- Column sums (119 gas a round at t = 16): `t` `DUP`s, the `ADD`s and one `ADDMOD` a column; every S-box output has two reads (its column sum and its `u`) and none comes up on top at the right moment, and an unreduced sum (up to `kp`) overflows the M4 (`t0 = u0 + u1` needs `u < 2.6p`). No gain found.
