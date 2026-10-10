# Osaka optimisation lanes

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
python3 -m unittest discover -s "$SEARCH" -p internal_test.py -v
python3 "$SEARCH/internal_check.py" "$SEARCH/results/t4-internal-incumbent.txt" 4 s0,P,s1,s2,s3 s0,P,s1,s2,s3 1 16
python3 "$SEARCH/internal_layouts.py"

# Historical invocations, not reproduction of the old frontier on corrected code.
RSS_GIB=8 UB=166 python3 "$SEARCH/bench.py" /tmp/poseidon2-lane1-any-end 300 "$SEARCH/target/release/internal" 4 s0,P,s1,s2,s3 O,O,O,O,P 1 16
RSS_GIB=8 UB=166 UNORDERED=1 python3 "$SEARCH/bench.py" /tmp/poseidon2-lane1-unordered 300 "$SEARCH/target/release/internal" 4 s0,P,s1,s2,s3 s0,P,s1,s2,s3 1 16

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
- `python3 "$ROOT/generator-rs/stacksearch/t3_periodic.py"` reads the production TS DSL and independently replays 64 complete 56-round chains, retaining garbage and checking PRIME, outputs, cost and strict bounds. This numeric probe is not a compiled measurement; the revm runs above provide that separate evidence.

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
python3 "$SEARCH/linear_probe.py" > /tmp/poseidon2-lane3-linear.json
python3 "$SEARCH/linear_probe.py" --programs > /tmp/poseidon2-lane3-linear.program
python3 -m unittest discover -s "$SEARCH" -p linear_probe_test.py -v
cargo test --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" finite_linear_arithmetic_candidates -- --test-threads=1 --nocapture
cargo test --release --locked --offline --manifest-path "$ROOT/generator-rs/Cargo.toml" -- --test-threads=1
node --test "$SEARCH/gas-floor.test.mjs" "$SEARCH/reduction-policy.test.mjs"
python3 "$SEARCH/t3_periodic.py"
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
| One clean-boundary scheduled model, including conversions | 8,586 |

The scheduled control uses fixed DAG order, last-use consumption, locally shortest commutative top-based SWAP transport with a stable tail, and clean `[a,P,u,v]` boundaries. Its entry/exit cost 29/38, with every literal PRIME, DUP and SWAP charged. The complete portable DSL is numerically replayed on 64 chains, including inclusive input endpoints and maximal constants. The replay also propagates independent intervals and checks ADD overflow, SUB order/nonnegativity, exact PRIME operands, reach, output parity and safe external re-entry. There is no compiled coordinate candidate. The 8,586 model rejects only this deliberately bounded transport policy; the 5,562 relaxation leaves 438 gas of possible placement allowance below the incumbent, so the basis itself is not rejected. No larger schedule search follows in this lane.

### t = 4 observable basis

The probe derives the actual diagonal-minus-one constants with the TS generator after its pinned Barretenberg assertion. For inactive `B=D+J`, rows `1^T, 1^T B, 1^T B^2` have determinant equal modulo P to the Vandermonde product of diagonal differences, here nonzero. It checks the characteristic coefficients and recurrence on 64 trials and records all constants in the portable JSON.

The direct recurrence has coefficients `d0+1, c1, c2, -q0, -q1, -q2`, all nonzero and outside +/-5 modulo P. Here `c1=sum(d)+9`, `c2=sum(d^2)+6sum(d)+27`, `q2=-sum(d)-3`, `q1=sum_pairs(d)+2sum(d)` and `q0=-product(d)-sum_pairs(d)`. Its six independent generic MULMODs, one small product by three and six additions have optimistic funded linear inventory 128, or 176 with the S-box. This already exceeds the incumbent scheduled 166 before conversion, extra reductions or placement. Only that naive unfactored DAG is rejected; generic coefficients do not prove that shared products or other factorizations cannot help. No new transform, opcode or parameter infrastructure is added to either production generator.

### Reproduction and verification

```sh
ROOT=/absolute/path/to/this/worktree
SEARCH="$ROOT/generator-rs/stacksearch"
python3 "$SEARCH/inactive_probe.py" > /tmp/poseidon2-lane4-inactive.json
python3 -m unittest discover -s "$SEARCH" -p inactive_probe_test.py -v
```

Six Python regressions regenerate [the portable evidence](results/lane4-inactive.json), check all finite inverses and policies, charged full-chain totals, unsafe entry ADD and reversed SUB rejection, and the scoped t=4 inventory. Python uses the installed standard library and existing Node, with no dependency or lockfile changes. The [Poseidon2 paper](https://eprint.iacr.org/2023/323) supplies the linear-layer prior art; the actual constants and arithmetic are checked locally, not inferred from search snippets. The t=2 PRIME backing-copy lead is the next bounded unit.
