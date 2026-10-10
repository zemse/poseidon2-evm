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
