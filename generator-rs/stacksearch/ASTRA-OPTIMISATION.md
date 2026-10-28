# Astra runtime gas search

Baseline 0aca28a, 2026-10-28, branch `bhai/afc34024-3f338a`. Serial experiments in an isolated worktree. The metric is compiled call-frame execution gas, not generator time, transaction intrinsic gas or deployment cost. No dependency or lockfile changes.

## Baseline

`cargo run --release --locked --offline --quiet --manifest-path generator-rs/Cargo.toml -- verify [--hardfork osaka] 2 3 4 8 12 16 20 24 28` passes on both forks. Each fork checks 288 calls: 24 per raw width, plus 72 t = 4 hash calls. Every model difference is zero.

| Entry | Amsterdam | Osaka |
| --- | ---: | ---: |
| t2 | 5,912 | 5,912 |
| t3 | 7,653 | 7,653 |
| t4 permutation | 12,083 | 12,083 |
| t4 hash_1 | 11,895 | 11,895 |
| t4 hash_2 | 11,902 | 11,902 |
| t4 hash_3 | 11,975 | 11,975 |
| t8 | 23,933 | 24,499 |
| t12 | 34,288 | 35,696 |
| t16 | 44,966 | 48,635 |
| t20 | 55,763 | 63,188 |
| t24 | 66,431 | 77,045 |
| t28 | 79,032 | 94,502 |

The raw t = 4 permutation is a verifier harness, not a public hash arity. All current Osaka widths fit one contract, so none of these rows includes an inter-contract hop.

## Trace and priority

Load and sanitize inputs, initial linear layer, four external rounds, internal rounds (56 at small widths, width-dependent above), four external rounds, output stores. t = 4 hashes use folded first-round forms and compute only the requested final row. Streamed wide external layers combine each M4 block with the next round's S-boxes. Shared internal bodies need separate dynamic accounting from their code size.

`node generator-rs/stacksearch/gas-floor.mjs` reproduces the fixed-mix small-width floors. These hold arithmetic and stack supply fixed, make placement free and are not attainable minima. The unchanged internal gaps are t4 672, t3 504, t2 339 gas. The old cycle searches already exclude cheaper schedules in their stated SWAP-only models, so repeating them without a new move is low priority.

The larger absolute opportunity is the legacy wide-state memory traffic: Osaka exceeds Amsterdam by 15,470 gas at t28, 10,614 at t24, 7,425 at t20 and 3,669 at t16. Most of that is required by the current representation and reach, not freely recoverable headroom. A streamed kept external block costs 347 gas; t28 runs 49 such blocks, so three gas a block is 147 gas a call.

## Experiments

### 1. EXCHANGE-enabled streamed blocks: no saving in windows 8 and 9

[EIP-8024](https://eips.ethereum.org/EIPS/eip-8024) supplies an additional three-gas move: exchange stack positions n and m (zero-based), with 1 <= n < m and n + m <= 30. Existing searched programs use only top-based SWAPs. A scan of every selected Amsterdam straight-line schedule finds no adjacent `swapA swapB swapA` opportunity. A new schedule, not a textual triple replacement, is needed.

The fixed-DAG `sblock` search now accepts `EXCHANGE=1`, keeping arithmetic, bounds, floor and clean goal unchanged. These searches both completed normally without a program below 347 gas:

| Working window | Expanded / retained states | Outcome |
| --- | ---: | --- |
| 8 | 7,160,279 | Exhausted below 347 |
| 9 | 21,161,769 | Exhausted below 347 |

Reproduce after `cargo build --release --locked --offline --manifest-path generator-rs/stacksearch/Cargo.toml --bin sblock`:

```sh
EXCHANGE=1 REACH=235 generator-rs/stacksearch/target/release/sblock S0,S1,S2,S3,P,_,_,_,_,x0,x1,x2,x3 kept 8 347
EXCHANGE=1 REACH=235 generator-rs/stacksearch/target/release/sblock S0,S1,S2,S3,P,_,_,_,_,x0,x1,x2,x3 kept 9 347
```

Window 9 finished in about ten minutes. RSS sampling began eight minutes into that run and peaked at 3,500,768 KiB during the sampled interval, not a whole-run peak. An 8 GiB / approximately 20 minute guard was armed; neither limit was reached. No larger frontier follows in this experiment.

Three focused Rust tests check exchange pair legality, all working depths through 16, preservation of the fixed floor and original move set, identical-value rejection, three-gas replay versus the equivalent nine-gas SWAP triple, and replay of the unchanged 347-gas incumbent with EXCHANGE off and on. This is a search-tool change, not a production gas saving. The result excludes only the fixed-DAG, bounded working windows and generation rules tested.

### 2. Compact raw input entries: lower wide legacy call gas

The first prototype left all shadowed t24/t28 inputs in calldata but retained their zero placeholders: Osaka 77,020 / 94,477, 25 gas saved at each width. Omitting the placeholders and counting PRIME depth from the slots actually loaded gives 76,985 / 94,434. Both prototypes were compiled and checked on 24 full-word/shared-vector calls per width. The final implementation has no width threshold: `compactInputs` is an additional attempt on the selected shadow schedule, and a failed, tied or slower attempt retains the original candidate.

Selection now includes actual entry, tail and memory costs. Later split parts load lazy calldata without the initial reductions and include their hand-over tail. Folded hash rounds start from the prologue's stack, pay no calldata entry, and return only the live output; fixed dispatch/prologue costs do not affect their ranking.

| Fork | Entry | Before | Selected after | Saving | Runtime bytes before | After |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Osaka | t16 | 48,635 | 48,635 | 0 | 24,302 | 24,302 |
| Osaka | t20 | 63,188 | 63,188 | 0 | 24,026 | 24,026 |
| Osaka | t24 | 77,045 | 76,985 | 60 | 24,213 | 23,873 |
| Osaka | t28 | 94,502 | 94,434 | 68 | 24,370 | 23,898 |
| Paris | t16 | 48,809 | 48,809 | 0 | 24,413 | 24,413 |
| Paris | t20 | 63,362 | 63,362 | 0 | 24,089 | 24,089 |
| Paris | t24 | 77,227 | 77,159 | 68 | 24,272 | 23,924 |
| Paris | t28 | 94,694 | 94,614 | 80 | 24,415 | 23,931 |

All Amsterdam entries and Osaka t2/t3/t4/t8/t12 retain the baseline gas table above. Default Amsterdam regeneration leaves every checked-in Huff/test file unchanged. The improvement is in the legacy generated output, which is not checked in.

Final gates completed:

- `verify 2 3 4 8 12 16 20 24 28` on Amsterdam and Osaka: 288 calls each, exact measured/model equality.
- `verify --hardfork paris 2 3 4 16 20 24 28`: 240 calls, exact equality. Separate baseline b534d07 source and target directories reproduce the Paris before values on 96 wide calls.
- `cargo test --release --locked --offline --manifest-path generator-rs/Cargo.toml`: 35 tests passed (22 library, one CLI, three known-answer, four generator, five execution).
- Five new unit tests cover marker/placeholder semantics, PRIME depth/reach, lazy and stored boundaries, unchanged selection on failure/tie/regression, and hash/split frame-cost distinctions. Existing strict gas assertions change only for the independently measured Osaka t24/t28 reductions; correctness and gas tolerances are unchanged.
- Full Foundry suite: 127 passed, zero failed/skipped, three t4 fuzz tests at 10,000 runs. Existing dependency sources are borrowed read-only with `--lib-paths` and two separate `--remappings` flags; no installation. An initial import-resolution failure and an incorrect two-value remapping invocation (zero tests) are not counted as passes.
- Default all-width regeneration, `forge fmt`, `cargo fmt --check`, Clippy with `--all-targets -- -D warnings`, five gas-floor tests and `git diff --check` pass.

Logs: `astra-compact-selected-{amsterdam,osaka,paris}.log`, `astra-baseline-paris-wide-isolated.log`, `astra-compact-{unit-tests,all-tests,forge,clippy,generation}.log`. The first attempted Paris baseline reused the candidate's Cargo target and was invalid evidence; only the isolated-target baseline is used. Do not share one target directory between baseline and candidate packages with the same name/version.

### 3. Factored internal state: two compiled regressions

Starting from daf9c7a, two prototypes keep inactive lanes as `a_i + q` modulo PRIME. Lane 0 remains materialized. The first internal round initializes `a_i = d_i*s_i` and q to that round's sum; later rounds compute `q' = x + sum(a_i) + (t-1)*q` and `a_i' = d_i*(a_i+q)`. The last round reconstructs every inactive lane. This uses diagonal-minus-one coefficients, not the full diagonal. Exact emitter bounds and reference outputs are checked throughout.

The existing consuming chains hold the products on the stack. q replaces the backing slot below the state using DUP, SWAP and POP (8 gas); the extra weighted term uses MULMOD, never an unchecked large integer multiplication. Shared-body layouts identify q separately so each call uses its own offset. These prototypes only admit stack-held lanes; legacy memory schedules were not widened.

| Amsterdam entry | daf9c7a | Reduced q prototype | Lazy q prototype | Best regression |
| --- | ---: | ---: | ---: | ---: |
| t16 | 44,966 | 46,086 | 45,638 | +672 |
| t20 | 55,763 | 56,435 | 55,987 | +224 |
| t24 | 66,431 | 67,267 | 66,819 | +388 |
| t28 | 79,032 | 79,728 | 79,264 | +232 |

Each prototype compiled and verified 24 full-word/shared-vector calls per changed width with zero gas-model differences. The first invocation also checked unchanged t8/t12, whose selected schedules do not use consuming internal rounds. Runtime sizes of the lazy prototype are 50,467 / 62,432 / 64,753 / 65,468 bytes. t24 needs a shorter body period (22 instead of 23), adding boundary/call costs.

The reduced prototype normalizes the weighted term and adds it with ADDMOD. The lazy variant uses ADD, keeps q below 2P and reconstructs inactive inputs below 3P, saving 8 gas in each later internal round. The remaining arithmetic saving is too small for this storage policy: an existing lazy-input sum reduces roughly every three lanes, not every two; reduced products roughly every five. At t28 the lazy prototype still costs four gas more in each later internal round. Initialization and final reconstruction are charged, not omitted.

The prototypes were removed after saving `astra-factored-lazy.patch`, `astra-factored-first.log` and `astra-factored-lazy.log` in scratch. A fresh all-width Amsterdam verify after restoration reproduces daf9c7a exactly (`astra-after-factored-restore.log`). No production representation change is retained. This rejects these two storage/sum policies, not the algebra or schedules that consume the old q in place at its last use.

Next structural target: tree-shaped rather than serial sum reductions. Balanced ADD/ADDMOD trees can feed two lazy partial sums to one ADDMOD, potentially lowering the reduction count without an extra scalar state or multiplication. Any gain must include actual stack placement and all boundaries.

### 4. Parameter-cache re-entry during the full tree gate

The expanded parallel execution suite stopped making progress before the tree gate completed. A macOS process sample (`astra-tree-stall.sample`) shows a worker inside `generate_params_uncached`, its parallel `check_minpoly_condition`, a stolen width-generation job, and another `generate_params` waiting on a per-width OnceLock. CPU was zero; the sampled test process was terminated, not counted as passing.

A controlled regression re-enters the same cache through a nested Rayon job before the outer derivation is published. Each test runs in its own subprocess with a 30-second timeout and a guard that kills and reaps it on failure. With the original blocking initializer the regression fails at 30.01 seconds (`astra-cache-before.log`). Deriving outside the initializer, then publishing the completed immutable result, passes both the nested request and four concurrent same-width callers in 0.31 seconds (`astra-cache-after.log`). All callers receive the same published Arc and all parameter fields match uncached derivation.

Uncached derivation does not call the parameter cache: it computes round counts, Grain constants and the diagonal/minpoly checks. Only its Rayon scheduling can execute another caller. No parameter algorithm, value or round count changes. Concurrent misses may repeat derivation, at most once per request before publication; the four-caller regression checks one to four derivations, and the controlled nested case exactly two. Cache hits do no work. Rayon and concurrent tests remain enabled.

The cache fix is verified independently of the uncommitted tree code: e1150f9 archived to `astra-cache-source`, with only `round_constants.rs` and its new test module copied in, using a separate `astra-cache-target`. The complete 37-test generator suite passes there, including pinned answers, generator equality and compiled reference/gas gates (`astra-cache-isolated-tests.log`).

### 5. Bound-checked sum trees

The serial sum reduces its accumulator when another lazy input would overflow. A tree can instead feed two lazy partial sums to one ADDMOD. `sum_tree.rs` plans ordered binary trees; `treeSums` emits the chosen tree with PRIME before each ADDMOD's operands. The consuming internal rounds and streamed column sums use it. No new scalar state, multiplication, fork opcode or public interface is needed.

Correctness follows by induction over the tree. Each leaf occurs once, in the supplied order. An ADD is admitted only when the exact inclusive child bounds have a checked uint256 sum; its bound is that sum. An ADDMOD takes the BN254 PRIME, accepts full-word operands and has bound P-1. Both nodes preserve the sum of their leaves modulo P. The root must meet the requested cap. Emission independently replays these operations through value.rs, which still rejects unsafe ADD/MUL/SHL and wrong moduli; no overflow check is bypassed.

The planner prices a leaf/PRIME copy at 3, ADD at 3 and ADDMOD at 8, common to all supported forks. Its cache key contains the complete ordered bound vector and cap. Fork, layout and memory options are not missing inputs to this model: reach, shadow loads, actual PRIME supply and code size are deliberately outside it, checked and priced by the emitter and complete-call option search. Smaller bounds with no greater arithmetic cost dominate for the primary objective. Peak is only a tie-break among retained trees; pruning may discard an equal-gas larger-bound tree with a smaller peak, so no global peak-optimality claim is made.

Trying trees only on the already-selected old schedule misses the Amsterdam t8/t12 savings and several legacy improvements. The final search retains the entire original family, evaluates the corresponding tree family separately (including compact-entry attempts), and keeps the old candidate on failure, tie or regression. Actual entry/tail/memory gas, body periods, inline rounds and code limits decide the winner, not planner gas alone.

Before is e1150f9, including compact inputs. All figures below are compiled call-frame gas with reference-checked outputs and exact model agreement:

| t | Amsterdam before | After | Osaka before | After | Paris before | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 23,933 | 23,807 | 24,499 | 24,217 | 24,560 | 24,278 |
| 12 | 34,288 | 34,145 | 35,696 | 35,047 | 35,707 | 35,058 |
| 16 | 44,966 | 44,494 | 48,635 | 48,635 | 48,809 | 48,809 |
| 20 | 55,763 | 54,835 | 63,188 | 62,956 | 63,362 | 63,130 |
| 24 | 66,431 | 65,489 | 76,985 | 76,281 | 77,159 | 76,455 |
| 28 | 79,032 | 77,826 | 94,434 | 93,372 | 94,614 | 93,552 |

Every t2/t3/t4 permutation and hash arity is unchanged. All widths still fit one contract. Amsterdam t8/t12 now choose consuming rounds, lowering peak depth from 657/931 to 140/184. t24/t28 keep 25/12 steady rounds inline instead of 24/11. The six Amsterdam permutations are regenerated; default wrappers, vectors, constants and round counts are unchanged.

Verification: all nine widths on each of Amsterdam/Osaka/Paris, 864 calls total. Four planner tests include 96 asymmetric/random bound lists compared with unpruned exhaustive interval-tree costs, numeric replay at zero, bounds, half-bounds and random values, uint256 endpoints and cache-order/cap isolation. Two emitter tests replay across all six supported forks and check gas, depth, preserved tail, bounds, overflow/reach rejection and fallback selection. After the independent cache fix, the complete 45-test Rust suite passes with concurrent tests and Rayon enabled. Foundry passes 127 tests with the configured 10,000-run t4 fuzz tests. Clippy, formatting, five gas-floor tests, 28 stacksearch tests and whitespace checks pass. A second all-width regeneration is byte-identical to the first generated diff.

Logs: `astra-tree-final-{amsterdam,osaka,paris}.log`, `astra-tree-unit-tests.log`, `astra-tree-all-tests-fixed.log`, `astra-tree-forge.log`, `astra-tree-clippy.log`, `astra-tree-stacksearch-tests.log`, `astra-tree-regeneration.log`. `astra-tree-selected-*` records the weaker selected-layout-only control. The failed pre-cache-fix suite remains in `astra-tree-all-tests.log`, not counted as a completed gate. `astra-tree-final-tests.log` is the final suite rerun after the iterator-only lint cleanup.

### 6. Peak-aware Pareto sum trees

The ordered bounds `[5, 1, 4, 2] * (P-1)` with cap P-1 expose a real lost alternative: the earlier planner chooses 37 gas with peak 5, but an exhaustive interval-tree enumeration finds 37 with peak 4. This was a lost optimisation, not unsafe arithmetic.

`treePeak` retains a frontier over inclusive output bound, arithmetic gas and working-stack peak. A candidate is removed only when another is no greater in all three coordinates (equal triples retain their first representative). This dominance composes at either child position: parent bounds are monotone checked sums or P-1, costs are additive, and peaks are maxima of the child peaks plus fixed offsets. Leaf order and the PRIME-before-operands convention stay fixed. The root still prefers gas, then peak, then bound. The old arithmetic-only tree policy remains a separate candidate, and tied, slower or failed peak-aware builds cannot replace it. The cache key now also includes frontier policy.

Regressions replace the diagnostic-only test: the concrete 37-gas witness reaches peak 4, all 3,905 bound lists of length 1..5 with entries 1..5 times P-1 match the complete nondominated triple set from unpruned parent composition, and additional zero/full-word endpoint lists agree. Both policies replay through the emitter on all six supported forks; cache tests distinguish policies. This is an exact frontier for the stated grammar and emission convention, not unrestricted EVM scheduling optimality.

Measured call-frame gas: before is b95f817, after is this candidate:

| Fork | t | Before | After | Saving | Runtime bytes before | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Osaka | 16 | 48,635 | 48,124 | 511 | 24,302 | 22,951 |
| Osaka | 24 | 76,281 | 75,942 | 339 | 24,036 | 23,985 |
| Osaka | 28 | 93,372 | 92,158 | 1,214 | 23,915 | 23,956 |
| Paris | 16 | 48,809 | 48,298 | 511 | 24,413 | 23,062 |
| Paris | 24 | 76,455 | 76,116 | 339 | 24,087 | 24,036 |
| Paris | 28 | 93,552 | 92,527 | 1,025 | 23,948 | 23,885 |

Every Amsterdam width and every other legacy entry/arity is unchanged. All nine widths on Amsterdam, Osaka and Paris pass compiled reference verification (864 calls, every gas-model difference zero). The actual whole-call improvements, not the peak witness alone, justify selection. The full 47-test generator suite and 127 Foundry tests pass, Clippy passes, and all-width default regeneration leaves checked-in Huff and generated tests unchanged. Formal exports and proof correspondence are coordinator-owned and have not been refreshed by this lane.

Evidence: `astra-tree-peak-diagnostic.log`, `astra-peak-unit-tests.log`, `astra-peak-{amsterdam,osaka,paris}.log`, `astra-peak-all-tests.log`, `astra-peak-forge.log`, `astra-peak-clippy.log`, `astra-peak-generation.log`. The Osaka full-family comparison remained CPU-active with about 126 MiB observed RSS; its longer generation time is not an EVM performance claim.

## Verification and evidence

Session scratch contains `astra-baseline-{amsterdam,osaka}.log`, `astra-baseline-floor.json`, `astra-baseline-schedule.json`, `astra-exchange-kept{8,9}.log`, `astra-exchange-kept9-resources.log`, `astra-search-tests.log` and the fetched EIP text. The durable tables above do not depend on those temporary files surviving.

`cargo test --release --locked --offline --manifest-path generator-rs/stacksearch/Cargo.toml` passes all 28 tests after the search extension. `cargo fmt` and `git diff --check` pass. No production generator or checked-in Huff changes accompany it.

The integration branch is `opt`, not the older local `main`. Coordinator commit a433745 corrects the diagnostic `schedule` wrapper-memory accounting; core floors and compiled baseline measurements above are unaffected. The old diagnostic small-width call totals were two to four gas too high. Subsequent experiments use `opt` as their base.

## Remaining search

- Preserve equal-gas tree alternatives with lower peak; test actual legacy reach/load costs, especially t16 where the serial candidate still wins.
- Tree leaf-order and code-size ties that could free more shared-body inline rounds.
- EXCHANGE in internal and streamed block scheduling outside the exhausted kept-block windows.
- More selective raw calldata entries than the retained all-shadowed compact candidate.
- Full-word input reduction placement and initial linear layer fusion, with exact interval bounds.
- Shared-body period and boundary cost interactions after any byte savings.

Do not repeat the finite renamed-body controls, adjacent ADD+MOD substitutions, or immediate-supply SHL transport from OSAKA-OPTIMISATION.md. Those rejections remain scoped to their tested schedules.
