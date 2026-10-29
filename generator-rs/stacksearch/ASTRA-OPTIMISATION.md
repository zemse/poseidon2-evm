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

### 7. Context-priced sum bytes and leaf orders: no runtime win

A temporary planner adds exact code bytes to bound/gas/peak frontiers. Its subproblem key includes leaf interval, live prefix depth and nearest PRIME depth; the outer key includes ordered bounds, original leaf depths, PRIME depth, reach and cap. A leaf prices DUP1..16 at one byte and DUPN at two; a PRIME copy costs one/two bytes when reachable and PUSH32 otherwise. The model is restricted to distinct, stack-held non-PRIME leaves, with no shadow loads or memory-backed PRIME. Every emitted kernel checks its gas and recorded bytes against that model.

Four forced Amsterdam candidates were compiled and reference-checked at t8/t12/t16/t20/t24/t28, 144 calls each (576 total), with zero model differences. A separate normal selection run retained the baseline on ties.

| t | Baseline gas | Deepest-first / shallowest-first gas | Either bound-sorted order gas | Baseline bytes | Deepest-first / shallowest-first bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| 8 | 23,807 | 23,807 | 23,815 | 24,725 | 24,725 |
| 12 | 34,145 | 34,145 | 34,153 | 35,906 | 35,906 |
| 16 | 44,494 | 44,494 | 44,502 | 48,380 | 48,323 |
| 20 | 54,835 | 54,835 | 54,843 | 60,455 | 60,286 |
| 24 | 65,489 | 65,489 | 65,505 | 65,015 | 64,867 |
| 28 | 77,826 | 77,826 | 77,842 | 65,151 | 65,105 |

The byte savings at t24/t28 do not buy another inline round: both still keep 25/12. The smaller widths are not code-size-bound on Amsterdam. Sorting by ascending or descending bound loses 8 gas at t8..t20 and 16 at t24/t28. These results reject the tested leaf orders and local tree-byte objective, not all cross-kernel code-size schedules. No runtime benefit is claimed from deployment size alone, and no prototype code is retained in production.

Artifacts: `astra-byte-tree-{amsterdam,forced-amsterdam,shallow,bound-desc,bound-asc}.log`, `astra-byte-tree-unit.log`, `astra-sum-bytes.rs` and `astra-byte-tree-bound-asc.patch`. A fresh all-width Amsterdam verify after removing the prototypes reproduces c7d63fc (`astra-byte-tree-restored.log`).

### 8. EXCHANGE-aware t3 linear-form search: memory cutoff

`t3int` now supports EXCHANGE moves within its at-most-16-slot window, replay with goal/suffix-bound checks, validation before narrowing CLI bounds, and upper-bound pruning before storing a child. EXCHANGE off retains the old move set. The heuristic counts missing final arithmetic, mandatory PRIME supply and the maximum leaf-copy deficit, without cleanup charges. Removing those charges is conservative; the tests do not establish an old-heuristic counterexample for this t3 graph.

Five focused tests cover all 105 exchange move codes, pair/window legality, three-gas exchanges versus equivalent nine-gas SWAP triples, unchanged disabled moves, six incumbent programs with both settings and every suffix, malformed bounds/windows/replays, displaced goals, consumable spare PRIME and recombinable partials. The complete stacksearch suite passes 33 tests. These tests validate the harness, not a new EVM optimisation.

One search was run, with an 8 GiB sampled RSS guard and a 20-minute deadline:

```sh
EXCHANGE=1 generator-rs/stacksearch/target/release/t3int 3 2 4 5 1 8 2 56
```

This is the low phase after its S-box, from x < P, s1 < 3P, s2 < 2P to bounds (2,4,5), with one garbage slot and window 8. Its incumbent replays at 56 gas. The search hit the RSS guard after 76.1168 seconds, sampled peak 9,072,128 KiB; sampling and allocation bursts permit overshoot. It received SIGTERM (return code -15). Last reported progress was 23,000,000 expansions, 55,589,909 retained states, queue 33,215,587, f = 51. These are last reported counters, not final totals. No cheaper candidate was returned, and the search did not exhaust. No larger version of this frontier follows here.

Logs: `astra-t3int-{tests,all-tests,clippy}.log`, `astra-t3-low-exchange-w8.log`, `astra-t3-low-exchange-w8-resources.log`, `astra-t3-low-exchange-w8-result.json`. Production generator and Huff are unchanged. The next scheduling approach fixes the incumbent's arithmetic DAG, whose funded post-S-box floor is 47 gas, rather than starting this broad linear-form search at h = 18.

### 9. Fixed low-phase DAG: scoped exhaustion below 56

`t3dag` fixes the incumbent's six arithmetic nodes: q = x + b; sum = ADDMOD(q,c); a' = sum + x; b' = sum + b; d = c + c; c' = sum + d. The initial stack is `[x,c,b]` with bounds (1,2,3). Outputs (a',b',c') have bounds (2,4,5), with goal stack `[a',P,c',b']` and at most one trailing garbage value. Each node runs once. The root funds 23 arithmetic gas, two PRIME supplies and six value copies, for 47 gas, not an attainable schedule claim.

Earlier prototypes with one spare copy per live value exhausted below 56 at windows 8 and 9 (70,941 and 135,717 states). The final tool removes that copy-count restriction: every live value can be copied and PRIME pushed whenever the window permits. A focused regression exercises copies the earlier filter rejected. The heuristic is checked for consistency on short reachable prefixes, the incumbent and all its suffixes still replay at 56 with EXCHANGE off/on, and the DAG's forms and inclusive bounds are checked.

One follow-up with the broader move set was justified by stock accounting: across valid computation masks at most nine useful entries are needed; an extra supplied entry costs three gas above the funded bound, and a sub-56 path has at most eight gas of headroom. This motivates window 11 rather than an arbitrary larger frontier. It does not remove the fixed-DAG, once-only computation and one-garbage restrictions.

```sh
EXCHANGE=1 generator-rs/stacksearch/target/release/t3dag 11 56
```

This completed normally in 1.2941 seconds, exhausting 213,997 states below 56, with sampled peak RSS 43,808 KiB. Neither the 8 GiB guard nor the 20-minute deadline fired. There is no cheaper candidate in this tested graph/window, not a proof over all EVM schedules or other internal-round DAGs. No generator or Huff change, and no new call-gas saving, follows from this result.

Six focused tests pass. Evidence: `astra-t3dag-tests.log`, `astra-t3dag-widened-tests.log`, `astra-t3dag-low-exchange-w{8,9}*`, `astra-t3dag-low-unrestricted-w11.log` and its result JSON. Further low-phase window increases are not pursued; delayed PRIME placement in legacy sum trees is next.

### 10. Delayed PRIME placement: uniform rejection, adaptive candidate

A late ADDMOD evaluates both children, supplies PRIME and uses SWAP2. Its funded node cost is 14 instead of 11 gas; peak is max(left peak, 1 + right peak, 3). Placement is explicit in the node, and uniform placement policy is part of the global cache key. A unit case with leaves at depths 16 and 15 confirms that preplacement loses DUP16 reach while late supply emits correctly at 20 gas with its caller stack preserved. A mechanism win is not a complete-call win.

Uniform late placement on the selected Osaka schedules compiles and verifies but regresses t16/t24/t28 to 48,877 / 76,704 / 93,148 gas. The t28 case passed through the split-selection machinery but ended with one runtime contract and identical cold/warm costs. A broader uniform-late option-family search improves those candidates to 48,250 / 76,446 / 93,088, still above 48,124 / 75,942 / 92,158. All reported candidates passed compiled reference checks with zero model differences; no uniform-late runtime improvement is claimed.

The adaptive candidate keeps the selected arithmetic tree and chooses preplaced or late PRIME per node. It scores primitive gas plus a three-gas extra-load estimate for each leaf moved beyond reach, then prefers fewer such reads and lower peak. Store costs, memory expansion and code-size effects are left to the full schedule comparison. The placement memo is local to one call: node identity and working offset are keys, with the entire original depth vector and reach fixed for that memo. It does not cache layout-dependent decisions globally. Mixed-node gas and peak are recomputed from the emitted placement.

A forced adaptive-family trial verifies t16/t24/t28 at 47,809 / 75,843 / 92,158. Normal strict winner selection retains every old serial/tree/peak/compact candidate on failure or non-improvement. All nine widths on Amsterdam, Osaka and Paris then pass compiled reference verification, 864 calls with every gas-model difference zero. Before is f1bef66 (runtime identical to c7d63fc):

| Fork | t | Before | Adaptive selected | Saving | Runtime bytes before | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Osaka | 16 | 48,124 | 47,809 | 315 | 22,951 | 24,242 |
| Osaka | 20 | 62,956 | 61,768 | 1,188 | 23,832 | 23,884 |
| Osaka | 24 | 75,942 | 75,843 | 99 | 23,985 | 23,738 |
| Paris | 16 | 48,298 | 47,983 | 315 | 23,062 | 24,353 |
| Paris | 20 | 63,130 | 61,942 | 1,188 | 23,907 | 23,947 |
| Paris | 24 | 76,116 | 76,017 | 99 | 24,036 | 23,789 |

Amsterdam, all other legacy widths and every t4 arity remain unchanged. The t16 runtime grows by 1,291 bytes while lowering call gas; deployment cost is not the objective. Every width still fits one contract.

The full 51-test generator suite passes (36 library, one CLI, three EIP, four generator, seven execution). Placement tests include exhaustive comparisons on small fixed trees, depth/reach isolation, cache-policy separation, value replay and emitter checks. Foundry passes 127 tests with the configured 10,000-run t4 fuzz tests. Clippy, formatting, five gas-floor tests, 39 stacksearch tests and whitespace checks pass. Default all-width regeneration leaves checked-in Huff and generated tests unchanged. New legacy formal exports/proofs remain a coordinator-owned integration gate, not a result claimed by this lane.

Logs: `astra-late-prime-{unit,selected-osaka,forced-osaka,family-osaka}.log`, `astra-adaptive-prime-{unit,osaka,final-unit,final-amsterdam,final-osaka,final-paris,all-tests,clippy,generation,forge,search-tests}.log`. `astra-late-prime-uniform.patch` and `astra-adaptive-prime-forced.patch` preserve the intermediate experiments. A separate remaining lead is the conservative wrapper-size budget in mod.rs/split.rs: actual compact entries can be smaller, but no budget-refinement saving has been measured here.

### 11. Actual entry-size budget retry

The whole-permutation search initially reserves the generic entry size without shadow slots or known memory. A selected compact/memory-output wrapper can be smaller, leaving bytes that the body search could not spend. `build_entry` first keeps the existing valid result, then makes at most one retry with its actual wrapper size when shared-body rounds or stored diagonals make sizing relevant. The retry must fit with its own wrapper and have strictly lower complete-frame gas. Error, no result, tie, regression or oversize retains the original. Runtime-size addition and the initial subtraction are checked.

Generation and CLI `schedule` share this whole-entry selector. Core-only `build_best` / `build_best_with` budgets, folded hash rounds and split-part budgeting remain separate. The whole-entry versus split comparison still charges each part's own entry, hand-over and memory costs. This is a bounded retry, not a claim of globally optimal byte allocation.

Before is 92f0819, after is the shared-helper implementation, independently remeasured after refactoring:

| Fork | Entry | Before | After | Saving | Runtime bytes before | After |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Osaka | t28 | 92,158 | 91,920 | 238 | 23,956 | 24,407 |
| Paris | t28 | 92,527 | 92,100 | 427 | 23,885 | 24,440 |

Every other width and hash arity is unchanged, including every Amsterdam output. All nine widths on all three forks pass reference execution and exact gas-model checks, 864 calls. Five selection tests cover tiny/overflowing budgets, initial failure/absence, failed/missing/tied/slower retries, changed wrappers, body-only improvements that lose in full-frame gas, exact-limit acceptance and bounded retry count. The new Osaka t28 CLI schedule pin agrees with the independently compiled execution pin; existing Paris/Osaka/Amsterdam small-width model checks and core-budget tests remain intact.

All 57 generator tests pass (41 library, two CLI, three EIP, four generator, seven execution), as do 127 Foundry tests, Clippy, formatting, five accounting tests and 39 search tests. Default all-width regeneration is unchanged. No formal-verification file is edited; affected legacy exports/proofs remain coordinator-owned.

Logs: `astra-entry-budget-probe-osaka.log`, `astra-entry-budget-unit.log`, `astra-entry-budget-final-{amsterdam,osaka,paris}.log`, `astra-entry-budget-{all-tests,clippy,generation,forge,search-tests}.log`. The initial probe and final helper used separate verifications. The extra search increases generation work; only EVM call gas is claimed as an improvement.

### 12. Retained-garbage shear schedules: compiled 82-gas regression

The t3 shear uses the previously checked inactive coordinates u = b + c, v = c and six-node DAG from OSAKA-OPTIMISATION.md. `fixed_dag.rs` extracts the existing t3 low-phase search engine without changing its move set. `sheardag` validates a reduction mask and inclusive input/output bounds before searching the same once-only-node grammar. The boundary is now `[a,P,v,u]` with one retained garbage value per round, not the rejected clean-boundary transport policy.

Seven serial search records use window 12 and an upper bound ten gas above the funded root bound. Each returned a replayable candidate; none was an exhaustion run. The inherited records do not encode the EXCHANGE flag, so these counts are not used to exclude either move family. Their model costs are not unrestricted schedule minima:

| Mask | Input bounds u,v | Post-S-box funded bound | Scheduled gas | Expanded | Retained states |
| --- | --- | ---: | ---: | ---: | ---: |
| 10 | 1,4 | 55 | 64 | 545,741 | 5,944,262 |
| 33 | 4,1 | 55 | 64 | 326,567 | 3,690,199 |
| 24 | 1,3 | 55 | 64 | 801,017 | 9,487,990 |
| 1 | 2,1 | 47 | 56 | 91,890 | 938,146 |
| 41 | 5,3 | 63 | 72 | 926,391 | 10,680,190 |
| 32 | 1,1 | 47 | 56 | 283,826 | 3,402,136 |
| 40 | 1,1 | 55 | 64 | 836,391 | 10,118,377 |

The largest sampled RSS among the seven runs was 2,923,120 KiB; no recorded resource stop fired. No host wall-time comparison is used. `results/astra-shear.program` preserves all seven programs, and tests replay their moves and every suffix bound with EXCHANGE disabled and enabled.

The 56-round policy repeats masks 10,33,24,1,41,32 through round index 52, then ends with 40,40,32. It uses 103 ADDMODs in the linear layer. The old funded linear inventory is 2,840 gas; the post-S-box root bounds total 3,008 because they also fund the outgoing PRIME slot. The actual constant-plus-S-box prefix costs 45 gas, consuming the incoming PRIME. Thus the unchanged funded round total is 3,008 + 56 * 45 = 5,528, not an extra 48 gas on top of the post-S-box bounds. Actual schedules total 3,512 linear gas and 2,520 prefix gas, or 6,032 for all rounds.

Entry consumes b and computes reduced u with `P dup4 dup6 addmod swap4 pop`, costing 22 gas. Exit computes b = (u + (4P - v)) mod P with `P dup4 4P sub dup6 addmod swap4 pop`, costing 28. Both preserve the original `[a,P,c,b]` boundary and underlying tail. Final v is at most 4(P-1), so SUB is nonnegative and 4P fits uint256. The complete candidate is 6,082 against the incumbent's 6,000 internal-chain gas.

`shear_probe.rs` independently replays all operations and inclusive intervals over the real BN254 field on 64 complete chains, including zero, maximum and half-bound inputs and maximal constants. It checks every ADD overflow, SUB order and bound, exact modular operand, stack reach/limit, per-round original-basis parity, retained tail and external re-entry bounds. Each round adds exactly one garbage slot, as does the incumbent. Negative tests reject unsafe entry ADD, wrong PRIME, reversed SUB and invalid reach.

A test-only replacement of the entire internal region then compiles and executes both baseline and candidate with the real constants, wrappers and surrounding external rounds:

| Fork | Baseline t3 call gas | Shear call gas | Regression |
| --- | ---: | ---: | ---: |
| Amsterdam | 7,653 | 7,735 | +82 |
| Osaka | 7,653 | 7,735 | +82 |
| Paris | 7,655 | 7,737 | +82 |

All 144 full-word/shared-vector calls match the independent permutation reference, and each measured difference equals the 82-gas chain model. No production schedule or generated Huff is changed. This rejects these seven schedules composed under this policy, not all shear DAGs or cross-round layouts.

Final gates: the full generator suite exits successfully with 60 tests (44 library, two CLI, three EIP, four generator and seven execution), including checked-in Huff equality. All 43 stacksearch tests and five accounting tests pass. Generator all-target Clippy, targeted t3dag/sheardag Clippy, both Rust format checks and whitespace checks pass. Foundry and formal verification are not rerun for this test/search-only unit; no Solidity, production generator, generated output, dependency or lockfile changes are included.

Evidence: `astra-shear-search-results.json`, `astra-shear-mask*.log`, `astra-shear-full-chain-tests.log`, `astra-shear-all-generator-tests.log`, `astra-shear-final-search-tests.log`, `astra-shear-{generator,final-search}-clippy.log`, `astra-shear-floor-tests.log`, and the portable program/test sources above.

### 13. Five other original-basis low DAGs: scoped exhaustion

The checked-in t3 trace has 27 internal rounds at 101 gas, 15 at 109 and 14 at 117, totaling 6,000. A three-gas improvement to the low phase would therefore save 81 call gas without coordinate conversions. Its existing funded gap is nine gas per round; that is headroom in a relaxation, not an attainable saving.

`t3variants` changes the common pair to x+c or b+c before forming the reduced sum, and independently replaces `(c+c)+sum` with `(sum+c)+c`. All six combinations preserve the original forms and inclusive low-phase bounds (x,b,c) = (1,3,2), outputs (2,4,5), goal `[a',P,c',b']` and at most one trailing garbage slot. Every arithmetic node still runs once. The previously exhausted x+b, c+c graph is only replayed as a test control, not searched again.

Each of the five new graphs was searched serially below 56 gas with window 11, first with ordinary DUP/SWAP/POP and then with EXCHANGE enabled. All ten runs exited normally with exhaustion in their stated graph/window:

| Common pair | Final c path | States, EXCHANGE off | States, EXCHANGE on |
| --- | --- | ---: | ---: |
| x+c | c+c | 213,092 | 224,500 |
| b+c | c+c | 213,389 | 224,500 |
| x+b | sum+c | 154,581 | 163,090 |
| x+c | sum+c | 170,062 | 179,589 |
| b+c | sum+c | 170,359 | 179,589 |

Expanded and retained counts agree in each run. A sampled 4 GiB RSS guard and five-minute deadline were armed per process; neither fired. Maximum sampled RSS was 45,616 KiB across the ten runs. This excludes sub-56 programs only under the fixed-DAG, once-only-node, boundary, working-window and move restrictions above. No new candidate was returned, no whole-call improvement is claimed and no larger frontier follows for these graphs.

Three focused tests check every graph's forms/bounds/funded root, unchanged incumbent replay and prefix heuristic consistency with EXCHANGE off/on. The complete 46-test search suite, targeted Clippy, Rust formatting and whitespace checks pass. Production, generated Huff and formal files are unchanged; the 60-test generator gate from the preceding search-only unit is not represented as a new run here.

Reproduce one case with `EXCHANGE=1 generator-rs/stacksearch/target/release/t3variants xc sc 11 56`. Evidence: `astra-t3-next-trace.json`, `astra-t3-variants-exchange{0,1}.json`, corresponding per-case logs, `astra-t3-variants-{tests,clippy,all-tests}.log`. A different remaining boundary experiment would allow the inactive stack order to change across rounds and charge every transition, rather than increasing these exhausted windows.

### 14. Inactive stack-order freedom: no sub-56 low phase

`t3variants` now accepts separate inactive input/output orders, leaving the active lane and PRIME positions fixed. Input `bc` renames only the two leaf IDs; output `bc` swaps only the two inactive target slots. The default `cb-cb` graph, move set and incumbent replay are unchanged. Bounds remain (x,b,c) = (1,3,2), outputs (2,4,5).

Only the three new boundaries `cb-bc`, `bc-cb` and `bc-bc` were searched, across all six arithmetic DAGs, with EXCHANGE off and on. None of the unchanged `cb-cb` searches was repeated. All 36 serial runs exhausted below 56 gas in window 11, with no candidate. For a given DAG and move set the expanded/retained counts were equal across the three new boundaries:

| Common pair | Final c path | States per boundary, EXCHANGE off | States per boundary, EXCHANGE on |
| --- | --- | ---: | ---: |
| x+b | c+c | 203,267 | 213,997 |
| x+b | sum+c | 154,581 | 163,090 |
| x+c | c+c | 213,092 | 224,500 |
| x+c | sum+c | 170,062 | 179,589 |
| b+c | c+c | 213,389 | 224,500 |
| b+c | sum+c | 170,359 | 179,589 |

Every process had a sampled 4 GiB RSS guard and five-minute deadline; neither fired. Maximum sampled RSS was 45,600 KiB. This is a result about the listed fixed DAGs, once-only nodes, boundaries, one-garbage allowance, working window and move families. It is not joint-round synthesis or unrestricted EVM optimality. No new program exists here to compile or charge as a full-chain candidate, and no runtime saving is claimed.

Tests cover all 24 DAG/layout combinations, original-basis forms and bounds, unchanged default graphs, wrong target orders, malformed layout strings and prefix heuristic consistency. Adapter controls replay the incumbent in each orientation and charge both ends: nine gas per changed end with SWAP triples, three with EXCHANGE. A free input/output relabeling is not counted as a caller-frame improvement. All 48 search tests, targeted Clippy, Rust formatting and whitespace checks pass. No production, generated Huff or formal files change.

Reproduce a new boundary with `LAYOUT=bc-cb EXCHANGE=1 generator-rs/stacksearch/target/release/t3variants xb cc 11 56`. Evidence: `astra-t3-layouts-exchange{0,1}.json`, the per-case logs, `astra-t3-layout-{tests,all-tests,clippy}.log`. Further window increases for these low-phase DAGs are deprioritized; the next inspection returns to the larger wide-state legacy placement and code-budget headroom.

### 15. Joint body-period/inline grids: selected wide Osaka schedules unchanged

`build_best_with` greedily spends bytes on diagonal literals and then inline rounds, checking shorter body periods until the next non-improvement. A finite test-only probe instead enumerates all `group_candidates` plus the ungrouped body, crossed with every legal inline count, around each selected whole-entry option set. Each build is reference-checked, rejects excessive depth and prices its own actual entry/tail bytes and full-frame gas. The original candidate is retained on ties or regressions; production selection is not changed.

All four selected Osaka schedules already use PUSH32 diagonals, so these runs do not explore stored-diagonal policies. They also hold consume slots, PRIME storage, sum-tree/placement policy and external scheduling fixed. This is not an exhaustive search across the generator's full option family.

| Width | Attempts | Successful builds | Fit runtime/depth limits | Baseline and best call gas | Runtime bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| 16 | 448 | 381 | 67 | 47,809 | 24,242 |
| 20 | 448 | 389 | 24 | 61,768 | 23,884 |
| 24 | 448 | 389 | 14 | 75,843 | 23,738 |
| 28 | 406 | 365 | 4 | 91,920 | 24,407 |

The 1,750 grid attempts finish without a lower-cost candidate. The selected baselines are independently compiled and executed on 24 full-word/shared-vector calls each, 96 calls total, with exact gas and runtime-byte agreement. The probe would compile each strict improvement before reporting it; none occurred. Each serial process had a sampled 4 GiB RSS guard and 20-minute deadline, neither reached. Maximum sampled RSS was 130,576 KiB. No host timing comparison or new runtime saving is claimed.

The explicit ignored test `joint_entry_budget_grid` in `entry_grid_probe.rs` passed once per listed width. The ordinary library suite passes 44 tests with this expensive probe ignored, and all-target Clippy, Rust formatting and whitespace checks pass. This unit adds only the test probe and its `cfg(test)` hook; no production, generated Huff, formal, dependency or lockfile edits. It does not rerun the previous full generator/Forge gates.

Reproduce from the repository root with `GRID_WIDTH=28 GRID_FORK=osaka cargo test --release --locked --offline --manifest-path generator-rs/Cargo.toml --lib joint_entry_budget_grid -- --ignored --nocapture`. Evidence: `astra-entry-grid-osaka-t{16,20,24,28}.log`, their resource JSONs, `astra-entry-grid-library-tests.log` and `astra-entry-grid-clippy.log`.

The next structural target is the fused sum of memory-held internal outputs. `internal_round_consume` still accumulates those outputs serially and uses late PRIME plus SWAP2 on overflow, even when the incoming sum uses a planned tree. A streaming tree may save reductions and placement there, but its pending values, reach, fused bounds, body size and complete-call selection must all be measured before claiming a benefit.

### 16. Streaming fused-memory trees: verified test-only candidates

The memory-held outputs of a consuming internal round are computed and stored in lane order. Each is `d_i * s_i mod P + sum`, with inclusive bound `2(P-1)`. The serial fused accumulator uses ADD until that would overflow, then supplies PRIME late and uses SWAP2 plus ADDMOD. A streaming tree instead leaves pending subtrees on the stack while each leaf computes and stores its output. It introduces no scalar state, changes no diagonal or round constant, and preserves every output store.

This prototype remains under `cfg(test)`. `FUSE_MIN` stays 6, production selection and defaults remain serial, and no generated Huff or formal file changes. The existing ordered sum-tree planner supplies the arithmetic choices; the emitter independently checks all ADD bounds, operands, PRIME supply, memory loads/stores and shared-body opcode replay. The final emitted inclusive bound must equal the plan's bound. No value bound is weakened or overwritten.

For nine memory lanes, the unrestricted tree changes the following incoming-sum schedule between shared-body calls and is rejected by replay. Forcing an extra inline round builds an oversized entry. The bounded alternative caps the tree at the serial accumulator's inclusive output bound, P-1 for nine lanes, without changing any primitive bound. This emits a stable body. Fourteen lanes admit the unrestricted tree without this extra reduction.

| Fork | Width | Serial call gas | Preplaced candidate | Saving | Runtime bytes before | Candidate bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Osaka | 24 | 75,843 | 75,348 | 495 | 23,738 | 23,720 |
| Paris | 24 | 76,017 | 75,522 | 495 | 23,789 | 23,771 |
| Osaka | 28 | 91,920 | 90,780 | 1,140 | 24,407 | 24,392 |
| Paris | 28 | 92,100 | 90,960 | 1,140 | 24,440 | 24,425 |

The t24 rows use `PreplacedBounded`; t28 uses `Preplaced`. Late-PRIME bounded t24 ties the serial baseline, while late-PRIME t28 saves 627 gas on each fork. The accumulation-only model excludes leaf generation/storage: nine lanes cost 57 gas serial, 40 unrestricted preplaced and 48 bounded preplaced; fourteen cost 83 serial and 63 preplaced. Actual full calls above include leaf computation, pending-stack effects, wrappers, memory expansion, boundaries and all shared-body calls. Fixed-body tests confirm unchanged load/store counts and maximum depth for the winning candidates.

The fresh serial reruns compile and check 288 full-word/shared-vector calls across four baselines and eight candidates. A required, non-ignored fixed-body test separately checks 480 compiled calls across Paris, Shanghai, Cancun, Prague and Osaka at both widths; it asserts the exact before/after gas, runtime-size limits and text/model agreement rather than silently skipping failed builds. Shanghai through Osaka give the same listed gas. Focused emitter tests check 432 tree/layout cases on all six forks, each with four boundary-value vectors, including full-word inactive inputs, inclusive root/output bounds, slot reuse, reloads, caller-tail preservation, deep PRIME from memory and rejection of an unsafe output ADD even when all concrete inputs are zero.

The complete generator suite passes 64 tests with two expensive probes ignored, including checked-in Huff/vector equality and the seven execution integration tests. All-target Clippy with warnings denied, Rust formatting and whitespace checks pass. The guarded suite finished in 1,139 seconds with sampled peak aggregate RSS 1,732,928 KiB, below the 20-minute/4 GiB limits; this is resource evidence, not an EVM speed measurement. The separate four prototype reruns also completed normally. No fresh Forge or formal gate is claimed for this test-only unit.

Reproduce the required fixed-body gate with `cargo test --release --locked --offline --manifest-path generator-rs/Cargo.toml --lib streaming_fused_replays_fixed_legacy_bodies`. The ignored comparison accepts `GRID_WIDTH=24 GRID_FORK=osaka FUSED_CAP=serial`, or width 28 with `FUSED_CAP=word`, using `streaming_fused_candidates -- --ignored --nocapture`. Evidence in worker scratch: `astra-fused-review-{osaka,paris}-t{24,28}.log`, `astra-fused-focused.log`, `astra-fused-review-all-tests.log`, `astra-fused-review-clippy.log` and their resource JSONs. These are credible candidates, not production-selected or independently integrated savings. Next is full-frame production selection with serial failure/tie/regression fallback, below-threshold checks, all-width fork verification, regeneration and the existing Forge gate before a runtime commit.

### 17. Production fused-tree selection with the serial entry retained

The verified prototype from section 16 is now available to production whole-entry selection. The original serial families and their actual-wrapper retry finish first. Their completed winner is retained while a separate seeded search tries preplaced/late PRIME, each with unrestricted/serial-bounded roots. Eligibility requires consuming internal rounds, stacked PRIME and at least six memory lanes; no width or fork is hardcoded. Default options and all original families still use Serial.

Each alternative runs the existing body-period, inline-round and PRIME-storage evaluation under its own core-byte budget. Before comparison it must satisfy maximum depth and its own full entry size, including its actual wrapper. The alternative entry starts with the serial winner's actual wrapper reservation and may reclaim further bytes once if its own wrapper is smaller. Only strictly lower complete entry gas replaces the serial result. An error, missing build, excess size/depth, tie or regression retains the completed serial winner, including the saving from its original retry. This avoids losing that winner when a new candidate changes the wrapper used to derive a retry budget.

Core-only `build_best`/`build_best_with`, folded hash rounds and split-part search still use the original serial families and their existing caller-supplied budgets. Whole-entry retry logic is not applied to those paths. The arithmetic emitter, exact bound equality and shared-body replay are unchanged from the verified prototype; no round, constant, input reduction or public EVM interface changes.

| Fork | Width | Before call gas | Selected call gas | Saving | Selected runtime bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Osaka | 24 | 75,843 | 75,348 | 495 | 23,720 |
| Paris | 24 | 76,017 | 75,522 | 495 | 23,771 |
| Osaka | 28 | 91,920 | 90,780 | 1,140 | 24,392 |
| Paris | 28 | 92,100 | 90,960 | 1,140 | 24,425 |

These are production `verify` results, not forced-option measurements. All Amsterdam widths, all small permutation/hash entries and legacy t8/t12/t16/t20 retain their previous gas. All widths remain single-contract entries. Default Amsterdam regeneration is byte-identical to the checked-in Huff and test files. The unrestricted t24 fixed-layout replay failure and oversized inline1 variants in section 16 remain rejected measurements, not additional savings; the production bounded result does not bypass those checks.

New regression tests preserve the completed serial retry after failed/missing/tied/slower alternatives, reject a cheaper core with a dearer wrapper, oversized wrappers, excessive depth and byte-count overflow, and exercise an alternative's smaller-wrapper retry followed by an invalid result. Eligibility tests cover absent consuming/PRIME modes and below-threshold layouts. Forced tree modes leave both text and model unchanged for selected t16/t20 bodies on Paris and Osaka. Existing hash/split frame-cost, fixed legacy body, full-word and caller-tail checks remain enabled.

Final worker gates pass:

- All nine widths on Amsterdam, Osaka and Paris: 864 compiled reference calls, exact runtime bytes and zero gas-model differences, including every t4 hash arity.
- Complete Rust suite in bounded serial invocations: 68 passed, two exploratory probes ignored (52 library, two CLI, three EIP, four generator and seven execution tests). No correctness assertion or tolerance was relaxed. Three gas pins were updated only after the compiled measurements above.
- Forge offline with existing local dependency remappings: 127 passed, no failures/skips. All three t4 fuzz tests ran 10,000 cases; existing Yul cross-check overrides ran 1,000 each. No dependency installation or lockfile change.
- All-target Clippy with warnings denied, Rust/Solidity formatting, whitespace checks and default all-width regeneration pass. No generated or formal file changes in this unit.

Evidence in worker scratch: `astra-fused-production-verify-{amsterdam,osaka,paris}.log`, `astra-fused-production-rust-core.log`, seven `astra-fused-production-test-*.log` files, `astra-fused-production-doc-tests.log`, `astra-fused-production-forge.log`, `astra-fused-production-clippy.log`, `astra-fused-production-regeneration.log` and resource JSONs. Every completed run stayed below the 20-minute/4 GiB guard; full Osaka/Paris verification took 993/1,027 seconds, while each separate execution test stayed below 367 seconds. Host durations are not the optimisation metric. Independent coordinator review and formal export/proof synchronization follow the fixed runtime commit.

Next headroom is t24's initial non-streamed fused sum versus the steady streaming tree. Aligning their sound root-bound policy may admit the cheaper unrestricted body without an extra oversized inline round. Another finite body/inline search on the new fused family is also distinct from section 15's exhausted serial-family grid. Neither lead is a measured saving yet.

## Verification and evidence

Session scratch contains `astra-baseline-{amsterdam,osaka}.log`, `astra-baseline-floor.json`, `astra-baseline-schedule.json`, `astra-exchange-kept{8,9}.log`, `astra-exchange-kept9-resources.log`, `astra-search-tests.log` and the fetched EIP text. The durable tables above do not depend on those temporary files surviving.

`cargo test --release --locked --offline --manifest-path generator-rs/stacksearch/Cargo.toml` passes all 48 tests with the t3int, t3dag, sheardag and t3variants extensions. Formatting and targeted Clippy pass for the changed tools. Their search-only commits do not change the production generator or Huff.

The integration branch is `opt`, not the older local `main`. Coordinator commit a433745 corrects the diagnostic `schedule` wrapper-memory accounting; core floors and compiled baseline measurements above are unaffected. The old diagnostic small-width call totals were two to four gas too high. Subsequent experiments use `opt` as their base.

## Remaining search

- Actual-wrapper-aware budgets for split parts and broader body-period choices; the whole-entry retry does not exhaust either space.
- Other internal arithmetic DAGs or cross-round layouts, not wider searches of the exhausted fixed t3 low-phase DAG.
- Cross-kernel code-size changes large enough to buy additional inline rounds, rather than the rejected local byte/leaf-order family.
- More selective raw calldata entries than the retained all-shadowed compact candidate.
- Full-word input reduction placement and initial linear layer fusion, with exact interval bounds.
- Shared-body period and boundary cost interactions after any byte savings.

Do not repeat the finite renamed-body controls, adjacent ADD+MOD substitutions, or immediate-supply SHL transport from OSAKA-OPTIMISATION.md. Those rejections remain scoped to their tested schedules.
