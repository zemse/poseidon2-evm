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

## Verification and evidence

Session scratch contains `astra-baseline-{amsterdam,osaka}.log`, `astra-baseline-floor.json`, `astra-baseline-schedule.json`, `astra-exchange-kept{8,9}.log`, `astra-exchange-kept9-resources.log`, `astra-search-tests.log` and the fetched EIP text. The durable tables above do not depend on those temporary files surviving.

`cargo test --release --locked --offline --manifest-path generator-rs/stacksearch/Cargo.toml` passes all 28 tests after the search extension. `cargo fmt` and `git diff --check` pass. No production generator or checked-in Huff changes accompany it.

The integration branch is `opt`, not the older local `main`. Coordinator commit a433745 corrects the diagnostic `schedule` wrapper-memory accounting; core floors and compiled baseline measurements above are unaffected. The old diagnostic small-width call totals were two to four gas too high. Subsequent experiments use `opt` as their base.

## Remaining search

- EXCHANGE in internal and streamed block scheduling, including PRIME preplacement.
- Width-selective raw calldata entries for legacy wide schedules. Earlier all-width forcing regressed t16/t20; compare candidates per width instead.
- Full-word input reduction placement and initial linear layer fusion, with exact interval bounds.
- Shared-body period and boundary cost interactions after any byte savings.

Do not repeat the finite renamed-body controls, adjacent ADD+MOD substitutions, or immediate-supply SHL transport from OSAKA-OPTIMISATION.md. Those rejections remain scoped to their tested schedules.
