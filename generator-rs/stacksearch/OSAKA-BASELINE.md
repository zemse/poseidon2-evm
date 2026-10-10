# Osaka gas baseline and scoped floors

Baseline `b7d7125`, measured 2026-10-10. BN254, exponent five, RF=8, RP=56. These are call-frame execution costs, excluding transaction intrinsic gas, deployment and the caller's CALL/STATICCALL overhead. Gas is deterministic, not a host CPU timing.

## Reproduce

From the repository root, with the existing dependencies and Node's native TypeScript support:

```
cargo run --release --locked --offline --manifest-path generator-rs/Cargo.toml -- verify --hardfork osaka 2 3 4
node generator-rs/stacksearch/gas-floor.mjs > /tmp/poseidon2-gas-floor.json
node --test generator-rs/stacksearch/gas-floor.test.mjs
```

The first command generates in memory, compiles with huff-neo and executes on revm's Osaka spec. Each raw permutation checks eight shared vectors and sixteen deterministic full-word random inputs against the reference. The t=4 verifier also checks all three hash entrypoints, giving 96 calls in total. Both baseline verification runs reproduced the gas model exactly. The generator checks pinned external known answers and tracks arithmetic bounds before emitting code.

`gas-floor.mjs` reads the selected generator's straight-line opcode output and emits counts, per-round costs and the relaxation below. It checks their sum against the generator's gas. This is generated-opcode accounting, not a revm instruction trace. It neither writes generated contracts nor changes generator options. New opcodes, PUSH0, shared bodies or deeper stack operations need a revised accounting model; unsupported forms fail rather than silently weakening the bound.

## Computation trace

1. Load and reduce t arbitrary 256-bit inputs.
2. Initial external linear layer.
3. Four external rounds, each with t constant additions, t S-boxes and an external linear layer.
4. 56 internal rounds, each with one constant addition, one S-box and an internal linear layer.
5. Four external rounds.
6. Store and return t reduced outputs.

| Segment                      |   t=2 |   t=3 |    t=4 |
| :--------------------------- | ----: | ----: | -----: |
| Initial linear layer         |    27 |    42 |    122 |
| Eight external rounds        | 1,000 | 1,539 |  2,571 |
| 56 internal rounds           | 4,987 | 6,112 |  9,296 |
| Wrapper and memory expansion |    52 |    75 |     98 |
| Full permutation call        | 6,066 | 7,768 | 12,087 |

The t=4 hash entrypoints cost 11,910 / 11,932 / 12,005 for one / two / three inputs. Their specialized first and final rounds make them different benchmarks from the raw permutation.

A separately compiled Amsterdam comparison gives 6,027 / 7,768 / 12,087. The current Osaka stack-reach restriction therefore adds 39 gas at t=2 and none at t=3/t=4. This comparison does not show that deeper access could never help a different schedule.

The core has no memory accesses, storage, calls or loops at these widths. Input/output memory spans 64 / 96 / 128 bytes. The relevant resources are arithmetic and stack supply/placement, not memory bandwidth or host launch latency.

## Fixed-mix relaxation

There is no established unrestricted EVM minimum here. This relaxation preserves the current arithmetic opcode counts and the macro boundary of t state values plus PRIME, while making placement free and removing surplus copies. The supply model uses three-gas PUSH/DUP, not arbitrary EVM instructions or PUSH0. The current wrapper is held fixed, not proved minimal.

ADD and MUL each consume one net stack slot. ADDMOD and MULMOD consume two. Initial and required final live stack sizes are equal, so three-gas supply must replace at least those slots:

```
B = N_ADD + N_MUL + 2*N_ADDMOD + 2*N_MULMOD
core floor = arithmetic gas + 3*B
```

This is a lower bound within the stated model, not a discovered schedule or a promised saving. Changing arithmetic, reduction policy, representation, allowed supply instructions or the macro boundary requires a fresh bound.

| Width | Arithmetic gas | Slots B | Core floor | Same-wrapper floor | Measured call | Gap |
| :---- | -------------: | ------: | ---------: | -----------------: | ------------: | --: |
| t=2   |          3,107 |     815 |      5,552 |              5,604 |         6,066 | 462 |
| t=3   |          3,883 |   1,057 |      7,054 |              7,129 |         7,768 | 639 |
| t=4   |          6,148 |   1,660 |     11,128 |             11,226 |        12,087 | 861 |

A second derivation from DAG fan-out gives the same totals. There are 72 / 80 / 88 S-boxes. Three MULMODs cost 24 arithmetic gas, but the current stack sequence also needs five DUPs (15), constant PUSH+ADD (6), and a supplied PRIME (3): 48 fully funded. The input PRIME credit and retained output PRIME cancel globally.

```
t2: 72*48 + (8*18 + 34) + (55*34 + 48) = 5552
t3: 80*48 + (8*30 + 54) + (55*52 + 60) = 7054
t4: 88*48 + (8*104 + 136) + 56*106 = 11128
```

The middle terms fund the initial/eight external linear layers; the final terms fund internal linear layers under the existing reduction policy. These are not proofs that those policies are optimal.

| Width | SWAP gas | Surplus supply above the slot bound | Total gap |
| :---- | -------: | ----------------------------------: | --------: |
| t=2   |       57 |                                 405 |       462 |
| t=3   |      444 |                                 195 |       639 |
| t=4   |      612 |                                 249 |       861 |

Removing a copy can require a SWAP. These columns are not independently recoverable savings. Dead values can be cheaper to leave below the result than to remove; POP does not refund their creation.

## Headroom by segment

Ranked by absolute gap, with the same relaxation throughout:

| Segment      | Measured | Relaxed floor | Gap |
| :----------- | -------: | ------------: | --: |
| t=4 internal |    9,296 |         8,624 | 672 |
| t=3 internal |    6,112 |         5,608 | 504 |
| t=2 internal |    4,987 |         4,606 | 381 |
| t=4 external |    2,571 |         2,400 | 171 |
| t=3 external |    1,539 |         1,416 | 123 |
| t=2 external |    1,000 |           928 |  72 |
| t=4 initial  |      122 |           104 |  18 |
| t=3 initial  |       42 |            30 |  12 |
| t=2 initial  |       27 |            18 |   9 |

- t=4 internal: 166 per round, versus 154 relaxed. The twelve-gas gap is three SWAPs and one surplus supplied slot. The existing internal search additionally charges a necessary placement move, giving 157 within its model and 504 total remaining headroom there. Its four-lane search did not finish proving optimality.
- t=3 internal: 109 steady, versus 100 relaxed; the first round is 117 versus 108 because external outputs are lazy. The previous search exhausted cheaper than the 64-gas post-S-box program only within its configured positive-linear-form, garbage and depth domain.
- t=2 internal: 88 steady, versus 82 relaxed; the first round is 105 versus 96. Fourteen rounds pay another three gas for PRIME refresh. Amsterdam still needs one such refresh, explaining the 39-gas fork difference.

The external searches already exhausted cheaper candidates in their configured graphs for t=2/t=3 and the regular t=4 round. The t=4 final-round search did not exhaust. [README.md](README.md) and [RESULTS.md](RESULTS.md) specify the restrictions; none is a proof over all equivalent EVM programs.

## Initial rejected options

These are generator-model costs with symbolic overflow and shared-vector checks, not separately compiled revm measurements of each candidate.

| Change                                          | Width | Call gas model | Regression |
| :---------------------------------------------- | ----: | -------------: | ---------: |
| Shared internal sum instead of MUL by three     |     2 |          6,136 |        +70 |
| Fresh PRIME each internal round                 |     2 |          6,192 |       +126 |
| Generic internal rounds instead of template     |     4 |         12,446 |       +359 |
| Generic internal rounds with garbage collection |     4 |         13,671 |     +1,584 |
| Diagonal constants in memory                    |     4 |         12,738 |       +651 |

The garbage-collection candidate reduces t=4 peak depth from 94 to 42, but adds 278 POPs and raises SWAPs from 204 to 318. Lower stack depth alone is not the objective. The t=2 generic-GC and t=3 generic-internal toggles failed with `no template fits the layout`, so neither has a valid gas comparison.

The next experiments are boundary-flexible round schedules, joint reduction/layout policies, alternative linear arithmetic, then transformed inactive-lane representations. Charge conversion and transition boundaries and verify the full 56-round path. No production speedup is claimed by this baseline report.

## Sources

- [Osaka gas schedule](https://github.com/ethereum/execution-specs/blob/master/src/ethereum/forks/osaka/vm/gas.py).
- [EIP-7883](https://eips.ethereum.org/EIPS/eip-7883): MODEXP's 500-gas minimum already exceeds the current three-MULMOD S-box before call/memory overhead. EVM EXP is modulo 2^256, not the BN254 prime.
- [Poseidon2 paper](https://eprint.iacr.org/2023/323).
- `generator/README.md` and `generator/round-constants/assert-known.ts`: parameter and external-oracle provenance.
- `generator/huff/schedule.ts`, `templates.ts`, `emitter.ts`, `generator/shared/value.ts`: selected schedules, bounds and gas accounting.
- `generator-rs/src/huff/verify.rs`: compiled execution and call-frame gas checks.
