# Lane 5: external rounds at t >= 8 (DAGs, take searches, seams)

Started Tue Nov 10 20:30 IST 2026 on opt ea5cf00.

## Baseline (Amsterdam call gas)

| t8 | t12 | t16 | t20 | t24 | t28 |
| --: | --: | --: | --: | --: | --: |
| 23,056 | 33,507 | 43,822 | 54,129 | 64,449 | 76,600 |

Osaka t8..t28: 24,073 / 35,047 / 47,790 / 61,748 / 74,963 / 90,721. Steady external round t8 740 (sums 52 + 2 x 344), t16 1,492, t28 2,596. Kept block 344 (h0 332), exit 152 (h0 140), exit0 155 (h0 143), final 183 (h0 168 with the six-reduction DAG).

## Where the gas of a block goes

A kept block's floor is h0 = 332: 4 u (36), the M4 (104), 4 lanes (180) and their PRIME copies (12). The M4 part is 6 a binary op (op and copy), 14 an ADDMOD or MULMOD by 4 (op, PRIME copy, PUSH1): every value but the inputs is made on top once and consumed once, so a DAG of B binary ops needs B copies (2B + U + 4 uses, B + U + 4 values). 12 ops and 4 reductions: 6 x 12 + 8 x 4 = 104. The 12 over h0 are 4 SWAPs.

The same identity holds for every rearrangement tried on paper: folding S into per-layer combinations (A_S = S0 + S1, ..), the M4 on x with W = M4 S added per block, W = sum of the blocks' M4 x computed in place right after the lanes. Each moves ops between leaves and nodes and keeps the count of binary ops (14 a block with the u adds), so none is cheaper; the W forms also raise the bounds of the column sums (y at 2 to 3 units: 4 ADDMODs a layer at t8 instead of 2, more from k = 3).

## Runs

Machine shared with other lanes; every run under a guard (RSS cap, time cap). States and RSS from the compact A* (below) unless noted.

### M4 DAGs (`m4dag`)

- Op count (`OPS=n`: adds and scalings by 2..7, nonnegative forms below a row, bounds left out, mirror (u0, u1) <-> (u2, u3) folded): 8, 9, 10 ops none (82k, 1.05M, 9.0M sets); 11 ops none (126.8M sets, 584 s, 16.4 GB). So 12 ops at least, and with 4 reductions (LANE2-EXTERNAL.md, item 2) 104 is the least M4 cost in this model.
- Within 12 ops the DAG is the paper's: a = u0 + u1, b = u2 + u3, 4a and 4b, e = b + 2u1, f = a + 2u3, o1 = 4a + e, o3 = 4b + f, o0 = o1 + f, o2 = o3 + e; any other grouping of e, f or the outputs takes a 13th op, and the bounds (u at 2 units, 4a and 4b at 16, e and f at 8) force the reductions onto 4a, 4b, e and f. The only freedom is a doubling as `PUSH1 1 SHL` instead of `DUP1 ADD` (same 6 gas, one copy less, one PUSH more).
- Not covered: forms with negative coefficients or fractions (MULMOD by p - 1, by 1/2): a MULMOD is a reduction the block pays anyway, so an 11-op DAG with 4 such reductions would cost 98. Not searched.
- Full enumeration at budget 104 with bounds (`m4dag 2,2,2,2 4,4,4,4 104`): passed 11 GB in 20 min, stopped.

### Kept block (floor `S0..S3,P,_,_,_,_,x0..x3`, REACH=235)

| Run | Window | UB | Result | States | Time | RSS |
| :-- | -: | -: | :-- | -: | -: | -: |
| SHL doublings (d1, d3) | 8 | 347 | none | 4.4M | 55 s | 0.7 GB (old A*) |
| SHL doublings | 10 | 347 | none | 24.6M | 389 s | 3.4 GB (old A*) |
| EXCHANGE=1 | 8 | 347 | none | 7.2M | 316 s | 0.8 GB (old A*) |
| LIFT=1 | 9 | 347 | none | 21.2M | 306 s | 3.3 GB (old A*; 21.2M without LIFT) |
| LIFT=2 (check) | 9 | 348 | 347 | 18.8M | 282 s | 3.3 GB (old A*) |
| TAKE=1 (x), LIFT=2 | 8 | 344 | none (exhausted) | 48.7M | 646 s | 1.6 GB |
| ROLL=1 GARBAGE=1 | 8 | 347 | 342.5 (7 half SWAPs) | 7.6M | 292 s | 0.3 GB |

The TAKE=1 run is the first exhaustive one: lane 2's took 11.4 GB in 37 min and was stopped.

### Exit and final blocks

| Run | Window | UB | Result | States | Time | RSS |
| :-- | -: | -: | :-- | -: | -: | -: |
| exit, EXCHANGE=1 | 8 | 152 | none | 4.3M | 136 s | 0.8 GB (old A*) |
| exit, ANY=1 (any order) | 9 | 152 | none | 10.4M | 138 s | 1.5 GB (old A*) |
| exit, ANY=2 GARBAGE=1 (anywhere, o0 on top) | 8 | 152 | none | 47.4M | 566 s | 1.8 GB |
| exit0 | 10 | 155 | none | 31.7M | 478 s | 1.3 GB |
| exit, ANY=3 GARBAGE=1 (in order, dead values under them) | 8 | 152 | none | 47.4M | 2,365 s (loaded machine) | 2.2 GB |

So the exit block's 12 over h0 are not its output order or its dead values: the M4 itself needs them.

### Final layer storing its own outputs (landed)

The last layer left [s0', .., s(t-1)'] on top in order and the entry stored them (`msize mstore`, 5 gas a word): a final block cost 183 + 4 x 5 = 203 with the order fixed. A private entry (as t2 / t3 already have: `Terminal::Stream`, the entry inlines the body) can store each block's outputs in word order as it makes them, blocks from 0 up, and leave dead values on the stack. `sblock` models it with `store` nodes after the six-reduction DAG (`stored` mode, GARBAGE=1): h0 188.

| Run | Window | UB | Result | States | Time | RSS |
| :-- | -: | -: | :-- | -: | -: | -: |
| six-reduction DAG + stores | 7 | 203 | none | 18.1M | | |
| six-reduction DAG + stores | 8 | 203 | stopped at f 197 | 84.6M | 30 min | 3 GB |
| eight-reduction DAG + stores | 8 | 203 | stopped at f 201 (h0 192) | 41.3M | 23 min | 1.6 GB |
| six-reduction + stores, WEIGHT=20 | 8 | 203 | none found, stopped | 31M | 658 s | 1.1 GB |

The searches stay below the window the stores need: o2 depends on o3 and o0 on o1, while the stores want o0, o1 first and o2 before o3, so each pair runs as `P dup2` (a copy of o1 / o3 over a PRIME copy over it) and its two other operands DUPed on top, which takes 11 slots. By hand, 200 (traced by `sblock`): the column-sum side builds [d3, t0, P] with t1 and d1 under them, the o1 / o0 half runs on copies of all four and stores, the o3 / o2 half takes d3 and t0 in place. The 12 over h0 are four originals left dead (u1, u3, t1, d1), each read once more by a DUP: t1 and d1 are read last by o2 and b2, which sit over o3, so neither can be the one consumed in place.

196 (`estore`: `PUSH offset MSTORE`, 6 gas, after the block's MSIZE stores): s3' is stored by offset first (`dup1`, then the store of the copy) and s2' by offset after it, so b2 and o2 take d1 and t1 in place from [o3, d1, t1, P]: two stores 1 gas dearer, two DUPs fewer. h0 190; the 6 over it are u1 and u3, each read by both a deep value (d1, t1) and one over a PRIME copy above it (t0, d3), so neither original is on top at its last read. Window 12 (`trace`).

| Program | Final block with stores | t8 | t12 | t16 | t20 | t24 | t28 |
| :-- | -: | -: | -: | -: | -: | -: | -: |
| before (183 + 20) | 203 | 23,056 | 33,507 | 43,822 | 54,129 | 64,449 | 76,600 |
| MSIZE stores only | 200 | 23,050 | 33,498 | 43,810 | 54,114 | 64,431 | 76,579 |
| landed (`estore`) | 196 | 23,042 | 33,486 | 43,794 | 54,094 | 64,407 | 76,551 |

Runtime bytes after: t8 24,645, t12 36,080, t16 47,828, t20 59,856, t24 64,529, t28 64,378 (all under 65,536). Osaka and Paris have no stack-only stream (reach 16), so no `Terminal::Stream`: unchanged.

- Fixed op order of the 200 program, window 12, UB 200: stopped at 1,201 s (1.5 GB), f 191, nothing below 191 in that order.

Why 196 looks like the floor of this DAG with these stores: u1 feeds d1 (deep, read last by b2) and t0 (over a PRIME copy above it), u3 feeds t1 and d3 the same way; whichever of the two is made first lands on top of u, so the other can only reach u by a DUP, and both live until the second half. All-offset stores (192 + 6 = 198) or the eight-reduction DAG (h0 192, t2 / t3 / t0 / t1 read across halves, 201 or more by the same count) do not do better.

Gate (6ef34be): generate:huff twice, identical; verify Amsterdam, Osaka, Paris on all nine widths (+0; Osaka and Paris figures unchanged); cargo test --release --no-fail-fast (lib 108, cli 2, eip8024 3, generators 4, verify 8: all pass, verify 6,729 s on a loaded machine); forge test 127/127.

## Tooling

- `sblock`: the states in an arena of 24 bytes behind an open-addressing table of indices, the queue an u64 an entry (exit window 8: 846 MB to 174 MB, same program, same states). `LIFT`, `ANY`, `shl` and `store` nodes (see the file's header).
- `m4dag`: the DAG enumerator and the op-count search.
