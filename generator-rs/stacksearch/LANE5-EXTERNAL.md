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

So the exit block's 12 over h0 are not its output order: the M4 itself needs them.

## Tooling

- `sblock`: the states in an arena of 24 bytes behind an open-addressing table of indices, the queue an u64 an entry (exit window 8: 846 MB to 174 MB, same program, same states). `LIFT`, `ANY`, `shl` and `store` nodes (see the file's header).
- `m4dag`: the DAG enumerator and the op-count search.
