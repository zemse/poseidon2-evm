# Lane 6: small widths t2, t3, t4 (junctions and seams)

Started 2026-11-10 20:25 IST on `opt` ea5cf00. Amsterdam unless stated; every search ran under a 25 GB RSS guard on the shared 96 GB machine.

## Baseline

| Entry | Amsterdam | Osaka |
| --- | ---: | ---: |
| t2 | 5,880 | 5,880 |
| t3 | 7,626 | 7,626 |
| t4 hash_1 / hash_2 / hash_3 | 11,841 / 11,882 / 11,922 | 11,865 / 11,883 / 11,946 |
| t4 permutation | 12,083 | |

## Tooling

`hashdag` takes the S-box (`sbox(a)`: its constant and body over a PRIME copy, 45), PUSH32 constants (`#name`, 3, like `4`), values only the starting stack holds (`INIT=...`, never made again: a state that lost one still needed is dropped) and an exact goal prefix (`LAYOUT=...`, `_` anything). States are a node arena of 24 bytes and an Fx-hashed map to it, half the memory of the earlier map of parents (the hash_1 prefix below: 59.4M states, 12.2 GB to 6.4 GB).

## Log

### 1. t4 hash round 0: forms fused with ROUND4 (hashdag, KEEP=1)

The forms DAG of each arity (templates::hash_forms) with ROUND4 up to its `sbox3` (`x0..x3`, `t0 = x0 + x1`, `2x1`), the goal the layout ROUND4's suffix takes, `x3,P,t0,2x1,_,p2` (the suffix reads nothing deeper; ROUND4 alone costs 165 to there, the suffix 152).

| Arity | Goal | Current | Found | Run |
| --- | --- | ---: | ---: | --- |
| hash_1 | 6 slots | 211 | 208 | 59.4M states, 127 s, 12.2 GB (first version); 19.6M states, 45 s, 2.0 GB (last) |
| hash_1 | 7 slots (3 dead under s3', as now) | 211 | none below 211 | 10.0M states, 95 s, 1.0 GB |
| hash_2 | 6 slots | 252 | stopped at f = 246 (322M states, 15.9 GB); WEIGHT=13 to f 286 (263M states) | |
| hash_3 | 6 slots | 292 | stopped at f = 277 (421M states, 17.7 GB) | |
| hash_1 | the whole round (`a0,P,a1,a2,a3`) | 363 | stopped at f = 342 (176M states, 14 GB) | |

hash_1 at 208: `P r0 mod=p2 P 4 dup3 mulmod=p1 P dup2 sbox1 P dup4 dup4 add=p0 sbox0 dup2 dup1 add=2s1 swap2 add=t0 P P dup6 sbox3`, then ROUND4's suffix. It computes x1 from a copy of p1 before p0 consumes p1, so round 0 leaves two dead values above SETUP's PRIME copy, not three: the rounds after (one macro for every arity, HASH_DEAD = 3) DUP that copy one slot too deep. Not landed: it needs a rounds macro per dead count (Amsterdam only, where each arity has its own copy) for -3 on hash_1, or a 2-gas junk value (MSIZE) under round 0 for -1 on every fork.

### 2. t4 hash row 0 (round 63): -3 every arity, landed

hashdag from `[s0, P, s1, s2, s3]` over `y_i = sbox(s_i)`, `5 y0` and `3 y3` by MUL, `7 y1` by MULMOD, `(3 y3 + y2) + 7 y1` and the ADDMOD with `5 y0`: 245 against final_round_row0's 248 (8.2M states, 19 s, 0.5 GB with the S-box move bound; the search without it passed 19 GB). s1 is taken in place (`P 7 P P swap6`) under the PRIME copies of its S-box, its MULMOD and the ADDMOD, instead of a copy and a SWAP of the ADDMOD's PRIME copy at the end. templates::row0_4; run_template takes numbers (a PUSH) and `mul=`.

hash 11,841 / 11,882 / 11,922 to 11,838 / 11,879 / 11,919 (Amsterdam), Osaka 11,865 / 11,883 / 11,946 to 11,862 / 11,880 / 11,943, Paris 11,866 / 11,884 / 11,947 to 11,863 / 11,881 / 11,944. Permutation entry unchanged (its last round is Final).

Round 62 after its `s2'` with row 0 as one DAG (`INIT=a2,P,t2,t0,a3,_,t3`, 274 with the new row 0): nothing below 271 (208M states, f 270 reached).

A first version of the hashdag S-box without a PRIME copy under it (48) was wrong: `P swap1` and the S-box, 51, is the cheapest, and that is already two moves and the S-box. Removed.

### 3. `ecycle` forced a copy of 4t0 and 4t1: its bounds were too high

`whole` dropped a state as soon as a value with a use left was gone; the `t23` productions keep a use of 4t0 (4t1) after s1' (s3') consumed it, so every program had to keep a dead copy of each: 6 gas a round. That is why "one round from the inputs" was 57 against ROUND4's 51. `whole` now asks whether every output of this round and the next can still be made from what is on the stack. Fixed, one round from `[s0,s1,s2,s3]` to itself is 51 (window 7). The earlier window 7 / 8 / 9 cycle brackets (54, [51, 54], [51, 54]) and RESULTS.md's "no schedule within window 8 beats 317" came from the old check and do not hold.

`FROM=... TO=...` runs k rounds from one layout and reports the cheapest end in TO (no lane symmetry then: the lanes of the layouts are fixed); `PATH_ROUNDS=1` keeps parents and prints the cheapest program's stacks.

### 4. t4 chains of external rounds (relaxed model, PRIME copies free)

With the fixed check, `FROM=s0,s1,s2,s3 TO=s0,s1,s2,s3 ecycle 7 3` (no lane symmetry): 1 round 51 (376 s), 2 rounds 96 (871 s), 3 rounds 141 (1,495 s, 9.0M states). Each junction of two rounds saves 6 of the moves the model counts, as at t2/t3. `PATH_ROUNDS=1` for 2 rounds (553 s) prints the program: the next round's S-box of lane 3 and lane 1 run on the copies of s3' and s1' the linear layer makes anyway (ROUND4 copies them twice: once for s2' / s0', once again in the next round for its S-boxes), s0' and s2' are taken by their S-boxes where they are made, and the next round's 4t0 and t3 are made before this round ends.

The model leaves the PRIME copies out (8 a round, 24 gas, placed free). In the real program an S-box needs one right under its input, an ADDMOD / MULMOD under its operands; an input consumed where it is made needs its copy pushed under the op's operands first, which the free placement hides. Runs that keep them:

- `PRIME=1 STRICT=1` (real opcodes only: no moves between depths, no SWAP with a copy below the live values) one round at window 10: stopped at the 30 min limit (7.9 GB, 12% of a core on the loaded machine).
- hashdag, the ROUND4 junction from ROUND4's stack after `t2` (`[t2, t0, s3', _, t3]`) to the next round's after its `sbox3` (`[x3, P, t0, 2x1, _, s2]`, what ROUND4's suffix takes): 206 in production (41 + 165).

  First run (S-box-only move bound): stopped at f = 203 (101.9M states, 9 GB). With the general move bound and larger-g ties: stopped at f = 203 (95.3M states). No program below 206 found; f 203 is the bound reached, so at most 3 gas could remain there, and fixing round B's suffix to ROUND4's likely forbids what the relaxed program does (it makes the next round's t3 and 4t0 before s2').
- hashdag, one round of work from after `t2` to the next round's after `t2` (`INIT=t2,t0,s3',_,t3`, goal `t2',t0',s3'',_,t3'`, 16 nodes, 317 in production): passed 22 GB at f = 305 (222M states, 2,291 s), no program found. The exact searches cannot reach the relaxed program's depth; the next step is a real program written from the relaxed one with its PRIME copies placed by hand, replayed (`REPLAY`) and checked by `verify`.

The R59/R60 seam with the new bound (`INIT=sum,P,x0,s1,s2,s3`, R60 to its `sbox3`, 254 in production): stopped at f = 239 (92.8M states). The t4 row 0 junction R62 tail + row 0 and the internal seam stay open.

### 5. t4 hash_1 round 0 fused, with a PUSH0 under it

hash_1's round 0 at 208 (item 1) leaves two dead values; a PUSH0 (2 gas, 3 on Paris) first keeps the three the rounds after expect: 363 to 362 on Amsterdam and Osaka, 363 on Paris. Landed: hash_1 11,838 to 11,837 (Amsterdam), 11,862 to 11,861 (Osaka), 11,863 (Paris). The forms interpreter takes `sboxI`, numbers and s<i>' outputs, so templates::hash_forms(1) holds the whole round.

### 6. t2 rounds 60 to 63 as one program: -3, landed

The Final pair (rounds 62, 63) starts with `[x1, P, x0, P]` after its S-boxes; the junction of rounds 61 and 62 to that layout is 126 (lane 3: nothing below). Without the PRIME copy under x0 (`JUNCTION=1 seam 2 x0,P,x1 o1,P,o0 8`: 120, 44K expanded; `o0,o1,P` also 120, `o0,P,o1` and `o1,o0,P` 123) the last two rounds push it themselves: `ROUNDS=2 seam 2 x1,P,x0 store 8` 164 (8.7M expanded) against 161 from `[x1, P, x0, P]` (4.7M). 120 + 164 = 284 against 287. templates::chains Final for t2 is now rounds 60 to 63 (the round pair's start, the new junction, the new last rounds); the old pair stays after it. t2 5,880 to 5,877 (Amsterdam, Osaka), Paris 5,882 to 5,879.

The same at t3 does not pay: the junction of rounds 62 and 63 to `[x1, P, x2, x0]` is 186 (44.7M expanded, w8) against 189 to `[x1, P, x2, x0, P]`, but the terminal round's linear layer and stores from there cost 72 against 66 (seam store, w8): 258 against 255.

### 7. t3 seams, other runs

- Junction of rounds 2 and 3 into the exit (`JUNCTION=1 seam 3 x2,P,x0,x1 o0,o2,G,o1 8 186`): no solution below 186 (54.0M expanded, 133.6M states, 1,824 s, 5.8 GB). Closed at window 8 (lane 3's run hit its 16 GB guard). Window 9: stopped after about 25 minutes.
- R59/R60 seam up to R60's S-box outputs at window 9 (`INTERNAL=1 JUNCTION=1 seam 3 b0:1,P,b1:1,b2:2,b3:3 o0,o2,o1 9 179`): no solution below 179 (69.1M expanded, 156.3M states, 2,397 s, 9.6 GB).

### 8. Other t4 runs

- hash_2 round 0 fused (6 slots, ub 252, new bound): stopped at f = 246 (463M states). hash_3: stopped at f = 277 earlier. Both open.
- Initial linear layer of the permutation entry (`INIT=s0,s1,s2,s3,P`, goal `s0',P,s1',s2',s3'`, 122 in production): stopped at f = 113 (166M states).
- ROUND4 tail of round 62 with the new row 0 (`INIT=t2,t0,s3',_,t3`, 286): stopped at f = 279 (402M states).
- hashdag `ORDER=` (the nodes in a fixed order) with `LIVEDUP=1`, ROUND4's own order: still at f = 316 after 90M states: fixing the op order alone does not tame the moves.
- A hand transcription of the relaxed 2-round t4 program with its PRIME copies placed (from after round A's t2 to round B's outputs) came to 25 moves against ROUND4's 22: the relaxed saving goes to placing the copies under in-place operands.

## Result

| Entry | Before | After |
| --- | ---: | ---: |
| t2 (Amsterdam / Osaka / Paris) | 5,880 / 5,880 / 5,882 | 5,877 / 5,877 / 5,879 |
| t3 | 7,626 | 7,626 |
| t4 hash Amsterdam | 11,841 / 11,882 / 11,922 | 11,837 / 11,879 / 11,919 |
| t4 hash Osaka | 11,865 / 11,883 / 11,946 | 11,861 / 11,880 / 11,943 |
| t4 hash Paris | 11,866 / 11,884 / 11,947 | 11,863 / 11,881 / 11,944 |
| t4 permutation | 12,083 | 12,083 |

## Still open

- t4 junctions: the relaxed model (PRIME copies free) saves 6 a junction (51 / 96 / 141 for 1 / 2 / 3 rounds); with the copies placed, no exact search finished (`PRIME=1 STRICT=1` ecycle, hashdag over the junction and the after-t2 cycle). A stronger hashdag bound for PRIME placement, or a search over the relaxed program's order with the copies as the only freedom, is the next step.
- hash_1's fused round 0 leaves two dead values: a rounds macro per dead count (Amsterdam, where each arity has its own copy) would take the PUSH0 back (-2 more at hash_1).
- hash_2 / hash_3 round 0 fused: not finished.
- The P-less junction trick (item 6) for the t2 Exit chain's junctions and for t3's round 61/62 junction: not tried.
