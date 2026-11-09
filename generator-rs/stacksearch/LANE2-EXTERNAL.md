# Lane 2: external rounds and the initial linear layer at t >= 8

Started Mon Nov 9 19:40 IST 2026 on opt f2d8830.

## Baseline (Amsterdam call gas, verify:huff on f2d8830)

| t8 | t12 | t16 | t20 | t24 | t28 |
| --: | --: | --: | --: | --: | --: |
| 23,547 | 33,912 | 44,249 | 54,578 | 65,220 | 77,475 |

Runtime bytes: t24 65,415, t28 65,526 (10 bytes under the 65,536 limit, so any byte growth at t28 is a hard stop).

Steady external round (static tally): t8 756 = 4 column sums 68 + 2 blocks of 344 (4 lanes of 48 each, M4 and u adds 152).

## Cost model

ADD, SUB, SHL with its PUSH: 6 a binary op (3 op + 3 for the consumed slot). ADDMOD and MULMOD by a constant: 14 (8 + PRIME copy + operand). A reduction costs 8 over the plain op. Floor B of a block with the paper DAG: 16 ops (4 u adds, 8 adds, 2 doublings, 2 times four) at 6 plus 4 reductions (t2, t3 ADDMOD; q0, q1 MULMOD) at 8 = 128, plus the column sums.

## Ideas and outcomes

1. Lazy column sums at t8 (B = 2). With S1, S3 reduced, S0 and S2 may stay lazy at 2(P-1): u0, u2 only feed t0 = u0 + u1 and t1 = u2 + u3, which stay at 5(P-1); d1 = 2 u1 and d3 = 2 u3 keep their 4(P-1). Two ADDMODs become ADDs per layer, 8 gas each. At B >= 3 every column needs one reduction anyway (B(P-1) > 2.29 P), so no saving there.
   Result: t8 core 23,365 to 23,221 (16 a layer, 9 layers), call 23,547 to 23,403. Other widths unchanged.

2. Reduction count of a block. With u = x + S at 2(p-1), every row of M4 needs about 16 u-weights, and every intermediate must stay below 5.29p. q0, q1 (MULMOD by 4) and t2, t3 (ADDMOD) are 4 reductions, and no 3-reduction scheme fits: with 3 reduced values R1..R3, each output is a sum of R's plus at most one raw u, and the singular choices of (M4 - raw) need fractional R coefficients. SHL by 2 instead of MULMOD by 4 needs t0 below 1.32p, so it moves the reduction elsewhere at the same 8 gas. 16 ops is the least found (u1, u3, t0, t1 two each, d1, d3, t2, t3, q0, q1, 4 outputs). Folding the round constants through S (kappa = M4^-1 c of one block) costs the same 4 adds it saves.

3. Copies. Floor B is op-count only; the per round gap (t8 60, t28 201) is x copied twice (colsum and u, floor once: 3t), S copied B times (floor B-1), and 5 SWAPs a block. One in-place use of x needs it on top when used; the lanes bury it, and every rearrangement tried on paper (accumulating S at birth, M4 x_b first then T = sum v_b, LIFO block order) trades the copy for a SWAP or a copy of the accumulator.

4. In-place takes in every kept block. The t8-only `first_stream_block8` / `last_stream_block8` programs (take x4, take S0; t2 goes down into the taken slot and z3 is parked there by the SWAP that brings t2 back) are one program with the taken slot's depth as a parameter (`take_stream_block`). Every kept block but the last takes its x_{4b} (its last read), the last takes S0. 3 gas a block a layer. Amsterdam call gas, with item 1: t8 23,547 to 23,400, t12 33,912 to 33,849, t16 44,249 to 44,165, t20 54,578 to 54,473, t24 65,220 to 65,094, t28 77,475 to 77,334.

5. Final layer DAG with 6 reductions (14 ops: y1 = ADDMOD(q0 + 2u1, t1), y3 = ADDMOD(q1 + 2u3, t0), y0 = ADDMOD(y1 + 2u3, t0), y2 = ADDMOD(y3 + 2u1, t1)) against 8 (12 ops): floor 132 against 136. `sblock` with `DAG=` (final goal, REACH=235, floor S0..S3,P,_x4,x0..x3, UB 184): none below 184 within 8 (21.7M states); 183 within 9 (75 min, 11 GB RSS). 1 gas a final block, not taken yet; window 10 would pass the memory cap.

6. `sblock` tooling added: `DAG=<spec>` replaces the M4 DAG; `TAKE=n` (n <= 3) allows `takex<i>` / `take<i>` (TAKE_S=1), which SWAP x_i / S_i up from the floor, park the working top in its slot, and add the other operand of u_i; later SWAP / DUP moves reach the parked values; the goal accepts them dead or kept. `VERBOSE=1` with `trace` prints the stack after every move. The generator reads `takex<i>` / `take<i>` for any i. Replay of the take0 program gives 344 (the plain kept program 347), as in the generator.
   Exact TAKE=1 search of the last kept block (TAKE_S=1, window 8, UB 344) did not finish: 11.4 GB RSS after 37 min, stopped. The take moves multiply the states within the 12-gas gap between h0 (332) and 344.
   Taken: the 183 program is the first `ordered_blocks(Final)` program (1 gas a final block on Amsterdam: t8 -2 to t28 -7). Amsterdam call gas after items 1, 4, 5: t8 23,398, t12 33,846, t16 44,161, t20 54,468, t24 65,088, t28 77,327.
   TAKE=2, WEIGHT=15, middle kept block (floor S0..S3,P,4 dead,x0..x3, window 8, UB 344): no program after 87 min, 9.6 GB, stopped. With no program below the bound the weight does not help: everything under 344 must be expanded.
   `ORDER=<names>` fixes the op order (only stack moves and the way each u is made are searched). Middle kept block, incumbent order, TAKE=3, window 9: none below 344 (exhausted, 20 min, 7.3 GB). Exit block, TAKE=1 with S takes, window 8: none below 152 (exhausted, 83 min, 11.5 GB). So more takes in the incumbent order and a take in the exit block do not pay.
   Last kept block, incumbent order, TAKE=3 with S takes: window 9 passed 14 GB in 5 min, window 8 in 29 min (stopped, no program). `PARK_LIVE=1` parks only values with uses left (no dead value, which is a POP in disguise).
   Last kept block, incumbent order, TAKE=2 with S takes and PARK_LIVE=1, window 8: none below 344 (exhausted, 14 min, 7.2 GB).
   Middle kept block, TAKE=2 (x only), PARK_LIVE=1, window 8, five hand-picked op orders (the incumbent, u0 before t0, u1 and d1 first, the o3/o2 half first, u3/d3/t3 first): none below 344 in each (1 to 5 min, under 2 GB each).
   24 random op orders (random linear extensions of the block DAG with its lanes), same setting: none below 344 in any.
   Final block (six-reduction DAG) with takes: TAKE=1, window 8, UB 183, and the 183 program order with TAKE=2, window 9: both passed 13 GB within 5 min and were stopped, no program.
   exit0 block, TAKE=1 with S takes, PARK_LIVE=1, window 8, UB 155: passed 12 GB in 10 min, stopped, no program.

## Where the lane stands

- Arithmetic: 16 ops and 4 reductions a block is the least found; every row of M4 on u = x + S needs reductions for overflow, not for the output bound, and the column sums need one reduction a column from B = 3 on. B = 2 (t8) needed only two, now taken.
- Copies: every x is read twice (its column sum, then its u), the last read is in its block, so the column sums must copy. One x (or S0 in the last block) a block is now read in place; more takes do not pay in any order searched (29 orders, window 8, two live takes) or in the incumbent order with three takes (window 9).
- Exit and final blocks: a take in the exit block does not pay (window 8), the exit0 and final take searches pass the memory cap; the final block is 183 at window 9 (the 184 below window 8), 10 would pass the memory cap.
- Left open: an exact take search of a kept block without a fixed order (it passes 11 GB at window 8), takes in the final and exit0 blocks, and a block program that interleaves two blocks (the ROLL bound of RESULTS.md says at most 6 gas a block within window 10, before takes).

## Landing

be974ab (gas) and c63ca61 (tooling, notes) are rebased on opt fa54a9a and pass the gate (cargo test --release: lib 106, verify tests Amsterdam 3 and Osaka 5; generate:huff with no diff, verify:huff, forge test 127/127). The sandbox of this lane refuses `git -C <main> merge --ff-only` (and a `cd` into the main checkout), so opt is not moved from here: the coordinator fast-forwards opt to this branch.
