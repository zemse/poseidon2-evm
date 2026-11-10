# Lane 7: internal rounds and their seams at t >= 8

Started Tue 10 Nov 2026. Scope: the consuming internal rounds (`internal_round_lane_copy`, schedule.rs), the first internal round and the seam into the external layer, Amsterdam.

## Baseline (opt ea5cf00, Amsterdam, verify)

| t | call gas | bytes |
| --- | ---: | ---: |
| 8 | 23,056 | 24,647 |
| 12 | 33,507 | 36,082 |
| 16 | 43,822 | 47,839 |
| 20 | 54,129 | 59,870 |
| 24 | 64,449 | 64,544 |
| 28 | 76,600 | 64,393 |

Steady round t28 910 gas: S-box 45, sum 224 (28 leaf DUPs, 20 ADD, 7 ADDMOD and their 7 PRIME copies, the copy under the sum), lanes 641 (28 copies, 28 diag pushes or DUPs, 28 MULMOD, 27 DUPs of the sum, 28 ADD, 27 SWAPs, one DUP of the deepest element).

## 1. Deferred sum (landed)

The sum tree's ADDMODs come from the lane bounds: s_i' = m_i + T is below 2P, so an ADDMOD (two operands of at most 5 (P - 1) each, 2^256 / (P - 1) = 5.29) takes four lanes, ceil(n / 4) a round (t28: 7, 56 gas over ADDs).

Keep the products and the sum apart: the state holds s0 and a_i = d_i s_(i, prev), with s_i = a_i + T for the T of the round before. A round:

- T' = s0^5 + sum a_i + (t - 1) T, the last term one MULMOD of a copy of T (`PUSH1 t-1`, PRIME copy, MULMOD: 14 gas and an ADD more in the tree). Every leaf is below P, so an ADDMOD takes nine or ten leaves.
- a_i' = d_i (a_i + T): the ADD before the MULMOD instead of after it, the same ops.
- s0' = d_0 s0^5 + T'.

T' may stay lazy up to 3 (P - 1): s0' + c is then at most 5 (P - 1). t28: 29 leaves, three ADDMODs and a final ADD instead of seven ADDMODs.

Layout (`internal_round_defer`): the PRIME copy for s0' and the t copies of the MULMODs go on first, the tree on top of them, and T' is swapped into the slot of the deepest element, which comes up for the first lane: the elements keep their slots, the T of the round before stays dead under them. Moves: n + 1 SWAPs as lane copy, and every use of T is a DUP (n + 1 of the old one, one of T' for s0'), one more than lane copy, where s0' consumes the sum. The first round has no T: its lanes are bare MULMODs (n ADDs and DUPs fewer) and its sum may be lazy, so the exit layer's looser bounds cost no extra ADDMOD (LANE4-SEAMS.md, 8 gas). The seam adds both: d_i (a_i + T) + T'.

Per round, with the floor B accounting (ADD 6, ADDMOD 14, MULMOD 14 with its two slots): the tree changes by -8 per ADDMOD saved, +14 for the MULMOD, +6 for its ADD, plus 3 for the DUP. t28 steady round 910 to 901; first round 918 to 759, seam 2,254 to 2,401.

| t | ADDMODs (before / deferred) | steady round |
| --- | --- | ---: |
| 16 | 4 / 2 | +7 (not taken) |
| 20 | 5 / 2 | -1 |
| 24 | 6 / 3 | -1 |
| 28 | 7 / 3 | -9 |

The search takes it where it wins (`deferSum` next to every `laneCopy` candidate). Amsterdam call gas:

| t | before | after | saved | bytes |
| --- | ---: | ---: | ---: | ---: |
| 20 | 54,129 | 54,062 | 67 | 61,548 |
| 24 | 64,449 | 64,393 | 56 | 64,546 (diagStack 5, was 4) |
| 28 | 76,600 | 76,078 | 522 | 64,391 (diagStack 13, was 12) |

ASTRA-OPTIMISATION.md section 3 measured this algebra at a loss on daf9c7a: serial sums then reduced every three lanes and q took a DUP, SWAP and POP; with tree sums the reduced products take nine leaves an ADDMOD.

## 2. No carrier at the seam (landed)

The lane-copy seam (the last consuming round, t8 to t16) took its deepest element with a SWAP over one more PRIME copy (`carrier`) so a copy lands under the state for the external round after it: 3 gas more than the DUP of lane copy. The streamed external rounds DUP the nearest copy at any depth, so the seam DUPs its deepest element like the steady rounds (the deferred seam already did). Round 60 at t8 674 to 671.

| t | before | after |
| --- | ---: | ---: |
| 8 | 23,056 | 23,053 |
| 12 | 33,507 | 33,504 |
| 16 | 43,822 | 43,819 |

## 3. First internal sum from the column sums (landed with 2)

The exit layer computes the column sums S_j = sum_b x_(b,j) and then block b's outputs M4 (x_b + S). The outputs therefore sum to sum_b colsum(M4) . (x_b + S) = (1 + t / 4) (11 (S0 + S2) + 17 (S1 + S3)) mod P (M4's column sums are 11, 17, 11, 17). The first consuming round needs s0^5 + sum_(i > 0) s_i: that total, less s0, plus s0^5. Two MULMODs by PUSH1 constants (t28: 88 and 136), their PRIME copies, four DUPs of S, K - s0 by `dup1 PUSH32 K sub` before the S-box (K the least multiple of P over the bound of s0, rotated under [s0, P] with two SWAPs) and one ADDMOD: about 84 gas against a tree of n + 1 leaves, 6n + 3 + 8k (t28 221). `SUB` is new in the emitter (`Op::Sub`, a constant minuend no less than the subtrahend's bound); Run.lean's whitelist already has 0x03.

S0 must outlive the exit layer: `firstSum` turns off the exit block that parks a PRIME copy in S0's slot (`exit_prime_block8`, 3 gas cheaper there). That parked copy was the one the external round after the seam DUPs (depth 88 at t28); without it the nearest copy sat at 235 and the round's programs fell back (+210). So with `firstSum` the seam takes its deepest element over one more PRIME copy (carrier, +3), which lands under the state.

First tried without the carrier: t28 76,146 (worse). With it, firstSum only (Amsterdam, before 2 landed): t12 33,495, t16 43,770, t20 53,989, t24 64,280, t28 75,933. t8 loses (8 leaves cost 61) and keeps the tree.

## 4. `defercycle`: the move floor of the deferred round (search)

`src/bin/defercycle.rs` is `cycle.rs`'s relaxed machine for the two DAGs as such (PRIME copies and constants left out, S-box and every MULMOD by a constant a unary move, a SWAP that moves a PRIME copy a move of one value to or from any depth, copy and SWAP 3, POP 2), rounds not overlapping, lanes interchangeable; value iteration over every end layout brackets the cycle mean. `TRACE=1` prints the cheapest rounds.

| Run | End layouts | States a round | Cycle mean | Wall / RSS |
| --- | ---: | ---: | --- | --- |
| `plain 2 7 4` | 45 | 628,845 | 24 (copies 15 + n + 1 = 3 moves) | 48 s / 116 MB |
| `defer 2 7 3` | 180 | 6,280,995 | in [27, 30], D_k / k 28.0 at k = 3 | 3,109 s / 506 MB |
| `TRACE=1 defer 2 7 5` | 180 | 6,280,995 | in [27, 30], D_5 = 141 (28.2) | about 1 h |
| `defer 2 8 4` | | | stopped after 30 min in the closure | |

The plain run reproduces lane copy's n + 1 moves. Our deferred round is 30 at n = 2 (copies 18, n + 2 = 4 moves). The search alternates rounds of 27 and 30 (mean 28.5): in the 27 round the last use of T is in place (u_2 = a_2 + T with T right under a_2), T' goes from the top to depth 3 with one move (the relaxation: in the EVM a SWAP over a PRIME copy, which must land where a later MULMOD consumes it), and the round ends with a lane output on top instead of s0'; the round after pays to bring s0 up. So at most 1.5 moves a round (4.5 gas) separate this schedule from the relaxed floor at n = 2, and only if those PRIME placements are free; not built.

### Rebased onto lane E (opt f30f959)

Lane E's stream terminal entry checks that the permutation before it is stack-only by a token whitelist (`t2_entry::stack_only`); firstSum's `sub` was not on it, so t12 to t28 fell back to the plain entry. With `sub` added, both stack. Amsterdam call gas after both: t8 23,039, t12 33,474, t16 43,742, t20 53,954, t24 64,238 (64,515 bytes), t28 75,884 (64,347 bytes).

## 5. `defercycle STRICT` (search)

`STRICT=1` leaves out the two relaxed moves (a value to or from any depth without a partner), so only DUP, SWAP and POP move values: `STRICT=1 plain 2 7 3` 24 (lane copy again); `STRICT=1 TRACE=1 defer 2 7 4` D_k - D_(k-1) in [29, 30], D_4 = 118 (29.5): rounds of 29 alternate with rounds of 30, the 29 one placing T' by a SWAP into a dead slot and a POP (5) where ours swaps it into the deepest element's slot. So without PRIME carriers the deferred round is within 0.5 gas a round of the cheapest cycle at n = 2, and the relaxed 28.5 needs carrier moves whose PRIME copy would land on top of s0^5 with nothing to consume it. Not pursued.
