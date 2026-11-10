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
