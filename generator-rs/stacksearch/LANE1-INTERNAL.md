# Lane 1: steady internal rounds at t >= 8

Started Mon 9 Nov 2026 19:40 IST. Scope: the steady consuming internal round (`internal_round_consume`, schedule.rs), Amsterdam.

## Baseline (opt f2d8830)

Model gas (`@dev` line): t8 23,365, t12 33,642, t16 43,891, t20 54,132, t24 64,658, t28 76,821.

Steady round t8 = 296: S-box 45, P block + sum 85, x step 14, 7 lanes x 20, end `swap2 add dup9 swap1` 12. Moves: 18 copies (S-box 3, sum 7, s0^5 1, lanes 7) and n + 3 = 10 SWAPs (n = t - 1 lanes).

The SWAPs: x up (the sum into its slot), one per lane (m0 is the carrier into the first lane's slot, every output into the next lane's slot), `swap2` to bring m0 back for s0' = m0 + sum, `swap1` to put a fresh PRIME copy under s0'.

## Lower bound reasoning

Every lane value has two uses (sum, product), so one copy each is forced (copies = uses - values). The other use is in place only if the value is in the top two slots then. Outputs are created on top and must outlive the round, so each output but the last one made (s0') covers the inputs still to be consumed: one SWAP per lane, or a second copy and a dead value. The t = 4 `cycle` bound (RESULTS.md) is exactly this: 7 copies + 4 = n + 1 further moves for n = 3. Nothing here contradicts n + 1 at larger t.

So the current n + 3 has two moves too many: `swap2` (m0 as carrier) and `swap1` (PRIME under s0').

## Idea 1: lane copy (t4 `internal4` shape), n + 1 moves

After the S-box `[x, L1..Ln]`: push P_u, the sum tree on top of it (`[sum, P_u, x, L..]`), then the n + 1 PRIME copies of the MULMODs on top. The deepest lane is taken by a DUP (its original stays dead), every output is swapped into the slot of the next lane, the last into x's slot, then `push d0 mulmod add` lands s0' = m0 + sum on P_u. Saves `swap2`, `swap1` and one lane SWAP for one DUP: 6 gas a round. Each round leaves one dead value below the lanes (stack +1 a round), lanes keep their slots (period 1).

Result (option `laneCopy`, schedule.rs `internal_round_lane_copy`): steady round t8 296 to 290. First measurement, inline rounds only (call gas, verify): t8 23,547 to 23,219, t12 33,912 to 33,590, t16 44,249 to 43,930, t20 54,578 to 54,262; t24 model 64,658 to 64,505 with its 26 inline rounds only (body unchanged).

The last consuming round (seam, old shape) wants a PRIME copy under the state: `dupn 65 swap9 pop` (8 gas). Fix: the round before it takes its deepest element by a SWAP over one more PRIME copy (carrier), which lands in that slot: +3, so 5 saved (t8 23,037 to 23,032 model).

Shared body: lanes keep their slots, so every body round is the same code if the PRIME copy under the sum comes from a fixed place: `[PRIME]` PUSH32 (3 gas, +32 bytes once) instead of DUPing the copy under the growing dead pile. The mid entry needs no SWAPs; its layout check compares only [s0, P, lanes].

`timeout` is not installed on this machine (no coreutils): `timeout N cmd` fails at once, so a build behind it silently does nothing.

Seam: the last consuming round (external_seam) in the same shape, each output's S-box of the next round run over a second stacked copy before its SWAP, s0' over P_u its own; it takes the carrier so the external round finds a PRIME copy under the state: 12 gas more at every width.

Verified totals (call gas, `verify`, all three in revm against the reference, forge passes):

| t | before | after | saved |
| --- | ---: | ---: | ---: |
| 8 | 23,547 | 23,202 | 345 |
| 12 | 33,912 | 33,573 | 339 |
| 16 | 44,249 | 43,910 | 339 |
| 20 | 54,578 | 54,239 | 339 |
| 24 | 65,220 | 64,881 | 339 |
| 28 | 77,475 | 77,124 | 351 |

## Is n + 1 the floor?

Copies are fixed by the DAG (2n + 4 a round: S-box 3, sum n, s0^5 1, lanes n). Each of the n outputs made before s0' is created on top and outlives the round, so it is SWAPped down or covers a value still needed, which then costs a move: at least n moves. The lane-copy round spends n SWAPs plus one DUP of the first element (it must come up from under the sum and the PRIME copies, which are made after the round starts). Getting rid of that last move needs the first element consumed in place, i.e. its product made before the sum and the copies are pushed, and its m then waits on top of everything until the sum exists: it covers the rest. The t = 4 `cycle` bound (exact over all multi-round schedules) is n + 1 for n = 3. So at most 3 gas a round is left, and only if the t = 4 result does not carry over; I found no construction.

Reductions: lanes < 2P, sum < P (s0^5 < P). One ADDMOD takes two operands below 2^256 (5.29P each): at most x + 4 lanes for the first, acc + 4 lanes after, so ceil(n / 4) ADDMODs, which is what the trees use. A looser sum (< 2P) makes lanes < 3P and only two fit an ADD. The factored state (lanes as d_i s_i, ASTRA-OPTIMISATION.md section 3) was measured at a loss.

## Open, outside this lane

- With laneCopy every body round is the same code but its round constant, so the shared body's period no longer has to be n (the rotation); any length works and the mid entry is free. Body length against call overhead and code size is the t24/t28 body lane's trade.
- Steady round now (t8): 290 against floor B 266; the 24 are the n + 1 = 8 moves above, at most one of them (3 gas a round) not shown inherent beyond t = 4.
