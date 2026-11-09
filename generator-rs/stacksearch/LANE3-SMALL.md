# Lane 3: small widths t2, t3, t4

Started 2026-11-09 19:40 IST on `opt` f2d8830. Gas only, Amsterdam (`verify 2 3 4`).

## Baseline

| Entry | Gas |
| --- | ---: |
| t2 | 5,898 |
| t3 | 7,644 |
| t4 hash_1 / hash_2 / hash_3 | 11,883 / 11,890 / 11,963 |
| t4 permutation | 12,083 |

Per round (gas-floor.mjs): t2 internal 86 (gap 6: two dead values, no SWAP), external 123, exit 139; t3 internal 101/109/117 (gap 9: two SWAPs, one dead), external 189, last internal 71, first external after 224, exit 216; t4 internal 166 (gap 12), external 317, exit 352.

## Ideas and outcomes

### 1. EXCHANGE in the `cycle` relaxation (t3 internal): no gain

`cycle` takes `EXCHANGE=1`: any transposition of two values below the top and any move of a value between two depths (an EXCHANGE with a PRIME copy or constant), 3 gas. `EXCHANGE=1 cycle 3 8 3`: 16,590 end layouts, 4,989,712 states a round, D_k - D_(k-1) = 27 for k = 2, 3 (1,786 s, 0.8 GB): the cycle mean stays 27, the rounds in the repository keep it. Window 6 also 27. t4 internal, `EXCHANGE=1 cycle 4 7 3`: 27,530 end layouts, mean 33 (2,084 s), as without EXCHANGE.

### 2. t2 internal rounds: two dead values or moves a round are forced

The round ends `[s0', P, s1']`, so s1' is made before s0' and P, and whatever sits under s1' when it is made stays there without a move. s0' needs information independent of s1', so some value is under s1'; with s0' made above from copies, two values end below s1' (w = s0' alone under s1' would need s1' from w alone). A SWAP or EXCHANGE replaces at most one of these DUPs. So 86 a round holds for a one-round layout with s0' on top. Not pursued.

### 3. t4 hash row 0 (s0' only): lane 0 in place, -3 gas each arity

`final_round_row0` ran lane 0 last on copies of s0 and of the PRIME copy under it, and pushed the ADDMOD's PRIME copy first. Lane 0 now runs first on [s0, P] in place (5 x0 by MUL) and the ADDMOD's PRIME copy is swapped under 5 x0 at the end: 251 -> 248. hash 11,883 / 11,890 / 11,963 -> 11,880 / 11,887 / 11,960 (Amsterdam, Osaka; Paris 11,881 / 11,888 / 11,961). Falls back to the old order when s0 + c0 needs ADDMOD.

### 4. `seam`: exact single-opcode search of the t2/t3 seams

New `src/bin/seam.rs`: linear forms over the S-box outputs (coefficients 0..2, bound in units of P-1), PRIME copies, DUP, SWAP, EXCHANGE, POP, ADD, ADDMOD, the S-box macro (45 on [s, P]) and `msize mstore` of the next output. Reproduces the 123 t2 external round (`seam 2 s0:3,P,s1:3 o0:4,P,o1:4 9`).

t2 terminal round (stores s0', s1'): production 146; `seam 2 s0:3,P,s1:3 store w` gives 143 for w = 7..10 with EXCHANGE on or off (from s1,P,s0 also 143). Program: sbox0, P, dup3, sbox1, dup1 dup3 add, P P swap4, dup3 addmod, store, addmod, store. t2 5,898 -> 5,895.

t3 terminal round: production 225 (gas-floor's 216 leaves out the three `msize mstore`); `seam 3 s0:4,P,s2:4,s1:4 store 8` gives 219 (49.4M expanded, 101M states, 2,081 s, 14.2 GB): sbox0 in place, P P swap3 sbox2, P P dup6 sbox1, P dup2 dup5 add dup6 add, dup1 swap6 addmod store, dup4 addmod store, addmod store. Nothing is left on the stack and no PUSH32 of PRIME. t3 7,644 -> 7,638.

t2 external rounds with a free layout between two of them (scratch `mid.mjs`: every layout of o0, o1 and up to three PRIME copies, one `seam` round to it and one from it to `[s1', P, s0']`, window 8): the least is 246 = 2 x 123 (also 126 + 120 and 129 + 117 through more PRIME copies). Nothing gained without interleaving; `ROUNDS=2` (both rounds in one search, interleaving allowed) passed 12 GB at window 8 and was stopped.

t3 external round `seam 3 s1:4,P,s0:4,s2:4 o0:4,P,o2:4,o1:4 8 189` (under the macro search's 189, with moves the macro graph lacks): not exhausted after 35 min at 17 GB, stopped. With the value-slot heuristic added (copies >= end values + ops still needed + stores - live values, PRIME copies >= S-boxes + ADDMODs + goal slots - copies on the stack) the t2 searches expand a third fewer states, but this one still hit the 12 GB guard after 1,226 s. Not pursued further: the macro search's 189 stands for t3 rounds.

Entry and round 0 of t2 jointly (`FIRST_LOADS=0,1 mid2.mjs P o1:4,P,o0:4 8`): 178 = 55 + 123, the production cost.

Entries with calldata loads (`LOADS=0,1` etc.: PRIME copy, PUSH, CALLDATALOAD, MOD, 14 a word): t2 `seam 2 P o1:4,P,o0:4 9` 55 (loads 28 + linear 27, the production cost), t3 `seam 3 P o2:4,P,o1:4,o0:4 8` 84 (production 84). No gain.

### 5. EXCHANGE in `ecycle` (t4 external): no gain

`EXCHANGE=1 ecycle 7 3`: 3,632 end layouts, D_k - D_(k-1) = 54 at k = 3 (780 s), as without EXCHANGE. Window 8 not run (the non-EXCHANGE bound there is already ROUND4's 51).

