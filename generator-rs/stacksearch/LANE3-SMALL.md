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

## Landing

The worktree sandbox refuses `git -C <main checkout> merge --ff-only` (and `cd` there), so the commits stay on branch `worktree-agent-ab58a21023b793cbc`, rebased onto `opt` and gated (cargo test, verify all widths, forge 127/127); the coordinator fast-forwards `opt`.

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

t3 external round `seam 3 s1:4,P,s0:4,s2:4 o0:4,P,o2:4,o1:4 8 189` (under the macro search's 189, with moves the macro graph lacks): not exhausted after 35 min at 17 GB, stopped. With the value-slot heuristic added (copies >= end values + ops still needed + stores - live values, PRIME copies >= S-boxes + ADDMODs + goal slots - copies on the stack) the t2 searches expand a third fewer states. Caution: the first two-round version of `seam` (committed in the stacksearch commit) put the second round's forms at a fixed token base that the t = 3 forms of a single round overlap, so its t = 3 runs (a 1,226 s run that hit the guard, and a "no solution below 189" at 63M expansions) are void. The forms now come from per-round tables with their own bases, and states are packed into a u128 key. Rerun: the t3 terminal round again 219 (30.8M expanded, 61M states, 235 s, 9.6 GB); the t3 external round at window 8 still passes the 12 GB guard (409 s).

Entry and round 0 of t2 jointly (`FIRST_LOADS=0,1 mid2.mjs P o1:4,P,o0:4 8`): 178 = 55 + 123, the production cost.

Entries with calldata loads (`LOADS=0,1` etc.: PRIME copy, PUSH, CALLDATALOAD, MOD, 14 a word): t2 `seam 2 P o1:4,P,o0:4 9` 55 (loads 28 + linear 27, the production cost), t3 `seam 3 P o2:4,P,o1:4,o0:4 8` 84 (production 84). No gain.

### 5. t2 external rounds in pairs: -12 gas

With the second round's input counted as an op still to make, `ROUNDS=2 seam 2 s1:3,P,s0:3 o1:4,P,o0:4 7 247` finishes (8.8M expanded, 26 s, 1.4 GB): two rounds cost 243 against 2 x 123, the second round's S-box of one lane runs before the first round's other output is made (window 8: 243 too, 46M expanded, 178 s, 10.7 GB). Same 243 for the exit pair (`... o0:3,P,o1:3`, rounds 2 and 3) and the re-entry pair (`s0:4,P,s1:2 o0:4,P,o1:4`, rounds 60 and 61); the last two rounds of the private entry with stores `s0:3,P,s1:3 store` 263 against 123 + 143. `templates::pairs` holds the four programs (`sboxI'` the second round's S-box, `tI` its outputs, `|` where its comment and step start, `store`), `external_pair` / `terminal_pair2` run them. t2 5,895 -> 5,883 (Osaka the same, Paris 5,885); the permutation entry 5,901 -> 5,892.

Window 7 single round t3 (`seam 3 s1:4,P,s0:4,s2:4 o0:4,P,o2:4,o1:4 7 189`): no solution below 189 (15.1M expanded, 40 s). The t3 R60 seam (`INTERNAL=1`, from `[sum, P, x, s2, s1]`): over 12 GB at windows 7 and 8, stopped.

### 6. Chains of external rounds: t2 -15, t3 -12 from the terminal changes

The pair gain is at the junction: the linear layer of one round together with the S-boxes of the next. `JUNCTION=1` searches exactly that (from the S-box outputs of one round to the S-box outputs of the next, in the layouts the templates have there), so t3 becomes tractable.

| Junction | Production | Found | Run |
| --- | ---: | ---: | --- |
| t2 rounds 1 -> 2 (between pairs), `x1,P,x0 -> o0,P,P,o1` | 126 | 123 | 64K expanded |
| t2 rounds 61 -> 62, `x0,P,x1 -> o1,P,o0,P` | 126 | none below | 69K expanded |
| t3 rounds 0 -> 1, `x1,P,x2,x0 -> o0,P,o1,o2` | 189 | 186 (w8; none at w7) | 300 s, 10.5 GB |
| t3 rounds 1 -> 2, `x0,P,x1,x2 -> o2,P,o0,o1` | 189 | 186 (w8) | 224 s, 10.4 GB |
| t3 rounds 2 -> 3 (exit), `x2,P,x0,x1 -> o0,o2,G,o1` | 186 | none at w7; w8 over 16 GB | |
| t3 rounds 61 -> 62, `x2,P,x1,x0 -> o0,P,o1,o2` | 189 | 186 (w8) | 233 s, 10.5 GB |
| t3 rounds 62 -> 63 (terminal), `x0,P,x1,x2 -> o1,P,o2,o0,P` | 192 | 189 (w7 and w8) | 60 s / 127 s |

The t3 seam R59/R60 up to R60's S-box outputs (`INTERNAL=1 JUNCTION=1 seam 3 b0:1,P,b1:1,b2:2,b3:3 o0,o2,o1 w 179`, the production 179): none below at w7 (39 s) and w8 (18M expanded, 232 s, 4.8 GB); w9 passed 12 GB after 789 s.

`templates::chains` (replacing `pairs`) holds programs of several rounds: `sboxI@J` lane I of the program's round J, `oJ.I` its outputs, `|` round starts, `store`. `external_chain` runs one when all its rounds are in range (Exit: ending at the exit; Round: ending before it, or before the last round; Final: the private entries' last rounds, `terminal_pair2` storing, `terminal_pair3` then `terminal3`). t2: rounds 0-3 (4 rounds, three junctions), 60-61, 62-63. t3: rounds 0-2, 61-63.

Gas: t2 5,895 -> 5,880 (Osaka the same, Paris 5,882), permutation entry 5,901 -> 5,889; t3 7,638 -> 7,626 (Paris 7,628), permutation entry 7,650 -> 7,644.

### 7. EXCHANGE in `ecycle` (t4 external): no gain

`EXCHANGE=1 ecycle 7 3`: 3,632 end layouts, D_k - D_(k-1) = 54 at k = 3 (780 s), as without EXCHANGE. Window 8 not run (the non-EXCHANGE bound there is already ROUND4's 51).

