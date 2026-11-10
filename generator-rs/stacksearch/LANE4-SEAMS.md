# Lane 4: one-off and structural overheads

Started Mon Nov 9 19:40 IST 2026 (8 h target: 03:40 IST).

## Baseline (opt f2d8830, Amsterdam, verify)

| Width | Bytes | Gas |
| :--- | ---: | ---: |
| t2 | 4,008 | 5,898 |
| t3 | 6,713 | 7,644 |
| t4 hash_1/2/3/perm | 13,607 | 11,883 / 11,890 / 11,963 / 12,083 |
| t8 | 24,912 | 23,547 |
| t12 | 36,497 | 33,912 |
| t16 | 49,028 | 44,249 |
| t20 | 60,920 | 54,578 |
| t24 | 65,415 | 65,220 |
| t28 | 65,526 | 77,475 |

Code size limit: execution-specs `forks/amsterdam/vm/interpreter.py` has `MAX_CODE_SIZE = 0x10000` (65,536), `MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE` (EIP-7954); revm 43 `eip7954.rs` agrees. fork.rs matches.

## Log

### 1. t24/t28: diag constants on the stack (landed)

The shared body existed only because the fully inline internal rounds did not fit: each round PUSH32es t - 1 diag constants (33 bytes each). A diag constant on the stack costs one PUSH32 (3 gas) at the macro start; every later use is a DUPN (3 gas, 2 bytes) instead of a PUSH32 (3 gas, 33 bytes), so 31 bytes a round for no gas. `diag_stack = n` keeps d0..d(n-1) on the stack; the option search tries it where the code size binds (or a shared body won) and takes the fewest n that fit, with all rounds inline. Picked: t24 diagStack=5 (15 gas), t28 diagStack=13 (39 gas), no shared body, no CODECOPY/MLOAD/return jumps.

| Width | Before | After | Bytes before | Bytes after |
| :--- | ---: | ---: | ---: | ---: |
| t24 | 65,220 | 64,923 (-297) | 65,415 | 63,906 |
| t28 | 77,475 | 77,108 (-367) | 65,526 | 63,779 |

All diag constants on the stack (n = t) gave 64,980 / 77,234: the fewest-n search saves 57 / 126 more. t8..t20 unchanged (they already fit inline). Limited to reach > 16 (DUPN); Osaka unchanged.

Left: 15 / 39 gas of pushes. One constant less needs about 1,770 (t24) / 1,830 (t28) more free bytes; spare is 1,630 / 1,757. Each is 3 gas, so not worth much.

### 3. t4 hash dispatch by computed jump (landed)

Before: `calldatasize 0x44 sub not_hash_2 jumpi` (hash_2 falls through), then `calldatasize 0x44 gt hash_1 jumpi`, and the two others `rounds jump`. Dispatch gas (to the prologue, plus the rounds JUMPDEST and jumps): hash_1 56, hash_2 22, hash_3 55.

Landed: `calldatasize 0x9 shl jump` (16 gas) to a JUMPDEST at 0x24 << 9 = 0x4800 (hash_1), 0x8800 (hash_2), 0xc800 (hash_3). Each region holds that arity's round 0, its own copy of POSEIDON2_HASH_ROUNDS (12,766 bytes, no labels inside) and the return, so no arity jumps again: 17 gas each. Zero bytes (`__VERBATIM`) fill the gaps. 64,254 runtime bytes (13,607 before), within 65,536. The generator takes the least shift whose regions fit; if three copies do not fit (Osaka, or rounds over about 14,300 bytes) it falls back to `calldatasize 0x21 xor jump`: 0x05 / 0x65 / 0x45, hash_2 highest falls through to the shared rounds, hash_1 / hash_3 hop through a 5-byte trampoline (18 / 41 / 41 gas).

| Arity | Before | xor (Osaka fallback) | Landed (shl 9, copies) |
| :--- | ---: | ---: | ---: |
| hash_1 | 11,883 | 11,868 (-15) | 11,844 (-39) |
| hash_2 | 11,890 | 11,886 (-4) | 11,885 (-5) |
| hash_3 | 11,963 | 11,949 (-14) | 11,925 (-38) |
| permutation entry | 12,083 | 12,083 | 12,083 |

17 is the floor for a computed dispatch here: one op on calldatasize needs its PUSH (3) and the op (3), the JUMP (8) and the JUMPDEST (1); `calldatasize jump` (11) has 32-byte gaps, and no PUSH-free op (`dup1 add`, `dup1 mul`) spreads the targets far enough. A JUMPI fall-through is 21 at least.

Behaviour change on malformed calldata: before, any length < 0x44 ran hash_1 and > 0x44 hash_3. Now only 0x24 / 0x44 / 0x64 land on a JUMPDEST (any other length << 9 is a multiple of 512 inside a region, on no JUMPDEST, or past the code): they revert. The xor fallback can also land on the `hash_1` / `hash_3` / `rounds` labels for odd lengths.

Trade-off variants of the shared-rounds layout (not landed; dispatch gas only):

| Variant | hash_1 | hash_2 | hash_3 |
| :--- | ---: | ---: | ---: |
| two JUMPI (before) | 56 | 22 | 55 |
| `xor 0x21`, hash_2 falls through | 41 | 18 | 41 |
| `calldatasize jump` (0x24 / 0x44 / 0x64), hash_3 falls through, trampolines | 35 | 35 | 12 |
| `xor` key with hash_1 highest, hash_1 falls through | 18 | 41 | 41 |
| `xor k` + `shl 3` (hash_1 / hash_3 inline, no trampolines) | 35 | 24 | 35 |
| landed: `shl 9`, a rounds copy per arity | 17 | 17 | 17 |


### 2. Seams for t >= 8 (analysis)

Per-segment static gas from `poseidon2-gen schedule <t>` (sum of opcode gas per `// Round` comment). Steady external segment (M4 + next S-boxes) and steady internal round:

| Width | Ext. steady | Round 3 (last M4) | Round 4 (1st internal) | Int. steady | Round 60 (last int. + S-boxes) | Round 64 (final M4) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| t8 | 756 | 378 | 296 | 296 | 680 | 436 |
| t12 | 1,133 | 554 | 420 | 420 | 993 | 644 |
| t16 | 1,504 | 730 | 552 | 544 | 1,309 | 852 |
| t20 | 1,875 | 906 | 676 | 668 | 1,625 | 1,060 |
| t24 | 2,246 | 1,082 | 800 | 792 | 1,941 | 1,268 |

- Round 3 is exactly half a steady segment (no S-boxes): no seam cost.
- Round 60 = steady internal + t S-boxes (45 each) + 3(t - 1): the 3(t - 1) are the PRIME copies under the S-boxes, which the streamed external segments pay too. No seam cost.
- Round 64 (final M4, reduced outputs): t8 +58 over the half segment, the reduction of 8 outputs (m4-final 157 vs block 125 in RESULTS.md). Every reduced output needs its last op modular.
- Entry 14 gas a word (DUP P, PUSH off, CALLDATALOAD, MOD; PUSH0 for word 0) + SETUP. Leaving a word raw moves the cost: its column sum is an ADDMOD anyway, but u = x + S must then be an ADDMOD (+5, +3 PRIME copy) = the 8 the MOD and its PRIME copy cost. Zero-sum.
- Exit 5 gas a word (MSIZE, MSTORE) + `msize 0x0 return`. Minimal: every word needs an MSTORE and an offset (2 gas at best).

First consuming round +8 at t16, t20, t24, t28 (t8, t12 pay nothing): the exit layer's outputs have bounds (units of P - 1, s1'..s15', x5 last)
`[2,3,3,2, 2,3,3,2, 2,3,3,2, 2,3,2, 1]` at t16, total 38; the steady rounds see `[2 x 15, 1]` = 31. With every ADDMOD operand at most 5 units (2^256 / (P - 1) = 5.29), k ADDMODs reduce at most 10k - (k - 1) units: k = 4 takes 37, so 38 needs a fifth (+8: ADDMOD 8 vs ADD 3, and its PRIME copy). Checked with `sum_tree::plan`: leaf reorders (ascending, big-small zigzag) do not help (133 / 141 / 133); replacing a single bound-3 leaf by a bound-2 one gives 125 = the steady tree.
So one exit-layer output one unit tighter would remove the 8 gas. In the M4 (t2, t3 ADDMOD, q0 = 4 t0, q1 = 4 t1 MULMOD; y1 = q0 + t2, y3 = q1 + t3 bound 2, y0 = y1 + t3, y2 = y3 + t2 bound 3) a bound-2 y0 or y2 needs a fifth reduced value, i.e. another modular op, +8 (op +5, its PRIME copy +3: every PRIME copy is consumed, so none is free). Lane 0 of block 0 is S-boxed, so its bound does not count; the other bound-3 output of block 0 still does. A cheaper path would need the total bound down without a modular op: no DAG found. Dead end (8 gas a width, 32 total, would need a search over exit-block DAGs with per-output bounds).

A lazier first-round sum does not help either: with cap 2 (root an ADD of two ADDMOD results) 4 ADDMODs take 38 units, but the round's outputs m_i + sum go to bound 3 and the next round's sum (15 x 3 + 1 = 46) needs two more ADDMODs.

### Other dead ends

- t24/t28 diag constants pushed just before the last external M4 (Round 3) instead of at the macro start, so the external rounds DUP no deeper: same gas and the same bytes (63,679 at t24); every DUP there is a DUPN either way.
- t4 rounds per arity (each region builds POSEIDON2_HASH_ROUNDS from its own prologue's bounds): every arity's round 0 leaves bounds [2, 1, 2, 1] (units of P), so all three build at 11,449, the shared program.
- Osaka (item 4): the npm scripts emit Amsterdam only, so no Osaka output is checked in; not pursued.
