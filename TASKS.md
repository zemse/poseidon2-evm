# Tasks

Goal: fastest Poseidon2 EVM code theoretically possible, with a proof of optimality in a stated model. Lean reproving cost accepted for any saving, however small. EVMMAX out of scope.

## Huff, open directions

- [ ] 4x4 block program search over alternative M4 DAGs (current `sblock` fixes the paper's DAG, orders moves only), wider window (>10), EIP-8024 `EXCHANGE`. Est. 5-10 gas/block: 280-560 at t28, 80-160 at t8.
- [ ] t2/t3/t4 re-search with restrictions lifted (window, live-only DUP filter, fixed DAG, whitelist). Relaxation floor gaps t2 339, t3 504, t4 672: upper bound, real gain unknown.
- [ ] t4 hash arity dispatch by computed jump: hash_1 -15, hash_3 -25, hash_2 +19. Needs decision on primary arity.
- [ ] t4 hash: fuse round-0 forms with ROUND4, consume p1/p3 in place. At most 6 gas per arity; search 881 s / 7.6 GB per round.
- [ ] First consuming round costs 8 more than steady (lazier exit-layer bounds force an extra ADDMOD). 8 gas per width t >= 8.
- [ ] Deferred-sum internal state (slots hold d_i s_i, sum added at next MULMOD). Measured ~1 gas/round net: ~57 at t28.
- [ ] t24/t28 shared-body rounds pay 3 gas/round for `MLOAD` constants; inlining costs ~1,100 bytes/round against the 65,536 limit.
- [ ] Osaka t8: `primeEarly` impossible within DUP16 reach (24,217 stays).

## Yul, open directions

- [ ] t12 via-IR: one function and 8-round chunks exceed 40 GB; 2-round chunks too deep. Memory-held state est. a net loss.
- [x] t2/t3/t4/t8 tuned for via-IR 1M (999f493, d7fd8be): t2 7,560, t3 9,505, t4 13,904, t8 29,321.
- [x] t12 all diag constants as PUSH32 and tree sum (4ac47ed, 870682a, fcb1904): 46,272 to 43,682 at legacy 1M.
- [x] t8 via-IR compiles with a rounds function (aa12830).
- [ ] t2/t3 legacy: ~10-15 gas/round of stack moves left; needs a simulator of solc's CodeTransform + CSE to search shapes. Est. 300-600.
- [ ] `Poseidon2Yul_BN254` fallback dispatch to hash_1/2/3 by calldatasize: ~-60/-20/+15.

## Lean

- [x] Refresh proofs for every Huff/Yul bytecode changed since b4afc03 (5b2903a, aa1e499).
- [x] Prove the via-IR 1M builds of t2/t3/t4/t8 (04f2d61, 75518ae); 39 targets proven.

## Optimality proof roadmap

Unrestricted "no faster EVM program exists" is out of reach: it is a circuit lower bound for an explicit function, beyond known techniques. Provable: optimality inside a stated model, layered.

- [ ] Model statement: straight-line EVM programs computing the Poseidon2 round DAG over GF(p), with allowed rewrites (reassociation, lazy reduction under 2^256 bounds, constant folding, seam fusion) and opcode set (ADD, MUL, ADDMOD, MULMOD, MOD, PUSH, DUP/DUPN, SWAP/SWAPN, EXCHANGE, MLOAD/MSTORE).
- [ ] L1 arithmetic floor: S-box x^5 needs 3 multiplications (addition chain); each diag product needs one MULMOD with a generic constant; count of irreducible ops per round. Lean.
- [ ] L2 reduction floor: minimal ADDMOD/MOD count given 256-bit bounds, as ILP/DP; Lean-checked dual certificate.
- [ ] L3 stack floor: minimal DUP/SWAP/PUSH gas per segment for fixed boundary layouts; exact search with checkable certificate.
- [ ] Composition: min-plus DP over boundary layouts across rounds, so per-round bounds sum to a whole-permutation bound.
- [ ] Gap report: proven floor vs shipped gas per width; zero gap = optimal in the model.
- [ ] First: prove floor B (arith gas + 3 per net consumed slot, `gas-floor.mjs`) in Lean for every width. Current gaps 7-10%, ~9.5% at t8-t20, mostly SWAP gas in internal consuming rounds.
- [ ] Certificate pipeline: SAT/PB encoding of "segment gas <= C-1", LRAT (Lean core checker) or VeriPB (pb-catcher) refutation; verified encoder is ours to write.
- [ ] Normal-form lemma for cutting at round boundaries; recent cross-seam savings may falsify a strict one.
- [ ] Research: `evm-gas-optimality-proofs/evm-gas-optimality-proofs.md`.

Prior art: ebso (Nagele, Schett, LOPSTR 2019, SMT superoptimizer for loop-free EVM code), SYRUP (Albert, Gordillo, Rubio, Schett, CAV 2020 Max-SMT; TOSEM 2022 "Super-optimization of Smart Contracts").
