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

- [ ] t2/t3/t4 tuned for via-IR 1M (their least-gas setting); all shape work so far measured on legacy. In progress (`gas-yul`).
- [ ] t12 `diagInMemory 7` (-216 at legacy 1M) and balanced internal sum tree (up to ~114). In progress.
- [ ] t8 via-IR: solc 0.8.30 stack layout assertion after 224 s / 48 GB; retry with a memory-state or smaller-function shape.
- [ ] t2/t3 legacy: ~10-15 gas/round of stack moves left; needs a simulator of solc's CodeTransform + CSE to search shapes. Est. 300-600.
- [ ] `Poseidon2Yul_BN254` fallback dispatch to hash_1/2/3 by calldatasize: ~-60/-20/+15.

## Lean

- [ ] Refresh proofs for every Huff/Yul bytecode changed since b4afc03 (handoff log per commit).
- [ ] Prove the via-IR 1M builds of t2/t3/t4 (now the recommended settings; only legacy builds are proven today).

## Optimality proof roadmap

Unrestricted "no faster EVM program exists" is out of reach: it is a circuit lower bound for an explicit function, beyond known techniques. Provable: optimality inside a stated model, layered.

- [ ] Model statement: straight-line EVM programs computing the Poseidon2 round DAG over GF(p), with allowed rewrites (reassociation, lazy reduction under 2^256 bounds, constant folding, seam fusion) and opcode set (ADD, MUL, ADDMOD, MULMOD, MOD, PUSH, DUP/DUPN, SWAP/SWAPN, EXCHANGE, MLOAD/MSTORE).
- [ ] L1 arithmetic floor: S-box x^5 needs 3 multiplications (addition chain); each diag product needs one MULMOD with a generic constant; count of irreducible ops per round. Lean.
- [ ] L2 reduction floor: minimal ADDMOD/MOD count given 256-bit bounds, as ILP/DP; Lean-checked dual certificate.
- [ ] L3 stack floor: minimal DUP/SWAP/PUSH gas per segment for fixed boundary layouts; exact search with checkable certificate.
- [ ] Composition: min-plus DP over boundary layouts across rounds, so per-round bounds sum to a whole-permutation bound.
- [ ] Gap report: proven floor vs shipped gas per width; zero gap = optimal in the model.

Prior art: ebso (Nagele, Schett, LOPSTR 2019, SMT superoptimizer for loop-free EVM code), SYRUP (Albert, Gordillo, Rubio, Schett, CAV 2020 Max-SMT; TOSEM 2022 "Super-optimization of Smart Contracts").
