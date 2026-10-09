# Poseidon2 for BN254

This is an instance of Poseidon2 for the BN254 curve (also known as alt_bn128).

**Compatible with:** [Noir](https://noir-lang.org/) / [Barretenberg](https://github.com/AztecProtocol/barretenberg) / [Aztec](https://aztec.network/) ecosystem.

## Parameters

| Parameter           | Value                                                                |
| ------------------- | -------------------------------------------------------------------- |
| Curve               | BN254 (alt_bn128)                                                    |
| Prime               | `0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001` |
| Full rounds (Rf)    | 8                                                                    |
| Partial rounds (Rp) | 56                                                                   |
| Total rounds        | 64                                                                   |
| State width (t)     | 4                                                                    |
| Rate                | 3                                                                    |
| S-box               | x^5                                                                  |

## Gas Costs

| Implementation  | hash_1  | hash_2  | hash_3  |
| --------------- | ------- | ------- | ------- |
| Pure Solidity   | 217,702 | 218,222 | 218,801 |
| Yul (contract)  | 15,127  | 15,127  | 15,127  |
| Huff (contract) | 11,964  | 11,986  | 12,059  |

## Recommendation

Using the Yul library is recommended for most use cases. It provides the best gas efficiency when inlined into your contracts.

For external calls to deployed contracts, the Huff implementation provides the lowest gas cost. The Huff source targets Amsterdam (it uses the EIP-8024 `DUPN` / `SWAPN` opcodes) and does not run on earlier forks; the contracts deployed from v2 and earlier (`deployed-artifacts/`) are pre-Amsterdam builds.

## Notes on Optimizations

### ADDMOD Optimization

This optimization is used in Yul and Huff implementations. Not used in Solidity.

Using `ADD` is cheaper (3 gas) compared to `ADDMOD` (8 gas) which also needs a prime argument (3 gas to duplicate on stack), saving 11 gas per instance. Using `ADD` instead of `ADDMOD` overflows the value beyond the field domain but we can `MOD` the value or use it with `MULMOD` which outputs a legal value.

Applying this optimization for the BN254 curve is tricky because the PRIME is almost close to uint256 max, which means the value could overflow the uint256 variable, corrupting the state and leading to an incorrect hash value. For other curves with smaller prime fields, this optimization is trivial.

BN254 prime allows adding 5 field values (4 additions, since 2^256 / p is about 5.29). Both the Yul and the Huff code are generated, and the generators prove every lazy operation: `generator/shared/value.ts` carries an exact inclusive upper bound per value and refuses an `ADD`, `MUL` or `SHL` whose result could exceed 2^256 - 1, so the choice between `ADD` and `ADDMOD` is made by the bound, never by hand. Where a reduction is forced early (the M4 temporaries, the internal round sum) it is because it keeps more of the following additions lazy. Which value to reduce matters: for t = 2 reducing the internal round sum leaves the second element growing, so its doubling falls back to `MULMOD` every second round, while reducing that element with `ADDMOD` and keeping the sum lazy (`internalReduceOutputs`) is one reduction per round and every doubling an `ADD`, 4 gas per round less. The generated code is also executed on test vectors against the BigInt reference before it is written.

If there is even a single situation where an unsafe addition could overflow uint256 max, then it is possible for an attacker to vanity mine the input. The published v1.0.0 Yul had such an addition (hand-tracked in comments); `test_regression_overflow_counterexamples` locks in the inputs that exposed it.

### No Stack Scheduling

This optimization is used in Huff. Not used in Yul or Solidity.

The EVM has a stack limit of 1024. Hence, compilers are designed to avoid running into stack overflow by scheduling every element pushed on the stack to be used later. This involves calling a bunch of `SWAP` opcodes to rearrange the stack before calling an internal function.

However, it is cheaper to not rearrange elements on the stack and instead `DUP`licate them in the order we want. This works when we are working with fewer than 16 variables (including temporary) because we have `DUP1` to `DUP16`.

This instance of Poseidon2 has 64 total rounds. The generator balances in-place consumption against leaving dead values below the live state; the selected t = 4 permutation reaches 93 stack slots. On Amsterdam `DUPN` / `SWAPN` reach slot 235, so the dead values can stay deeper than 16; from t = 12 the generator reclaims dead slots with `SWAP` + `POP` because the 1024 limit would otherwise be hit.

### Huff Generator

`generator/huff/generate.ts` (shared modules in `generator/`, Huff-specific ones in `generator/huff/`) builds the Huff permutation for a state width t:

- `round-constants.ts` ports the HorizenLabs `poseidon2_rust_params.sage` script: round numbers, Grain LFSR round constants and the internal matrix diagonal with its minimal polynomial check. Both generators first run `assert-known.ts`, whatever width they build: t = 4 against `constants.ts`, the Barretenberg KAT and the sponge vectors, t = 3 against the HorizenLabs instance, permutation KATs from TACEO for t = 2, 4, 8, 12, 16, sample gnark-crypto constants for t = 8, 12, 16, and the round numbers against the paper, each pinned to a commit permalink.
- `reference.ts` is the BigInt reference permutation.
- `huff/emitter.ts` is a symbolic stack simulator. Every value carries an exact upper bound; `ADD` and `MUL` are only emitted when the bound stays below 2^256, otherwise `ADDMOD` / `MULMOD`. It also tracks depth, the deepest `DUP`, gas and bytecode size, and executes the emitted stream on test inputs. The hardfork (`huff/fork.ts`, `--hardfork <name>`) sets the reach: `DUP16` / `SWAP16` for the legacy opcodes, slot 235 with the EIP-8024 `DUPN` / `SWAPN` of Amsterdam (3 gas and 2 bytes each, so the one-byte opcodes are still preferred up to 16). A value the reach cannot `DUP` can be shadowed: stored to a memory slot when produced and loaded from there instead (see Osaka below).
- `huff/schedule.ts` orders the field operations like the hand-written code did (results land on top, operands are pre-placed so results land in place) and tries a few option sets per t (diag constants in memory, garbage collection, two forms of the t = 4k linear layer, which value the internal round reduces, whether it leaves a PRIME copy under the state every round, whether the internal rounds consume the old state in place, whether the steady internal rounds share one body reached by `JUMP`, and in sub-chains of what length when that body would not fit, whether the external rounds of t <= 4 and the internal rounds of t = 4 follow the stack programs of `huff/templates.ts`), keeping the cheapest one that fits. The programs are searched by `generator-rs/stacksearch/` with A* over a configured macro graph (a lane's S-box is one move, with swap sequences from a table and an admissible bound on the moves left). The t = 3 re-entry costs 189 and both final-cycle layouts cost 216. The full t = 4 programs compose a fixed S-box prefix with a separately searched M4, so they are not globally optimal. The scheduler tries a matching full-round template before applying S-boxes, then falls back to a linear template or generic M4 when needed. Rounds may retain dead values below the required output prefix; standalone M4 block programs leave no extra values. The t = 4 internal round is the program `stacksearch`'s `internal` (an A* over single opcodes) finds for the three-lane analogue, extended to four lanes: 166 gas instead of 169, one dead value a round instead of five, with three `SWAP`s, as any round without `SWAP` leaves five (the sum is never consumed, so everything under it stays). From t = 8 the same search gives the M4 of a block of the `externalD` layer (its four inputs on top, consumed, nothing left behind, with a variant that leaves the PRIME copy the internal rounds expect and one with reduced outputs for the last round), which is what lets every width from t = 8 take that layer. `huff/split.ts` cuts a permutation over the fork's code size into parts at round boundaries.

Every generated permutation lives in `huff/t<t>/Permutation.huff`. t = 4 is called through the generated hash entry `huff/t4/Poseidon2.huff` (`hash_1` / `hash_2` / `hash_3`, tested in `test/Poseidon2.t.sol`): the arity comes from calldatasize, each arity runs its own round 0 with the missing words and the capacity `n << 64` folded into its constants, then jumps into the shared rounds 1 to 63, whose last linear layer computes only the returned `s0'` (row 0 of M4 straight from the S-boxes). The three cost 11,964, 11,986 and 12,059 gas. The other widths get a generated entry contract (calldata t words, returns t words) and vectors from the reference in `test/Poseidon2T<t>.t.sol`. All of them target Amsterdam (below), and `forge test` runs on an Amsterdam EVM (`evm_version = "amsterdam"` in `foundry.toml`); CI checks that the output fails on Osaka.

| t   | Rf  | Rp  | permutation gas | call gas | max stack depth | max dup | runtime bytes | placement                                                                       |
| --- | --- | --- | --------------- | -------- | --------------- | ------- | ------------- | ------------------------------------------------------------------------------- |
| 2   | 8   | 56  | 5,975           | 6,027    | 131             | 118     | 4,007         | stack, 3 s1 by MUL (internalMul3), external rounds from templates               |
| 3   | 8   | 56  | 7,839           | 7,914    | 244             | 121     | 5,033         | stack, external rounds from templates                                           |
| 4   | 8   | 56  | 12,067          | 11,986   | 93              | 85      | 13,647        | stack, hash entry: round 0 per arity, s0' only, external and internal templates |
| 8   | 8   | 57  | 24,018          | 24,208   | 707             | 121     | 25,310        | stack, diag as PUSH32, externalD, block templates                               |
| 12  | 8   | 57  | 34,494          | 34,776   | 996             | 143     | 36,896        | stack, diag as PUSH32, gcInternal from round 56, externalD, block templates     |
| 16  | 8   | 57  | 45,166          | 45,540   | 335             | 145     | 49,607        | stack, diag as PUSH32, internalConsume, externalD, block templates              |
| 20  | 8   | 57  | 56,019          | 56,485   | 407             | 153     | 61,742        | stack, diag as PUSH32, internalConsume, externalD, block templates              |
| 24  | 8   | 57  | 66,781          | 67,343   | 479             | 157     | 49,750        | stack, diag as PUSH32, internalConsume, sharedBody, externalD, block templates  |
| 28  | 8   | 59  | 79,395          | 80,049   | 552             | 149     | 55,634        | stack, diag as PUSH32, internalConsume, sharedBody, externalD, block templates  |

Call gas is the Huff call-frame gas checked by the verifier against the model (t = 4 is `hash_2`, the others are the raw permutation entry). Runtime bytes are the entry plus the permutation as compiled by huffc; t = 24 and t = 28 fit the 65,536 byte limit through the shared body, with 49,750 and 55,634 bytes. Up to t = 12 every width but t = 4 DUPs the PRIME copies of its internal rounds from wherever the nearest one sits (`floatPrimeInternal`), which is why the deepest DUP is above 100 everywhere; from t = 16 the internal rounds consume the old state in place (`internalConsume` with `primeStack`, see the legacy opcodes below), which beats collecting it within the 1024 depth, and t = 24 and t = 28 run their steady internal rounds through one shared body (`sharedBody`, below) rather than keep diag constants in memory. With the legacy opcodes (before Amsterdam) the raw permutation entries cost 6,066, 7,992, 12,165, 24,507 and 35,718 gas for t = 2, 3, 4, 8, 12; the unrolled Yul wrapper costs 78,287 (t = 16), 101,842 (t = 20), 125,985 (t = 24) and 154,826 gas (t = 28, 67,097 bytes, over the limit).

#### Hardforks

`--hardfork <name>` picks a row of `huff/fork.ts`; the emitted code uses exactly the features of that fork and the generator refuses a schedule over its limits. The default, and the only fork whose output is in the repository, is amsterdam. Nothing emitted depends on Cancun (no `MCOPY`), Prague or Osaka, so their output is the Shanghai output.

| fork      | zero                      | DUP / SWAP reach       | code size (EIP-170 / EIP-7954) | initcode (EIP-3860 / EIP-7954) | STATICCALL account access (EIP-2929 / EIP-8038) |
| --------- | ------------------------- | ---------------------- | ------------------------------ | ------------------------------ | ----------------------------------------------- |
| paris     | `PUSH1 0x00` (3 gas, 2 B) | 16                     | 24,576                         | none                           | 2,600 cold / 100 warm                           |
| shanghai  | `PUSH0` (2 gas, 1 B)      | 16                     | 24,576                         | 49,152                         | 2,600 cold / 100 warm                           |
| cancun    | `PUSH0`                   | 16                     | 24,576                         | 49,152                         | 2,600 cold / 100 warm                           |
| prague    | `PUSH0`                   | 16                     | 24,576                         | 49,152                         | 2,600 cold / 100 warm                           |
| osaka     | `PUSH0`                   | 16                     | 24,576                         | 49,152                         | 2,600 cold / 100 warm                           |
| amsterdam | `PUSH0`                   | 235 (`DUPN` / `SWAPN`) | 65,536                         | 131,072                        | 3,000 cold / 100 warm                           |

A fork other than amsterdam writes `huff/<fork>/t<t>/` and `test/<fork>/`; its tests need a foundry profile with that `evm_version`. huffc turns every zero literal into `PUSH0`, so before Shanghai the generator writes `ZERO()` (`huff/<fork>/Zero.huff`, `__VERBATIM(0x6000)`) and the test deploys with `with_evm_version`.

#### Amsterdam (EIP-8024)

`DUPN` / `SWAPN` reach stack slot 235 and EIP-7954 raises the code size limit to 65,536 bytes. huffc and huff-neo have no mnemonic for them, so `huff/Eip8024.huff` defines `DUP17()` .. `DUP235()` and `SWAP17()` .. `SWAP235()` as `__VERBATIM` bytes (immediate x encodes n = (x + 145) % 256). The whole state stays on the stack; two options use the reach: `gcInternalFrom` leaves the garbage of the first internal rounds in place while the 1024 depth allows (saves the `SWAPn POP` of 5 gas per slot) and `floatPrimeInternal` lets an internal round DUP its PRIME copies from the nearest one however deep it sits, leaving a fresh copy under the state only when that one is about to leave the reach (saves the 3 gas copy of every other round; with `DUP16` it is needed every round). `diagPush32` keeps as many diag constants as `PUSH32` as the code size allows when the others are in memory (3 gas instead of 6 per use), on every fork. The generator finds the two limits by binary search. From t = 20 the depth limit makes the collected internal rounds dearer than `internalConsume` (below), which those widths take; t = 24 and t = 28 no longer fit unrolled with every diag constant as `PUSH32`, so they take the shared body (below) with 9 and 3 steady rounds kept inline.

#### Legacy opcodes (not shipped)

For a fork before Amsterdam two things give from t = 16: the state does not fit the `DUP16` reach, and the code does not fit the 24,576 byte limit. t = 12 already has no room for garbage (12 elements, the sum and PRIME fill 14 of the 16 slots), so its internal rounds consume the old state in place (`internalConsume`): the sum chain DUPs every element in advance with the PRIME copies of its reductions between them (16 slots exactly) and lands on a PRIME copy, so `s0^5` swapped on top of it is consumed by its own MULMOD, then every other element is SWAPped to the top and consumed by its MULMOD, its output taking the slot of the previous one, and the last ADD consumes the sum. Nothing is popped (26 gas per element instead of 23 plus the 5 of `SWAPn POP`). The order of the elements decides the next layout, so the last internal round takes the order that puts block 0 of the external layer back on top (an Eulerian circuit of the blocks). t = 8 fits within reach without it and keeps as many diag constants as `PUSH32` as the code budget allows. From t = 16 the stack holds 12 elements this way and the first t - 13 indices (block 0 and whole blocks, so the external layer still finds its blocks in place) live in memory: loaded for the chain and for their MULMOD and stored again (38 gas per element), with `s0^5` joining the chain from memory as well; the split parts below take this over shadowing the whole state.

- Reach: with the `shadow` schedule option a value the reach cannot `DUP` is stored to a memory slot when it is produced (`DUP1 <off> MSTORE`, 9 gas) and loaded from there (`<off> MLOAD`, 6 gas) whenever it is out of reach. Neither changes the stack, so a permissive pass first records which values need it and the real pass with the same schedule shadows exactly those (the permissive pass also records each value's last load, where the real pass frees its slot for reuse, so the memory expansion stays small; the simulation refuses a load from a reused slot). The option is only tried when no stack-only schedule works.
- Code size: `huff/split.ts` cuts the permutation at step boundaries (the initial linear layer, then one step per round) into `Part<i>.huff` contracts, as few as fit (fewer only while they cost less, since a part may fit only through the dearest schedules; a whole permutation that fits only that way is compared with the split as well), each built and checked like a whole permutation (bound tracker, reference check of its own rounds with `permutationSteps`, size check with its entry and tail).
- Linking: part i ends with the state in memory at `[0, 32t)` and `STATICCALL`s part i + 1 with it as calldata, the output lands in the same region and is returned (`returndatasize` must equal 32t). The address of the next part is the 32-byte word the deployer appends to the initcode: `NEXT_PART()` is a `PUSH32` of it (3 gas), which the generated `CONSTRUCTOR` patches into the runtime code before deploying it (the immediate ends where `HAND_OVER()`, the call itself, begins, so its offset is `__codesize(MAIN) - __codesize(HAND_OVER) - 32`), and the deployed code is the runtime alone. The generated `DeployParts.sol` next to the parts deploys a chain last to first.
- Hand-over: a part leaves lazy values below 2p (an internal round leaves `m_i + sum` with both reduced; anything above the bound is reduced before it is stored), and the next part takes them as they are: its entry loads the words without the `mod` of part 0 (8 gas per word), and an input the reach cannot `DUP` is loaded from calldata (`<off> CALLDATALOAD`, 6 gas) instead of being copied to a memory slot by the entry (9 gas each). Only part 0 reduces its calldata, so the chain is to be entered there.
- Shared body (`sharedBody`): a consuming round moves every output one slot deeper and the last one to the top, so after as many rounds as the stack holds elements (11 for t = 12, 12 from t = 16) the layout is back where it started, and the bounds are a fixed point after the first round. The steady internal rounds (all but the first and the last of a part) are therefore emitted once as a body of that period: a call `CODECOPY`s its round constants from a code table (`RC<i>`) into a memory scratch, stores its return label and `JUMP`s to the body, which reads each constant with `MLOAD` (3 gas more than `PUSH32`) and `JUMP`s back through the stored label; the last call falls into the body and a call of fewer rounds leaves at a mid exit. The body's diag constants are `PUSH32` as it exists once, and the generator simulates every call, so the opcodes of each one are checked to be those of the first. `bodyInline` keeps as many steady rounds inline as the code size allows, preferring a count that leaves no partial call.
- Sub-chains (`consumeGroup`): a body of 12 rounds is too large for the legacy code size next to the external rounds from t = 16. The consuming round can instead take the elements in sub-chains of `consumeGroup` slots (the last takes the rest): m0 takes the slot of a chain's first element, each output the slot of the next one, and the last output the first slot when m0 is swapped back on top, one `SWAP` more per chain (the last chain's close is the swap the single chain made anyway). Each chain then rotates on its own, so the period is the lcm of their lengths and the body that much shorter, at the price of the extra swaps and of more calls. When the single-chain body does not fit, the search takes the sub-chains of the longest period that does (12 = 9 + 3 gives 9, 6 + 6 gives 6, 4 + 4 + 4 gives 4); the last round of a part takes the same closes to leave every element in its block, one chain per connected component of the blocks, which is also what lets the consuming schedule build at t = 8 (after 56 rounds the layout is back where it started and the blocks are two cycles).
- PRIME from memory (`primeInMemory`): where no PRIME copy is within `DUP16` reach (the M4 blocks of an external layer, the sum chains of the first and last internal rounds) the schedule pushes one with `PUSH32` (33 bytes). Where the code size binds (sub-chains, diag constants in memory, or no fit), the search also tries storing PRIME once at a slot below the shadow slots and loading it there with `PUSH2` `MLOAD` (3 bytes, 3 gas more), keeping it when the whole schedule costs less. For t = 24 that frees 2,341 bytes for 255 gas, where a sub-chain period of 2 instead of 4 costs about 1,400 gas and each diag constant in memory 180.

Measured on Osaka, t = 12 costs 35,718 gas and t = 16 fits one contract at 53,927 gas. The cheaper M4 templates also let t = 20 use one 23,910-byte contract at 69,398 gas instead of the previous two-part 72,368-gas schedule. PRIME from memory lets t = 24 run its body in sub-chains of 4 (period 4) within one 24,508-byte contract at 85,043 gas instead of two parts at 87,333 (cold hop). t = 28 still uses two parts, costing 105,773 gas with a cold hop or 103,273 with a warm one; as one contract it costs 109,970 even with PRIME from memory (period 2, diag constants in memory). A hop costs about 2,800 gas cold: the 2,600 EIP-2929 account access (100 when warm), the state to memory and the call (about 50), the next part's entry (6 gas per word) and its memory expansion.

The constants and permutation outputs for every generated t match other implementations of the same HorizenLabs instance (gnark-crypto, TACEO, Polygon pil2). See [generator/README.md](../../generator/README.md#evidence-that-the-output-matches-other-implementations) for the links.

### Yul Generator

`generator/yul/generate.ts` builds the Yul libraries from the same `round-constants.ts`, `reference.ts` and `value.ts`:

- `yul/program.ts` emits straight-line Yul. Every operand is a bound-tracked value whose name is the Yul text producing it (a local, a literal, an `mload` or a nested expression), so an `add` is only written where the bound allows it and the whole permutation is checked against the reference before the file is written.
- `yul/schedule.ts` orders the field operations and places the state. Internal round outputs stay lazy (below 2p) with one reduced sum per round (t = 2 keeps the sum lazy and reduces `state1` instead, so its doubling stays a shift), M4 reduces only its two inner temporaries, and the text is shaped for the legacy solc pipeline, which compiles inline assembly literally with the optimizer off: nested expressions instead of assignments, temporaries in blocks that end right after their last use, and for t = 12 a two-temporary M4 and sum chains cut so that the deepest local stays within `DUP16` / `SWAP16` (the generator models the reach of every local). The libraries are inlined into the consumer's contract with the consumer's settings, so `compat-check.sh` compiles a consumer of each library with the legacy pipeline (optimizer off, 200 runs, 1,000,000 runs) and via-IR (200 and 1,000,000 runs, t <= 4 only); CI runs it. From t = 8 a via-IR compile of the single straight-line function needs tens of GB of memory (t = 12 passed 69 GB with solc 0.8.37 before it was stopped), so t = 8 and t = 12 are for the legacy pipeline.

t = 4 keeps `LibPoseidon2Yul` (`hash_1` / `hash_2` / `hash_3` / `poseidon2_core`) and only computes the first output of the last round. Other widths get `yul/t<t>/LibPoseidon2YulT<t>.sol` with `permute(uint256[t] memory state)`, which permutes the array in place after reducing it mod PRIME, and a test in `test/Poseidon2YulT<t>.t.sol` with the reference vectors, input sanitisation and a fuzz against the Huff permutation of the same width.

| t   | Rf  | Rp  | call gas | runtime bytes | state placement                                   |
| --- | --- | --- | -------- | ------------- | ------------------------------------------------- |
| 2   | 8   | 56  | 9,019    | 5,169         | locals                                            |
| 3   | 8   | 56  | 11,403   | 6,092         | locals                                            |
| 4   | 8   | 56  | 15,127   | 14,483        | locals                                            |
| 8   | 8   | 57  | 31,833   | 24,130        | 8 locals, 2 diag constants in memory              |
| 12  | 8   | 57  | 49,892   | 24,105        | 12 locals, 10 diag constants in memory, 2-temp M4 |

Call gas and runtime bytes are those of a contract that inlines the library: `Poseidon2Yul_BN254` for t = 4 (one `hash_*` call) and the `permute(uint256[t])` wrapper deployed by each test otherwise, so they include the ABI decoding and encoding of t words. The gas is above the Huff table because solc inserts a `SWAP` + `POP` per assignment and `DUP`s every operand, and because the diag constants that do not fit the code size as `PUSH32` are loaded from memory (9 gas more each). t = 12 is the largest shipped width: the 2-temporary M4 and the split sum chains are already at the `DUP16` limit, and the code is at the 24,576 byte limit with 10 of 12 diag constants in memory (a consumer of t = 8 or t = 12 built with the optimizer off lands about 200 bytes above it, so such a deployment needs the optimizer). t = 16 generates and passes its vectors with 11 locals and 5 elements kept in the state array (78,287 gas), but its permutation alone is 33 KB of runtime code, so it is not shipped.

## Security Considerations

The `ADDMOD` optimization, while gas-efficient, carries inherent risks related to potential `uint256` overflows if not meticulously handled. Our implementation carefully tracks "dirty" values to ensure that intermediate additions do not exceed `uint256` maximum before a modular reduction. However, it is crucial to understand that **this code has not undergone a formal third-party security audit**.
