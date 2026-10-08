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
| Huff (contract) | 12,558  | 12,558  | 12,558  |

## Recommendation

Using the Yul library is recommended for most use cases. It provides the best gas efficiency when inlined into your contracts.

For external calls to deployed contracts, the Huff implementation provides the lowest gas cost.

## Notes on Optimizations

### ADDMOD Optimization

This optimization is used in Yul and Huff implementations. Not used in Solidity.

Using `ADD` is cheaper (3 gas) compared to `ADDMOD` (8 gas) which also needs a prime argument (3 gas to duplicate on stack), saving 11 gas per instance. Using `ADD` instead of `ADDMOD` overflows the value beyond the field domain but we can `MOD` the value or use it with `MULMOD` which outputs a legal value.

Applying this optimization for the BN254 curve is tricky because the PRIME is almost close to uint256 max, which means the value could overflow the uint256 variable, corrupting the state and leading to an incorrect hash value. For other curves with smaller prime fields, this optimization is trivial.

BN254 prime allows adding 5 field values (4 additions, since 2^256 / p is about 5.29). Both the Yul and the Huff code are generated, and the generators prove every lazy operation: `generator/value.ts` carries an exact inclusive upper bound per value and refuses an `ADD`, `MUL` or `SHL` whose result could exceed 2^256 - 1, so the choice between `ADD` and `ADDMOD` is made by the bound, never by hand. Where a reduction is forced early (the M4 temporaries, the internal round sum) it is because it keeps more of the following additions lazy. The generated code is also executed on test vectors against the BigInt reference before it is written.

If there is even a single situation where an unsafe addition could overflow uint256 max, then it is possible for an attacker to vanity mine the input. The published v1.0.0 Yul had such an addition (hand-tracked in comments); `test_regression_overflow_counterexamples` locks in the inputs that exposed it.

### No Stack Scheduling

This optimization is used in Huff. Not used in Yul or Solidity.

The EVM has a stack limit of 1024. Hence, compilers are designed to avoid running into stack overflow by scheduling every element pushed on the stack to be used later. This involves calling a bunch of `SWAP` opcodes to rearrange the stack before calling an internal function.

However, it is cheaper to not rearrange elements on the stack and instead `DUP`licate them in the order we want. This works when we are working with fewer than 16 variables (including temporary) because we have `DUP1` to `DUP16`.

This instance of Poseidon2 has 64 total rounds. Each external round leaves 13 dead values on the stack and each internal round 6, so the stack height reaches 456 for t = 4. For t = 12 the generator reclaims dead slots with `SWAP` + `POP` because the 1024 limit would otherwise be hit.

### Huff Generator

`generator/huff/generate.ts` (shared modules in `generator/`, Huff-specific ones in `generator/huff/`) builds the Huff permutation for a state width t:

- `params.ts` ports the HorizenLabs `poseidon2_rust_params.sage` script: round numbers, Grain LFSR round constants and the internal matrix diagonal with its minimal polynomial check. `test-reference.ts` checks t = 4 against `constants.ts` and the Barretenberg KAT, t = 3 against the HorizenLabs instance, and the round numbers against the paper.
- `reference.ts` is the BigInt reference permutation.
- `huff/emitter.ts` is a symbolic stack simulator. Every value carries an exact upper bound; `ADD` and `MUL` are only emitted when the bound stays below 2^256, otherwise `ADDMOD` / `MULMOD`. It also tracks depth, the deepest `DUP`, gas and bytecode size, and executes the emitted stream on test inputs. The hardfork (`huff/fork.ts`, `--hardfork <name>`) sets the reach: `DUP16` / `SWAP16` for the legacy opcodes, slot 235 with the EIP-8024 `DUPN` / `SWAPN` of Amsterdam (3 gas and 2 bytes each, so the one-byte opcodes are still preferred up to 16). A value the reach cannot `DUP` can be shadowed: stored to a memory slot when produced and loaded from there instead (see Osaka below).
- `huff/schedule.ts` orders the field operations like the hand-written code did (results land on top, operands are pre-placed so results land in place) and tries a few option sets per t (diag constants in memory, garbage collection, two forms of the t = 4k linear layer), keeping the cheapest one that fits. `huff/split.ts` cuts a permutation over the fork's code size into parts at round boundaries.

Generated permutations for t other than 4 live in `huff/t<t>/` with an entry contract (calldata t words, returns t words) and vectors from the reference in `test/Poseidon2T<t>.t.sol`; the output for a fork other than the default lives in `huff/<fork>/t<t>/` and `test/<fork>/`.

| t   | Rf  | Rp  | permutation gas | call gas | max stack depth | max dup | runtime bytes |
| --- | --- | --- | --------------- | -------- | --------------- | ------- | ------------- |
| 2   | 8   | 56  | 6,463           | 6,515    | 276             | 13      | 4,032         |
| 3   | 8   | 56  | 8,049           | 8,124    | 351             | 15      | 4,743         |
| 4   | 8   | 56  | 12,480          | 12,558   | 456             | 16      | 13,192        |
| 8   | 8   | 57  | 25,719          | 25,909   | 889             | 16      | 14,394        |
| 12  | 8   | 57  | 43,912          | 44,194   | 274             | 16      | 23,646        |

Call gas is the Huff contract call measured by forge (t = 4 is `hash_*`, the others are the raw permutation entry). t = 16 and above does not fit a stack-only schedule with the legacy opcodes: the deepest state element plus the PRIME copy under the S-box input already exceeds `DUP16`, so the generator shadows the deep values in memory, and since the code then exceeds the 24,576 byte limit it splits the permutation into several contracts (Osaka below); Amsterdam reaches the whole state with `DUPN` / `SWAPN`. For t >= 8 the diag constants are stored in memory once and loaded with `MLOAD`, otherwise the `PUSH32`s exceed the code size limit.

#### Hardforks

`--hardfork <name>` picks a row of `huff/fork.ts`; the emitted code uses exactly the features of that fork and the generator refuses a schedule over its limits. Nothing emitted depends on Cancun (no `MCOPY`), Prague or Osaka, so their output is the Shanghai output; the default is shanghai, the fork the t = 2, 3, 4, 8, 12 output in `huff/` targets.

| fork      | zero                        | DUP / SWAP reach           | code size (EIP-170 / EIP-7954) | initcode (EIP-3860 / EIP-7954) | STATICCALL account access (EIP-2929) |
| --------- | --------------------------- | -------------------------- | ------------------------------ | ------------------------------ | ------------------------------------ |
| paris     | `PUSH1 0x00` (3 gas, 2 B)   | 16                         | 24,576                         | none                           | 2,600 cold / 100 warm                |
| shanghai  | `PUSH0` (2 gas, 1 B)        | 16                         | 24,576                         | 49,152                         | 2,600 cold / 100 warm                |
| cancun    | `PUSH0`                     | 16                         | 24,576                         | 49,152                         | 2,600 cold / 100 warm                |
| prague    | `PUSH0`                     | 16                         | 24,576                         | 49,152                         | 2,600 cold / 100 warm                |
| osaka     | `PUSH0`                     | 16                         | 24,576                         | 49,152                         | 2,600 cold / 100 warm                |
| amsterdam | `PUSH0`                     | 235 (`DUPN` / `SWAPN`)     | 65,536                         | 131,072                        | 2,600 cold / 100 warm                |

huffc turns every zero literal into `PUSH0`, so before Shanghai the generator writes `ZERO()` (`huff/paris/Zero.huff`, `__VERBATIM(0x6000)`) and the test deploys with `with_evm_version("paris")` so the huffc bootstrap has no `PUSH0` either. `npm run generate:huff:paris` builds t = 3 that way (8,127 gas per call, 3 more than the Shanghai output, 4,747 bytes); `FOUNDRY_PROFILE=paris forge test` runs it on a Paris EVM, where the default output fails on `PUSH0` (CI checks that, and that the Amsterdam output fails on Osaka).

#### Amsterdam (EIP-8024)

`node generator/huff/generate.ts --hardfork amsterdam 16 20 24 28` (`npm run generate:huff:amsterdam`) builds the wider permutations with the EIP-8024 `DUPN` / `SWAPN` opcodes, which reach stack slot 235, and the EIP-7954 code size limit of 65,536 bytes. huffc and huff-neo have no mnemonic for them, so `huff/amsterdam/Eip8024.huff` defines `DUP17()` .. `DUP235()` and `SWAP17()` .. `SWAP235()` as `__VERBATIM` bytes (immediate x encodes n = (x + 145) % 256). The whole state stays on the stack; two options use the reach: `gcInternalFrom` leaves the garbage of the first internal rounds in place while the 1024 depth allows (saves the `SWAPn POP` of 5 gas per slot), `diagPush32` keeps as many diag constants as `PUSH32` as the code size allows when the others are in memory (3 gas instead of 6 per use). The generator finds both limits by binary search. The output lives in `huff/amsterdam/t<t>/` with tests in `test/amsterdam/`; these contracts execute on Amsterdam and later only, and `FOUNDRY_PROFILE=amsterdam forge test` (`npm run test:amsterdam`) runs the tests on that EVM (the default profile skips `test/amsterdam`).

| t   | Rf  | Rp  | permutation gas | call gas | max stack depth | max dup | runtime bytes | placement                                               |
| --- | --- | --- | --------------- | -------- | --------------- | ------- | ------------- | ------------------------------------------------------- |
| 16  | 8   | 57  | 48,347          | 48,721   | 999             | 123     | 50,133        | stack, diag as PUSH32, gcInternal from round 44         |
| 20  | 8   | 57  | 61,107          | 61,573   | 995             | 147     | 63,737        | stack, diag as PUSH32, gcInternal from round 34         |
| 24  | 8   | 57  | 74,636          | 75,195   | 989             | 171     | 64,816        | stack, 7 diag in memory, 17 PUSH32, gcInternal from 27  |
| 28  | 8   | 59  | 91,120          | 91,771   | 994             | 63      | 65,414        | stack, 16 diag in memory, 12 PUSH32, gcInternal from 22 |

For comparison the unrolled Yul wrapper of the same widths costs 78,287 (t = 16), 101,842 (t = 20), 125,985 (t = 24) and 154,826 gas (t = 28, 67,097 bytes, over the limit). Runtime bytes are the entry plus the permutation as compiled by huffc; t = 28 is 122 bytes under the limit. t = 20 fits with every diag constant as `PUSH32`; from t = 24 the code size, not the stack, decides how many are loaded from memory.

#### Osaka (split permutations)

`node generator/huff/generate.ts --hardfork osaka 16 20 24 28` (`npm run generate:huff:osaka`) builds the same widths for the legacy opcodes, where two things give: the state does not fit the `DUP16` reach, and the code does not fit the 24,576 byte limit.

- Reach: with the `shadow` schedule option a value the reach cannot `DUP` is stored to a memory slot when it is produced (`DUP1 <off> MSTORE`, 9 gas) and loaded from there (`<off> MLOAD`, 6 gas) whenever it is out of reach. Neither changes the stack, so a permissive pass first records which values need it and the real pass with the same schedule shadows exactly those (slots are reused two rounds later; the simulation refuses a load from a reused slot). In-place rounds then replace the shallow elements first, so the `SWAP` + `POP` of every old slot stays within reach and only the deepest few values per round are shadowed. The option is only tried when no stack-only schedule works, so t <= 12 keeps its output.
- Code size: `huff/split.ts` cuts the permutation at step boundaries (the initial linear layer, then one step per round) into `Part<i>.huff` contracts. Every hop costs the same whatever the cut, so the fewest parts cost the least gas: a greedy pass extends each part as far as the probe schedule fits, the cuts are balanced by bytes, and the generator retries with one part fewer while the per-part option search still fits. Each part is built and checked like a whole permutation (bound tracker, reference check of its own rounds with `permutationSteps`, size check with its entry and tail).
- Linking: part i ends with the state in memory at `[0, 32t)` and `STATICCALL`s part i + 1 with it as calldata, the output lands in the same region and is returned (`returndatasize` must equal 32t). Part i + 1 reduces the words mod PRIME on entry like part 0, so the hand-off carries lazy values. The address of the next part is the 32-byte word the deployer appends to the initcode: the generated `CONSTRUCTOR` keeps it behind the runtime code and `NEXT_PART()` reads it with `CODECOPY` (26 gas), so the artifact is fixed and any deployer links it. `huff/DeployParts.sol` deploys a chain last to first (`DeployParts.deploy(bytes[] initcodes)`), and the generated tests build the initcodes with `HuffDeployer.config().creation_code` and deploy through it.

A hop costs the `MSTORE`s of the state in the caller (t x 9 gas, or an `MLOAD` instead of the `DUP` for shadowed values), the `STATICCALL` with its EIP-2929 account access (2,600 cold, 100 if the part was already touched in the transaction) plus 72 gas of pushes, address read and result check, and the callee's entry (`CALLDATALOAD` + `MOD` per word, 14 gas, 9 more for a word the part shadows, plus the memory expansion). The gas below is measured by forge on one call with every part cold; the generator prints the same numbers from its model within 10 gas.

| t   | Rf  | Rp  | call gas | parts | bytes per part                 | steps per part   | Amsterdam | Yul     |
| --- | --- | --- | -------- | ----- | ------------------------------ | ---------------- | --------- | ------- |
| 16  | 8   | 57  | 65,975   | 2     | 18,764, 17,261                 | 34, 32           | 48,721    | 78,287  |
| 20  | 8   | 57  | 83,892   | 2     | 24,466, 24,471                 | 32, 34           | 61,573    | 101,842 |
| 24  | 8   | 57  | 103,941  | 3     | 24,517, 20,909, 22,752         | 22, 24, 20       | 75,195    | 125,985 |
| 28  | 8   | 59  | 127,733  | 4     | 23,243, 21,766, 21,767, 22,127 | 13, 23, 23, 9    | 91,771    | 154,826 |

The output runs on any fork from Shanghai on (it uses `PUSH0`, nothing newer); it lives in `huff/osaka/t<t>/` with tests in `test/osaka/`, and `FOUNDRY_PROFILE=osaka forge test` (`npm run test:osaka`) runs them on that EVM. The difference to Amsterdam is the shadow traffic, the garbage collection the reach forces, and 2,600 per hop.

The constants and permutation outputs for every generated t match other implementations of the same HorizenLabs instance (gnark-crypto, TACEO, Polygon pil2). See [generator/README.md](../../generator/README.md#evidence-that-the-output-matches-other-implementations) for the links.

### Yul Generator

`generator/yul/generate.ts` builds the Yul libraries from the same `params.ts`, `reference.ts` and `value.ts`:

- `yul/program.ts` emits straight-line Yul. Every operand is a bound-tracked value whose name is the Yul text producing it (a local, a literal, an `mload` or a nested expression), so an `add` is only written where the bound allows it and the whole permutation is checked against the reference before the file is written.
- `yul/schedule.ts` orders the field operations and places the state. Internal round outputs stay lazy (below 2p) with one reduced sum per round, M4 reduces only its two inner temporaries, and the text is shaped for the legacy solc pipeline, which compiles inline assembly literally with the optimizer off: nested expressions instead of assignments, temporaries in blocks that end right after their last use, and for t = 12 a two-temporary M4 and sum chains cut so that the deepest local stays within `DUP16` / `SWAP16` (the generator models the reach of every local). The libraries are inlined into the consumer's contract with the consumer's settings, so `compat-check.sh` compiles a consumer of each library with the legacy pipeline (optimizer off, 200 runs, 1,000,000 runs) and via-IR (200 and 1,000,000 runs, t <= 4 only); CI runs it. From t = 8 a via-IR compile of the single straight-line function needs tens of GB of memory (t = 12 passed 69 GB with solc 0.8.37 before it was stopped), so t = 8 and t = 12 are for the legacy pipeline.

t = 4 keeps `LibPoseidon2Yul` (`hash_1` / `hash_2` / `hash_3` / `poseidon2_core`) and only computes the first output of the last round. Other widths get `yul/t<t>/LibPoseidon2YulT<t>.sol` with `permute(uint256[t] memory state)`, which permutes the array in place after reducing it mod PRIME, and a test in `test/Poseidon2YulT<t>.t.sol` with the reference vectors, input sanitisation and a fuzz against the Huff permutation of the same width.

| t   | Rf  | Rp  | call gas | runtime bytes | state placement                                   |
| --- | --- | --- | -------- | ------------- | ------------------------------------------------- |
| 2   | 8   | 56  | 9,103    | 5,141         | locals                                            |
| 3   | 8   | 56  | 11,403   | 6,092         | locals                                            |
| 4   | 8   | 56  | 15,127   | 14,483        | locals                                            |
| 8   | 8   | 57  | 31,833   | 24,130        | 8 locals, 2 diag constants in memory              |
| 12  | 8   | 57  | 49,892   | 24,105        | 12 locals, 10 diag constants in memory, 2-temp M4 |

Call gas and runtime bytes are those of a contract that inlines the library: `Poseidon2Yul_BN254` for t = 4 (one `hash_*` call) and the `permute(uint256[t])` wrapper deployed by each test otherwise, so they include the ABI decoding and encoding of t words. The gas is above the Huff table because solc inserts a `SWAP` + `POP` per assignment and `DUP`s every operand, and because the diag constants that do not fit the code size as `PUSH32` are loaded from memory (9 gas more each). t = 12 is the largest shipped width: the 2-temporary M4 and the split sum chains are already at the `DUP16` limit, and the code is at the 24,576 byte limit with 10 of 12 diag constants in memory (a consumer of t = 8 or t = 12 built with the optimizer off lands about 200 bytes above it, so such a deployment needs the optimizer). t = 16 generates and passes its vectors with 11 locals and 5 elements kept in the state array (78,287 gas), but its permutation alone is 33 KB of runtime code, so it is not shipped.

## Security Considerations

The `ADDMOD` optimization, while gas-efficient, carries inherent risks related to potential `uint256` overflows if not meticulously handled. Our implementation carefully tracks "dirty" values to ensure that intermediate additions do not exceed `uint256` maximum before a modular reduction. However, it is crucial to understand that **this code has not undergone a formal third-party security audit**.
