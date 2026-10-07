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
| Yul (contract)  | 19,639  | 19,639  | 19,639  |
| Huff (contract) | 12,558  | 12,558  | 12,558  |

## Recommendation

Using the Yul library is recommended for most use cases. It provides the best gas efficiency when inlined into your contracts.

For external calls to deployed contracts, the Huff implementation provides the lowest gas cost.

## Notes on Optimizations

### ADDMOD Optimization

This optimization is used in Yul and Huff implementations. Not used in Solidity.

Using `ADD` is cheaper (3 gas) compared to `ADDMOD` (8 gas) which also needs a prime argument (3 gas to duplicate on stack), saving 11 gas per instance. Using `ADD` instead of `ADDMOD` overflows the value beyond the field domain but we can `MOD` the value or use it with `MULMOD` which outputs a legal value.

Applying this optimization for the BN254 curve is tricky because the PRIME is almost close to uint256 max, which means the value could overflow the uint256 variable, corrupting the state and leading to an incorrect hash value. For other curves with smaller prime fields, this optimization is trivial.

BN254 prime allows adding 4 field values (3 additions, i.e., a + b + c + d < uint256 max). This implementation tracks dirty values in the comments using the notation:

- `0/3` means clean (no pending additions)
- `1/3` means one addition pending
- `2/3` means two additions pending
- `3/3` means no further unsafe additions possible

If there is even a single situation where an unsafe addition could overflow uint256 max, then it is possible for an attacker to vanity mine the input.

### No Stack Scheduling

This optimization is used in Huff. Not used in Yul or Solidity.

The EVM has a stack limit of 1024. Hence, compilers are designed to avoid running into stack overflow by scheduling every element pushed on the stack to be used later. This involves calling a bunch of `SWAP` opcodes to rearrange the stack before calling an internal function.

However, it is cheaper to not rearrange elements on the stack and instead `DUP`licate them in the order we want. This works when we are working with fewer than 16 variables (including temporary) because we have `DUP1` to `DUP16`.

This instance of Poseidon2 has 64 total rounds. Each external round leaves 13 dead values on the stack and each internal round 6, so the stack height reaches 456 for t = 4. For t = 12 the generator reclaims dead slots with `SWAP` + `POP` because the 1024 limit would otherwise be hit.

### Huff Generator

`generator/huff/generate.ts` (shared modules in `generator/`, Huff-specific ones in `generator/huff/`) builds the Huff permutation for a state width t:

- `params.ts` ports the HorizenLabs `poseidon2_rust_params.sage` script: round numbers, Grain LFSR round constants and the internal matrix diagonal with its minimal polynomial check. `test-reference.ts` checks t = 4 against `constants.ts` and the Barretenberg KAT, t = 3 against the HorizenLabs instance, and the round numbers against the paper.
- `reference.ts` is the BigInt reference permutation.
- `huff/emitter.ts` is a symbolic stack simulator. Every value carries an exact upper bound; `ADD` and `MUL` are only emitted when the bound stays below 2^256, otherwise `ADDMOD` / `MULMOD`. It also tracks depth, the deepest `DUP`, gas and bytecode size, and executes the emitted stream on test inputs.
- `huff/schedule.ts` orders the field operations like the hand-written code did (results land on top, operands are pre-placed so results land in place) and tries a few option sets per t (diag constants in memory, garbage collection, two forms of the t = 4k linear layer), keeping the cheapest one that fits.

Generated permutations for t other than 4 live in `huff/t<t>/` with an entry contract (calldata t words, returns t words) and vectors from the reference in `test/Poseidon2T<t>.t.sol`.

| t   | Rf  | Rp  | permutation gas | call gas | max stack depth | max dup | runtime bytes |
| --- | --- | --- | --------------- | -------- | --------------- | ------- | ------------- |
| 2   | 8   | 56  | 6,463           | 6,515    | 276             | 13      | 4,032         |
| 3   | 8   | 56  | 8,049           | 8,124    | 351             | 15      | 4,743         |
| 4   | 8   | 56  | 12,480          | 12,558   | 456             | 16      | 13,192        |
| 8   | 8   | 57  | 25,719          | 25,909   | 889             | 16      | 14,394        |
| 12  | 8   | 57  | 43,912          | 44,194   | 274             | 16      | 23,646        |

Call gas is the Huff contract call measured by forge (t = 4 is `hash_*`, the others are the raw permutation entry). t = 16 and above does not fit a stack-only schedule: the deepest state element plus the PRIME copy under the S-box input already exceeds `DUP16`, so the generator refuses it. For t >= 8 the diag constants are stored in memory once and loaded with `MLOAD`, otherwise the `PUSH32`s exceed the 24,576 byte code size limit.

The constants and permutation outputs for every generated t match other implementations of the same HorizenLabs instance (gnark-crypto, TACEO, Polygon pil2). See [generator/README.md](../../generator/README.md#evidence-that-the-output-matches-other-implementations) for the links.

## Security Considerations

The `ADDMOD` optimization, while gas-efficient, carries inherent risks related to potential `uint256` overflows if not meticulously handled. Our implementation carefully tracks "dirty" values to ensure that intermediate additions do not exceed `uint256` maximum before a modular reduction. However, it is crucial to understand that **this code has not undergone a formal third-party security audit**.
