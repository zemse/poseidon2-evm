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
| Pure Solidity   | 264,090 | 264,836 | 265,733 |
| Yul (contract)  | 20,304  | 20,304  | 20,304  |
| Huff (contract) | 14,845  | 14,845  | 14,845  |

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

This instance of Poseidon2 has 64 total rounds. There are 8 rounds that do `MATRIX_MULTIPLICATION_4X4` and each pushes 19 elements on the stack. The 56 internal rounds each push 7 elements on the stack. It can be estimated that the stack height reaches 549 for these Poseidon2 parameters.

## Security Considerations

The `ADDMOD` optimization, while gas-efficient, carries inherent risks related to potential `uint256` overflows if not meticulously handled. Our implementation carefully tracks "dirty" values to ensure that intermediate additions do not exceed `uint256` maximum before a modular reduction. However, it is crucial to understand that **this code has not undergone a formal third-party security audit**.
