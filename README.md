# Poseidon2 for EVM

Gas-optimized, formally verified implementations of the [Poseidon2 hash function](https://eprint.iacr.org/2023/323.pdf) for the EVM.

## Implementation Details

See impl-specific documentation:

- [BN254 (t = 2 to 28)](src/bn254/README.md)

> Goldilocks support is planned.

## Gas Costs

Call gas of the current sources, each figure proven exact in Lean (see [Formal verification](#formal-verification)).

> The Huff contracts (every width, Amsterdam and Osaka builds) are proven in Lean 4, on their runtime bytecode, to return the Poseidon2 output over BN254 for every input, with exactly the gas below. The Yul contracts carry the same proof for the compiler settings listed in [Formal verification](#formal-verification).

### t = 4 hash (`IPoseidon2`)

| Implementation                                | hash_1 | hash_2 | hash_3 |
| --------------------------------------------- | ------ | ------ | ------ |
| Huff (Amsterdam)                              | 11,837 | 11,879 | 11,919 |
| Yul, solc 0.8.30 via-IR, 1,000,000 runs       | 13,904 | 13,904 | 13,904 |
| Yul, solc 0.8.30 legacy, 1,000,000 runs       | 15,153 | 15,153 | 15,153 |
| Deployed v2 Huff (pre-Amsterdam, below)       | 14,869 | 14,869 | 14,869 |
| Deployed v2 Yul (below)                       | 19,639 | 19,639 | 19,639 |

### Permutation, state width t

| t   | Huff (Amsterdam) | Yul (least-gas setting)   |
| --- | ---------------- | ------------------------- |
| 2   | 5,877            | 7,560 (via-IR, 1M runs)   |
| 3   | 7,626            | 9,505 (via-IR, 1M runs)   |
| 8   | 23,039           | 28,391 (via-IR, 1M runs)  |
| 12  | 33,474           | 43,226 (legacy, 1M runs)  |
| 16  | 43,742           |                           |
| 20  | 53,954           |                           |
| 24  | 64,238           |                           |
| 28  | 75,884           |                           |

Huff is the raw permutation entry (t words in, t words out). Yul is the `permute(uint256[t])` test wrapper, so it includes the ABI decoding and encoding of t words. Each Yul library states its least-gas solc settings in its natspec; with the legacy pipeline at 1,000,000 runs t = 2, 3, 8 cost 8,851, 10,740 and 30,773.

The t = 4 Huff hash takes the arity from the exact calldata size and does not check the selector: 36, 68 or 100 bytes run `hash_1`, `hash_2` or `hash_3`, and any other size fails on an invalid jump, which consumes the gas of the call.

### Compile targets

- Huff: Amsterdam only. The generated source uses the EIP-8024 `DUPN` / `SWAPN` opcodes and the EIP-7954 65,536 byte code limit, so it does not run before Amsterdam. Osaka builds exist only in memory, for the formal verification.
- Yul: solc 0.8.30 with `evmVersion` osaka (the newest it knows); the bytecode runs on Osaka and Amsterdam. The tests run the Amsterdam EVM (`foundry.toml`).

It is recommended to use Yul implementation. Huff is experimental; the deployed Huff contract below is a pre-Amsterdam build. Pure solidity impl is still kept in this repository for reference, but it costs 200k+ gas.

## Deployed Contracts

Contracts are deployed with same address on popular EVM testnets.

### BN254 (t=4, Rf=8, Rp=56)

Both contracts have same interface [IPoseidon2](./src/IPoseidon2.sol).

| Implementation | Address                                    |
| -------------- | ------------------------------------------ |
| Yul            | 0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2 |
| Huff           | 0xB25421813D7d7B8001BB19d6b70642A277422eff |

The deployed Huff contract returns a value that is not the Poseidon2 hash for calldata shorter than 4 bytes, which no `IPoseidon2` call sends (see [its README](deployed-artifacts/bn254-huff/v2/README.md#short-calldata)).

_If you need help deploying the contract on new network, feel free to msg [@zemse](https://t.me/zemse)._

## Usage example

Both contracts implement the [IPoseidon2](./src/IPoseidon2.sol) interface and are live at the same address on popular EVM networks (see [Deployed Contracts](#deployed-contracts) above). Inputs are reduced `mod PRIME` on-chain, so any `uint256` yields a correct, deterministic hash — just point the interface at the address and call it.

```solidity
// Or import it instead: import {IPoseidon2} from "poseidon2-evm/src/IPoseidon2.sol";
interface IPoseidon2 {
    function hash_1(uint256 x) external pure returns (uint256);
    function hash_2(uint256 x, uint256 y) external pure returns (uint256);
    function hash_3(uint256 x, uint256 y, uint256 z) external pure returns (uint256);
}

contract MyContract {
    IPoseidon2 constant POSEIDON2 = IPoseidon2(0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2);

    function someFunction(uint256 left, uint256 right) external view {
        uint256 result = POSEIDON2.hash_2(left, right);
    }
}
```

## Development

Needs [Foundry](https://getfoundry.sh), [huff-neo](https://github.com/cakevm/huff-neo) `hnc` 1.7.1 or later on the PATH (the tests compile the Huff through it) and Rust 1.98 or later for the generators.

- Run tests: forge test
- Generate gas report: ./gas-report.sh
- Check the yul libraries compile for consumers with every compiler mode: ./compat-check.sh
- Generate yul code: npm run generate:yul (or `cargo run --release --manifest-path generator-rs/Cargo.toml -- yul <t>` for one state width)
- Generate huff code: npm run generate:huff (or `cargo run --release --manifest-path generator-rs/Cargo.toml -- huff <t>` for one state width)

Both generators derive the Poseidon2 parameters for any supported state width t (Yul 2, 3, 4, 8, 12; Huff also 16, 20, 24, 28) the same way as the reference sage script, then emit code whose every lazy addition is proven by exact bounds and which is simulated against a reference permutation before anything is written. The t = 4 Yul is `LibPoseidon2Yul` (`hash_1` / `hash_2` / `hash_3`); the other widths are `src/bn254/yul/t<t>/LibPoseidon2YulT<t>.sol` with `permute(uint256[t] memory)`. See [src/bn254/README.md](src/bn254/README.md#huff-generator).

Tests include correctness vectors, fuzz testing against the reference Solidity implementation, and overflow safety checks for the ADDMOD optimization.

## Formal verification

The runtime bytecode of the contracts is formally verified in this scope: Lean 4 theorems, checked by the Lean kernel, state that for any calldata and any call value each of 39 bytecodes returns exactly what a Lean specification of Poseidon2 over BN254 says, with an exact gas cost. The 39 are the Huff permutations and the t = 4 Huff hash for Amsterdam and Osaka, the Yul contracts as compiled by solc 0.8.30 at three legacy optimizer settings and, for t = 2, 3, 4 and 8, with via-IR at 1,000,000 runs (for t = 2, 3, 8, 12 the test wrappers `Poseidon2YulT<t>`, not a contract that inlines the library), and the two deployed contracts above. The EVM semantics is EVMLean's Cancun model, with an EIP-8024 overlay for the Amsterdam builds; that Osaka and Amsterdam behave the same on the opcodes used is read from execution-specs, not proven. Trusted are the Lean kernel, EVMLean, the Lean specification, the fork tables transcribed from execution-specs, Mathlib's prebuilt files and the round numbers; not huff-neo, solc or the generators. See [formal-verification/README.md](formal-verification/README.md) for the exact statements, the trusted base and the limits (no external reference exists for t = 20, 24, 28).

Inputs are reduced `mod PRIME`, not rejected, so `x` and `x + PRIME` (and `x + 2 * PRIME`, ..., below `2^256`) give the same hash. If your application needs different inputs to give different hashes, check that each input is below `PRIME` before hashing.

## Security

**Not yet audited.** These implementations have not undergone a formal third-party security audit. Review the code before using in production. Also see [SECURITY.md](./SECURITY.md).

## License

MIT
