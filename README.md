# Poseidon2 for EVM

Gas-optimized implementations of the [Poseidon2 hash function](https://eprint.iacr.org/2023/323.pdf) for the EVM.

## Implementation Details

See impl-specific documentation:

- [BN254 (t=4, Rf=8, Rp=56)](src/bn254/README.md)

> Goldilocks support is planned.

## Gas Costs

| Implementation | hash_1 | hash_2 | hash_3 |
| -------------- | ------ | ------ | ------ |
| Yul            | 15,152 | 15,152 | 15,152 |
| Huff           | 11,895 | 11,902 | 11,975 |

It is recommended to use Yul implementation. Huff is experimental, and the Huff source targets Amsterdam (EIP-8024 `DUPN` / `SWAPN`); the deployed Huff contract below is a pre-Amsterdam build. Pure solidity impl is still kept in this repository for reference, but it costs 200k+ gas.

## Deployed Contracts

Contracts are deployed with same address on popular EVM testnets.

### BN254 (t=4, Rf=8, Rp=56)

Both contracts have same interface [IPoseidon2](./src/IPoseidon2.sol).

| Implementation | Address                                    |
| -------------- | ------------------------------------------ |
| Yul            | 0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2 |
| Huff           | 0xB25421813D7d7B8001BB19d6b70642A277422eff |

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

- Run tests: forge test
- Generate gas report: ./gas-report.sh
- Check the yul libraries compile for consumers with every compiler mode: ./compat-check.sh
- Generate yul code: npm run generate:yul (or `node generator/yul/generate.ts <t>` for one state width, node 24+)
- Generate huff code: npm run generate:huff (or `node generator/huff/generate.ts <t>` for one state width)

Both generators derive the Poseidon2 parameters for any supported state width t (2, 3, 4, 8, 12) the same way as the reference sage script, then emit code whose every lazy addition is proven by exact bounds and which is simulated against a BigInt reference permutation before anything is written. The t = 4 Yul is `LibPoseidon2Yul` (`hash_1` / `hash_2` / `hash_3`); the other widths are `src/bn254/yul/t<t>/LibPoseidon2YulT<t>.sol` with `permute(uint256[t] memory)`. See [src/bn254/README.md](src/bn254/README.md#huff-generator).

Tests include correctness vectors, fuzz testing against the reference Solidity implementation, and overflow safety checks for the ADDMOD optimization.

## Security

**Not yet audited.** These implementations have not undergone a formal third-party security audit. Review the code before using in production. Also see [SECURITY.md](./SECURITY.md).

## License

MIT
