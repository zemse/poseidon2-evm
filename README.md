# Poseidon2 for EVM

Gas-optimized implementations of the [Poseidon2 hash function](https://eprint.iacr.org/2023/323.pdf) for the EVM. [Updates on TG](https://t.me/poseidon2_evm)

## Implementation Details

See impl-specific documentation:

- [BN254 (Rf=8, Rp=56)](src/bn254/README.md)

> Goldilocks support is planned.

## Gas Costs

| Implementation | hash_1  | hash_2  | hash_3  | Notes                     |
| -------------- | ------- | ------- | ------- | ------------------------- |
| Solidity       | 264,090 | 264,836 | 265,733 | Reference implementation  |
| Yul            | 20,304  | 20,304  | 20,304  | **Recommended** optimised |
| Huff           | 14,845  | 14,845  | 14,845  | Heavy optimised           |

It is recommended to use yul implementation.

## Usage example

### Recommended: Helper Library

1. Install the dependency.

```bash
# Foundry
forge install zemse/poseidon2-evm

# npm
npm install poseidon2-evm
```

2. Import the file

```solidity
import {Poseidon2} from "poseidon2-evm/src/bn254/Poseidon2.sol";

contract MyContract {
    function someWork() external {
        uint left;
        uint right;

        // Default: calls the globally deployed Yul contract with checked input
        uint result = Poseidon2.hash_2(left, right);
    }

    function someExperiment() external pure returns (uint256) {
        uint left;
        uint right;

        // Explicitly use Huff contract (lowest gas, unchecked)
        uint result = Poseidon2.hash_2_huff_unchecked(secret, nullifier);
    }
}
```

### Alternative: Direct Interface

Copy the interface into your project [IPoseidon2.sol](./src/IPoseidon2.sol) and use it.

```solidity
interface IPoseidon2 {
    function hash_2(uint256 x, uint256 y) external pure returns (uint256);
}

contract MyContract {
    function someWork() external {
        uint left;
        uint right;

        // Makes direct call to the contract. But you need to make sure inputs i.e.
        // left & right are valid field elements (< PRIME).
        uint result = IPoseidon2(0xDeployedAddress).hash_2(left, right);
    }
}
```

## Deployed Contracts

Contracts are deployed with same address on all EVM networks.

### BN254 (Rf=8, Rp=56)

| Implementation | Address |
| -------------- | ------- |
| Yul            | TODO    |
| Huff           | TODO    |

## Development

- Run tests: forge test
- Generate gas report: ./gas-report.sh
- Generate yul code: npm run generate:yul
- Generare huff code: npm run generate:huff

Tests include correctness vectors, fuzz testing against the reference Solidity implementation, and overflow safety checks for the ADDMOD optimization.

## Security

**Not yet audited.** These implementations have not undergone a formal third-party security audit. Review the code before using in production. Also see [SECURITY.md](./SECURITY.md).

## License

MIT
