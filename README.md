# Poseidon2 for EVM

Gas-optimized implementations of the [Poseidon2 hash function](https://eprint.iacr.org/2023/323.pdf) for the EVM.

## Implementation Details

See impl-specific documentation:

- [BN254 (t=4, Rf=8, Rp=56)](src/bn254/README.md)

> Goldilocks support is planned.

## Gas Costs

| Implementation | hash_1 | hash_2 | hash_3 |
| -------------- | ------ | ------ | ------ |
| Yul            | 20,304 | 20,304 | 20,304 |
| Huff           | 14,845 | 14,845 | 14,845 |

It is recommended to use Yul implementation. Huff is experimental. Pure solidity impl is still kept in this repository for reference, but it costs 200k+ gas.

## Deployed Contracts

Contracts are deployed with same address on popular EVM testnets.

### BN254 (t=4, Rf=8, Rp=56)

Both contracts have same interface [IPoseidon2](./src/IPoseidon2.sol).

| Implementation | Address                                    |
| -------------- | ------------------------------------------ |
| Yul            | 0xB25415b1512b1f179978b3028645Dbd6E1AaE20e |
| Huff           | 0xB2541a90d8c72C6CfD85bC4E9e85B1595CAc00ff |

_If you need help deploying the contract on new network, feel free to msg [@zemse](https://t.me/zemse)._

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
    function myFunction() external {
        uint left;
        uint right;

        // Calls the globally deployed Yul contract
        // Checks that left and right are valid field elements
        uint result = Poseidon2.hash_2(left, right);
    }

    function myFunction2() external pure returns (uint256) {
        uint left;
        uint right;

        // Explicitly use experimental Huff contract lowest gas
        // Does not check if left and right are invalid field elements, this
        // results incorrect hash value.
        uint result = Poseidon2.hash_2_huff_unchecked(secret, nullifier);
    }
}
```

### Advanced: Direct Interface

Copy the interface into your project [IPoseidon2.sol](./src/IPoseidon2.sol) and use it.

```solidity
interface IPoseidon2 {
    function hash_2(uint256 x, uint256 y) external pure returns (uint256);
}

contract MyContract {
    function someFunction() external {
        // yul contract is deployed on most testnets
        address poseidon2addy = 0xB25415b1512b1f179978b3028645Dbd6E1AaE20e;

        uint left;
        uint right;

        // Makes direct call to the contract. But you need to make sure inputs i.e.
        // left & right are valid field elements (< PRIME).
        uint result = IPoseidon2(poseidon2addy).hash_2(left, right);
    }
}
```

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
