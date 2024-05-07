# poseidon2

solidity implementation of poseidon2 hash function (https://eprint.iacr.org/2023/323.pdf)

## usage

### though contract

the `Poseidon2` contract needs to be deployed on the network and then you can make calls to it.

```solidity
import {IPoseidon2} from "poseidon2/IPoseidon2.sol";

contract MyContract {
    function myFunction() external returns (uint256) {
        uint256 result = 0xPoseidon2ContractAddress.call(
            abi.encode(
                0x1762d324c2db6a912e607fd09664aaa02dfe45b90711c0dae9627d62a4207788,
                0x1047bd52da536f6bdd26dfe642d25d9092c458e64a78211298648e81414cbf35
            )
        );
        return result;
    }
}
```

## yul benchmarks

| num elements | est gas   |
|--------------|-----------|
| hash_1       | 27517    |
| hash_2       | 27531    |
| hash_3       | 28127    |

## solidity benchmarks

| num elements | est gas   |
|--------------|-----------|
| hash_1       | 219544    |
| hash_2       | 220018    |
| hash_3       | 220641    |
| hash 4       | 416486    |
| hash 5       | 417197    |
| hash 6       | 417952    |
| hash 7       | 604599    |
| hash 8       | 605311    |
| hash 9       | 606064    |
| hash 10      | 792604    |