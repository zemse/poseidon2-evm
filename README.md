# poseidon2 for evm

implementations of poseidon2 hash function (https://eprint.iacr.org/2023/323.pdf) in solidity, yul and huff.

## usage

the `Poseidon2` contract needs to be deployed on the network and then you can make calls to it. here is an example to hash two field elements:

```solidity
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

## benchmarks

### huff

gas cost for hashing one, two or three elements: 16949 

### yul benchmarks

gas cost for hasing one, two or three elements: 27517

### solidity benchmarks

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