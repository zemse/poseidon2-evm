# poseidon2 for evm

implementations of poseidon2 hash function (https://eprint.iacr.org/2023/323.pdf) in solidity, yul and huff.

> attention: code in this repository has not been reviewed for security

## install

```
forge install zemse/poseidon2-evm
npm install poseidon2-evm
```

## usage

contracts:
- solidity: [Poseidon2.sol](./src/Poseidon2.sol)
- yul: [Poseidon2Yul.sol](./src/Poseidon2Yul.sol)
- huff: [Poseidon2.huff](./src/huff/Poseidon2.huff)

any of the above contracts needs to be deployed on the network and then you can make calls to it. here is an example to hash two field elements:

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

## notes

solidity code is inefficient due to lot of memory usage and functions.

yul is generated using [yul-generator.ts](./yul-generator.ts) file and provides an inlined implementation that simply mutates 4 stack variables, uses no memory, which brings a lot of gas savings.

huff uses a dirty approach where SWAPs are avoided which leaves unused elements on stack. EVM allows the stack to grow upto 1024 until we run into stack overflow. for parameters (t=4, rf=8, rp=56), we would leave 4*(8+56) = 256 garbage elements on stack which is much lower than 1024 limit.

## benchmarks

### huff

gas cost for hashing one, two or three elements: 14934

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