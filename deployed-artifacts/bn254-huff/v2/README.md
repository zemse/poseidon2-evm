## Deterministic deployment

```
eth-vanity create2 ./deployed-artifacts/bn254-huff/v2/Poseidon2huff.json 0xB2542...ff --checksum


=== FOUND ===
Salt:             0x0700000000000000811f3b040000000000000000000000000000000000000000
Contract Address: 0xB25421813D7d7B8001BB19d6b70642A277422eff
Deployer:         0x4e59b44847b379578588920cA78FbF26c0B4956C
Init Code Hash:   0x6e4c320baa9b5b376d94b9fb261b322da55e4662ad410ba2e19973f20a4bea57
```

```
gm deploy ./deployed-artifacts/bn254-huff/v2/Poseidon2huff.out --create2 0x0700000000000000811f3b040000000000000000000000000000000000000000
```

## Deployments

Contract is deployed at `0xB25421813D7d7B8001BB19d6b70642A277422eff` (verified on-chain; CREATE2 binds this address to the init code hash, so any code here is exactly this artifact).

- [Sepolia](https://sepolia.etherscan.io/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)
- [Hoodi](https://hoodi.etherscan.io/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)
- [Arbitrum Sepolia](https://sepolia.arbiscan.io/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)
- [OP Sepolia](https://sepolia-optimism.etherscan.io/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)
- [Base Sepolia](https://sepolia.basescan.org/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)
- [Polygon Amoy](https://amoy.polygonscan.com/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)
- [Scroll Sepolia](https://sepolia.scrollscan.com/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)
- [Monad Testnet](https://testnet.monadvision.com/address/0xB25421813D7d7B8001BB19d6b70642A277422eff)

## Short calldata

A call with 0 to 3 bytes of calldata returns `0x0fcc8f62b28d181b60d780425f6a28111c2de73ab52e084c8c15975a470682d5`, whatever the bytes are. That is not the Poseidon2 value, which the Yul contract returns for the same calldata (`0x003de6b37e6ccfed9e5c029c49d7c7ac43f1170dc1b08dbc74fdb22b848ed244`): below 4 bytes the capacity word `((calldatasize - 4) >> 5) << 64` wraps below zero, and this build adds it to another word without reducing it first. Such calldata is not a call of `IPoseidon2` (a 4-byte selector and at least one 32-byte argument), so `hash_1`, `hash_2`, `hash_3` and every call with 4 bytes of calldata or more are not affected. This contract also accepts a call value, where the Yul contract reverts.

The proofs in [formal-verification](../../../formal-verification/README.md#deployments) cover this runtime code for every calldata (`hashV2_correct`, `hashV2_total`): from 4 bytes on the Poseidon2 value, for 0 to 3 bytes the fixed value above (`hashV2Short`, stated as this code's observed behaviour, not as Poseidon2), each with 14,869 gas for the call frame. `formal-verification/scripts/check-deployed.sh <rpc-url>` checks that the code at the address is the proven one.

The Huff t = 4 source in `src/bn254/huff/t4` is newer than this build and behaves differently off the ABI: it takes the arity from the calldata size alone (1 below `0x44` bytes, 2 at `0x44`, 3 above), so on calldata whose size is not 36, 68 or 100 bytes it can return a different value than this contract and the Yul one.
