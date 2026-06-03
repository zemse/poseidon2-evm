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
