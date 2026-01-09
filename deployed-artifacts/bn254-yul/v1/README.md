## Deterministic deployment

```
eth-vanity create2 ./deployed-artifacts/bn254-yul/v1/Poseidon2Yul_Bn254.json 0xB2541... --checksum


=== FOUND ===
Salt:             0x0b00000000000000254810000000000000000000000000000000000000000000
Contract Address: 0xB25415b1512b1f179978b3028645Dbd6E1AaE20e
Deployer:         0x4e59b44847b379578588920cA78FbF26c0B4956C
Init Code Hash:   0xdce460b66d649f08764debb9791d8a5584fb587fc4bd7bd4daa970c8f3b98368
```

```
gm deploy ./deployed-artifacts/bn254-yul/v1/Poseidon2Yul_Bn254.json --create2 0x0b00000000000000254810000000000000000000000000000000000000000000
```

## Txs

Contract is deployed at 0xB25415b1512b1f179978b3028645Dbd6E1AaE20e

- [Sepolia](https://sepolia.etherscan.io/tx/0x9ef51c5a172b8e38ac601fc4ac1a0ae5b5047a015bacdda893fe4323b4be0a0b)
- [Hoodi](https://hoodi.etherscan.io/tx/0x392c5aa5d6e6148175d7e11c0a878836a156ad98dfbf4c28f9194220ec3aca74)
- [Arbitrum Sepolia](https://sepolia.arbiscan.io/tx/0xe3c30b19d4f7ac0424ca23e4c45ffb561353cd8f5502da647900972130e25cd3)
- [OP sepolia](https://sepolia-optimism.etherscan.io/tx/0x024b93d864f0aab5bd24e01d667ba042ed4251a521ab9a1abadeceec1345364c)
- [Base Sepolia](https://sepolia.basescan.org/tx/0x74f8dd2cd39d74345da857691522200e2a82bbe8ffdc147b343ea12ff0320b44)
- [Polygon Amoy](https://amoy.polygonscan.com/tx/0xe5396fb26e427b7ea503db675c6b2567d5c8247ddf60990f4c9bb262c8876dfb)
- [Scroll Sepolia](https://sepolia.scrollscan.com/tx/0x5b22fe81afbb55cbcde9f60eb2c0fa0ff46890b3dde704e16b9c9759f24bcc1a)
- [Monad Testnet](https://testnet.monadvision.com/tx/0x308ff40863b5ec39f018bbeb466947f379d746186d8d10f2a8b036ef8d3b87b7)
