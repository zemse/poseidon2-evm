## Deterministic deployment

```
eth-vanity create2 ./deployed-artifacts/bn254-yul/v2/Poseidon2Yul_Bn254.json 0xB2542 --checksum


=== FOUND ===
Salt:             0x0800000000000000e6af00000000000000000000000000000000000000000000
Contract Address: 0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2
Deployer:         0x4e59b44847b379578588920cA78FbF26c0B4956C
Init Code Hash:   0x3f8b1015894740f2e993c7c9f1cc80e9e8fe66704cc3b1ea678e78b0482cf4ea
```

```
gm deploy ./deployed-artifacts/bn254-yul/v2/Poseidon2Yul_Bn254.json --create2 0x0800000000000000e6af00000000000000000000000000000000000000000000
```

## Verification

Source verified on [Sourcify](https://sourcify.dev) with `exact_match` (full bytecode incl. metadata) on all networks below. Compiler: solc 0.8.30, optimizer enabled (1,000,000 runs), EVM version cancun. No constructor arguments.

## Deployments

Contract is deployed at `0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2` (verified on-chain; CREATE2 binds this address to the init code hash, so any code here is exactly this artifact).

- [Sepolia](https://sepolia.etherscan.io/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
- [Hoodi](https://hoodi.etherscan.io/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
- [Arbitrum Sepolia](https://sepolia.arbiscan.io/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
- [OP Sepolia](https://sepolia-optimism.etherscan.io/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
- [Base Sepolia](https://sepolia.basescan.org/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
- [Polygon Amoy](https://amoy.polygonscan.com/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
- [Scroll Sepolia](https://sepolia.scrollscan.com/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
- [Monad Testnet](https://testnet.monadvision.com/address/0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2)
