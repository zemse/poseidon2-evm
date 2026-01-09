# Deployed artifacts

## Generate new artifacts

Examples:

```
./prepare-deploy.sh bn254 yul minor
./prepare-deploy.sh bn254 huff patch
```

## Deploy

```
gm deploy deployed-artifacts/bn254-huff/v1.1.0/Poseidon2.out --create2 <salt>
```
