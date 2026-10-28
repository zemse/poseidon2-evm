# Deployed artifacts

## Generate new artifacts

Examples:

```
./prepare-deploy.sh bn254 yul
./prepare-deploy.sh bn254 huff
```

## Deploy

```
gm deploy deployed-artifacts/bn254-huff/v<n>/Poseidon2huff.out --create2 <salt>
```
