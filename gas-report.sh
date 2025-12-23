#!/bin/bash

# Run tests with traces and extract actual internal gas
# Only keep one entry per contract::function combination

# This approach produces same values from forge test --gas-report
# but it is difficult to have huff contracts included in gas report

OUTPUT=$(forge test --match-contract Poseidon2Test -vvvv 2>&1 | \
  grep -E "^\s+├─ \[\d+\] (Poseidon2|Poseidon2Yul|Poseidon2Huff)::(hash_1|hash_2|hash_3|fallback)" | \
  sed 's/.*├─ \[\([0-9]*\)\] \(.*\)::\([a-z_0-9]*\).*/\2:\3: \1 gas/' | \
  sort -u)

echo "$OUTPUT" | tee gas-report
