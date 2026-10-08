#!/bin/bash

# Compile a consumer of every generated Yul library with the compiler settings
# a downstream project may use: legacy pipeline with the optimizer off and on
# (200 and 1,000,000 runs) and via-IR with the optimizer on. The libraries
# are internal and inlined into the consumer, so the stack and code size
# limits apply there. via-IR is only checked for t <= 4: from t = 8 it needs
# tens of GB of memory. Usage: ./compat-check.sh [library.sol ...]

set -u
cd "$(dirname "$0")"

SOLC=0.8.30
LIBS=("$@")
if [ ${#LIBS[@]} -eq 0 ]; then
  LIBS=(src/bn254/yul/LibPoseidon2Yul.sol src/bn254/yul/t*/LibPoseidon2YulT*.sol)
fi

# name: via_ir optimizer runs
MODES=(
  "legacy-noopt false false 200"
  "legacy-200 false true 200"
  "legacy-1m false true 1000000"
  "via-ir-200 true true 200"
  "via-ir-1m true true 1000000"
)

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/src"
cat > "$WORK/foundry.toml" <<TOML
[profile.default]
src = "src"
out = "out"
libs = []
evm_version = "cancun"
TOML

failed=0
for lib in "${LIBS[@]}"; do
  name=$(basename "$lib" .sol)
  cp "$lib" "$WORK/src/$name.sol"
  if [ "$name" = "LibPoseidon2Yul" ]; then
    cat > "$WORK/src/Consumer.sol" <<SOL
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.13;
import {LibPoseidon2Yul} from "./LibPoseidon2Yul.sol";
contract Consumer {
    function h(uint256 a, uint256 b) external pure returns (uint256) {
        return LibPoseidon2Yul.hash_2(a, b);
    }
}
SOL
  else
    t=${name#LibPoseidon2YulT}
    cat > "$WORK/src/Consumer.sol" <<SOL
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.13;
import {$name} from "./$name.sol";
contract Consumer {
    function permute(uint256[$t] memory state) external pure returns (uint256[$t] memory) {
        $name.permute(state);
        return state;
    }
}
SOL
  fi
  for mode in "${MODES[@]}"; do
    read -r label via_ir optimizer runs <<< "$mode"
    if [ "$via_ir" = true ] && [[ "$name" =~ T(8|12)$ ]]; then
      echo "skip $name $label (via-IR needs tens of GB of memory from t = 8)"
      continue
    fi
    out=$(cd "$WORK" && FOUNDRY_VIA_IR=$via_ir FOUNDRY_OPTIMIZER=$optimizer FOUNDRY_OPTIMIZER_RUNS=$runs \
      forge build --use $SOLC --force --sizes 2>&1)
    if echo "$out" | grep -q "Compiler run successful"; then
      size=$(echo "$out" | awk -F'|' '/\| Consumer /{gsub(/[ ,]/, "", $3); print $3}')
      note=""
      [ "${size:-0}" -gt 24576 ] && note=", over the 24,576 byte limit"
      echo "ok   $name $label (consumer runtime $size bytes$note)"
    else
      echo "FAIL $name $label"
      echo "$out" | grep -iE "error" | head -3 | sed 's/^/     /'
      failed=1
    fi
  done
  rm -f "$WORK/src/$name.sol"
done
exit $failed
