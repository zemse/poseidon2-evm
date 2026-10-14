#!/bin/sh
# Rewrites Poseidon2/Bytecode/ from the repository with `poseidon2-gen lean-export`: the Huff
# contracts (Amsterdam from the checked-in sources, Osaka generated in memory), the Yul wrappers
# built by forge at solc optimizer 1,000,000 runs (foundry.toml), 200 runs and off, and the
# deployed v2 artifacts. Run from anywhere; needs forge, cargo and the git submodules. The forge
# builds go to a temporary directory, the repository's out/ and cache/ are not touched.
# `git diff formal-verification/Poseidon2/Bytecode` afterwards shows whether the proofs still
# cover the bytecode the sources compile to.
#
# The remappings are given explicitly: forge's detected ones carry the checkout's absolute path,
# which goes into the solc metadata and so into the metadata hash at the end of the code, and
# the bytes would then depend on where the repository is checked out.
set -eu
cd "$(dirname "$0")/../.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# build <label> [VAR=value...]: the Yul wrappers into $tmp/<label>
build() {
  label=$1
  shift
  env FOUNDRY_AUTO_DETECT_REMAPPINGS=false "$@" forge build \
    src/bn254/yul/Poseidon2Yul.sol test/Poseidon2YulT2.t.sol test/Poseidon2YulT3.t.sol \
    test/Poseidon2YulT8.t.sol test/Poseidon2YulT12.t.sol \
    --remappings forge-std/=lib/forge-std/src/ \
    --remappings foundry-huff/=lib/foundry-huff/src/ \
    --remappings stringutils/=lib/foundry-huff/lib/solidity-stringutils/ \
    --out "$tmp/$label" --cache-path "$tmp/cache-$label"
}
build runs1000000
build runs200 FOUNDRY_OPTIMIZER_RUNS=200
build optimizerOff FOUNDRY_OPTIMIZER=false
cargo run --release --quiet --manifest-path generator-rs/Cargo.toml -- lean-export \
  --yul "runs1000000=$tmp/runs1000000" --yul "runs200=$tmp/runs200" \
  --yul "optimizerOff=$tmp/optimizerOff"
