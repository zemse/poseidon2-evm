#!/bin/sh
# Rewrites Poseidon2/Bytecode/ from the repository with `poseidon2-gen lean-export`: the Huff
# contracts (Amsterdam from the checked-in sources, Osaka generated in memory), the Yul wrappers
# built by forge at solc optimizer 1,000,000 runs (foundry.toml), 200 runs and off,
# `Poseidon2Yul_BN254` and the t = 2, 3, 8 wrappers with via-IR at 1,000,000 runs (the least-gas
# setting the libraries' natspec names for them; t = 12 is least with the legacy pipeline), and
# the deployed v2 artifacts. Run from anywhere; needs forge, cargo and the git submodules. The
# forge builds go to a temporary directory, the repository's out/ and cache/ are not touched.
# `git diff formal-verification/Poseidon2/Bytecode` afterwards shows whether the proofs still
# cover the bytecode the sources compile to.
#
# No remappings: these sources import no library, and forge's detected ones carry the checkout's
# absolute path, which goes into the solc metadata and so into the metadata hash at the end of
# the code, and the bytes would then depend on where the repository is checked out.
set -eu
cd "$(dirname "$0")/../.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# build <label> <widths> [VAR=value...]: Poseidon2Yul_BN254 and the wrappers of <widths> into
# $tmp/<label>
build() {
  label=$1
  files=src/bn254/yul/Poseidon2Yul.sol
  for t in $2; do files="$files test/wrappers/Poseidon2YulT$t.sol"; done
  shift 2
  # shellcheck disable=SC2086
  env FOUNDRY_AUTO_DETECT_REMAPPINGS=false "$@" forge build $files \
    --out "$tmp/$label" --cache-path "$tmp/cache-$label"
}
build runs1000000 "2 3 8 12"
build runs200 "2 3 8 12" FOUNDRY_OPTIMIZER_RUNS=200
build optimizerOff "2 3 8 12" FOUNDRY_OPTIMIZER=false
build viaIrRuns1000000 "2 3 8" FOUNDRY_VIA_IR=true
cargo run --release --quiet --manifest-path generator-rs/Cargo.toml -- lean-export \
  --yul "runs1000000=$tmp/runs1000000" --yul "runs200=$tmp/runs200" \
  --yul "optimizerOff=$tmp/optimizerOff" --yul "viaIrRuns1000000:2,3,8=$tmp/viaIrRuns1000000"
