#!/bin/sh
# Compares the EIP-8024 overlay (Poseidon2/Evm/Eip8024.lean) with revm (Amsterdam) on the corpus
# of programs `poseidon2-gen eip8024-corpus` writes (generator-rs/src/eip8024.rs): every
# DUPN / SWAPN / EXCHANGE immediate at the stack boundaries, the immediate cut by the end of the
# code, the gas boundary, the EIP's execution tests, jumps into immediates. Dev mode, not a proof.
# Run from formal-verification/ after `lake build`:
#   scripts/eip8024-diff.sh [corpus file]
set -eu
out=${1:-.lake/eip8024-corpus.txt}
cargo run --release --quiet --manifest-path ../generator-rs/Cargo.toml -- eip8024-corpus --out "$out"
lake env lean --run scripts/Eip8024Diff.lean "$out"
