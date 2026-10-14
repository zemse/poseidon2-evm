#!/bin/sh
# Kernel-checks exported artifacts: writes each proof with scripts/Emit.lean, then builds it.
# The 17 small artifacts (t <= 4 and the deployed v2) have committed proofs in Poseidon2/Proofs/,
# which this rewrites (so `git diff` shows a stale one); the 18 large ones go to
# Poseidon2/Proofs/Generated/ (not committed) as a chain of parts, see the README.
# Run from formal-verification/ after `lake build`:
#   LEAN_NUM_THREADS=1 scripts/proof.sh huff/amsterdam/t28 [more artifacts]
#   scripts/proof.sh --list [small | large]   # artifact names
set -eu
small() {
  case $1 in
  huff/*/t2 | huff/*/t3 | huff/*/t4 | yul/*/t2 | yul/*/t3 | yul/*/t4 | deployed/*) return 0 ;;
  *) return 1 ;;
  esac
}
if [ "${1:-}" = "--list" ]; then
  for art in $(grep -ho 'name := "[^"]*"' Poseidon2/Bytecode/Deployed/*.lean \
    Poseidon2/Bytecode/Huff/*/*.lean Poseidon2/Bytecode/Yul/*/*.lean |
    sed 's/name := "\(.*\)"/\1/' | sort); do
    case ${2:-} in
    small) if small "$art"; then echo "$art"; fi ;;
    large) if ! small "$art"; then echo "$art"; fi ;;
    *) echo "$art" ;;
    esac
  done
  exit 0
fi
for art in "$@"; do
  if small "$art"; then
    out=Poseidon2/Proofs seg=8000 spec=100 per=1000
  else
    out=Poseidon2/Proofs/Generated seg=1000 spec=10 per=3
  fi
  mod=$(OUT=$out ART=$art SEG=$seg SPEC=$spec PER=$per lake env lean --tstack=1000000 scripts/Emit.lean |
    sed -n "s/^module //p")
  if [ -z "$mod" ]; then
    echo "no artifact named $art" >&2
    exit 1
  fi
  lake build "$mod"
done
