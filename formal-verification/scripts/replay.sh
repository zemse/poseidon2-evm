#!/bin/sh
# Replays declarations through the Lean kernel with `leanchecker` (it ships with the toolchain), in
# a process apart from the elaborator, from the .olean files the build wrote. Fails if the kernel
# rejects one. Run from formal-verification/ after `lake build` (and, for an artifact, after
# scripts/proof.sh has built it):
#   scripts/replay.sh library              # every constant of Poseidon2.Audit's import closure:
#                                          # Lean, Mathlib, EVMLean, all of Poseidon2/ but Proofs/
#   scripts/replay.sh committed            # the modules of Poseidon2/Proofs/ outside Generated/
#   scripts/replay.sh huff/osaka/t28 [...] # an artifact's proof modules (its file and its parts)
# The last two replay each module's own constants on top of its imports, so the rest of the
# closure is what `library` replays.
set -eu
case ${1:-} in
library)
  lake env leanchecker --fresh Poseidon2.Audit
  ;;
committed)
  lake env leanchecker $(find Poseidon2/Proofs -name '*.lean' ! -path '*/Generated/*' |
    sed 's/\.lean$//; s#/#.#g' | sort)
  ;;
*)
  for art in "$@"; do
    # an artifact's file is its name with each part capitalised (scripts/Emit.lean, moduleOf)
    file=$(find Poseidon2/Proofs -name '*.lean' |
      grep -ix "Poseidon2/Proofs/\(Generated/\)\{0,1\}$art\.lean" || true)
    if [ -z "$file" ]; then
      echo "no proof of $art; run scripts/proof.sh $art first" >&2
      exit 1
    fi
    # a module name also selects the modules below it, here the artifact's parts
    lake env leanchecker "$(echo "${file%.lean}" | sed 's#/#.#g')"
  done
  ;;
esac
