#!/bin/sh
# Replays declarations through the Lean kernel with `leanchecker` (it ships with the toolchain), in
# a process apart from the elaborator, from the .olean files the build wrote. Fails if the kernel
# rejects one. Run from formal-verification/ after `lake build` (and, for an artifact, after
# scripts/proof.sh has built it):
#   scripts/replay.sh deps                 # every constant of Poseidon2.Deps's import closure
#                                          # (Lean, the Mathlib part, EVMLean) into an empty
#                                          # environment (`leanchecker --fresh`)
#   scripts/replay.sh spec | minpoly | core
#                                          # Poseidon2/Spec/ but MinpolyCheck, Spec/MinpolyCheck,
#                                          # the rest of the library outside Proofs/
#   scripts/replay.sh library              # the four above, one process each
#   scripts/replay.sh committed            # the modules of Poseidon2/Proofs/ outside Generated/
#   scripts/replay.sh huff/osaka/t28 [...] # an artifact's proof modules (its file and its parts)
#   scripts/replay.sh coverage [artifact ...]
#                                          # checks (scripts/ReplayCoverage.lean) that these
#                                          # pieces replay every module of the closure of
#                                          # Poseidon2.Audit, Poseidon2.Proofs.Audit and the
#                                          # artifacts named
# All but `deps` replay each module's own constants on top of its imports, so one piece's
# imports are what another piece replays; `coverage` checks no module is left out.
set -eu
# module names of the .lean files find prints
mods() { sed 's/\.lean$//; s#/#.#g' | sort; }
spec() { find Poseidon2/Spec -name '*.lean' ! -path '*/MinpolyCheck*' | mods; }
core() {
  find Poseidon2 -name '*.lean' ! -path 'Poseidon2/Spec/*' ! -path 'Poseidon2/Proofs/*' | mods
}
committed() { find Poseidon2/Proofs -name '*.lean' ! -path '*/Generated/*' | mods; }
artifact() {
  # an artifact's file is its name with each part capitalised (scripts/Emit.lean, moduleOf)
  file=$(find Poseidon2/Proofs -name '*.lean' |
    grep -ix "Poseidon2/Proofs/\(Generated/\)\{0,1\}$1\.lean" || true)
  if [ -z "$file" ]; then
    echo "no proof of $1; run scripts/proof.sh $1 first" >&2
    exit 1
  fi
  # a module name also selects the modules below it, here the artifact's parts
  echo "${file%.lean}" | sed 's#/#.#g'
}
case ${1:-} in
deps)
  lake env leanchecker --fresh Poseidon2.Deps
  ;;
spec)
  lake env leanchecker $(spec)
  ;;
minpoly)
  lake env leanchecker Poseidon2.Spec.MinpolyCheck
  ;;
core)
  lake env leanchecker $(core)
  ;;
library)
  for p in deps spec minpoly core; do
    echo "replay.sh $p"
    "$0" $p
  done
  ;;
committed)
  lake env leanchecker $(committed)
  ;;
coverage)
  shift
  roots="Poseidon2.Audit Poseidon2.Proofs.Audit"
  arts=
  for art in "$@"; do
    m=$(artifact "$art")
    roots="$roots $m"
    arts="$arts $m"
  done
  lake env lean --run scripts/ReplayCoverage.lean $roots -- fresh:Poseidon2.Deps $(spec) \
    Poseidon2.Spec.MinpolyCheck $(core) $(committed) $arts
  ;;
*)
  for art in "$@"; do
    m=$(artifact "$art")
    lake env leanchecker "$m"
  done
  ;;
esac
