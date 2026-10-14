#!/bin/sh
# Checks whether the code at an address is one of the runtime bytecodes the proofs are about:
# fetches it with `cast code` (eth_getCode), hashes it with `cast keccak` and looks the hash up
# among the keccak256 recorded in Poseidon2/Bytecode/ (Bytecode/Keccak.lean checks each against
# its bytes at build time). Read-only; needs cast (Foundry). Run from anywhere:
#   scripts/check-deployed.sh <rpc-url> [address ...]
# Without an address it checks the two deployed v2 contracts of deployed-artifacts/ (Yul, Huff).
# Prints one line per address with the matching artifact, its kind (Spec/Interface.lean) and the
# fork its theorems need; warns when that is Amsterdam (Huff Amsterdam uses EIP-8024 DUPN / SWAPN,
# which halt on earlier forks). Exits 1 if one has no code or matches no artifact.
set -eu
if [ $# -lt 1 ]; then
  echo "usage: $0 <rpc-url> [address ...]" >&2
  exit 2
fi
rpc=$1
shift
if [ $# -eq 0 ]; then
  set -- 0xB2542195Ad96AcfBC962C48A97D7640A9F5386D2 0xB25421813D7d7B8001BB19d6b70642A277422eff
fi
cd "$(dirname "$0")/.."
# one line per artifact: keccak256, name, Lean module, kind
table=$(find Poseidon2/Bytecode -name '*.lean' | sort | while read -r f; do
  awk -v mod="$(echo "${f%.lean}" | tr / .)" '
    $1 == "name" && $2 == ":=" { gsub(/"/, "", $3); name = $3 }
    $1 == "keccak" && $2 == ":=" { hash = tolower($3) }
    $1 == "kind" && $2 == ":=" { kind = $3; sub(/^\./, "", kind) }
    END { if (name != "" && hash != "") print hash, name, mod, kind }' "$f"
done)
if [ -z "$table" ]; then
  echo "no artifacts found under Poseidon2/Bytecode" >&2
  exit 2
fi
status=0
for addr in "$@"; do
  if ! code=$(cast code --rpc-url "$rpc" "$addr"); then
    echo "$addr: eth_getCode failed"
    status=1
    continue
  fi
  if [ "$code" = "0x" ] || [ -z "$code" ]; then
    echo "$addr: no code"
    status=1
    continue
  fi
  size=$(((${#code} - 2) / 2))
  hash=$(cast keccak "$code" | tr 'A-F' 'a-f')
  # the same code can be exported twice (Huff t = 3 is the same on both forks)
  match=$(echo "$table" | awk -v h="$hash" '
    $1 == h { s = s (s == "" ? "" : ", ") $2 " (" $3 ", " $4 ")" }
    END { print s }')
  if [ -n "$match" ]; then
    echo "$addr: $size bytes, keccak256 $hash, matches $match"
    # every artifact but Huff Amsterdam t != 3 runs no DUPN / SWAPN (its `cancun` theorem, on
    # EVMLean's Cancun semantics); Huff t = 3 has the same bytes on both forks
    case $match in
    *huff/osaka/* | *yul/* | *deployed/*)
      echo "  fork: Cancun or later. Proven on EVMLean's Cancun semantics; that later forks agree on"
      echo "  the opcodes used is read from execution-specs, not proven."
      ;;
    *)
      echo "  fork: Amsterdam (EIP-8024 DUPN / SWAPN). WARNING: the theorems hold only on a chain"
      echo "  with EIP-8024; on Osaka or earlier these opcodes halt. Confirm the chain supports it."
      ;;
    esac
  else
    echo "$addr: $size bytes, keccak256 $hash, matches no proven artifact"
    status=1
  fi
done
exit $status
