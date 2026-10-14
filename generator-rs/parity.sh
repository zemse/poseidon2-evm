#!/usr/bin/env bash
# Runs the TypeScript and the Rust generators into separate temporary copies
# of the repository and diffs every file under src/ and test/ byte for byte,
# plus the logged lines, before forge fmt (identical raw output stays
# identical after it).
#
#   generator-rs/parity.sh [amsterdam] [osaka] [paris] [yul]   (default: all)
#
# The TS runs go in parallel in the background; the osaka one takes ~65 min.
# PARITY_KEEP=1 keeps the temporary directory.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
targets=("$@")
[ ${#targets[@]} -eq 0 ] && targets=(amsterdam osaka paris yul)

args() {
  case "$1" in
    amsterdam) echo "huff 2 3 4 8 12 16 20 24 28" ;;
    osaka) echo "huff --hardfork osaka 2 3 4 8 12 16 20 24 28" ;;
    paris) echo "huff --hardfork paris 3" ;;
    yul) echo "yul 2 3 4 8 12" ;;
    *) echo "unknown target: $1 (amsterdam, osaka, paris, yul)" >&2; exit 2 ;;
  esac
}

for target in "${targets[@]}"; do args "$target" > /dev/null; done

cargo build --release --quiet --manifest-path "$root/generator-rs/Cargo.toml"
bin="$root/generator-rs/target/release/poseidon2-gen"

tmp="$(mktemp -d)"
if [ "${PARITY_KEEP:-}" = 1 ]; then
  echo "temporary copies in $tmp"
else
  trap 'rm -rf "$tmp"' EXIT
fi

copy() {
  rsync -a --exclude /.git --exclude /out --exclude /cache --exclude /node_modules \
    --exclude /generator-rs/target "$root/" "$1/"
}

# run <dir> <log> <command...>: the command in dir, its wall-clock seconds
# to <log>.time
run() {
  local dir="$1" log="$2"
  shift 2
  touch "$log.start"
  local TIMEFORMAT=%R
  { time (cd "$dir" && "$@" > "$log" 2> "$log.err"); } 2> "$log.time"
}

pids=()
for target in "${targets[@]}"; do
  copy "$tmp/ts-$target"
  copy "$tmp/rs-$target"
  # shellcheck disable=SC2046
  script=generator/$(args "$target" | cut -d' ' -f1)/generate.ts
  # shellcheck disable=SC2046
  run "$tmp/ts-$target" "$tmp/ts-$target.log" node "$script" $(args "$target" | cut -d' ' -f2-) &
  pids+=($!)
done

for target in "${targets[@]}"; do
  # shellcheck disable=SC2046
  run "$tmp/rs-$target" "$tmp/rs-$target.log" "$bin" $(args "$target")
done
for pid in "${pids[@]}"; do wait "$pid"; done

status=0
for target in "${targets[@]}"; do
  # the files the TS run wrote (rsync keeps the older times of the copy)
  files=$(cd "$tmp/ts-$target" && find src test -type f -newer "$tmp/ts-$target.log.start" | wc -l | tr -d ' ')
  if diff -r "$tmp/ts-$target/src" "$tmp/rs-$target/src" > "$tmp/$target.diff" &&
    diff -r "$tmp/ts-$target/test" "$tmp/rs-$target/test" >> "$tmp/$target.diff" &&
    diff "$tmp/ts-$target.log" "$tmp/rs-$target.log" >> "$tmp/$target.diff"; then
    result=identical
  else
    result=DIFFERENT
    status=1
  fi
  echo "$target: $files files $result (ts $(cat "$tmp/ts-$target.log.time") s, rust $(cat "$tmp/rs-$target.log.time") s)"
  [ "$result" = identical ] || head -40 "$tmp/$target.diff"
done
exit $status
