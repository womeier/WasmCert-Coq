#!/bin/bash
set -euo pipefail
generator="$1"
runner="$2"
export EXE="$3"
export JOBS=1
out="$(mktemp -d "${TMPDIR:-/tmp/opencode}/binary-script-negative.XXXXXXXX")"
python3 "$generator" inline > "$out/inline.wast"
bash "$runner" "$out" inline > "$out/inline.log" 2>&1
grep -q "Result: 1/1" "$out/inline.log"
python3 "$generator" unsupported-reference > "$out/display.wast"
"$EXE" --stage --wast "$out/display.wast" > "$out/display.log" 2>&1
grep -q "Result: 0/1" "$out/display.log"
for mode in invalid malformed unknown trapping nonnull; do
  python3 "$generator" "$mode" > "$out/$mode.wast"
  if bash "$runner" "$out" "$mode" > "$out/$mode.log" 2>&1; then
    echo "Unexpected successful strict run for $mode" >&2
    exit 1
  fi
  expected="Result: 0/1"
  if [[ "$mode" = trapping || "$mode" = nonnull ]]; then expected="Result: 1/2"; fi
  grep -q "$expected" "$out/$mode.log"
  if grep -Eq 'CRASH:|NO RESULT:|PARSE ERROR:' "$out/$mode.log"; then
    cat "$out/$mode.log" >&2
    exit 1
  fi
done
