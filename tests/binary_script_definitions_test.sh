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
grep -q "Result: 1/1" "$out/display.log"
grep -q "legacy diagnostic formatter failed" "$out/display.log"
python3 "$generator" malformed-reference > "$out/malformed-reference.wast"
"$EXE" --stage --wast "$out/malformed-reference.wast" > "$out/malformed-reference.log" 2>&1
grep -q "Result: 0/1" "$out/malformed-reference.log"
grep -q "legacy diagnostic formatter failed" "$out/malformed-reference.log"
python3 "$generator" unknown-reference > "$out/unknown-reference.wast"
"$EXE" --stage --wast "$out/unknown-reference.wast" > "$out/unknown-reference.log" 2>&1
grep -q "Result: 0/1" "$out/unknown-reference.log"
grep -q "legacy diagnostic formatter failed" "$out/unknown-reference.log"
if grep -q "error in parsing module" "$out/unknown-reference.log"; then
  echo "Out-of-scope source reference was rejected as malformed, not invalid" >&2
  exit 1
fi
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
