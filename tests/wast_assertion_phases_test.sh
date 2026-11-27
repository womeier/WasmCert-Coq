#!/bin/bash
# Wrong failure phases must fail the assertion, not be counted as passing.
set -euo pipefail
runner=$(realpath "$1")
export EXE
EXE=$(realpath "$2")
export JOBS=1
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

while IFS= read -r assertion; do
  echo "$assertion" > "$tmp/probe.wast"
  if bash "$runner" "$tmp" > "$tmp/output" 2>&1; then
    echo "Incorrectly accepted assertion: $assertion" >&2
    cat "$tmp/output" >&2
    exit 1
  fi
  # A crash or missing summary does not demonstrate phase discrimination.
  if ! grep -q 'Result: 0/1' "$tmp/output"; then
    echo "Probe did not finish with exactly one failed assertion: $assertion" >&2
    cat "$tmp/output" >&2
    exit 1
  fi
done <<'EOF'
(assert_malformed (module (func (result i32))) "")
(assert_invalid (module binary "") "")
(assert_invalid (module (import "absent" "f" (func))) "")
(assert_malformed (module (func $s unreachable) (start $s)) "")
(assert_unlinkable (module (func $s unreachable) (start $s)) "")
(assert_trap (module (import "absent" "f" (func))) "")
EOF
