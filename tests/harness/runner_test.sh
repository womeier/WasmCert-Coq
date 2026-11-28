#!/bin/bash
set -euo pipefail
runner="$(realpath "$1")"
fake="$(realpath "$2")"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
# The runner requires an executable; do not depend on git executable bits.
cp "$fake" "$work/interpreter"
chmod +x "$work/interpreter"
mkdir "$work/cases"
touch "$work/cases/pass.wast"
checks=0
run() {
  EXE="$work/interpreter" JOBS=1 bash "$runner" "$work/cases" > "$work/report" 2>&1
}
if ! run; then cat "$work/report"; exit 1; fi
checks=$((checks + 1))
for kind in fail crash missing malformed duplicate impossible; do
  touch "$work/cases/$kind.wast"
  if run; then
    echo "Runner incorrectly passed $kind alongside a passing test." >&2
    cat "$work/report"
    exit 1
  fi
  rm "$work/cases/$kind.wast"
  checks=$((checks + 1))
done
echo "Conformance runner: $checks/$checks checks passed"
