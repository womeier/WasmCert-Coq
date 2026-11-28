#!/bin/bash
set -euo pipefail

# Includes the full table.wast, including its currently unsupported typed-ref
# dependencies and script result patterns. Never omit it to report a green run.
root="$(cd "$(dirname "$0")/.." && pwd)"
suite="$root/wast_testsuite"
expected=b497cbb853db21be875bd5c81fcc3334168fb0b4
actual="$(git -C "$suite" rev-parse HEAD)"
if [[ "$actual" != "$expected" ]]; then
  echo "Expected testsuite $expected; found $actual" >&2
  exit 1
fi
python="${WAT2WASM_PYTHON:-python3}"
out="$(mktemp -d "${TMPDIR:-/tmp/opencode}/table64-official.XXXXXXXX")"
echo "Testsuite: $actual"
echo "Binary frontend: $python (wasmtime.wat2wasm)"
echo "Converted WAST retained in: $out"
files=(table table_get table_set table_size table_grow table_fill
       table_copy table_copy_mixed table_init)
for file in "${files[@]}"; do
  "$python" "$root/tests/wast_to_binary.py" \
    "$suite/proposals/wasm-3.0/$file.wast" "$out/$file.wast"
done
cd "$root"
bash run_wast.sh "$out"
