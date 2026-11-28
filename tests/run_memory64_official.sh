#!/bin/bash
set -euo pipefail

# Explicit non-text conformance entry point. A conversion failure, unsupported
# WAST directive, missing summary or runtime crash must fail the whole run.
root="$(cd "$(dirname "$0")/.." && pwd)"
suite="$root/wast_testsuite"
expected=b497cbb853db21be875bd5c81fcc3334168fb0b4
actual="$(git -C "$suite" rev-parse HEAD)"
if [[ "$actual" != "$expected" ]]; then
  echo "Expected testsuite $expected; found $actual" >&2
  exit 1
fi
python="${WAT2WASM_PYTHON:-python3}"
out="$(mktemp -d "${TMPDIR:-/tmp/opencode}/memory64-official.XXXXXXXX")"
echo "Testsuite: $actual"
echo "Binary frontend: $python (wasmtime.wat2wasm)"
echo "Converted WAST retained in: $out"
files=(address64 align64 endianness64 float_memory64 load64 memory64
       memory_grow64 memory_redundancy64 memory_trap64)
for file in "${files[@]}"; do
  "$python" "$root/tests/wast_to_binary.py" \
    "$suite/proposals/wasm-3.0/$file.wast" "$out/$file.wast"
done
cd "$root"
bash run_wast.sh "$out"
