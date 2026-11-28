#!/bin/bash
# Actual binary parse -> validation -> instantiation -> execution tests.
# No text parser, WAST parser or external assembler is used.
set -euo pipefail
exe="$(realpath "$1")"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

header='\x00\x61\x73\x6d\x01\x00\x00\x00'
functions='\x03\x02\x01\x00'
exports='\x07\x08\x01\x04\x6d\x61\x69\x6e\x00\x00'
check_result() {
  if ! sed 's/\x1b\[[0-9;]*m//g' "$work/result" | grep -Fxq 'i32.const 42'; then
    cat "$work/result" >&2
    echo 'Expected i32.const 42 from binary fixture.' >&2
    exit 1
  fi
}

# () -> i32, with two-byte zero parameter and local-declaration vectors.
types='\x01\x06\x01\x60\x80\x00\x01\x7f'
code='\x0a\x07\x01\x05\x80\x00\x41\x2a\x0b'
printf '%b' "$header$types$functions$exports$code" > "$work/padded.wasm"
"$exe" "$work/padded.wasm" -r main > "$work/result"
check_result

# The same function with the maximum permitted five-byte zero lengths.
types='\x01\x09\x01\x60\x80\x80\x80\x80\x00\x01\x7f'
code='\x0a\x0a\x01\x08\x80\x80\x80\x80\x00\x41\x2a\x0b'
printf '%b' "$header$types$functions$exports$code" > "$work/max-padded.wasm"
"$exe" "$work/max-padded.wasm" -r main > "$work/result"
check_result

# Six-byte zero is malformed, despite denoting an in-range value.
types='\x01\x0a\x01\x60\x80\x80\x80\x80\x80\x00\x01\x7f'
printf '%b' "$header$types$functions$exports$code" > "$work/overlong.wasm"
if "$exe" "$work/overlong.wasm" -r main > "$work/result" 2>&1; then
  echo 'Malformed six-byte vector count was accepted.' >&2
  exit 1
fi
grep -Fq 'error in parsing module' "$work/result"
echo 'Binary module vector execution: 3/3 checks passed'
