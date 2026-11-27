#!/bin/bash
set -euo pipefail
exe="$1"
good="$2"
bad="$3"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
"$exe" --wast "$good" > "$tmp/good"
"$exe" --wast "$bad" > "$tmp/bad"
grep -q 'Result: 4/4 ' "$tmp/good"
grep -q 'Result: 0/6 ' "$tmp/bad"
echo "Strict assertion stages: 4 positive, 6 negative checks"
