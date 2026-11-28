#!/bin/bash
set -euo pipefail
exe=$(realpath "$1")
tmp=$(mktemp -d "${TMPDIR:-/tmp/opencode}/named-binary-module.XXXXXXXX")
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/duplicate.wast" <<'EOF'
(module $same binary "\00asm\01\00\00\00")
(module $same binary "\00asm\01\00\00\00")
(register "first-module-still-bound" $same)
EOF
# Duplicate script bindings must fail without losing the first binding or
# crashing. A missing summary is not evidence of correct rejection.
"$exe" --wast "$tmp/duplicate.wast" > "$tmp/result.log" 2>&1
grep -q 'Result: 2/3 ' "$tmp/result.log"
test "$(grep -c 'Result: ' "$tmp/result.log")" = 1
echo "Named binary module duplicate rejection: 1/1"
