#!/bin/bash
# A failed file must never disappear from the suite's aggregate result.
set -euo pipefail

runner=$(realpath "$1")
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/suite"
cat > "$tmp/interpreter" <<'EOF'
#!/bin/bash
case "$2" in
  */pass.wast) echo "Result: 2/2" ;;
  */fail.wast) echo "Result: 1/2" ;;
  */crash.wast) exit 1 ;;
  */missing.wast) echo "not a result" ;;
  */malformed.wast) echo "Result: invalid" ;;
esac
EOF
chmod +x "$tmp/interpreter"
touch "$tmp/suite/pass.wast"
EXE="$tmp/interpreter" JOBS=2 bash "$runner" "$tmp/suite" > "$tmp/output"
grep -q 'Total Passed: 2/2' "$tmp/output"

for outcome in fail crash missing malformed; do
  touch "$tmp/suite/$outcome.wast"
  if EXE="$tmp/interpreter" JOBS=2 bash "$runner" "$tmp/suite" > "$tmp/output" 2>&1; then
    echo "Runner incorrectly accepted $outcome alongside passing tests" >&2
    exit 1
  fi
  rm "$tmp/suite/$outcome.wast"
done

rm "$tmp/suite/pass.wast"
if EXE="$tmp/interpreter" JOBS=2 bash "$runner" "$tmp/suite" > "$tmp/output" 2>&1; then
  echo "Runner incorrectly accepted an empty suite" >&2
  exit 1
fi
