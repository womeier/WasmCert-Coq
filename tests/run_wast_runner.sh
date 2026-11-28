#!/bin/bash
# A passing file must not mask crashes or missing/malformed result summaries.
set -euo pipefail
runner=$(realpath "$1")
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir "$scratch/suite"
touch "$scratch/suite/pass.wast"
cat > "$scratch/fake-interpreter" <<'EOF'
#!/bin/bash
case "$2" in
  */pass.wast) echo 'Result: 1/1 (100.00%)' ;;
  */fail.wast) echo 'Result: 0/1 (0.00%)' ;;
  */crash.wast) exit 2 ;;
  */missing.wast) echo 'no summary' ;;
  */malformed.wast) echo 'Result: not a count' ;;
  */impossible.wast) echo 'Result: 2/1 (200.00%)' ;;
  */prefix.wast) echo 'Result: 1/1garbage' ;;
esac
EOF
chmod +x "$scratch/fake-interpreter"
export EXE="$scratch/fake-interpreter" JOBS=1
bash "$runner" "$scratch/suite" > "$scratch/output"
grep -q 'Total Passed: 1/1' "$scratch/output"
for kind in fail crash missing malformed impossible prefix; do
  touch "$scratch/suite/$kind.wast"
  if bash "$runner" "$scratch/suite" > "$scratch/output" 2>&1; then
    echo "runner incorrectly accepted $kind alongside a passing file" >&2
    exit 1
  fi
  rm "$scratch/suite/$kind.wast"
done
echo 'Wast runner regression tests: 7/7'
