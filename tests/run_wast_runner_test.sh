#!/bin/bash
# Runner failures must not disappear beside another file's passing summary.
set -euo pipefail
runner="$1"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/suite"
touch "$tmp/suite/good.wast" "$tmp/suite/bad.wast"
cat > "$tmp/interpreter" <<'EOF'
#!/bin/bash
if [[ "$2" == */good.wast ]]; then
  echo "Result: 2/2 (100.00%)"
else
  case "$CASE" in
    pass) echo "Result: 3/3 (100.00%)" ;;
    crash) echo "Result: 3/3 (100.00%)"; exit 7 ;;
    missing) echo "no result available" ;;
    malformed) echo "Result: not a summary" ;;
    impossible) echo "Result: 4/3 (133.33%)" ;;
    partial) echo "Result: 2/3 (66.67%)" ;;
  esac
fi
EOF
chmod +x "$tmp/interpreter"
export EXE="$tmp/interpreter" JOBS=1
CASE=pass bash "$runner" "$tmp/suite" > "$tmp/log" 2>&1
grep -q "Total Passed: 5/5" "$tmp/log"
for CASE in crash missing malformed impossible partial; do
  export CASE
  if bash "$runner" "$tmp/suite" > "$tmp/log" 2>&1; then
    echo "Runner falsely accepted $CASE" >&2
    cat "$tmp/log" >&2
    exit 1
  fi
done
echo "WAST runner regression cases: 6/6"
