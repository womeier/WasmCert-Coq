#!/bin/bash
# Regression: a successful file must not conceal another file's crash or
# missing/malformed summary. No WebAssembly assertions are involved here.
set -euo pipefail
runner=$(realpath "$1")
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/good.wast" "$tmp/other.wast"
cat > "$tmp/interpreter" <<'EOF'
#!/bin/bash
if [[ "$2" == */good.wast ]]; then
  echo 'Result: 1/1'
else
  case "$MODE" in
    pass) echo 'Result: 2/2' ;;
    failure) echo 'Result: 1/2' ;;
    crash) exit 7 ;;
    missing) echo 'not a result' ;;
    malformed) echo 'Result: unknown' ;;
    zero) echo 'Result: 0/0' ;;
    overcount) echo 'Result: 3/2' ;;
  esac
fi
EOF
chmod +x "$tmp/interpreter"
export EXE="$tmp/interpreter" JOBS=1
MODE=pass bash "$runner" "$tmp" > "$tmp/output"
grep -q 'Total Passed: 3/3' "$tmp/output"
for mode in failure crash missing malformed zero overcount; do
  if MODE="$mode" bash "$runner" "$tmp" > "$tmp/output"; then
    echo "Runner incorrectly accepted $mode" >&2
    exit 1
  fi
done
echo 'run_wast runner regressions: 7/7'
