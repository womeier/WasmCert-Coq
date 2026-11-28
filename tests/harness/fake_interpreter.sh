#!/bin/bash
set -euo pipefail
case "$2" in
  */pass.wast) echo "Result: 1/1 (100.00%)" ;;
  */fail.wast) echo "Result: 0/1 (0.00%)" ;;
  */crash.wast) exit 7 ;;
  */missing.wast) echo "No result summary" ;;
  */malformed.wast) echo "Result: malformed" ;;
  */duplicate.wast) printf 'Result: 1/1 (100.00%%)\nResult: 1/1 (100.00%%)\n' ;;
  */impossible.wast) echo "Result: 2/1 (200.00%)" ;;
  *) exit 8 ;;
esac
