#!/bin/bash
# Wasm 2 core plus the pinned proposal's official replacements/additions.
# No tests are rewritten; the unchanged root suite can still be run separately.
set -euo pipefail
root=$(dirname "$(realpath "$0")")
suite=$(realpath "${1:-$root/wast_testsuite}")
proposal="$suite/proposals/multi-memory"
shopt -s nullglob
core_files=("$suite"/*.wast)
proposal_files=("$proposal"/*.wast)
if (( ${#core_files[@]} == 0 || ${#proposal_files[@]} == 0 )); then
  echo "Both the core suite and official multi-memory proposal suite are required." >&2
  exit 1
fi

combined=$(mktemp -d "${TMPDIR:-/tmp/opencode}/wasmcert-multi-memory.XXXXXXXX")
trap 'rm -rf "$combined"' EXIT
for file in "${core_files[@]}"; do
  ln -s "$file" "$combined/$(basename "$file")"
done
for file in "${proposal_files[@]}"; do
  name=$(basename "$file")
  if [[ -L "$combined/$name" ]]; then
    echo "Official multi-memory replacement: $name"
  fi
  ln -sf "$file" "$combined/$name"
done
echo "Suite revision: $(git -C "$suite" rev-parse HEAD)"
echo "Features: existing Wasm 2 core + multi-memory; no other proposal overlays."
export JOBS="${JOBS:-1}"
export EXE="${EXE:-$root/_build/default/src/wasm_coq_interpreter.exe}"
bash "$root/run_wast.sh" "$combined"
