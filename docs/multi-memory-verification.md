# Multi-memory verification status

This is an implementation ledger, not a completion claim. The PR remains draft.
New text parsing/printing/annotations and text-specific proofs are deferred by
the user; existing text behavior is preserved. Memory64 and relaxed SIMD are
outside this branch.

## Reused foundations

`tc_mems`, `inst_mems`, and `s_mems` already contain lists. Imported memories
precede defined memories; `alloc_mems` and instance allocation already allocate
lists. Active data segments already carry `MD_active midx offset`, and data-mode
validation checks `midx`. The required changes are instruction indices and their
propagation, zero-index runtime helpers, the Wasm 2 module memory-count guard,
and active-data initialization (which currently discards `midx`).

## Parser trust boundary and required proof work

Binary input uses extracted `binary_format_parser.run_parse_module_str` directly.
Text modules go through external `wasm` 2.0.2 parsing/encoding, then through the
same binary parser (`src/parse.ml`). Scripts also use that external text parser.
`text_format_parser.v` parses invocation values, not complete modules.

The binary parser uses Parseque, size/range guards, and the executable LEB128
decoder. Existing `binary_format_tests.v` and `leb128_tests.v` establish concrete
examples, not general parser soundness/completeness or printer round trips.
General verification must establish the byte grammar and bounded/noncanonical
LEB acceptance, prove the actual Parseque primitives and combinators implement
it, then lift through indexed memargs, instructions, expressions and modules.
Printer round trips require representability/well-formedness hypotheses: the
AST uses unbounded `N` for u32 indices and also admits ill-typed instructions.
These obligations are **not discharged** by concrete computation tests.
No verified-replacement or external-parser correspondence is claimed.

Existing validator reflection, proof-carrying interpreter, instantiation
correctness, preservation and progress must continue to compile as each
instruction changes. Every implementation commit requires a full successful
`dune build -j 1` on its exact tree, not just selected targets.

## Pinned conformance baseline

Suite: WasmCert/testsuite `b497cbb853db21be875bd5c81fcc3334168fb0b4`.
Runtime baseline: source `8ad1340` (empty placeholder atop `58a3d3f`).
No filename filters or proposal flags applied to the root suite.

Commands run from the exclusive multi-memory worktree:

| Command | Result |
| --- | --- |
| `dune build -j 2` (baseline) | Passed |
| `bash tests/run_wast_test.sh run_wast.sh` | Passed; success, mixed failure/crash/missing/malformed summary, empty suite |
| `EXE=/tmp/opencode/multi-memory-baseline.exe JOBS=2 bash run_wast.sh wast_testsuite` | 148 files; **54,004/54,004** |
| `EXE=/tmp/opencode/multi-memory-baseline.exe JOBS=1 bash run_wast.sh wast_testsuite/proposals/multi-memory` | **FAILED**: 12 summarized files, **654/668** assertions; 36 additional files crashed in the external text frontend with `unexpected token` |

The latter assertion denominator excludes crashed files and is **not** a
proposal-suite pass rate. The hardened runner rejects these runs.

The pinned root is Wasm 2, not a final Wasm 3 suite: `memory.wast` and
`imports.wast` explicitly require multiple memories to be invalid. Enabling
multi-memory necessarily changes these assertions. Run and report the unchanged
root suite as well as the proposal's official replacement tests; do not silently
filter those assertions or describe obsolete expectations as runtime regressions.
The multi-memory directory provides the corresponding replacement files.

## Still required

- Finish explicit scalar, SIMD, size/grow and bulk indices across every layer.
- Validate and execute copies between distinct or aliased imported memories.
- Preserve the memory index of active data initialization; enable multiple
  imports/definitions with the existing allocation foundations.
- Add binary fixtures for nonzero indices, malformed encodings, invalid memory
  references, imports plus definitions, aliasing, traps and boundary behavior.
- Discharge affected proofs and general binary-format obligations above.
- Full build/test and full supported/proposal conformance after implementation;
  account for every crash, failure and missing summary. Text-dependent proposal
  execution is blocked by the deferred external frontend, not counted as passed.

## Verified implementation increments

- `e1ca3f0`: explicit `memory.size`/`memory.grow` indices in syntax,
  declarative/executable validation, semantics, the proof-carrying interpreter,
  binary codecs and affected proofs. Full `dune build -j 1` and
  `dune test -j 1` passed. Concrete tests cover nonzero/multibyte/maximal indices,
  truncated/overflowing encodings and validation bounds. This does not yet
  enable multi-memory modules or establish general codec theorems.

## Suspected specification assertion error (reported, not worked around)

Source: WebAssembly/spec tag `wasm-3.0`, commit
`d7aada502455b3d9176ca4cbe48be4724d511d2a`,
`document/core/exec/instructions.rst`, `exec-memory.copy`, steps 18e and 18g.
Those steps assert `d+1 < 2^32` and `s+1 < 2^32` from the earlier memory bound.
For a legal 4-GiB memory with `d=s=2^32-1` and `n=1`, both bounds pass and
`d <= s` selects the forward case, but both increments equal `2^32`.
The expected mathematical bound is non-strict. Confidence is high that the
strict assertion is false; runtime impact is not established: modular wrapping
may make the following zero-length recursion harmless. This is not a basis for
silently changing the operational rules or weakening proofs. Reported to the
parent/user and on the draft PR; no unauthorized upstream issue was filed.
