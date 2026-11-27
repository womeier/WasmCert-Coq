# Binary tail-call conformance

`return_call.wast` and `return_call_indirect.wast` are binary projections of
`wast_testsuite/proposals/wasm-3.0/{return_call,return_call_indirect}.wast`,
at testsuite revision `b497cbb853db21be875bd5c81fcc3334168fb0b4`.
They retain all 115 binary-scope commands (47 direct, 68 indirect), including
invalid validation cases, indirect traps, multi-results, imports, nonzero table
indices, and recursion up to one million tail calls.

Generation uses **wasm-tools 1.263.0** solely as an external test encoder, not as
the interpreter's parser or validator. From the repository root:

```sh
python3 tests/binary_wast.py wast_testsuite/proposals/wasm-3.0/return_call.wast tests/conformance/return_call.wast
python3 tests/binary_wast.py wast_testsuite/proposals/wasm-3.0/return_call_indirect.wast tests/conformance/return_call_indirect.wast
python3 tests/binary_wast.py tests/tail_call_cases.wast.in tests/conformance/tail_call_cases.wast
bash run_wast.sh tests/conformance
```

Use `--wasm-tools PATH` to select the encoder. No validation feature flags or
relaxed-SIMD support are enabled. Generated binaries exercise the actual extracted
`run_parse_module_str`, module validator/instantiator, and context interpreter.
`tail_call_cases.wast` adds frame/label/operand-stack unwinding, tail calls in a
start function, a nonzero table index, null and mismatch traps, and four malformed
binary cases, plus cross-instance imported tail calls. Both `dune test` and CI run the checked-in fixtures without requiring
wasm-tools. Binary invalid assertions must decode then fail validation; binary
malformed assertions must fail decoding.

## Boundaries and dependencies

- The official spec at `04931610158e1ae1c69a3abf49e73984c0d4ddaf`
  adds typed-reference result-covariance cases to both files, beyond the pinned
  suite above. These are an explicit integration dependency, not omitted tests
  presented as a complete final-spec pass. Its additional concrete result
  arity/type rejection cases are also covered by `tail_call_cases.wast`.
  Running its unmodified binary projections currently gives **35/123**, failing
  as expected: each initial module contains unsupported typed-reference types,
  so its dependent invocations cannot execute. The negative covariance modules
  also fail decoding instead of reaching validation. No such failure is counted
  as a passing invalid assertion.
- Eleven **text-only** malformed assertions in the indirect source are outside
  the current non-text scope. The generator prints their exact source lines and
  records them in the output header; they are not included in pass totals.
  Production text behavior is unchanged.
- `return_call_ref`, typed/non-null reference result covariance, and reference
  subtyping for indirect dispatch depend on function-references/GC integration.
  Table64 indices depend on the memory64/table64 representation. This branch
  does not supply competing representations or claim those combinations pass.
- `tail_call_properties.v` proves that final result matching reduces to the
  existing equality premise for lists of concrete types in the current fragment
  (excluding internal `T_bot`). The validator reflection, preservation, progress,
  interpreter and instantiation proofs are reused, not replaced.
- The binary parser is Rocq code using Parseque and is extracted into the actual
  execution path. It has **no general correctness theorem against a declarative
  binary grammar**. `binary_format_tests.v` proves closed parser/round-trip
  regressions and universal tail opcode printer equations, not general parser
  correctness. General bounded-u32 LEB parsing, combinator consumption/backtracking,
  recursive instruction parsing, and section/module assembly correctness remain
  required verification work. No new trusted parser or correspondence axiom is
  introduced here. This PR remains draft while that obligation is open.
- The existing WAST harness checks trap occurrence, not exact trap-message
  equality. The existing text assertion paths retain their historical behavior.
  Do not interpret these counts as verification of those harness properties.
- Strict binary malformed assertions reveal five stale expectations in the
  pinned root `align.wast` (lines 891, 910, 929, 948, 967): that file expects
  flags `0x20`, `0x21`, `0x3f`, `0x40`, `0x41` to be malformed. Previously,
  validation failure was accepted instead. Consequently the full unchanged
  root suite reports **53,999/54,004**, not a conformance pass. At the official
  spec revision above, `test/core/align.wast` changes the first three and last
  of these cases to `assert_invalid` and removes/replaces the `0x40` case as part
  of multi-memory alignment. This is a pinned-test mismatch, not evidence of a
  tail-call regression or a suspected specification error. Updating the shared
  suite and multi-memory parser must be coordinated at integration; this branch
  neither changes the submodule pin nor weakens binary assertions.
