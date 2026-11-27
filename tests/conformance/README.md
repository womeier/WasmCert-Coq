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
start function, a nonzero table index, null and mismatch traps, four malformed
binary cases, and cross-instance imported tail calls. Both `dune test` and CI run
the checked-in fixtures without requiring wasm-tools. Binary invalid assertions
must decode then fail validation; binary malformed assertions must fail decoding.

## Scope and provenance

- Eleven **text-only** malformed assertions in the indirect source are outside
  the binary-only projection. The generator prints their exact source lines and
  records them in the output header; they are not included in pass totals.
- The pinned tail-call fixtures use the concrete Wasm 2.0 type fragment plus
  tail calls. They are not the complete current Wasm 3.0 core suite: typed
  reference covariance, `return_call_ref`, and table64 combinations are not
  represented by these files.
- The existing WAST harness checks trap occurrence, not exact trap-message
  equality. A conformance command count is not a proof of that harness property.
- The projected official fixtures are distributed under the Apache 2.0 license
  included in `LICENSE`.
