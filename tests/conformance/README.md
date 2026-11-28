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
instruction immediates, cross-instance imported tail calls, incorrect function
sizes, and permitted u32 padding in function-size and zero-local-count fields.
It also covers zero-count entries in nonempty local vectors and aggregate local
count overflow with individually valid u32 counts.
Nonempty-local bodies exercise a multibyte local count, both wrong-size
directions, and an executed tail transfer from a caller with 64 locals.
Indexed-memory tail calls use explicit flag 65 with nonzero memory selection;
registration regressions preserve named binary modules and earlier aliases.
Both `dune test` and CI run the checked-in fixtures without requiring wasm-tools.
Binary invalid assertions must decode then fail validation; binary malformed
assertions must fail decoding.

## Complete non-text multi-memory profile

The root suite predates multi-memory. Its historical malformed reserved-zero
fields and multiple-memory invalid assertions are not final-format expectations.
Keep running the unchanged root suite separately; do not rewrite its assertions.
Prepare the entire core plus all official multi-memory replacements/additions
at the same testsuite pin with:

```sh
python3 tests/prepare_multi_memory_binary.py \
  --wasm-tools /path/to/wasm-tools \
  --output /tmp/opencode/multi-memory-binary-profile
JOBS=2 bash run_wast.sh /tmp/opencode/multi-memory-binary-profile
```

The output must be a new or empty directory. The generator reports every
same-name replacement and every excluded text-only malformed assertion with
its source line. `provenance.json` records the testsuite revision, encoder
version and source hashes. No binary-scope command is filtered or reclassified.
This uses the existing external fixture encoder, not a new production text
frontend. Use wasm-tools 1.263.0 to reproduce the pinned projection.

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

### Final tail-call coverage is three files, not two

The final-spec comparison is pinned to
`WebAssembly/spec@04931610158e1ae1c69a3abf49e73984c0d4ddaf`.
Use all of `test/core/{return_call,return_call_indirect,return_call_ref}.wast`
for a final tail-call audit. Their Git blob IDs and binary-scope command counts
are:

| Source | Git blob | Binary commands |
|---|---|---:|
| `return_call.wast` | `0285662f4d01fe72d79ef2748e06f8342c74d6d7` | 51 |
| `return_call_indirect.wast` | `9ef29f074aa1ee41c17bc3adba65fbe58036888f` | 72 |
| `return_call_ref.wast` | `acf8013a5b600c8daf608e7093459beccf476fad` | 53 |

Download each source at that exact commit and project each with
`tests/binary_wast.py --wasm-tools /path/to/wasm-tools-1.263.0 SOURCE DESTINATION`.
Put the three projected files in a new audit directory and run the entire
directory with `JOBS=2 bash run_wast.sh DIRECTORY`. This is separate from the
checked-in 115-command concrete-type baseline above; it must not be presented
as passing merely because that older baseline passes.

All 176 binary commands are in scope. Only 11 text-only malformed assertions
are outside scope, in final `return_call_indirect.wast` at source lines
310, 322, 334, 346, 358, 370, 382, 389, 399, 409, 421. The direct and reference
files have no text-only exclusions. Final reference tests are required even
while their shared implementation dependency is unfinished.
