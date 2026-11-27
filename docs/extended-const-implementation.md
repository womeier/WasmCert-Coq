# Extended constant expressions: implementation status

**Incomplete; the module validator has not been switched to Wasm 3.0.**
This branch is an implementation increment, not a claim of proposal support.
Text-format changes and text-specific proofs are deferred by explicit user
instruction. Existing text behavior is unchanged. GC constants and relaxed SIMD
are outside this branch's scope.

## Audited foundations

The instruction datatype, general instruction typing and its validator
reflection, operational semantics, interpreter, binary parser, binary printer,
and pretty-printer already represent i32/i64 add/sub/mul. These instructions
need no new opcode or runtime arithmetic implementation.

The existing constant-expression whitelist excludes arithmetic. In addition:

- `bet_const_exprs_len` and `const_exprs_impl` in
  `theories/instantiation_properties.v` assume every allowed instruction produces
  one value. This is false for binary arithmetic.
- `init_value_typing` uses this singleton characterization.
- `module_typing` and `module_type_checker` give every global initializer the
  same imports-only context.
- `instantiate_globals`, `get_global_inits`, and the main instantiation soundness
  proofs evaluate all globals under the same imports-only frame.
- Element initializers use that frame too; referring to defined globals requires
  updating their initialization environment as well.

## Implemented increment

- A terminating, stack-based `interp_const_stack`, integrated into
  `interp_get_const`. It accepts only the six extended-const arithmetic
  instructions, checks operand widths, and requires exactly one final value.
  Existing singleton evaluation remains a fast path.
- Declarative extended-global validity and a sequential executable checker.
  Each global is checked before its own type is added to the context.
  Immutable predecessors are visible; mutable, self, and forward references
  are rejected.
- Sequential global evaluation/allocation (`interp_global_chain`) and its
  operational counterpart (`global_init_chain`). These are not yet used by
  the module instantiator.
- Completed proofs in `theories/extended_const.v`: arithmetic totality and
  result type, global-validator soundness/completeness (reflection), evaluator
  operational soundness, sequential evaluation operational soundness, and
  result-list length.
- `theories/extended_const_binary.v` proves binary printer/parser round trips
  for **all six** arithmetic instructions using the actual parser/printer.
  It also checks an initializer round trip and malformed/trailing input.
- Executable Coq regressions cover nested arithmetic, modular overflow,
  operand order, width errors, stack errors, forbidden arithmetic,
  prefix validation, and sequential global initialization.
- The WAST runner now fails on crashes or missing/invalid result summaries,
  including when another input passed. Its regression tests run under
  `dune test`.

## Binary parser verification boundary

`src/parse.ml:parse_binary_module` calls the extracted
`run_parse_module_str`; `theories/extraction_instance.v` re-exports that
function, and `src/extraction.v` extracts it. The binary implementation is
`theories/binary_format_parser.v`, using Parseque. Its `run` wrapper requires
all input tokens to be consumed. The printer is
`theories/binary_format_printer.v`.

There is no existing module-parser soundness/completeness or generic
printer/parser round-trip development in this checkout. The printer's header
refers to `binary_format_spec.v`, but that file is absent. The new opcode
round-trip theorem connects to the actual extracted parser, not a replacement;
it does **not** prove the surrounding expression/module parser correct.
Applicable expression/module parsing and malformed-input proofs therefore
remain required work, not an exemption based on the existing trust boundary.

Extraction also retains its pre-existing OCaml integer/list/array overrides
and runtime library trust boundary; this increment adds no extraction override
or axiom.

## Remaining integration and proof obligations

1. Replace the old constant whitelist in module validity and executable module
   validation, together with the singleton-dependent typing proofs.
2. Connect prefix validity and sequential allocation to `module_typing`,
   `module_type_checker`, `instantiate`, and `interp_instantiate`. Ensure
   element/data initializer environments expose the defined globals permitted
   by Wasm 3.0. Avoid allocating globals twice when reusing `alloc_module`.
3. Complete the corresponding module-validator and instantiation proofs,
   initialized-value typing, preservation/progress integration, and any
   evaluator completeness obligations.
4. Discharge applicable non-text parser correctness and round trips beyond
   the six-opcode fragment.
5. Exercise actual extracted acceptance/execution with binary module fixtures.
   Run the complete supported core suite and official extended-const
   conformance, fixing all relevant failures without skipping tests.

The unchanged module validator still rejects extended-const modules. The
standalone checker/evaluator proofs and regressions are not substitutes for
the unfinished module-level connections.

## Verification record

Configuration: direct Dune commands, one build/test worker; default extracted
CLI and its existing `wasm` 2.0.2 text frontend. No feature filters, instruction
disabling, assertion weakening, or new axioms. All 21 Coq evaluator/validator
regressions and five binary-parser checks compile; the six-opcode round-trip
theorem is universally quantified over the whitelisted fragment.

```sh
dune build -j 1
dune test -j 1
```

Both pass, including existing proofs, extraction/CLI compilation, MDX tests,
and the new runner regressions (6/6). The full build is rerun on the final tree
before committing, as required.

The repository's pinned `WasmCert/testsuite` revision is
`b497cbb853db21be875bd5c81fcc3334168fb0b4`. Test archives were downloaded to
untracked `.test-artifacts/`, not added to the branch. Commands and outcomes:

```sh
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh \
  .test-artifacts/testsuite-b497cbb853db21be875bd5c81fcc3334168fb0b4
```

**54,004/54,004**, all 148 root core WAST files, including ordinary SIMD.
This is the complete existing root core suite, not a filename-filtered sample.

```sh
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh \
  .test-artifacts/testsuite-b497cbb853db21be875bd5c81fcc3334168fb0b4/proposals/extended-const
```

**FAIL: 211/290**, all three files: data 61/65, elem 99/111, global 51/114.
The official `WebAssembly/extended-const` repository at
`8d4f6aa2b00a8e7c0174410028625c6a176db8a1`, `test/core/{data,elem,global}.wast`,
was independently downloaded to `.test-artifacts/proposal`; the equivalent
command `JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh .test-artifacts/proposal`
reports the same **211/290**. These failures are expected from the unfinished
module-level integration; they are not skipped or treated as passing.

Additional integration probes:

- `JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh
  .test-artifacts/testsuite-b497cbb853db21be875bd5c81fcc3334168fb0b4/proposals/tail-call`
  **fails**: both input files crash in the unchanged text frontend
  (`unknown operator return_call` / `return_call_indirect`); no passing
  conformance count is asserted.
- `JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh .test-artifacts/spec-wasm3`
  runs official `WebAssembly/spec` revision
  `d7aada502455b3d9176ca4cbe48be4724d511d2a`, `test/core/{const,global}.wast`.
  **Fails overall**: const is 778/778, global crashes with
  `Wasm.Parse_error.Syntax(_, "unexpected token")`. This is not a full
  Wasm 3.0 suite run or a passing proposal result. New text support is deferred.

No suspected specification error has been identified. The recorded failures
are implementation/integration limitations, not proposed semantic workarounds.
