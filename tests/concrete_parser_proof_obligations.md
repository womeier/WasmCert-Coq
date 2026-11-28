# Concrete parser contracts — current discharge ledger

This ledger distinguishes soundness, completeness and printer membership.
It is **not whole-module completion**.

## Conditional recursive soundness: discharged

The actual `production_parse_expr_sound` schema previously required:

```coq
forall n p, In p (primitive_parsers n) -> parser_sound p Atom
forall n, parser_sound (parse_block_type (n := n)) BlockType
```

Both are now instantiated with concrete independent grammars:

- `wasm_primitive_parsers_sound` covers **all 20 actual primitive alternatives**;
- `parse_block_type_sound` covers all actual source block-type forms;
- `wasm_production_parse_expr_sound` and `wasm_run_parse_expr_sound` consequently
  have **no primitive, memory, block or catch correctness premises**.

The resulting grammar includes the actual `try_table` constructor with its
concrete verified catch vector. Control/reference rules include `throw`,
`throw_ref`, reference calls, `br_on_non_null`, i31 instructions, source-indexed
heap nulls and typed selects. The abstract-only earlier reference grammar is
not substituted for these source forms.

The concrete memory grammar describes this tree's existing memory-zero/
u32-offset AST and final flags, including explicit memory-zero padded indices.
It does not import the other branch's addressing/multi-memory model or claim
unsupported memory64/u64-offset coverage. All scalar, bulk and ordinary SIMD
memory alternatives are discharged against that grammar. Ordinary numeric and
SIMD alternatives are also concrete; relaxed SIMD is not added.

Kernel regression derivations use the unconditional theorem for all four
catches, source-indexed block/null types, reference calls/i31, and a raw
one-byte SIMD memory lane. A padded explicit-memory-zero memarg regression
retains its exact suffix. These are syntax derivations, not semantic-validation
passes or replacements for official conformance.

## Completeness contracts already discharged

```coq
forall n, parser_complete (parse_block_type (n := n)) block_type_encoding
forall n, parser_complete (parse_catch_clause (n := n)) catch_clause_encoding
forall n, parser_complete (parse_numeric_instruction (n := n)) numeric_atomic_encoding
forall n, parser_complete (parse_memarg (n := n)) memarg_encoding
```

The numeric result includes the actual ordered ordinary SIMD dispatch,
noncanonical u32 subopcodes and raw-byte lanes. `run_parse_memarg_correct`
is an actual arbitrary-suffix iff, not just canonical examples.
`scalar_memory_instruction_complete` discharges concrete scalar payload
composition; it is not called full memory-family completeness.

Source heap/reference/value/global prefixes, catch/tag/custom composition and
their earlier wire-bounded printer contracts remain available unchanged.

## Exact open instruction-completeness obligations

The following are **not yet exported proofs**:

```coq
forall n,
  parser_complete (parse_memory_instruction (n := n)) memory_instruction_encoding

forall n
  (body : Box (byte_parser (list basic_instruction)) n)
  (if_body : Box (byte_parser (list basic_instruction * list basic_instruction)) n),
  parser_complete (parse_be_layer body if_body) wasm_atomic_encoding
```

The second contract must select every concrete control/table/EH/GC atom and
prove ordered-choice disjointness, including shared `fc` and `fd` prefixes.
The complete numeric-family theorem alone does not imply it.

Then the actual four-component recursive language completeness invariant must
be proved, with the additional `try_table` induction case and concrete catch
vector. In particular **`wasm_run_parse_expr_sound` is not an iff**.
The exact remaining gap is completeness, not an undisclosed `PrimitiveSound`
assumption.

## Exact open module composition obligations

The pinned flat-function-type grammar cannot typecheck as a description of this
tree's recursive declaration groups. A concrete source recursive-group/
field/composite grammar and corresponding actual leaf contracts still have to
be installed. The actual code/local expansion, all import/export tag branches,
table/global/element/data records, section framing and optional/custom sequence
must be composed with those leaves and the complete expression grammar.

Only after those concrete contracts are discharged can the independent
`module_binary_encoding` / actual AST wire-bounds predicate be adapted and the
actual module/string general iff and bounded printer round trips exported.
The existing `finish_printed_module_sections` and tag/custom leaf results do not
by themselves prove those statements.

No unfinished generic module theorem or parser-success domain is installed to
conceal these gaps. GC's closed administrative-stack migration remains a
separate runtime dependency and is not an explanation for these open proofs.

## Validation of this increment

Full exact-tree build, forced tests and relevant `coqchk` pass. The actual
unconditional theorem types are printed in the assumption audit, not merely
their names. Concrete expression soundness and numeric completeness retain
the disclosed inherited classical real-decision/dependent extensionality
assumptions; memarg completeness and its prefix iff are globally closed.
No admission, new axiom, runtime decoder/model or weakened test is introduced.

The unchanged extracted suites pass (163 positive script commands and 12
deliberate failure detections). Official EH remains **489/489 binary commands**
and **18 mapped text-only deferrals**, with zero infrastructure errors. Indexed
payload probes remain **7 PASS / 3 FAIL**, not executed transport. Strict core
remains **53,999/54,004**, 148 files, zero infrastructure errors: the same five
alignment expectations.

Logs: `/tmp/opencode/eh-concrete-expression-final-build.log`,
`/tmp/opencode/eh-concrete-expression-final-tests.log`,
`/tmp/opencode/eh-concrete-expression-final-coqchk.log`,
`/tmp/opencode/eh-concrete-expression-assumptions.log`,
`/tmp/opencode/eh-concrete-expression-official.log`,
`/tmp/opencode/eh-concrete-expression-indexed.log`,
`/tmp/opencode/eh-concrete-expression-core.log`.
