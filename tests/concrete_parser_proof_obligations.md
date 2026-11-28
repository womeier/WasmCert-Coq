# Concrete parser contracts — current discharge ledger

This ledger distinguishes binary syntax correctness, printer membership and
runtime EH safety. Actual whole-module/string grammar iff and bounded printer
roundtrips are now proved. This is **not completion of indexed runtime payload
transport or of EH as a whole**.

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
forall n, parser_complete (parse_memory_instruction (n := n)) memory_instruction_encoding
```

The numeric result includes the actual ordered ordinary SIMD dispatch,
noncanonical u32 subopcodes and raw-byte lanes. `run_parse_memarg_correct`
is an actual arbitrary-suffix iff, not just canonical examples.
`parse_memory_instruction_complete` now discharges the **full actual memory
family**, including every scalar/vector/bulk alternative and its ordered-choice
disjointness. `run_parse_memory_instruction_correct` exports its arbitrary-suffix
iff against the independent concrete grammar. Padded vector/bulk dispatch
regressions retain an exact trailing byte; vector lanes remain raw bytes.

`parse_be_layer_control_complete` and `parse_be_layer_bulk_complete` also now
discharge actual control/EH/reference/i31 and table/bulk atom completeness
for arbitrary recursive body parsers. This includes the full source heap/value
codecs, both indirect-call forms and branch-table vectors; no abstract-only
reference codec is substituted.

Source heap/reference/value/global prefixes, catch/tag/custom composition and
their earlier wire-bounded printer contracts remain available unchanged.

## Actual recursive expression iff: discharged

The remaining combined atom contract is now proved:

```coq
forall n
  (body : Box (byte_parser (list basic_instruction)) n)
  (if_body : Box (byte_parser (list basic_instruction * list basic_instruction)) n),
  parser_complete (parse_be_layer body if_body) wasm_atomic_encoding
```

`wasm_parse_be_layer_atomic_complete` connects all actual families with
**cross-family** disjointness for shared `fc` and `fd` prefixes. Rejection proofs
use the production parsers and independent byte grammars, not another decoder.

`wasm_production_language_complete` proves all four components of the actual
recursive parser simultaneously, including the additional `instruction_try_table`
case and concrete catch vector. `wasm_production_parse_expr_complete` has no
primitive/block/catch/memory correctness hypotheses.

The public `wasm_run_parse_expr_correct` is now an **unconditional exact-input
iff**, and `wasm_parse_expr_prefix_correct` is its arbitrary-suffix iff.
The grammar remains independent of parser execution. Padded `fc` numeric and
`fd` vector constants under an EH handler are regression-tested in both
directions, including an exact trailing suffix.

## Actual module composition: discharged

The pinned flat-function-type grammar cannot describe this tree's recursive
declaration groups. That mismatch is now discharged by the concrete
`source_function_encoding`, `source_storage_encoding`, `source_field_encoding`,
`source_composite_encoding`, `source_subtype_encoding` and
`source_recursive_encoding` grammars. Their actual parser soundness/completeness
is proved, including source-indexed references, explicit/implicit subtypes and
singleton/explicit recursive groups. `run_parse_recursive_type_correct` and
`parse_recursive_type_prefix_correct` are unconditional iffs.

AST-only wire-bounds predicates support general actual group and type-section
printer membership/roundtrip theorems (`source_recursive_printer_roundtrip`,
`source_type_section_printer_roundtrip`), not just examples. They constrain
source-type/index/vector/section-size encodability, not parser-success domains.
The actual type-section framing codec is proved as well. Regressions combine
packed and indexed-reference fields, subtype supers and final EH references
inside a multi-member recursive declaration group.

All remaining concrete leaves and assembly contracts are now proved:

- Code locals use the full `source_local_encoding`, with exact repeated-local
  expansion, u32 total guard and actual code-size framing. Printer packing
  preserves full source types, not merely non-bottom or abstract function refs.
- Import/export descriptors include tags; tables, globals and element segments
  use full source references. Every one of the eight element and three data
  wire forms has independent consumed-byte grammar soundness/completeness.
- Actual recursive type sections and the tag slot **memory → tag (13) → global**
  compose with every ordinary framed section, arbitrary custom prefixes and
  trailing customs, optional absence, legal section order, EOF, function/code
  counts, data counts and handler-recursive data-count requirements.

Public final results in `binary_format_module_complete.v`:

```coq
run_parse_module_general_correct :
  forall bytes modul,
    run_parse_module bytes = Some modul <-> module_binary_encoding bytes modul

run_parse_module_str_general_correct :
  forall source modul,
    run_parse_module_str source = Some modul <->
    module_binary_encoding (String.list_byte_of_string source) modul
```

The independent grammar retains padded integer headers and custom bytes; it
does not mention parser runs. No primitive, declaration, code, record, segment,
section, framing, absence or finishing correctness hypotheses remain.

`binary_of_module_roundtrip` and `binary_of_module_string_roundtrip` in
`binary_format_module_roundtrip.v` apply to the actual AST-only `module_binary_wf`
domain. Its explicit source-type/index/opcode/lane/memarg/vector/section bounds
cover the existing memory-zero/u32-offset AST and final EH forms. It has no
parser-success or printed-byte grammar membership premise. The concrete
mixed-module regression inhabits this domain with recursive groups, indexed
locals/globals/table/element types, imported/exported tags, all four catches,
block index 64, a vector load and `data.drop` under a handler.

The printer proof exposed and repaired existing ordinary-SIMD encodings:
vector loads previously emitted a zero constant; shuffles emitted a spurious
vector-length prefix; splat opcodes were shifted; lane immediates used LEB128
instead of raw bytes. General membership proofs and exact regressions now
cover these corrected semantics. No relaxed SIMD or new addressing model was
added. GC's main closed-stack/runtime migration remains separate and untouched.

## Validation of this increment

Final whole-module increment: full exact-tree `dune build -j 1`, forced
`dune test -j 1 --force` and relevant `coqchk` pass. The audit prints both general
iff types, both bounded whole-module/string printer roundtrip types and the
actual AST wire-bound record. No concrete correctness hypotheses remain.
They disclose the same inherited classical real-decision/dependent
extensionality assumptions as the expression/numeric contracts. The local
overflow arithmetic theorem is globally closed. No admission or new/masking
axiom is introduced.

Official EH remains **489/489 binary commands + 18 mapped text-only deferrals**,
zero infrastructure errors. Indexed probes remain **7 PASS / 3 FAIL**, with
transport not executed. Strict core remains **53,999/54,004**, 148 files, zero
infrastructure errors and the same five stale alignment expectations. New Coq
syntax regressions are not counted as official execution or runtime safety.

Logs: `/tmp/opencode/eh-whole-module-final-build.log`,
`/tmp/opencode/eh-whole-module-final-tests.log`,
`/tmp/opencode/eh-whole-module-final-coqchk.log`,
`/tmp/opencode/eh-whole-module-assumptions.log`,
`/tmp/opencode/eh-whole-module-official.log`,
`/tmp/opencode/eh-whole-module-indexed.log`,
`/tmp/opencode/eh-whole-module-core.log`.

Earlier validation notes are historical, not current open parser obligations.

### Historical validation through `3401685`

Recursive declarations/type-section follow-up: full exact-tree build, forced
tests and relevant kernel checks pass. Recursive-group exact/prefix iffs and
both general group/type-section printer roundtrips are **globally closed**.
At that increment, whole-module and string contracts remained open. Official binaries remained
**489/489 + 18 mapped text deferrals**; indexed probes remain **7 PASS / 3 FAIL**.
Strict core remains **53,999/54,004**, 148 files, zero infrastructure errors and
the same five stale alignment expectations.

Logs: `/tmp/opencode/eh-declaration-final-build.log`,
`/tmp/opencode/eh-declaration-final-tests.log`,
`/tmp/opencode/eh-declaration-final-coqchk.log`,
`/tmp/opencode/eh-declaration-assumptions.log`,
`/tmp/opencode/eh-declaration-official.log`,
`/tmp/opencode/eh-declaration-indexed.log`,
`/tmp/opencode/eh-declaration-core.log`.

Follow-up combined dispatch and recursive expression iff: full exact-tree
build, forced tests and relevant kernel checks pass. The audit prints the
unconditional public theorem types and discloses the inherited classical
real-decision/extensionality assumptions; no new axioms are added.
At that increment, module composition remained open; expression iff alone did
not establish module/string iff or printer round trips. No runtime or test
expectation changes: the preceding official **489/489 + 18 text deferrals**
and indexed **7 PASS / 3 FAIL** accounting remains unchanged.

Logs: `/tmp/opencode/eh-expression-iff-final-build.log`,
`/tmp/opencode/eh-expression-iff-final-tests.log`,
`/tmp/opencode/eh-expression-iff-final-coqchk.log`,
`/tmp/opencode/eh-expression-iff-assumptions.log`.

Follow-up memory/control completeness: full exact-tree build, forced tests and
kernel checks of the new lookahead, memory/control completeness and regression
modules pass. The full memory completeness theorem and its exported prefix
iff are **globally closed**. Control/bulk layer completeness retains the same
inherited classical real-decision/extensionality assumptions; no axioms were
added. Official binary execution remains **489/489**, with **18 mapped text-only
deferrals**; indexed payload probes remain **7 PASS / 3 FAIL** with zero
infrastructure errors. No runtime/parser/printer or test expectation changed.

Follow-up logs: `/tmp/opencode/eh-memory-control-final-build.log`,
`/tmp/opencode/eh-memory-control-final-tests.log`,
`/tmp/opencode/eh-memory-control-final-coqchk.log`,
`/tmp/opencode/eh-memory-control-assumptions.log`,
`/tmp/opencode/eh-memory-control-official.log`,
`/tmp/opencode/eh-memory-control-indexed.log`.

Earlier expression-soundness increment:

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
