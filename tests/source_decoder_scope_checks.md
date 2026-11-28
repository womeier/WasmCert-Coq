# Production source codecs and canonical-context scope checking

The indexed-global counterexample from `ffa5a0c` is repaired, not relabeled.
Its exact bytes remain
`0061736d01000000010401600000060701630000d0000b`.
The actual module parser and string wrapper now reconstruct its source AST.
The extracted instantiator accepts it; an exported function reading the indexed
global and applying `ref.is_null` returns 1.

## Decoder paths

The actual global/table types, inline block results, typed selects,
`ref.null` immediates and explicit element reference types now use the same
full **source** declaration codecs as locals/function declarations. These
codecs were moved before the instruction parser so it can use them directly.
No alternative module parser was introduced.

The public abstract fragment parsers and their existing contracts remain
unchanged. Production source positions no longer accidentally select that
fragment. Indexed heap types use bounded nonnegative s33; ordinary indices
still use u32. Wrong scope is not a wire grammar error.

`binary_format_global_properties.v` proves:

- generalized source value/global type prefix iff, with arbitrary suffixes and
  ambient bounds;
- actual heap/reference/value/global printer membership with explicit wire
  bounds, not parser-success/membership premises;
- value/global printer prefix round trips;
- actual `ref.null` source grammar soundness/completeness and printer membership.

`binary_format_block_properties.v` now proves soundness/completeness and actual
bounded printer round trips for **every source block-type form**, including
multi-byte indexed reference results, not just signed `BT_id`.

## Actual validation boundary

`module_source_types` collects type-bearing source occurrences from globals,
tables, imports, element types/initializers/offsets, data offsets and function
locals/bodies. The recursive traversal includes nested blocks/loops/ifs/
`try_table`, `ref.null`, typed selects and type-index instruction immediates,
including unreachable code.

After successful existing component validation, `check_module_source_types`
requires every occurrence to close through the module's actual canonical name
map and satisfy shared `closed_value_validb`. Type declarations continue to use
the existing shared group validation. This is source well-formedness, **not
runtime value lowering or source-index identity transport**.

`module_type_checker_source_types_closed` and
`module_type_checker_global_source_closed` connect successful actual validation
to that shared closing/validity property. Existing errors and their order are
preserved: a previously rejected component retains its existing error rather
than being hidden by a new blanket source error. Main validator/instantiation/
preservation theorem statements were not weakened.

The exact wrong-scope source-global AST still prints and parses, but actual
validation returns `None`; `indexed_global_wrong_scope_still_parses` and
`indexed_global_wrong_scope_is_invalid` kernel-check both stages.
Wire overflow remains malformed.

## No newly enabled raw-index import matching

The still-source-typed runtime has no closed global/table cache boundary yet.
Exposing source syntax must not let equal local numbers equate unrelated types.
Function/table/global cache matching therefore additionally requires closing
with **no local names**; indexed caches fail closed. This uses the same shared
closing and validity predicates, not a new descriptor/classifier.

`import_global_subtyping_index_rejected`,
`import_table_subtyping_index_rejected` and
`import_function_subtyping_index_rejected` prove actual checks reject such raw
indexed caches. Tag imports retain their mandatory stored canonical IDs,
bidirectional equivalence and existing portable boundary.

This restriction is **not final canonical import completeness**: even matching
canonical indexed extern signatures still need the shared closed runtime/
administrative-stack migration. No valid matching-indexed import failure is
counted as passing final-spec conformance. The forced negative global-link
fixture uses genuinely different referenced function types at source index 0.

## Regression scope and remaining whole-module proof

New binary checks cover the exact fixed bytes, indexed-global execution,
out-of-scope/max-index and wire-overflow classification, unreachable `ref.null`,
inline indexed block results, typed selects, table/element types and typed
imports. All earlier official commands/expectations remain unchanged.

The actual recursive production parser is now factored into the shared
`parse_be_layer` / `language_step` interfaces without changing its alternatives.
The shared structural soundness proof is adapted with an explicit `try_table`
grammar production and the **concrete proved catch-vector grammar**.
Its atomic and block contracts remain explicit parameters: this is not a
discharged concrete full-expression iff or a whole-module theorem.

Still open: concrete full atomic grammar/recursive completeness, recursive
declaration/record/segment composition and the final actual module round-trip/
general iff assembly. No generic theorem is claimed to cover those obligations.
The parser repair itself does not wait for GC; runtime indexed transport remains
separate.

## Verification for this increment

Full exact-tree build, forced tests and relevant `coqchk` pass, including the
actual validator/instantiation soundness and preservation modules. The binary
driver has **163 positive commands** and detects the same 12 deliberate
wrong-outcome/stage failures. Independent wasm-tools validation agrees on all
18 new source-position binaries (including individually valid modules in the
negative cross-module link test).

The audited source value/global/block codecs, printer-prefix contracts and
indexed-cache rejection theorems are globally closed. The connected actual
validator source-closing theorem retains the already disclosed inherited
classical real-decision/extensionality assumptions. The structural expression
soundness theorem's `PrimitiveSound` / `BlockSound` parameters are explicitly
printed in the audit; they are **not discharged or disguised as a concrete
whole-module result**.

Official EH remains **489/489 binary commands + 18 mapped text-only deferrals**.
Indexed payload probes remain **7 PASS / 3 FAIL**, with two required-success
link failures and an invocation cascade, not executed transport. Strict core
remains **53,999/54,004**, 148 files, zero infrastructure errors, the same five
alignment expectations.

Logs: `/tmp/opencode/eh-source-codec-final-build.log`,
`/tmp/opencode/eh-source-codec-final-tests.log`,
`/tmp/opencode/eh-source-codec-final-coqchk.log`,
`/tmp/opencode/eh-source-codec-assumptions.log`,
`/tmp/opencode/eh-source-codec-official.log`,
`/tmp/opencode/eh-source-codec-indexed.log`,
`/tmp/opencode/eh-source-codec-core.log`.
Fixture validation/hashes: `/tmp/opencode/eh-source-position-fixtures/validation.json`.
