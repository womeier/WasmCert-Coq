# Canonical closed bridge: public handoff

This revision replaces the source-based stored/administrative bridge. It is
**not completion of GC aggregate/cast execution**. The PR remains draft.
The exact published commit is pinned in PR #3's description; use that commit,
not an unrelated proposal branch tip.

## Identity and stored descriptors

`theories/datatypes.v`:

- `defined_type := Def_type { defined_group : N; defined_member : N }`.
  Source `HT_type i` is never a canonical ID or runtime address.
- `closed_heap_type := CH_abstract heap_type | CH_defined closed_type_use`;
  operational defined references use `CT_def id`, not `CT_rec`.
- `closed_value_type := CV_num number_type | CV_vec vector_type |
  CV_ref bool closed_heap_type`. There is no storable bottom.
- `closed_reference_type := Closed_ref { closed_ref_nullable : bool;
  closed_ref_heap : closed_heap_type }`.
  `closed_reference_value` embeds it into `closed_value_type`.
- `closed_function_type` uses `Closed_ft` with closed value lists.
- `closed_table_type` and `closed_global_type` retain the existing limits/
  mutability fields, but reference/value descriptors are closed.
- `tableinst_type : closed_table_type`, `globalinst.g_type : closed_global_type`,
  `eleminst_type : closed_reference_type`.
- `moduleinst` retains flattened source declarations in `inst_types`,
  canonical source-index names in `inst_defined_types`, and its declared
  consumer view in `inst_context`. `Build_t_context` now has the final
  `tc_defined_types` argument. Preserve actual maps when constructing instances.

Checked closing in `gc_type_context.v`:

```coq
close_heap_type : list defined_type -> N -> heap_type -> option closed_heap_type
close_value_type : list defined_type -> N -> value_type -> option closed_value_type
close_function_type :
  list defined_type -> N -> function_type -> option closed_function_type
```

The `N` argument is the recursive-member scope; use `N0` for instance storage
and runtime declarations, not an arbitrary caller index.
`gc_declaration_typing.v` additionally provides:

```coq
close_reference_type : list defined_type -> reference_type -> option closed_reference_type
close_table_type : list defined_type -> table_type -> option closed_table_type
close_global_type : list defined_type -> global_type -> option closed_global_type
```

Closing remains checked and partial. Do not replace failure with an invented
source spelling or treat a source index as a `Def_type`.

## Values, classification and null lowering

`theories/typing.v` now exposes these signatures (implicit host parameters omitted):

```coq
typeof_closed_ref : store_record -> value_ref -> option closed_reference_type
typeof_closed_value : store_record -> value -> option closed_value_type
closed_value_typing : store_record -> value -> closed_value_type -> bool
value_typing : store_record -> list defined_type -> value -> value_type -> bool
source_value_typing : store_record -> moduleinst -> value -> value_type -> bool
values_typing : store_record -> list defined_type -> list value -> list value_type -> bool
lower_source_null : store_record -> moduleinst -> heap_type -> option value_ref
```

`source_value_typing s inst` is `value_typing s inst.(inst_defined_types)`.
Pass the **producing/declaring instance's actual names**, not `nil` or a
consumer's unrelated map. `closed_value_typing` validates and matches the
principal closed runtime type.

`VAL_ref_func address` classifies as a **non-null defined** reference through
`lookup_func_defined_type`. Native functions resolve their real instance/code
type index; host functions require canonical signature registration.
`ext_func_typing`/`cl_type` still expose source signatures for compatibility;
they are **not evidence of canonical import identity**.

Source `BI_ref_null (HT_type i)` executes a real lowering step under the
producing instance. Runtime null annotations preserve hierarchy (`nofunc`
versus `none`); source-indexed runtime null annotations are rejected.
The runtime administrative form is `AI_ref_null`, not an unchanged source
instruction. Use `lower_source_null_typed` and `lower_closed_null_typed`.

Identity/expansion APIs remain in `operations.v`/`gc_type_context.v`:
`funcinst_defined_type`, `funcinst_type_names`, `lookup_func_defined_type`,
`resolve_inst_type`, `expand_inst_function_type`, `expand_defined_type`,
`expand_function_type`, `defined_type_matches`, `defined_type_equiv`.

## Source and administrative typing

Source `be_typing` still uses `t_context`, `value_type`, and `Tf`.
Administrative typing is now closed:

- `closed_operand_type := CO_value closed_value_type | CO_bot`.
- `closed_operand_result_type := list closed_operand_type`;
  `closed_instr_type` uses operand-valued `Closed_ft`.
- `lift_closed_result_type` and `lift_closed_function_type` embed concrete
  runtime signatures into the operand calculus.
- `e_typing` takes `closed_t_context` and `closed_instr_type`.
- `thread_typing` takes optional closed operand results and closed operand
  results; `config_typing` takes closed operand results.
- `closed_frame_typing` derives its context from actual `inst_typing`, checked
  `close_t_context`, and typed concrete locals.

`CO_bot` is **proof-stack-only**: it has no accepted runtime values, no storage
descriptor, no null encoding, and no binary syntax.
`close_operand_type`/`close_instr_type` are checked.
`interpret_operand_type`/`interpret_instr_type` are proof-only interpretations
for structural source derivations; they must not be used to allocate storage,
validate imports, classify runtime values, or manufacture an intermediate type.

`closed_source_translation.v` supplies the actual source entry boundary:

```coq
source_structural_entry s source closed instructions signature :
  be_typing source instructions signature ->
  close_t_context source = Some closed ->
  e_typing s closed (to_e_list instructions)
    (interpret_instr_type source.(tc_defined_types) signature).
```

Use structural closed composition/subtyping/control proofs after entry.
Canonical runtime intermediates need not have any representable source spelling.
For table fill/copy/init, `closed_bulk_properties.v` uses the **stored**
canonical element descriptor and proved two-way matching. Keep exact generated
indices, operand order, bounds and zero-count branches.
`closed_context_properties.v` transports only permitted table/memory limits;
canonical descriptor identity, locals, names and operand slots stay fixed.
The `store_extension` invariant was not weakened.

## Imports, allocation and completeness

`external_typing s value` now returns/checks a **closed** external descriptor.
`closed_import_subtyping` is the executable per-kind matcher.
`canonical_import_properties.v` states independent `canonical_extern_matching`
and proves `canonical_extern_matching_correct`,
`external_import_checker_correct`, `canonical_import_checker_correct`, and
`successful_instantiation_checks_canonical_imports`.

Function matching follows closed defined-type equality/declared paths.
Tables are invariant in references; immutable globals are covariant; mutable
globals are invariant; limits match by bounds.
`canonical_module_imports s m actual` contains only actual checked declaration/
import closure and relational closed matching, **not assumed instantiation
success or output-store typing**.

`extended_const_complete.v:interp_instantiate_complete` retains its typed-store,
validated-module and actual external-typing premises and successful conclusion,
but **replaces historical raw source `import_subtyping` with
`canonical_module_imports s m actual`**. Raw signatures lose recursive-group
identity. The restricted `interp_instantiate_closed_identity_profile_complete`
requires checked closing to produce identical canonical descriptors.

`alloc_tabs` takes closed table descriptors with actual initial references;
`alloc_globs` takes closed global descriptors; `alloc_elems` takes closed
reference descriptors. `interp_alloc_module` returns an **option** and checks
storage closure/lengths. `const_frame_add_global` also takes the source global
descriptor to extend the declared context.

`allocated_module_initializer_registration` and `function_preview_properties`
derive registration from real validated allocation before unfinished globals
are typed. Sequential globals preserve actual names/functions/registry and
derive canonical value acceptance. Do not assume the entire preview store typed.

The original `instantiation_sound` store/extension/source-frame endpoint remains.
`instantiation_sound_with_code` and `instantiation_sound_configuration` also type
the actual generated segment/start code as a closed configuration.
`closed_extraction_safety.v` connects actual `Extraction_instance` parse-result,
instantiate-wrapper, context-decomposition and step entries, including all
finite execution prefixes. Traps/divergence are allowed; invalid/ill-typed
outcomes are excluded. Actual-parser acceptance is not an independent
whole-module codec-correctness theorem.

## Consumer migration and remaining scope

- **Typed references / tail calls:** close the expected signature in the
  consumer's names, use actual canonical IDs/expansion and
  `defined_function_matches_variance`/`closed_function_operand_inversion`, then
  lift concrete signatures to administrative operands. Do not equate raw source
  signatures, matching IDs, or arbitrary source indices.
- **Tables / memory:** retain closed stored descriptors and all limits, index,
  value-order, zero-count, width and resource-policy contracts. This bridge does
  not implement another proposal's width/storage changes.
- **EH:** reuse the shared identity/closing interfaces; tag execution/import
  integration is not claimed finished. Do not remove portability guards merely
  because the base bridge compiles.
- **Extended constants:** migrate to canonical matching and the actual registered
  preview allocation. The exact `fe3c7ea` pending-code/execution proof ideas were
  adapted; no unconstrained branch tip was imported.

Verified gates: full `dune build -j 1`, forced `dune test -j 1 --force`,
independent `coqchk`, extraction 1347/1347, vectors 3/3, references 19/19,
i31 48/48, sequential initializers 15/15, storage/null 14/14, recursive
declarations 25/25, canonical import boundary 2/2 semantic cases (5/5 commands),
strict assertion stages 4 positive/6 negative, constants 22/22, runner suites.
See `tests/gc_import_boundary.md` for exact final-spec/reference provenance.

The unchanged dependent table-reference script gate is **not passing**:
the installed script parser rejects `module definition` before validation.
Use existing external **binary** projection paths for subsequent feature work;
do not count this as semantic success or implement deferred text here.
Non-null indexed instruction typing, GC aggregates/casts and full conformance
remain unfinished. Text and relaxed SIMD remain excluded.
