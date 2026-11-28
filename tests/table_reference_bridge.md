# Remaining table reference bridge: strict failing handoff

At `42f0b2c`, the unchanged original table suite reports **2946/2956**;
`table.wast` is **50/60**. Three quoted-text cases (#21–23) remain deferred.
The seven non-text failures are **two root module validation failures and five
dependent invokes**, not seven independent table64 failures:

| Original command | Source lines | Actual failure | Required contract |
|---|---:|---|---|
| #47 provider | 110–114 | Parses; module validation rejects the indexed, non-null global initialized by `ref.func $f` | Classify `ref.func` by the function's closed defined type, and match it against the declared reference closed under the module's actual names |
| #49 consumer | 117–134 | Parses; fails validation **before linking**, independently of whether provider #47 exists | Defined-function references match their own non-null type and the abstract `func` supertype; imported global initializers and getter results use closed reference matching |
| #50 `get1` | 136 | Missing export: consumer #49 was not instantiated | After the root fixes, the default nullable `funcref` table returns null |
| #51 `get2` | 137 | Missing export | Abstract table initialized by `ref.func` returns a non-null function reference |
| #52 `get3` | 138 | Missing export | Non-null indexed table initialization, stored classification and indexed-to-abstract getter result matching |
| #53 `get4` | 139 | Missing export | Canonical imported-global matching plus defined-function-to-abstract matching for the initializer/result |
| #54 `get5` | 140 | Missing export | Canonical imported-global matching, non-null indexed initializer/storage and getter result widening |

The intervening #48 `register "M"` misleadingly succeeds by registering the
previous default instance after #47 failed. It does not establish a valid
provider. The five missing exports therefore are **not** evidence of five
table addressing or result-assertion defects.

All tables in this failing source fragment are table32. The reductions repeat
the independent failures at **both address widths**, alongside passing abstract
reference controls. Neither a width change nor a codec workaround fixes them.

## Reproduce and preserve the failures

```text
dune build -j 1
python3 tests/table_reference_bridge.py \
  _build/default/src/wasm_coq_interpreter.exe \
  --emit /tmp/opencode/closed-reference-handoff
# equivalently, the explicit strict handoff gate:
dune build @closed-reference-handoff -j 1
```

This gate deliberately returns **nonzero** until the bridge satisfies the
expected semantics. It is not an xfail, an assertion rewrite, or a green
conformance count. The original official suite still runs all 60 table commands.
The explicit handoff alias is separate from the green default `runtest` alias
because it preserves the already disclosed bridge failures. Do not advertise
default test success as this gate passing.

The 19 reductions currently produce **8/19**, including:

- indexed `ref.func` globals, non-null indexed table initializers and their
  equivalent-signature source aliases (currently rejected);
- abstract reference controls (accepted);
- imported indexed global → exact indexed table (validation accepted), versus
  indexed global → abstract `funcref` table (currently rejected);
- nullable indexed table → abstract `funcref` getter (currently rejected);
- the reduced eight-command official dependency chain;
- a positive link with producer source index 0 and consumer source index 1 but
  the same closed function type;
- a negative link with the **same raw source index 0** but incompatible closed
  function types. It must reject linking, never accept by raw index equality.

These exact binary modules were independently validated with the pinned
wasmtime-py 51.0.0 reference engine (memory64/function-reference/GC features
enabled). The reference engine accepts every intended-valid module, rejects
the wrong-signature global, runs both positive linked scripts with the expected
null/function results, and rejects the incompatible import: **19/19** expected
outcomes. No WAT frontend is needed to encode the reductions.

`theories/table_reference_bridge_tests.v` checks **only the positive source
boundary**: production module codec roundtrips and canonical source-context
validity of the reduced provider, indexed table, getter and imported
initializers, at both widths. It does not count their current semantic
validation rejection as successful conformance.

## Exact shared contracts needed

1. **Validation/classification:** after closing the module's groups and
   obtaining `registry, names`, a source `(ref h)` is closed with
   `close_value_type names 0`. A declared function's `ref.func` has the
   corresponding **non-null defined function type**, not only abstract
   `(ref func)`. Function-kind checks must consult the defined declaration;
   an aggregate at a valid source index is not a function type.
2. **Closed matching:** non-null defined function references match their
   identical defined type and nullable/abstract `func` supertypes. Reject
   incompatible signatures/kinds. Apply this to global/table initializers,
   imported globals, table gets and exported function results. The current
   `reference_type_matches`/instruction checker path does not discharge it.
3. **Stored descriptors and imports:** producer globals/tables carry their
   closed descriptors. Classify stored function references with the store's
   canonical registry. Close consumer declarations under the **consumer**
   names before import matching. Do not reinterpret a source `HT_type i`
   as a runtime `Def_type`, and do not compare producer/consumer raw indices.
4. **Null lowering:** default nullable indexed table values must be lowered
   under that table's defining names to its closed heap type before allocation.
   Preserve nullable vs non-null rules and explicit initializers. The original
   `get1` uses abstract nulls, but the indexed-default getter reduction also
   checks this necessary storage boundary after validation is repaired.
5. **Width/storage preservation:** closing and matching must leave each
   table's `tt_address_type`, limits and compact persistent storage intact.
   `table.get` still consumes the independently selected i32/i64 address.
   No host-sized narrowing, eager allocation or resource policy change.

GC owns these existing closed-descriptor/classifier/matching/null-lowering
contracts. This handoff adds no competing runtime representation.

## Existing proof closure, not new runtime milestones

The actual production parser already has
`run_parse_module_general_correct` / `run_parse_module_str_general_correct`
against its independent consumed-byte grammar, and
`binary_of_module_roundtrip` under explicit AST/field/count bounds.
They cover actual parser behavior, not full Wasm validation or unimplemented
ordinary indexed expression syntax.

The table declaration contracts are
`parse_table_type_source_sound`, `parse_table_type_source_complete`,
`binary_of_table_type_source_encoding`, `parse_module_table_sound` and
`parse_module_table_complete`. The 59 address-body statements remain unchanged.
The audited storage results listed below, the concrete table codec handoff,
scalar/SIMD memory body codecs and `b_e_type_checker_reflects_typing` are
**closed under the global context**. `run_parse_module_general_correct`,
`run_parse_module_str_general_correct` and `binary_of_module_roundtrip` retain
`ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec`,
`Classical_Prop.classic` and dependent functional extensionality.

The width-aware `run_one_step_ctx`, `t_preservation`, `instantiation_sound`
and `interp_instantiate_imp_instantiate` retain those same assumptions **plus
the existing ordinary-SIMD operation parameters**
`SIMD_ops.app_vunop_str`, `app_vtestop_str`, `app_vternop_str`,
`app_vshiftop_str` and `app_vbinop_str`. These are disclosed existing trust
boundaries, not new admissions or relaxed SIMD checks. `run_one_step_ctx`
also has its explicit caller-supplied host-application correctness premise;
that is not a proof about callback evaluation timing or native resources.

Compact storage already has `TableStorage.size_spec`, `repeat_spec`,
`append_spec`, `get_spec`, `set_spec`, `set_size`, `all_spec` and the proved
binary count wrappers. Those pure results do not prove native OOM handling,
callback effects or evaluation timing. Resource/callback policy is unchanged.
