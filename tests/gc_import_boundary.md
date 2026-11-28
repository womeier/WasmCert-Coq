# Canonical function import boundary

## Exact specification and reference provenance

Wasm Core 3.0 pin:
[`d7aada502455b3d9176ca4cbe48be4724d511d2a`](https://github.com/WebAssembly/spec/tree/d7aada502455b3d9176ca4cbe48be4724d511d2a).

- `document/core/valid/matching.rst`, **Defined Types**: matching is equality
  after closure, or follows an explicitly declared supertype. Expansion to the
  same function signature is not a defined-type equivalence rule.
- The same file, **External Types / Functions**: match the defined types.
- `interpreter/valid/match.ml`: `match_externtype` calls `match_deftype`;
  that compares substituted defined types, then follows declared supertypes.
- `interpreter/syntax/types.ml`: defined types retain their entire recursive
  group and member projection. This is not an arbitrary inequality of IDs.

The exact pin was downloaded from its GitHub codeload archive and built locally
with `dune build -j 1 wasm.exe` in `interpreter/`. Archive SHA-256:
`440e4dba14fdf4479cbd197602113373d8daa56539bcc9690bfea1d786016e87`.
The preinstalled `wasm 2.0.2` was **not** used as the GC reference.

Both reference and production execute `gc_import_boundary_binary.py` successfully:

1. A producer with one explicit recursive group `[struct []; func [] -> []]`
   exports a function of member type 1. An identical-group consumer imports it,
   and invoking the imported function succeeds.
2. Changing the consumer group to `[array i32; func [] -> []]` must fail linking,
   not validation. Both function expansions are `[] -> []`, but the closed
   recursive types differ and neither declares a supertype.

These are **2 semantic cases / 5 script commands**. Production must report
`Result: 5/5`; the reference must successfully execute both assertions.
Every module is supplied as literal binary, without a GC text assembler.

<pre>
python3 tests/gc_import_boundary_binary.py _build/default/src/wasm_coq_interpreter.exe
python3 tests/gc_import_boundary_binary.py --reference /path/to/pinned/interpreter/_build/default/wasm.exe
python3 tests/gc_import_boundary_binary.py --emit /tmp/opencode/canonical-import-boundary.wast
</pre>

Complete module bytes:

<pre>
producer:
0061736d01000000 0108014e025f00600000 03020101 07050101660000 0a040102000b

identical-group consumer:
0061736d01000000 0108014e025f00600000 020701017001660001 07050101660000

different-group consumer:
0061736d01000000 0109014e025e7f00600000 020701017001660001 07050101660000
</pre>

## Proof boundary and completeness contract

`closed_completeness_boundary_regression.v` proves the typed-store,
validated-module counterexample to the historical raw-signature premise.
`canonical_import_properties.v` states independent relational matching:
defined-type paths for functions; invariant table references; covariant
immutable globals; invariant mutable globals; and subtype limits.
It proves equivalence to the executable closed descriptor matcher and actual
external-type/import checker. Successful actual instantiation implies this
checked boundary as well.

`interp_instantiate_complete` now takes `canonical_module_imports`, replacing
the false historical source `import_subtyping` premise. The relation includes
only checked declaration closure and relational import matching: no successful
instantiation, initializer result, or output-store typing is assumed.
`interp_instantiate_closed_identity_profile_complete` recovers the equality
profile only when actual source closing yields the same canonical descriptors.

`instantiation_code_typing.v` adapts the exact `fe3c7ea` proof idea to the
current generated code. The current single-memory profile proves an active
data segment's selected index is zero from its validated bound; it does not
silently replace an arbitrary index. `instantiation_sound_with_code` types
the actual generated pending segment/start code and returns closed
configuration typing. The original public store/frame theorem is preserved.

`closed_extraction_safety.v` connects the actual `Extraction_instance` parse
result, instantiate wrapper, context decomposition and `run_one_step` entries.
Every finite execution prefix preserves configuration typing and context
validity; traps/divergence remain allowed, while invalid/ill-typed outcomes are
excluded and successful initialization returns no values. Its parser premise
is the **actual parser result**, not an independent whole-module binary codec
correctness claim. Existing parametric host, array-backend and ordinary-SIMD
trust obligations remain explicit.
