# Extended-const non-text completion audit

## Verdict

The current compact AST's binary parser/printer, relational validator, sequential
global evaluator and initializer/allocator connections are proved. The complete
mapped **current-AST** final-spec profile passes **437/437 script commands**.
This is **not** a claim that every unchanged final-spec binary is supported, nor
an unqualified end-to-end runtime safety theorem. Keep the PR draft for review.

One proof connection remains: derive `config_typing` for the **pending active
element/data initialization and start instructions returned by instantiation**.
`instantiation_sound` gives a typed store and frame, but not that instruction
typing conclusion. Generic preservation/progress require it; they must not be
silently applied on frame typing alone. Active initialization/start may
legitimately trap: completeness must not promise trap-free execution.

## Proof entry points

All names below are actual compiling definitions/theorems, not framework
parameters or assumptions of atomic completeness.

| Stage | Import and public entry points | Contract/boundary |
|---|---|---|
| General actual binary parsing | `binary_format_module_complete`: `run_parse_module_general_correct`, `run_parse_module_str_general_correct`, `production_parse_module_general_complete_eof`, `run_parse_module_general_rejected` | Whole-input iff independent `module_binary_encoding`; bounded padded LEBs, exact sizes/consumption, customs, all eight element and three data source forms. No printer-image restriction. |
| Order/count/custom erasure | `binary_format_module_sound`: `run_parse_module_general_invariants`; `binary_format_module_grammar`: `module_sections_encoding`, `module_sections_erasure` | Unique ordered ordinary sections; function/code counts; data-count value and required presence; custom bytes consumed but erased semantically. |
| Actual module printer | `binary_format_module_roundtrip`: `binary_of_module_roundtrip`, `binary_of_module_string_roundtrip`, `production_module_printed` | Explicit structural `module_binary_wf` wire bounds, not semantic validity. Canonical parent/tail handoff is `ea96c78`; general codec handoff is `bc7c190`. |
| Validator | `module_validation_complete`: `module_type_checker_spec`; `extended_const`: `extended_global_type_checker_reflects`, `extended_globals_type_checker_reflects` | Relational module typing iff actual validator success; global contexts grow by preceding globals, not future globals; immutable reads only. |
| Constant evaluation | `extended_const`: `interp_get_const_sound`, `extended_init_value_typing`; `extended_const_complete`: `interp_get_const_complete` | Successful evaluator refines actual reduction; validated expressions terminate with a typed value under an explicit typed function/global environment. |
| Sequential globals | `extended_const`: `interp_global_chain_sound`, `interp_global_chain_results`; `extended_const_complete`: `interp_global_chain_complete` | Sequential stores/frames, preceding-global reads, result typing, environment growth. No circular assumption of typed output store. |
| Module initialization | `extended_const_complete`: `module_initializers_complete`, `interp_instantiate_complete`; `interp_instantiate_sound`: `interp_instantiate_imp_instantiate`; `instantiation_sound`: `instantiation_sound` | Typed imports/subtyping and a typed input store yield global/element initialization and allocation; success refines relational instantiation and yields a typed store/frame and store extension. Pending segment/start code is not yet a proven typed configuration. |
| Connected binary-to-allocation result | `extended_const_end_to_end`: `binary_valid_module_instantiation_complete`, `printed_valid_module_instantiation_complete` | Independent grammar + relational validity + typed imports/store imply actual parse and instantiation success, relational instantiation, typed output store/frame and extension. The printer corollary discharges grammar membership, rather than assuming it. |
| Runtime | `type_preservation`: `t_preservation`; `type_progress`: `t_progress_interp_ctx`; `interpreter_ctx`: `run_one_step_ctx`, `interp_cfg_of_wasm` | Preservation/progress for typed configurations; dependent interpreter step refines reduction, under the explicit host-application contract. Does not discharge the pending-code gap above. |

Audits of these theorem dependencies expose exactly the inherited
`ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep`, and
`Classical_Prop.classic`. No additional axioms/admissions were introduced.
The arbitrary-custom codecs/iteration and custom-prefixed absence audit closed.

### Trusted executable boundary

`theories/extraction_instance.v:134` aliases the production
`run_parse_module_str`; `src/extraction.v` extracts `Extraction_instance`.
The executable uses the proved validator, initializer and interpreter definitions.
Coq extraction, OCaml compilation/runtime, handwritten numeric/SIMD/array shims,
`lookup_N`'s machine conversion, external encoders, WAST driver and host
implementation remain trusted—not kernel-proved executable equivalence.
`Parametric_host` explicitly requires host store-extension, typing and result
agreement contracts. These are not replaced with dummy host semantics.

Compact source `ref.func` indices are looked up in the allocated function
environment; no indexed heap type/source index is identified with a runtime
canonical identity. Non-null/indexed/EH reference codecs, GC, full memory64/table64,
text implementation and relaxed SIMD are not added by this work. Final-u64
memargs remain decoded without narrowing; memory32 validation is separate.

## Complete official-source provenance

Final sources are the immutable WebAssembly/spec **`wg-3.0`** revision
`9d36019973201a19f9c9ebb0f10828b2fe2374aa`, `test/core/{global,data,elem,align}.wast`.
There is no `test/core/extended-const.wast` at this revision (HTTP 404); final
extended-const cases are integrated into global/data/elem.
The originals are preserved byte-for-byte under
`.test-artifacts/end-to-end-audit/originals/`, with source URLs/SHA256s.
The committed projection script enforces those hashes.

Encoder: **wasm-tools 1.263.0 (7a2fa422c 2026-10-30)**, SHA256
`694cb37dcda84a5d557334c1db882b986e43061abdb0af976b41b1614ee4530b`.
It is used read-only, not implemented or replaced here. Every top-level source
command is matched in order to its external `json-from-wast` command, source
span/line, original source text/hash and encoded file/hash. Binary originals are
kept. There is no outcome-driven exclusion.

### Exact final-spec accounting

The runner counts module setup/register/action commands as tests too.
The profile contains **308 assertions**, not 437 assertions.

| File | Original commands | Included commands passed | Included assertions | Text-only deferred | Outside current AST |
|---|---:|---:|---:|---:|---:|
| global | 124 | 120/120 | 110 | 3 | 1 |
| data | 65 | 65/65 | 34 | 0 | 0 |
| elem | 151 | 133/133 | 70 | 0 | 18 |
| align | 165 | 119/119 | 94 | 46 | 0 |
| Total | 505 | **437/437** | **308** | **49** | **19** |

Exact text-only malformed WAT source lines:

* global: **685, 692, 699**.
* align: **27, 33, 39, 45, 51, 57, 63, 69, 75, 81, 87, 93, 99, 105,
  111, 117, 123, 129, 135, 141, 147, 153, 159, 165, 171, 177, 183, 189,
  196, 202, 208, 214, 220, 226, 232, 238, 244, 250, 256, 262, 268, 274,
  280, 286, 292, 298**.

These are encoder-designated text modules in `assert_malformed`, not valid
modules omitted because of text parser limitations. A non-malformed text module
causes the adapter to fail rather than be silently deferred.

Non-text cases **outside the current compact reference/table AST**, not
mislabelled text-only:

* elem: **87, 315, 448, 453, 465, 470, 482, 487, 499, 504, 516, 524, 539,
  544, 556, 561, 573, 578**: non-null `(ref func)` and/or table initializer forms.
* global: **674**: table initializer `(global.get $g)`, an unsupported table
  constructor. Its invalidity must not be claimed to be checked by this AST.

Two explicit adapters are recorded, never presented as unchanged-source input:

1. global **634**: externally reencode the redundant table initializer
   `(table $t 10 funcref (ref.null func))` as `(table $t 10 funcref)`. Both
   initialize every entry to the same null function reference. This exercises
   the entire official definition-order module and its later global/data/elem
   assertions, but **does not prove acceptance of the original table-init
   binary**. Both binaries and the source variant/hash are preserved.
2. global **659**: spell generic `(ref.null)` as `(ref.null func)` in the old
   script harness. `get-elem` declares `funcref`; the exact null result is
   retained, not weakened to a wildcard.

Without the current-AST exclusions/default-null table adapter, the broader
external binary projection is **431/456**, not green: global **114/121**, elem
**133/151**, data **65/65**, align **119/119**. The original final text scripts
produce **data 65/65**, and **global/elem/align crashes**, with no valid aggregate
pass claim. These logs remain available.

### Historical suite/version replacements

The untouched pinned testsuite `b497cbb853db21be875bd5c81fcc3334168fb0b4`
was rerun: **53,978/54,004**, **148 summaries**, no missing summaries or crashes.
Its original extended-const proposal files (verified identical to
`proposals/extended-const` in that archive) remain **284/290**.
Neither unchanged suite is green.

The six stale preceding-global expectations are precisely:

| Historical root line | Proposal line | Final positive replacement |
|---|---|---|
| data 84, 88 | data 84, 88 | final data **89, 90** |
| elem 170, 174 | elem 170, 174 | final elem **178, 182** (global.get on lines 180, 184) |
| global 351, 355 | global 363, 367 | final global **373, 374** |

They formerly expected `unknown global` for a defined preceding immutable global;
the final spec permits it. The six original assertions are retained, not flipped
in place or added to a fabricated passing total.

The five stale alignment expectations are historical align
**891, 910, 929, 948, 967** (all formerly `assert_malformed`):

* Flags 32, 33, 63: final align **891, 910, 929** require validation failure for
  over-natural alignment, not malformed decoding.
* Flags 65: historical **967** maps to final **948**, validation `type mismatch`
  after decoding explicit-memory syntax. Flags 64 at historical **948** are
  removed from final align; existing memarg regressions retain explicit flags
  64/65 coverage. No restrictive decoding guard is restored.

The remaining 15 historical failures are also retained and listed with full
source text in `historical-failures.json`: binary **125, 145, 165, 184, 203,
223, 242, 261, 279, 297** assume reserved memory.size/grow bytes rather than
current LEB memory indices; imports **487, 491, 495** and memory **10, 11**
forbid multiple memories. Do not claim fixing these old expected outcomes is
new feature coverage.

## Reproduction and gates

Run from the `extended-const-mechanization` worktree. `$ENCODER` is the existing
wasm-tools binary above. `$ORIGINALS` is the preserved official-source directory;
the script verifies all four SHA256s before projecting.

```sh
python3 tests/extended_const_official_projection.py \
  --encoder "$ENCODER" --originals "$ORIGINALS" \
  --output .test-artifacts/end-to-end-audit/current-ast-profile \
  --current-ast-profile --runner _build/default/src/wasm_coq_interpreter.exe
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh \
  .test-artifacts/testsuite-b497cbb853db21be875bd5c81fcc3334168fb0b4
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh .test-artifacts/proposal
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh "$ORIGINALS"
dune build -j 1
dune test -j 1 --force
```

The projection gate requires successful exit, exactly one valid summary per
file, and exact equality to the accounted included command count. It retains
every file's output and writes `provenance.json`/`results.json`. The broader
projection is reproduced by omitting `--current-ast-profile`; its failure is
expected and recorded, not ignored.

The ordinary Dune gate retains extended-const **22/22**, prior final binary
probes **6/6** (not official coverage totals), cross-feature **3/3**, framing
**40/40**, addressing **43/43**, scalar **16410/16410**, SIMD **78/78**, block
types **52/52**, multi-memory **181/181**, strict phase discrimination and runner
failure-summary tests. New tests cover binary named-module binding **4/4**,
duplicate-binding rejection, and four projection source-span/error cases.

Audit logs live in `.test-artifacts/end-to-end-audit/`. The audit found and fixed
the WAST driver's failure to bind `$name` on binary modules: previously later
register/actions failed although decoding/instantiation succeeded. No Coq
parser, validator, source reference interpretation or assertion was weakened.

## Review obligations

* Close the pending segment/start **configuration typing** connection before
  claiming a derived whole-instantiation-to-preservation/progress theorem.
* Shared reference owners must supply non-null/indexed/table-initializer codecs
  and safe closing agreement before the 19 outside-AST official cases can be
  claimed supported. The redundant-null adapter is not such a codec.
* Keep the explicit trusted extraction/host/driver boundary. The accepted trust
  model does not turn those handwritten components into Coq-verified code.
* Parent/user reviews scope, adapters and evidence. Do not mark ready or merge
  automatically.
