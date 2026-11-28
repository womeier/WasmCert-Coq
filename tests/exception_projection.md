# Final-EH non-text binary projection

The official source files are **not edited**. `wasm-tools json-from-wast` is
an external test encoder, not WasmCert text-format support. The extracted
WasmCert parser, validator, instantiator and interpreter execute the binaries.
The JSON driver is used because the old external WAST frontend cannot parse
final-EH script syntax, including `assert_exception`.

1. `dune build -j 1 tests/eh_script/eh_script.exe`
2. `python3 tests/prepare_exception_binary.py --wasm-tools /path/to/wasm-tools --output /tmp/opencode/eh-official-binary`
3. `python3 tests/run_exception_binary.py /tmp/opencode/eh-official-binary`

The output directory must be new/empty. Preparation records the suite revision,
encoder version/executable hash, source and binary hashes, and **every** source
command's ordinal, line span, byte span and hash. Only `assert_malformed` modules
reported by the encoder as text are deferred. Encoder failure, unsupported
commands, source-map disagreement or changed artifacts are errors, not skips.
Actions, registration and all other assertions are retained in order.

At testsuite `b497cbb853db21be875bd5c81fcc3334168fb0b4`, the eight files contain
**507 commands**: **489 binary-scope commands** and **18 deferred text-only
malformed assertions**. The latter are at `imports.wast` lines
615, 619, 623, 627, 632, 636, 640, 644, 649, 653, 657, 661, 666, 670, 674, 678,
and `try_table.wast` lines 339, 344. They are not passes.

Results are recorded for every retained command, with its original provenance.
The runner exits nonzero for any assertion or infrastructure failure. It
distinguishes parsing, validation, import matching, traps and exceptions.
Successful actions retain their store changes; registration adds an alias
without moving the original module or changing the default instance.

`dune test -j 1 --force` includes independent binary-driver and source-mapping
regressions without requiring an installed external encoder. **It does not
replace the explicit full official projection run above** or bless its failures.

## Initial measured baseline and diagnosis

With the EH implementation at `884aa80` and this harness, externally encoded by
wasm-tools **1.263.0** (`7a2fa422c`, executable SHA-256
`694cb37dcda84a5d557334c1db882b986e43061abdb0af976b41b1614ee4530b`):

| Official source | Passed / retained commands |
| --- | ---: |
| binary.wast | 136 / 136 |
| exports.wast | 96 / 97 |
| imports.wast | 133 / 168 |
| ref_null.wast | 4 / 4 |
| tag.wast | 1 / 4 |
| throw.wast | 13 / 13 |
| throw_ref.wast | 15 / 15 |
| try_table.wast | 8 / 52 |
| **Total** | **406 / 489 (FAIL)** |

There are **zero infrastructure errors**, unlike the original WAST run's seven
external-parser crashes. These results do **not** make the official suite pass.
The 83 failed commands comprise:

- Six ordinary modules rejected by the actual binary parser: `imports.wast`
  lines 3, 30; `tag.wast` lines 3, 13; `try_table.wast` lines 3, 10.
  These modules contain final tag imports or exports, which are not yet
  represented in the main import/export syntax.
- Five `assert_unlinkable` commands fail **at parsing**, not import matching;
  these are failures, not successful negative assertions.
- One duplicate-tag-export `assert_invalid` at `exports.wast:70` fails
  **at parsing**, not validation; it is a failure.
- Forty-five subsequent commands lack a default instance and 26 encounter
  unresolved imports after failed setup. These remain failed commands in the
  aggregate, not skipped assertions or evidence of handler execution.

In particular, `try_table.wast` tests at lines 258–313 have not executed their
intended imported-tag instance. Its 8/52 is not broad official handler coverage.
The separate 81-case binary handler regression suite remains relevant but is
not substituted for these source commands.

## Parser proof handoff to the common parser owner

The merged EH-aware production contracts are in
`theories/gc_binary_parser_properties.v` (available through `884aa80`):

- `shared_reference_parser_correspondence` equates
  `run_parse_prefix (fun _ => parse_reference_type) bs` with
  `decode_shared_reference bs`, including rejection and remaining bytes.
- `shared_reference_parser_correct` gives the iff with
  `shared_reference_encoding bs rt rest`.
- `exception_reference_codec_roundtrip` uses the **actual** printer/parser for
  both nullabilities of `HT_exn`/`HT_noexn`, with an arbitrary suffix.
- `shared_reference_parser_consumes` proves a one- or two-byte prefix.

The grammar includes GC abstract heaps and the exception hierarchy; indexed
heap descriptors use the separate declaration parser. These contracts do not
claim a verified whole-module parser or general instruction correspondence.
All four contracts are globally closed, with no added axioms.

## Shared closed-payload handoff

The GC-owned runtime classifier, expected-type closing and producer null
lowering must supply the following semantic laws (names for pending judgments
are schematic, not new EH definitions):

- Given `inst_typing s inst = Some C` and
  `close_function_type inst.(inst_defined_types) 0 (Tf ps []) =
  Some (Closed_ft cps [])`, the actual contextual payload-typing check in that
  frame agrees with `closed_values_typing s fields cps`. This is **not** a law
  about the current context-free `values_typing s fields ps`; the compiled
  `source_payload_transport_counterexample` disproves that shortcut.
- `store_extension s s' -> closed_values_typing s fields cps ->
  closed_values_typing s' fields cps`, with existing successful
  `expand_function_type` results stable under that extension.

EH then owns the concrete tag and exception adaptation: resolve each tag's
canonical `defined_type`, require expansion to `Closed_ft cps []`, type its
exception fields with the shared judgment, and match expected/provided tag
identities with `defined_type_equiv` in the same extended registry. This
requires both directions of canonical matching, not equality of expanded
payloads or module-local index numbers. Imported tag addresses precede local
addresses in `inst_tags`; catches retain actual tag-address identity.

The existing `validated_closing_portable` proof at authorized GC `a1b7949`
addresses registry closing, not this runtime payload law. No duplicate
portability proof, classifier, or raw-index transport is introduced here.

## Main tag extern-kind integration: 445/489

The next implementation increment adds main `MID_tag`, `MED_tag`, `EV_tag`
and source/cache `ET_tag` descriptors. Binary imports use kind 4, attribute
zero, then u32 type index; exports use kind 4 then u32 tag index. Source
validation checks the referenced declaration is a function with no results.
The tag context and allocation use imported tags before locally defined tags.
Tag exports preserve their actual tag address and can be registered, aliased,
and distinguished from function/table/memory/global exports.

Full main checker soundness, instantiation soundness, preservation and progress
continue to compile. Compiled examples exercise a module that imports one tag,
throws local tag 1, exports that local tag, and round-trips through the actual
module printer/parser. The actual import parser rejects every nonzero attribute;
concrete descriptor round trips include multi-byte and maximum-u32 indices.

The **unchanged 489-command projection now fails at 445/489**, zero
infrastructure errors. The same 18 text-only malformed commands remain deferred.

| Official source | Passed / retained commands |
| --- | ---: |
| binary.wast | 136 / 136 |
| exports.wast | 97 / 97 |
| imports.wast | 165 / 168 |
| ref_null.wast | 4 / 4 |
| tag.wast | 3 / 4 |
| throw.wast | 13 / 13 |
| throw_ref.wast | 15 / 15 |
| try_table.wast | 12 / 52 |
| **Total** | **445 / 489 (FAIL)** |

All prior tag extern-kind parsing failures are resolved. The three remaining
root failures are now **concrete tag import matching**, at `imports.wast:30`,
`tag.wast:13`, and `try_table.wast:10`; these modules parse and validate. Their
41 dependent action failures remain failures. The function-only imported
`try_table` mismatch case at lines 315–337 now executes successfully, but the
main imported-tag handler tests at lines 258–313 still do not.

**No final tag linking claim:** `ET_tag ps` is expressly a source signature/cache,
not a canonical identity. The current concrete `import_subtyping` does not
accept such caches, even when equal. EH still needs the per-tag canonical
`defined_type` store wiring and actual closed import-matching boundary, plus
the shared GC payload/classifier law above for general indexed payloads.
Scalar-only tag fixtures are not grounds for a payload-equality shortcut.
The proved no-source-tag lemmas document the present executable boundary; they
do not add premises to existing safety theorems or stand in for canonical linking.

New extracted binary tests cover tag exports/aliases, duplicate and unknown tag
exports, import attribute/truncation/overflow, invalid tag signatures and
tag/function kind separation. CLI host loading validates before resolving host
imports, so a missing provider cannot mask an invalid import declaration.
Full official artifacts are in `/tmp/opencode/eh-tag-extern-official-binary/`.

## Canonical per-tag linking: 489/489

The following implementation increment resolves all three root imports and
their 41 cascades. The **same 489 binary-scope commands now pass 489/489**, with
zero infrastructure errors. All eight projected files pass, including
`imports.wast` 168/168, `tag.wast` 4/4 and `try_table.wast` 52/52. The same 18
mapped text-only malformed commands remain deferred and are not passes.
Artifacts are under `/tmp/opencode/eh-canonical-tag-official-binary/`.

Each tag address now has a canonical `defined_type` in `s_tag_ids`. Allocation
uses the module's actual `inst_defined_types` map, retains old identities, and
preserves imported-before-local tag address order and re-exports. Store typing
requires equal lengths for the identity table and `s_tags`; store extension preserves
old tag IDs and their registry meanings.

Both the executable instantiator and relational `instantiate` require the
nominal `module_tag_imports_matching` check. It resolves the expected import's
type index through the newly closed module map; looks up the provided tag's
stored canonical ID; checks the actual signature in the **old** registry and
the expected signature in the extended registry; requires empty results and
bidirectional `defined_type_equiv`. Missing, invalid or future-only provided
IDs cannot be accepted using the new registry. Payload equality alone is not
tag identity.

The existing source-typed runtime additionally uses `portable_tag_parameters`:
both compatibility signatures must close without local type names and compare
equal as **closed** function types. `portable_tag_parameters_equal` proves the
source-cache agreement used by the connected preservation/instantiation
proofs; the executable does not compare source indices as an identity test.
`CH_defined` payloads are not erased or reconstructed from local numbers.

Explicit properties in `instantiation_properties.v`:

- `tag_import_matching_correct`: iff with two directed canonical matches,
  checked expansions and closed cache agreement.
- `tag_import_matching_store_extension` and
  `tag_import_matching_registry_extension`: stable checks under store/registry
  extension (the latter assumes the existing canonical supertype well-formedness).
- `tag_import_matching_closed_signature_agreement`: the actual and expected
  canonical types expand to the same closed parameter list.
- `alloc_module_tag_defined_identity`: allocated addresses, including the import
  offset, have exactly the ID selected by the module's closed type map.

`instantiated_tag_canonical_signature` in `instantiation_sound.v` connects actual
instantiation, tag-address lookup, the stored ID, source closing and canonical
signature expansion. Existing main soundness/preservation statements retain
their premises; nominal matching is an actual required instantiation check.
The matcher/extension/signature-agreement proofs are globally closed. Connected
allocation/instantiation proofs retain disclosed inherited assumptions.

Extra binary regressions distinguish equal payloads and equal source index
numbers from canonical identity, reject directed child-to-parent tag matches,
and exercise successful import/re-export/import chains. Extracted store tests
inspect canonical IDs across repeated allocation, mixed type-index order and
extension with existing exceptions. No official commands/expectations changed.

**Not general final-EH completeness:** all pinned official binary commands pass,
but indexed-payload tag imports cannot yet cross the legacy source-typed runtime
boundary. Such imports fail the explicit portability check rather than aliasing
raw indices. GC's main closed storage/context/classifier/null-lowering migration
is still required to replace this restriction with contextual closed payload
typing. GC `b2fbd83` was inspected; no unfinished migration or competing runtime
descriptor model was imported. Existing GC39 expansion and bidirectional
equivalence contracts suffice for this nominal tag-linking increment.

Additional indexed-payload probes deliberately remain red; their exact stages,
canonical-ID diagnostics and the connected GC/common-parser handoff contracts
are recorded in `exception_payload_handoff.md`. They are not included in the
489/489 claim, and no text deferral is used for their binary failures.
