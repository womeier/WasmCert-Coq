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

## Measured baseline and diagnosis

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
