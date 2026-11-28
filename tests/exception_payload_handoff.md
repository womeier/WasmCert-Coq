# Indexed EH payload handoff — not finished

The official non-text projection is **489/489**, with the same **18 explicit
text-only malformed deferrals**. This does not cover general indexed payloads.
The following additional binary probes retain their correct final-spec
expectations and currently **fail overall**; they are not golden failures,
invalid fixtures, skipped tests or substituted coverage.

## Minimal reproducible binaries and exact stages

1. Build `dune build -j 1 tests/eh_script/eh_script.exe`.
2. Run `python3 tests/exception_payload_boundaries.py --output /tmp/opencode/eh-indexed-payload-boundaries --wasm-tools /path/to/wasm-tools`.
3. Re-run existing artifacts with `python3 tests/exception_payload_boundaries.py --output /tmp/opencode/eh-indexed-payload-boundaries --run-existing`.

The generator emits raw binaries, binary hashes, source-index metadata,
requirements and JSON actions. `wasm-tools validate` independently accepts
**all six modules**; it does not execute any test. The extracted WasmCert
parser, validator, instantiator and evaluator are the system under test.
The driver reports actual stored and expected canonical IDs from the production
registry, canonical equivalence, portable-boundary status and exact failure stage.

| Probe | Required final behavior | Current observed behavior |
| --- | --- | --- |
| Same canonical reference, producer index 0 / importer index 1 | Parse, validate, link and re-export the tag | Producer/registration pass; consumer parses/validates but fails import matching. Actual and expected tag IDs are both `(7,0)`, canonical equivalence is **true**, portability guard is **false**. |
| Different canonical reference, both source index 0 | Parse, validate, reject at import matching | Correctly unlinkable. Actual/expected IDs are `(7,0)` / `(9,0)`, canonical equivalence **false**. The portability guard also rejects, so this negative result alone is not evidence that indexed nominal linking is complete. |
| Same canonical reference at different indices, indexed nullable local → imported emitter → throw → catch → `ref.is_null` | Link and return `i32 1`; local default must be lowered in its producer instance | Producer/registration pass; consumer fails binary parsing at its indexed local descriptor. The subsequent invocation failure is a cascade, not executed payload transport. |

Measured result: **7/10 commands, exit 1, zero infrastructure errors**.
Canonical ID numbers above belong to this fresh driver/spectest run, not to
module-local indices or hard-coded identity expectations. The fixture manifest
and driver results preserve the actual values and SHA-256 hashes.

The transport function has no text input. Its source type section already
uses the declaration parser's indexed-reference support. Its local declaration
is `(ref null type 1)` in binary, which currently reaches
`parse_locals -> parse_value_type -> parse_reference_type`; that last parser is
the proved **abstract** GC/EH fragment, not the indexed declaration grammar.
This is an explicit common-parser composition dependency. Do not weaken the
existing abstract parser iff/consumed-prefix contracts or special-case this
fixture. Once it parses, the same closed tag/function import and main runtime
context/default-lowering dependencies still need to be satisfied.

Artifacts from the measured run:
`/tmp/opencode/eh-indexed-payload-boundaries-final/provenance.json`,
per-case `projection.json` / `results.json` / binaries, and
`/tmp/opencode/eh-indexed-payload-boundaries-final.log`.

## Independent EH checks that do execute now

The forced binary-script regression suite tests all **16 pairs** of nullable /
non-null `exn` / `noexn` tag payload descriptors. Equal types link; every unequal
pair is unlinkable: value subtyping does not make tag types covariant. The
uninhabited non-null `noexn` case is tested only for linking; no value is invented.

Three additional cross-module native-call / imported-tag / catch flows execute:
non-null exception references carried by nullable and non-null `exn` payloads
both return `ref.is_null = 0`; a nullable `noexn` null payload returns `1`.
Together with the existing nominal/finality/re-export checks, the driver
regressions now have **66 positive commands** and detect the same 12 deliberate
wrong-stage/outcome failures. These checks do not replace the red indexed probes.

## Public connected contracts needed from the shared migration

No second runtime descriptor or raw-index transport is requested. Use GC's
existing `defined_type`, `closed_value_type`, `close_function_type`,
`typeof_closed_value`, `closed_value_typing`, `source_value_typing` and producer
null-lowering primitives. GC `b2fbd83` already proves closed operand inversion,
declared function expansion/variance, primitive source/closed typing correctness
and extension properties; those primitive facts alone do not migrate main
runtime contexts or stored values.

The required **connected** emission contract, expressed using the current
public EH judgments, is:

- `inst_typing s inst = Some C`;
- `close_function_type inst.(inst_defined_types) 0 (Tf ps []) = Some (Closed_ft cps [])`;
- fields have the shared closed runtime typing at `cps`;
- **then** `e_typing s C (v_to_e_list fields) (Tf [] ps)`, with the analogous
  result under local/label/return context updates preserving the same closed
  name map.

The actual main typing/constant-value rules must implement this law. A new
standalone lemma about an unused classifier is not a handoff. The current
context-free `values_typing s fields ps` cannot replace contextual closing:
`source_payload_transport_counterexample` already disproves that shortcut.
If main administrative typing migrates entirely to closed stack types, the
equivalent closed-stack emission contract is preferable; EH will adapt to
that shared representation rather than reconstruct local indices.

The other required connected contracts are:

- **Throw/exception storage:** expansion of the stored tag ID to
  `Closed_ft cps []` is the authoritative field signature;
  `exninst_typing` uses shared closed field typing, not a producer's raw source
  parameter list.
- **Runtime production:** actual `BI_ref_null` handling and local-default
  initialization use `lower_source_null` / the shared closed default mechanism
  in the producing instance. The resulting values satisfy the shared closed
  classifier. Source `HT_type i` must not escape as an unqualified runtime null.
- **Extension:** shared closed field typing survives `store_extension` with
  typed old/new stores. The scalar theorem already exists at `b2fbd83`; main
  runtime producers/contexts/storage must actually use its judgment.
- **Import boundaries:** expected source descriptors close through the
  importing instance's `inst_defined_types`; supplied function/tag identities
  come from the store, not source index numbers or expanded payload equality.
  Closed function imports use the existing directed matching/variance contract;
  tag imports require bidirectional equivalence.

EH already supplies the public connected pieces at `e27a6b1`:
`tag_import_matching_correct`, store/registry extension,
`tag_import_matching_closed_signature_agreement`,
`alloc_module_tag_defined_identity` and
`instantiated_tag_canonical_signature`. The canonical tag ID table is
`s_tag_ids`, with imported-before-local `inst_tags`. These can be reused when
adding the tag kind to the shared closed extern boundary. The portability guard
must only be removed when the main closed field/emission contracts above hold.

## Handoff state

No portable-boundary restriction has been removed to make a red fixture green.
No pending GC migration or uncommitted other-worktree changes were imported.
Parent coordination needed: a pinned compiling main closed runtime/context/
producer revision and the common parser's indexed-local composition revision.
Until those handoffs, the indexed cases remain explicit failing conformance
probes and the draft PR is not finished.
