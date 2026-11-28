# Selective whole-module parser integration — partial

Concrete composition failures and repairs are in
`exception_module_counterexamples.md`. The indexed-global premise failure
identified there has now been repaired, with canonical-context validation;
see `source_decoder_scope_checks.md` for current contracts and remaining
whole-module proof obligations.

The concrete recursive soundness hypotheses have subsequently been discharged
for every actual primitive family, not assumed. Current proved/open contracts
are listed explicitly in `concrete_parser_proof_obligations.md`; soundness is
not described there as the still-open expression/module iff.

Pinned sources: `ea96c785ba6004c3994622b75b2d1312336c218f` and
`bc7c1906d4dc86c783aa808c1bb33107013badc4`.
Neither aggregate branch was merged. No addressing, multi-memory AST,
extended-constant or unfinished closed-runtime migration was imported.

## Initial connected increment at d3daf14

- `binary_format_parser.v` exposes the pinned production interfaces
  `module_section_results`, `finish_module_sections` and
  `parse_module_section_sequence_after`, adapted to recursive source types
  and **the tag slot between memory and global sections**. The actual parser
  uses these definitions. The existing count/data-count guards are unchanged.
- `binary_format_module_properties.v` adapts the pinned consistency/rejection
  proofs and printer-section reconstruction to that interface. Successful
  finishing preserves tags and import/export descriptors; these are not
  projected away. `finish_printed_module_sections` holds for every actual
  module AST, including EH instructions and kind-4 import/export descriptors.
  This is **postprocessing reconstruction**, not a binary round-trip theorem.
- `binary_parser_lookahead_properties.v` selectively reuses the pinned generic
  ordered-choice proofs. No changed integer decoder is imported.
- `binary_format_eh_properties.v` supplies an independent consumed-byte grammar
  for all four final catch forms, soundness/completeness at arbitrary bounds,
  and `run_parse_catch_clause_correct`, an iff retaining arbitrary suffixes.
  The index grammar includes padded u32 encodings, value bounds and width
  bounds. Tag entries, kind-4 imports/exports, `throw` and `throw_ref` have
  actual leaf contracts. Import/export results here are positive completeness
  for the tag branches, not whole-descriptor soundness/iff.
- `binary_format_section_properties.v` adapts exact section-payload soundness
  and completeness to this tree's guarded u32 decoder. The actual parser now
  checks every declared section payload size, including recursive types and
  tags. The pinned custom-section fix rejects missing positive-length payloads
  instead of treating optional failure as an empty payload.

All six audited public contracts are globally closed; `coqchk` passed for the
EH leaf, module postprocessor and section framing proof modules
(`/tmp/opencode/eh-module-parser-coqchk.log`). No admission, parser-success
grammar, test expectation weakening or new axiom was used.

## Initial verification at d3daf14

The forced extracted binary driver adds **45** framing/order commands:
too-small/too-large sizes for each section ID 1–13; legal padded sizes;
truncated custom payloads; duplicate/misordered tag sections; and successful
custom-prefixed memory → tag → global composition. A standalone start section
with a legal padded size correctly reaches validation and is invalid, not
malformed. These run in addition to all earlier tests, not instead of them.

The official projection still executes **489/489**, with exactly **18 mapped
text-only deferrals** outside that count. The separate indexed-payload probes
remain **7/10, exit 1**: correct canonical IDs but blocked portability for the
positive indexed link; correct negative link rejection; indexed-local parser
failure before null transport, plus its invocation cascade.

Full exact-tree build and forced tests pass, including **111 positive script
commands**, 12 deliberate failure detections and the earlier suites unchanged.
Strict core remains **53,999/54,004**, 148 files, zero infrastructure errors:
the same five stale alignment expectations, not a green core-suite claim.

Logs: `/tmp/opencode/eh-module-parser-full-build.log`,
`/tmp/opencode/eh-module-parser-forced-tests.log`,
`/tmp/opencode/eh-module-parser-official.log`,
`/tmp/opencode/eh-module-parser-indexed.log`,
`/tmp/opencode/eh-module-parser-assumptions.log`.

## Initial dependency audit — no whole-module verification claim

The pinned whole-module proof's transitive closure has 40 modules absent from
the initial EH tree. Several cannot be copied unchanged:

- The pinned module/type grammar uses flat function types; this tree uses
  recursive groups and indexed declaration references.
- Its reference leaves cover one-byte `funcref`/`externref`; actual EH leaves
  include multi-byte nullable/non-null abstract references and `exn`/`noexn`.
  Reuse `gc_binary_parser_properties.v`'s EH-aware contracts instead of
  restricting the actual grammar back to those two types.
- Recursive instruction syntax and its printer-membership/termination
  induction must include `try_table`, the catch vector, `throw`, `throw_ref`,
  and the existing GC/function-reference instructions.
- Pinned memory leaves depend on a different memarg/addressing AST and
  multi-memory constructors. Those models are not minimal drop-in dependencies.
- The full section sequence grammar/optional absence/custom completeness must
  insert tag section ID 13 at its actual **nonnumeric** position. The executable
  tests and finishing theorem alone do not prove the general ordering iff.
- Canonical printer round trips require adapting the leaf domains and their
  byte bounds, not merely importing the old `module_binary_wf`.

Consequently neither `binary_of_module_roundtrip` nor
`run_parse_module_general_correct` / `run_parse_module_str_general_correct`
has yet been ported to this EH tree. The top-level pinned modules are not
installed with false coverage claims or unresolved proof obligations.

## Follow-up after d3daf14

The shared vector/optional/arbitrary-custom proof dependencies have now been
selectively adapted without the addressing decoder. Arbitrary custom decoding,
custom-before/after iteration, custom-prefixed optional absence and the actual
tag wrapper's grammar iff compile. `binary_of_tagsec_roundtrip` proves a
bounded round trip for the actual tag-section printer, not the entire module.
The canonical code-section-only corollaries in the copied custom-completeness
module were not imported: they depend on still-unported whole-expression
printer membership.

Full exact-tree build, forced tests and kernel checking pass for this follow-up
as well. The driver now has **126 positive commands**, with the same 12
deliberate wrong-outcome/stage failures detected. The official non-text
projection remains **489/489**, with **18 text-only deferrals**; strict core
remains 53,999/54,004 (the same five alignment expectations).
Kernel checks include `interp_instantiate_sound` after the stronger local
source-validation check, not only isolated parser helpers.

The eight audited custom/tag/reference/local decoding contracts are globally
closed. `module_type_checker_locals_closed`, which mentions the actual full
validator, exposes inherited classical real-decision and dependent functional
extensionality assumptions; no new axiom was added. Audit/build logs:
`/tmp/opencode/eh-parser-custom-locals-assumptions.log`,
`/tmp/opencode/eh-parser-custom-locals-final-build.log`,
`/tmp/opencode/eh-parser-custom-locals-final-tests.log`,
`/tmp/opencode/eh-parser-custom-locals-final-coqchk.log`.

`binary_format_reference_properties.v` now discharges independent full source
heap/reference/value grammar leaves (including EH abstract heaps and signed
indexed references), and `run_parse_source_locals_correct` characterizes actual
local descriptor decoding with arbitrary suffixes/bounds. `parse_locals` uses
that declaration codec. `source_local_properties.v` reflects the production
validator's new mandatory canonical-context local-closing check; this does not
change source indices into runtime identities or claim canonical null lowering.

Additional binary local fixtures cover indices 0/63/64/127/128, padded s33,
out-of-context and maximum-u32 indices (validation failures), and wire overflow
(parse failure). The transport consumer now passes parsing/validation and
reaches the portability import failure. The indexed summary means **7 passing
commands and 3 failing commands**, not seven failing commands.

Still unported: the actual whole-module `binary_of_module_roundtrip`,
`run_parse_module_general_correct` and string iff; recursive instruction
composition including `try_table`; recursive declaration/field/group grammar;
and remaining atomic, block/type, record/segment and printer membership
dependencies. None is assumed to follow from these new concrete leaf proofs.

The connected GC closed-runtime/**closed administrative stack signature**
handoff is separately documented in `exception_payload_handoff.md`.
The PR remains draft and final EH is unfinished.
