# Actual whole-module composition failures

This is a counterexample/repair record, **not whole-module verification or
passing conformance coverage**. The general module round-trip and grammar iff
remain unproved.

**Follow-up:** the indexed-global decoder failure below is now repaired.
Current production paths, generalized proofs and source-scope checks are
documented in `source_decoder_scope_checks.md`; the exact binary is a positive
round-trip/instantiation regression, not an expected malformed input.

## Repaired: unsigned block indices

The old printer encoded `BT_id 64` as unsigned `40`. The actual parser chooses
the empty-block alternative on that byte:

```coq
run_parse_be (x02 :: binary_of_u32 64 ++ [x0b]) =
  Some (BI_block (BT_valtype None) []).
```

`legacy_unsigned_block64_decodes_as_empty` preserves this exact witness.
The actual block parser now uses the existing nonnegative **s33** heap-index
codec, and the actual printer emits signed indices.
`binary_of_block_type_id_roundtrip` proves all bounded u32 block indices round
trip, discharging ordered-choice collisions against empty and EH value types;
it does not assume one-byte reference encodings.

The extracted binary tests execute indices 0/63/64/127/128, reject the old
unsigned `41` encoding for index 65 as malformed, and distinguish a maximum
u32 out-of-context index (invalid) from wire overflow (malformed).

## Repaired: omitted data count under handlers

The old `binary_of_module` did not emit a data-count section, but the actual
parser requires it when a function contains `data.drop` / `memory.init`,
including under `try_table`. Thus the old printer failed the finishing
judgment even if every section's individual printer/parser contract held.

The shared syntax traversal now lives in `datatypes.v` and is used by both
production paths. The actual printer emits section 12 between elements and
code when required. No parser guard was removed.

`legacy_missing_count_inside_handler_is_rejected` preserves the old assembly
failure. `actual_eh_section_assembly_roundtrip` and its string counterpart
round-trip a concrete actual AST with recursive source type groups, tag
imports/definitions/exports, all four catches, indexed block type 64 and
`data.drop` under a handler. This is a **wire-syntax** regression, not a claim
that the deliberately combined catch targets validate semantically.

A separate semantically valid extracted handler/data-count fixture executes
and returns 7; its count-omitting counterpart is malformed. Independent
wasm-tools validation agrees on all ten new block/count fixtures (six valid
and four deliberately rejected). Artifacts:
`/tmp/opencode/eh-wholemodule-block-count-fixtures/validation.json`.

## Historical failed premise at ffa5a0c: indexed globals (now repaired)

This is an actual failed derivation, not a list of unimplemented proofs.
Take the single source type `(func)` at index 0 and one immutable global:

```text
(global (ref null 0) (ref.null 0))
```

No text frontend is used. The exact binary, proved equal to the production
printer by `indexed_global_printed_bytes`, is:

```text
0061736d01000000 010401600000 060701630000d0000b
```

SHA-256:
`6d1b654656aa8528644b308a45bd4bcd213dfd04ae5d9a9d2e024b0391ed8c12`.
The independently pinned wasm-tools validator accepts it.

At `ffa5a0c`, the following facts were kernel checked in
`theories/binary_format_eh_module_tests.v`:

1. `indexed_global_source_type_is_in_grammar` derives
   `source_value_encoding [x63; x00] (T_ref (Ref_type true (HT_type 0)))`.
2. The abstract-fragment decoder rejected the bytes (now retained as
   `indexed_global_abstract_fragment_rejects`); the production decoder no longer
   uses that fragment.
3. `indexed_global_source_module_validates` proves the current production
   validator accepts the source AST; this is not an out-of-scope index or
   unencodable AST.
4. The actual module round trip then failed. It is now replaced by the positive
   `indexed_global_whole_module_roundtrip` and `indexed_global_string_roundtrip`.

The failed shared-template premise was therefore concrete: global-type
completeness cannot instantiate its value leaf with the full source grammar.
`parse_global_type -> parse_value_type -> parse_reference_type` selected
the abstract-only reference codec. The initializer's `parse_ref_null` path
also used an abstract-only heap decoder. Both production paths are now wired
to the already-proved full source codecs.

This blocked the **claimed full source-AST** module round trip and the
corresponding full grammar iff at that revision. It did not justify
assuming the shared non-EH theorem, filtering out this valid module, calling
the binary malformed, or introducing a parser-success grammar. Repairing
these source decoder/composition paths was independent parser work, and did
not wait for GC.

The binary is now in the green harness with a required successful module load,
**not** an `assert_malformed` expectation. The historical diagnostic artifact is:
`/tmp/opencode/eh-wholemodule-block-count-fixtures/indexed-global-gap.json`.

Official EH accounting remains separate: **489/489 binary-scope commands**
and **18 explicit mapped text-only deferrals**. The indexed payload probes
remain **7 passes / 3 failures**, not seven failures. General closed payload
transport and the shared closed administrative-stack bridge remain open as
documented in `exception_payload_handoff.md`.

## Historical validation of the ffa5a0c repair increment

Full exact-tree build and forced tests pass. The extracted script suite has
**142 positive commands** and detects the same 12 deliberately wrong
outcome/stage assertions. The 16 new block/count commands are separate from
the red indexed-global counterexample.

Relevant kernel checks include the signed block proof, concrete module
assembly/counterexample proofs, existing module finishing/tag composition,
`interp_instantiate_sound` and `type_preservation`. The signed block theorem,
source grammar/leaf-rejection witnesses and exact printed-byte equality are
globally closed. The whole-module/validator statements expose the previously
disclosed inherited classical real-decision and dependent extensionality
assumptions, not newly introduced axioms.

Logs: `/tmp/opencode/eh-wholemodule-final-build.log`,
`/tmp/opencode/eh-wholemodule-final-tests.log`,
`/tmp/opencode/eh-wholemodule-final-coqchk.log`,
`/tmp/opencode/eh-wholemodule-assumptions.log`,
`/tmp/opencode/eh-wholemodule-official.log`.
Strict core remains **53,999/54,004**, 148 files, zero infrastructure errors
(the same five alignment expectations; `/tmp/opencode/eh-wholemodule-core.log`).
