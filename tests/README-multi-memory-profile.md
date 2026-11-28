# Complete official multi-memory non-text profile

The six original checked-in projections exercise 93 commands. They are retained
as regressions, **not** represented as complete proposal coverage.

`binary_wast.py` and `prepare_multi_memory_binary.py` selectively reuse test
tooling from `b3748f1468e4a36d21623c656502db9d510e1649` / `724b72b`.
They do not import the donor's production memory, reference or tail-call source.
The only script-runner repairs are named binary-module variable bindings and
additive `register` aliases, reproduced by `binary_register_aliases.py`.
The original executable passes only 1/19 commands in that regression.
No allocator, persistent memory, native-array or backend selection is changed.

## Measured combined-profile result

On this tree, the pre-repair executable
`68675dc0d853a4d4136219b18fe569cd2fd2def9f6f95d8f151d5ae0382113c2`
passes **54,783/54,853**, with 187 summaries and no crashes/missing summaries.
After the two runner repairs, executable SHA256
`cac816335fe861b9f02436d6d10e32b280890d4de1195fdcb34182b275da9c4d`
passes **54,853/54,853**, again 187 summaries and no crashes/missing summaries,
using `JOBS=1`. The alias regression improves from **1/19 to 19/19**.
All 657 proposal module commands are externally encoded and all 1,785
binary-scope proposal commands are included in this result.

This is a finite conformance result under the scope below, not full text/Wasm 3
coverage or a proof of the unsafe native memory implementation.

## Reproduce

Use testsuite `b497cbb853db21be875bd5c81fcc3334168fb0b4` and the external test
encoder `wasm-tools 1.263.0 (7a2fa422c 2026-10-30)`. For the audited Linux encoder,
SHA256 is `694cb37dcda84a5d557334c1db882b986e43061abdb0af976b41b1614ee4530b`.
The encoder is test tooling only, not the production parser or validator.

Generate with `python3 tests/prepare_multi_memory_binary.py --suite wast_testsuite
--wasm-tools /path/to/wasm-tools --output /tmp/opencode/multi-memory-complete-profile`.
Then run `EXE="$PWD/_build/default/src/wasm_coq_interpreter.exe" JOBS=1 bash
run_wast.sh /tmp/opencode/multi-memory-complete-profile` from the repository root.

The output directory must be empty and outside the testsuite. The generator
checks the suite pin, encoder version, all 148 root and 48 proposal files, and
every source byte against the pinned Git revision. It selects all 48 official
multi-memory files, replacing exactly nine same-name root scripts and retaining
the other 139 core scripts unchanged: **187 files total**.

## Exact scope and accounting

- All **1,785 binary-scope proposal commands** are retained, in source order.
  This includes every module, assertion, action and registration, not only
  successful/valid examples. Only module forms are replaced with encoder bytes;
  assertion kinds, expected results, module variables and later commands remain.
- Exactly **88 text-only malformed proposal assertions** are explicitly
  deferred, not passed. Their source lines and full original commands appear
  in `provenance.json`; each projected script also lists the excluded lines.
  Unexpected non-malformed text commands cause generation to fail.
- `provenance.json` maps **every** original proposal command to either a numbered
  projected command or an explicit text-only deferral. It records source line,
  assertion kind, original/projected command hashes, encoded-module hashes,
  unchanged assertion prefix/suffix, source/projection file hashes, suite pin,
  encoder version/hash, and the hashes of all unchanged core scripts.
- Source/encoder command-count mismatch, changed pinned input, missing files,
  or totals other than 1,785 retained / 88 deferred are errors, not silent skips.
- The combined profile includes the unchanged, non-overlaid core scripts;
  those scripts still use their existing frontend. It is not a claim that every
  core text assertion has been translated or that text translation is proved.
  Full proposal binary coverage and combined-profile results must be reported
  separately from the untouched historical root/proposal/cumulative runs.

The normal forced Dune tests include projection-bookkeeping unit tests and the
19-command extracted-runner alias regression without requiring wasm-tools or
network access. The entire generated profile is an additional explicit
conformance run. It is finite testing, not a replacement for the module grammar,
validation/instantiation proofs or the remaining native heap/`Obj` boundary.

## Limits

Memory64 and relaxed SIMD are not enabled. Text implementation/proofs remain
deferred. The historical root has obsolete single-memory/reserved-byte and
malformed-versus-invalid expectations; no original assertions are edited.
The historical proposal/cumulative text crashes remain failures, not passes
inferred from the binary projections. The existing WAST harness checks trap
occurrence, not exact trap-message equality; passing counts are bounded by that
inherited oracle behavior.
