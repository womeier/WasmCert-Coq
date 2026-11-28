# Official extended-const binary projection recipes

This document specifies reusable test inputs, provenance and commands. Completion
status, proof plans and review decisions belong in PR #5's description.

## Inputs and encoder

Use the immutable WebAssembly/spec `wg-3.0` revision
`9d36019973201a19f9c9ebb0f10828b2fe2374aa`, files
`test/core/{global,data,elem,align}.wast`. The hashes are enforced by
`extended_const_official_projection.py`; keep the originals unchanged.
There is no separate `test/core/extended-const.wast` at this revision.

Encoder used to construct these projections and the minimal dependency fixtures:
`wasm-tools 1.263.0 (7a2fa422c 2026-10-30)`, executable SHA256
`694cb37dcda84a5d557334c1db882b986e43061abdb0af976b41b1614ee4530b`.
Set `$ENCODER` to that external encoder and `$ORIGINALS` to the preserved input
directory. The adapter implements only source-span/provenance bookkeeping, not
WAT encoding or Wasm semantics.

```text
python3 tests/extended_const_official_projection.py \
  --encoder "$ENCODER" --originals "$ORIGINALS" \
  --output .test-artifacts/end-to-end-audit/full-projection-audit \
  --runner _build/default/src/wasm_coq_interpreter.exe

python3 tests/extended_const_official_projection.py \
  --encoder "$ENCODER" --originals "$ORIGINALS" \
  --output .test-artifacts/end-to-end-audit/current-ast-profile \
  --current-ast-profile --runner _build/default/src/wasm_coq_interpreter.exe
```

The default command is the broader binary gate: do not assume that it succeeds.
The explicit profile is a different input domain, not evidence of support for
the omitted original binaries.

Each command is mapped to the original top-level source span/line/text/hash and
the external encoder command/file/hash. A nonzero exit, missing/duplicate
summary, failed command, or total different from the ledger fails the gate.
`provenance.json`, `results.json`, encoder outputs and per-file run logs are
retained. The runner counts module/register/action setup commands as tests too.

## Fixed profile accounting

| File | Original commands | Profile commands | Profile assertions | Malformed text | Non-null/table-init domain |
|---|---:|---:|---:|---:|---:|
| global | 124 | 120 | 110 | 3 | 1 |
| data | 65 | 65 | 34 | 0 | 0 |
| elem | 151 | 133 | 70 | 0 | 18 |
| align | 165 | 119 | 94 | 46 | 0 |
| Total | 505 | 437 | 308 | 49 | 19 |

The text-only commands are encoder-designated malformed **text modules** inside
`assert_malformed`. A non-malformed text module is an adapter error, not a
silently deferred command.

* global malformed-text lines: **685, 692, 699**.
* align malformed-text lines: **27, 33, 39, 45, 51, 57, 63, 69, 75, 81, 87,
  93, 99, 105, 111, 117, 123, 129, 135, 141, 147, 153, 159, 165, 171,
  177, 183, 189, 196, 202, 208, 214, 220, 226, 232, 238, 244, 250, 256,
  262, 268, 274, 280, 286, 292, 298**.

The explicit profile additionally separates these **non-text** proposal inputs:

* elem **87, 315, 448, 453, 465, 470, 482, 487, 499, 504, 516, 524, 539,
  544, 556, 561, 573, 578**: non-null `(ref func)`/table-initializer forms.
* global **674**: table initializer `(global.get $g)`.

Do not infer exclusions from test outcomes. The source hashes and explicit line
sets define this profile in advance.

Two adapters are separately recorded:

1. global **634**: externally reencode
   `(table $t 10 funcref (ref.null func))` as `(table $t 10 funcref)`.
   These have identical default null values, but **different binaries**. Both
   original and variant binaries/source hashes are retained. This is not a
   parser test of the original explicit table-initializer encoding.
2. global **659**: the old harness's `(ref.null func)` spelling replaces generic
   `(ref.null)` for `get-elem`, whose declared result is `funcref`. The exact
   null assertion remains; it is not changed into a non-null/type wildcard.

## Minimal binary dependency fixtures

`extended_const_reference_dependencies.wast` contains three final-spec valid
modules and one decode-success/validation-failure assertion, with the generating
WAT shown beside each unchanged binary. It is intentionally **not** registered
as a passing Dune gate. Execute it independently to observe proposal support:

```text
_build/default/src/wasm_coq_interpreter.exe --wast \
  tests/extended_const_reference_dependencies.wast
```

The first fixture isolates nullable-table initialization from a non-null element
type (`0x64 0x70`). The second isolates a non-null table initialized with
`ref.func`; the third isolates explicit nullable/default-null table initialization.
The fourth isolates the restricted table-initializer context: the final-spec
validator rejects global 0 as unknown, **after decoding** the table initializer.
Binary table constructors use `0x40 0x00` before the reference type/limits.

To independently reproduce an encoded fixture, write its adjacent WAT comment
to `case.wat`, then run:

```text
"$ENCODER" parse case.wat -o case.wasm
"$ENCODER" validate case.wasm
```

The first three validate. The fourth fails validation with `unknown global 0`.
None of these requires a GC structure or EH instruction; the relevant source
constructors come from Function References/non-null reference and table
initializer support.

## Historical expectation provenance

Keep testsuite `b497cbb853db21be875bd5c81fcc3334168fb0b4` and its
`proposals/extended-const` files unchanged when comparing results.

```text
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh \
  .test-artifacts/testsuite-b497cbb853db21be875bd5c81fcc3334168fb0b4
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh .test-artifacts/proposal
JOBS=1 TMPDIR=/tmp/opencode bash run_wast.sh "$ORIGINALS"
```

Six old `unknown global` expectations map to final positive cases:

| Historical root lines | Proposal lines | Final positives |
|---|---|---|
| data 84, 88 | data 84, 88 | data 89, 90 |
| elem 170, 174 | elem 170, 174 | elem 178, 182 |
| global 351, 355 | global 363, 367 | global 373, 374 |

The five old `assert_malformed` alignment cases at **891, 910, 929, 948, 967**
must not motivate restrictive decoding guards. Final align **891, 910, 929**
use validation rejection for flags 32/33/63. Old **967** (flags 65) maps to final
**948**, validation `type mismatch` after explicit-memory decoding. Old **948**
(flags 64) was removed from final align; flags 64/65 remain explicit memarg
regressions, not invented official replacements.

The remaining historical expected failures concern reserved memory.size/grow
bytes versus LEB memory indices (binary **125, 145, 165, 184, 203, 223, 242,
261, 279, 297**) and multiple-memory rejection (imports **487, 491, 495**;
memory **10, 11**). Record their original results rather than editing assertions
or combining separate probe counts into an unchanged-suite pass total.
