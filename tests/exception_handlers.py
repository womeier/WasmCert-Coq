"""Actual binary-path final tag/catch_all handler tests (no WAST frontend)."""
import pathlib
import re
import subprocess
import sys
import tempfile

EXE = sys.argv[1]


def u32(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    return bytes(out + bytes([n]))


def vec(xs):
    return u32(len(xs)) + b"".join(xs)


def section(n, data):
    return bytes([n]) + u32(len(data)) + data


def signature(args=b"", results=b""):
    def types(data):
        out = []
        while data:
            size = 2 if data[0] in (0x63, 0x64) else 1
            out.append(data[:size])
            data = data[size:]
        return out
    return b"\x60" + vec(types(args)) + vec(types(results))


def module(body, *, tags=(1, 1), helpers=(), extra_types=(), result=b"\x7f",
           tag_parameters=b"\x7f", tables=()):
    bodies = list(helpers) + [body]
    types = [signature(results=result), signature(tag_parameters)] + list(extra_types)
    code = [b"\0" + body + b"\x0b" for body in bodies]
    return (
        b"\0asm\x01\0\0\0"
        + section(1, vec(types))
        + section(3, vec([b"\0" for _ in bodies]))
        + (section(4, vec(list(tables))) if tables else b"")
        + section(13, vec([b"\0" + u32(t) for t in tags]))
        + section(7, vec([b"\x04main\0" + u32(len(bodies) - 1)]))
        + section(10, vec([u32(len(c)) + c for c in code]))
    )

def typed_functions(types, function_types, bodies):
    code = [b"\0" + body + b"\x0b" for body in bodies]
    return (
        b"\0asm\x01\0\0\0"
        + section(1, vec(types))
        + section(3, vec([u32(t) for t in function_types]))
        + section(7, vec([b"\x04main\0" + u32(len(bodies) - 1)]))
        + section(10, vec([u32(len(c)) + c for c in code]))
    )


def block(body, result=b"\x7f"):
    return b"\x02" + result + body + b"\x0b"


def try_table(body, catches=(), result=b"\x7f"):
    return b"\x1f" + result + vec(list(catches)) + body + b"\x0b"


def catch(tag, label):
    return b"\0" + u32(tag) + u32(label)


def catch_all(label):
    return b"\x02" + u32(label)

def catch_ref(tag, label):
    return b"\x01" + u32(tag) + u32(label)


def catch_all_ref(label):
    return b"\x03" + u32(label)


def i32(n):
    assert 0 <= n < 64
    return b"\x41" + bytes([n])


throw0 = i32(42) + b"\x08\0"
cases = []


def value(name, body, expected, **kwargs):
    cases.append((name, module(body, **kwargs), 0, f"i32.const {expected}", True))


def invalid(name, body, **kwargs):
    cases.append((name, module(body, **kwargs), 123, "Module type checking failure", False))


value("tag-payload", block(try_table(throw0, [catch(0, 0)])), 42)
value("normal-completion", block(try_table(i32(7), [catch(0, 0)])), 7)
value(
    "catch-all-discards-fields",
    block(try_table(throw0, [catch_all(0)], b"\x40"), b"\x40") + i32(7),
    7,
)
value("branch-body-label", block(try_table(i32(32) + b"\x0c\0", [])), 32)
value("branch-across-handler", block(try_table(i32(23) + b"\x0c\x01", [])), 23)
value("return-across-handler", try_table(i32(37) + b"\x0f", []), 37)
value(
    "nonmatching-inner-handler",
    block(try_table(try_table(throw0, [catch(1, 0)]), [catch(0, 0)])),
    42,
)
value(
    "innermost-handler-first",
    block(try_table(block(try_table(throw0, [catch(0, 0)])) + i32(1) + b"\x6a",
                    [catch(0, 0)])),
    43,
)
value(
    "ordered-catch-all-first",
    block(block(try_table(throw0, [catch_all(0), catch(0, 1)], b"\x40"),
                b"\x40") + i32(61)),
    61,
)
value(
    "ordered-tag-first",
    block(block(try_table(throw0, [catch(0, 1), catch_all(0)], b"\x40"),
                b"\x40") + i32(61)),
    42,
)
value(
    "call-frame-caught",
    block(try_table(b"\x10\0", [catch(0, 0)])),
    49,
    helpers=[i32(49) + b"\x08\0"],
)
cases.append((
    "tail-call-removes-handler",
    module(block(try_table(b"\x12\0", [catch(0, 0)])),
           helpers=[i32(49) + b"\x08\0"]),
    123, "uncaught WebAssembly exception", True,
))
cases.append((
    "unmatched-exception",
    module(block(try_table(throw0, [catch(1, 0)]))),
    123, "uncaught WebAssembly exception", True,
))
cases.append((
    "trap-not-caught",
    module(block(try_table(b"\0", [catch(0, 0)]))),
    0, "trap", True,
))
value(
    "mixed-payload-order",
    block(try_table(i32(11) + b"\x42\x16\x08\0", [catch(0, 0)], b"\x02"),
          b"\x02") + b"\x1a",
    11,
    tags=(3,),
    extra_types=[signature(results=b"\x7f\x7e"), signature(b"\x7f\x7e")],
)
invalid("unknown-tag", block(try_table(throw0, [catch(2, 0)])))
invalid("unknown-label", block(try_table(throw0, [catch(0, 9)])))
invalid("catch-all-nonempty-label", block(try_table(throw0, [catch_all(0)])))
invalid(
    "wrong-payload-label-type",
    block(try_table(throw0, [catch(0, 0)], b"\x7e"), b"\x7e") + b"\x1a" + i32(1),
)

# The body's implicit label is NOT in scope for catch immediates.
invalid(
    "catch-does-not-see-implicit-label",
    try_table(throw0, [catch(0, 0)]),
    result=b"",
)

nonnull_exn = b"\x64\x69"
value(
    "catch-all-ref-is-nonnull",
    block(try_table(throw0, [catch_all_ref(0)], nonnull_exn), nonnull_exn) + b"\xd1",
    0,
)
value(
    "catch-ref-payload-then-reference",
    block(try_table(throw0, [catch_ref(0, 0)], b"\x02"), b"\x02") + b"\x1a",
    42,
    extra_types=[signature(results=b"\x7f" + nonnull_exn)],
)
value(
    "catch-ref-mixed-payload-order",
    block(try_table(i32(11) + b"\x42\x16\x08\0", [catch_ref(0, 0)], b"\x02"),
          b"\x02") + b"\x1a\x1a",
    11,
    tags=(3,),
    extra_types=[signature(results=b"\x7f\x7e" + nonnull_exn),
                 signature(b"\x7f\x7e")],
)
for name, clauses in [
    ("rethrow-catch-ref", [catch_ref(0, 0)]),
    ("rethrow-catch-all-ref", [catch_all_ref(0)]),
    ("nonmatch-then-catch-ref", [catch_ref(1, 0), catch_ref(0, 0)]),
]:
    cases.append((
        name,
        module(block(try_table(throw0, clauses, b"\x02"), b"\x02")
               + b"\x0a",
               extra_types=[signature(results=(
                   nonnull_exn if name == "rethrow-catch-all-ref"
                   else b"\x7f" + nonnull_exn))]),
        123, "uncaught WebAssembly exception", True,
    ))
for heap in (b"\x69", b"\x74"):
    cases.append((
        "null-throw-ref-" + heap.hex(),
        module(b"\xd0" + heap + b"\x0a"),
        0, "trap", True,
    ))
    value("null-is-null-" + heap.hex(), b"\xd0" + heap + b"\xd1", 1)
cases.append((
    "return-nonnull-exception-reference",
    module(block(try_table(throw0, [catch_all_ref(0)], nonnull_exn), nonnull_exn),
           result=nonnull_exn),
    0, "exnref 0", True,
))
invalid("throw-ref-numeric", i32(1) + b"\x0a")
invalid("throw-ref-func-null", b"\xd0\x70\x0a")
invalid("throw-ref-extern-null", b"\xd0\x6f\x0a")
invalid("throw-ref-missing-operand", b"\x0a")
invalid("catch-ref-unknown-tag", block(try_table(throw0, [catch_ref(3, 0)])))
invalid("catch-all-ref-unknown-label", block(try_table(throw0, [catch_all_ref(9)])))
invalid("catch-ref-requires-reference-label", block(try_table(throw0, [catch_ref(0, 0)])))
invalid("catch-all-ref-requires-reference-label", block(try_table(throw0, [catch_all_ref(0)])))

nullable_exn = b"\x69"
nullable_noexn = b"\x74"
exception_types = [
    (False, False, b"\x64\x74"),
    (False, True, nullable_noexn),
    (True, False, nonnull_exn),
    (True, True, nullable_exn),
]
for source_exn, source_nullable, source in exception_types:
    for target_exn, target_nullable, target in exception_types:
        matches = (not source_exn or target_exn) and (not source_nullable or target_nullable)
        cases.append((
            f"exception-subtype-{source.hex()}-{target.hex()}",
            typed_functions([signature(source, target)], [0], [b"\x20\0"]),
            0 if matches else 123,
            "" if matches else "Module type checking failure",
            False,
        ))
    for other in (b"\x70", b"\x6f"):
        for left, right in ((source, other), (other, source)):
            cases.append((
                f"separate-hierarchies-{left.hex()}-{right.hex()}",
                typed_functions([signature(left, right)], [0], [b"\x20\0"]),
                123, "Module type checking failure", False,
            ))

cases.append((
    "nonnull-return-widens-to-nullable",
    module(block(try_table(throw0, [catch_all_ref(0)], nonnull_exn), nonnull_exn),
           result=nullable_exn),
    0, "exnref 0", True,
))
value(
    "catch-all-ref-widens-label",
    block(try_table(throw0, [catch_all_ref(0)], nullable_exn), nullable_exn) + b"\xd1",
    0,
)
value(
    "catch-ref-widens-reference-above-payload",
    block(try_table(throw0, [catch_ref(0, 0)], b"\x02"), b"\x02") + b"\x1a",
    42,
    extra_types=[signature(results=b"\x7f" + nullable_exn)],
)
value("noexn-null-widens-block",
      block(b"\xd0\x74", nullable_exn) + b"\xd1", 1)
value(
    "noexn-null-in-exception-payload",
    block(try_table(b"\xd0\x74\x08\0", [catch(0, 0)], nullable_exn),
          nullable_exn) + b"\xd1",
    1, tag_parameters=nullable_exn,
)
for selector in (0, 1):
    value(
        f"br-table-exception-meet-{selector}",
        block(block(b"\xd0\x74" + i32(selector) + b"\x0e\x01\0\x01",
                    nullable_noexn), nullable_exn) + b"\xd1",
        1,
    )
value(
    "table-set-noexn-in-exn-table",
    i32(0) + b"\xd0\x74\x26\0" + i32(0) + b"\x25\0\xd1",
    1, tables=[b"\x69\0\x01"],
)
value(
    "table-grow-noexn-in-exn-table",
    b"\xd0\x74" + i32(1) + b"\xfc\x0f\0\x1a\xfc\x10\0",
    2, tables=[b"\x69\0\x01"],
)
cases.append((
    "native-call-noexn-argument-widens",
    typed_functions([signature(nullable_exn, b"\x7f"), signature(results=b"\x7f")],
                    [0, 1], [b"\x20\0\xd1", b"\xd0\x74\x10\0"]),
    0, "i32.const 1", True,
))

with tempfile.TemporaryDirectory(prefix="wasmcert-handlers-") as directory:
    for name, binary, code, expected, execute in cases:
        path = pathlib.Path(directory, name + ".wasm")
        path.write_bytes(binary)
        args = [EXE, str(path)] + (["-r", "main"] if execute else ["--no-exec"])
        result = subprocess.run(args, capture_output=True, text=True, timeout=20)
        output = " ".join(re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr).split())
        assert result.returncode == code and expected in output, (
            name, result.returncode, output
        )

print(f"Extracted tag handler binary tests: {len(cases)}/{len(cases)}")
