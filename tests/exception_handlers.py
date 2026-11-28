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
    return b"\x60" + vec([bytes([x]) for x in args]) + vec(
        [bytes([x]) for x in results]
    )


def module(body, *, tags=(1, 1), helpers=(), extra_types=(), result=b"\x7f"):
    bodies = list(helpers) + [body]
    types = [signature(results=result), signature(b"\x7f")] + list(extra_types)
    code = [b"\0" + body + b"\x0b" for body in bodies]
    return (
        b"\0asm\x01\0\0\0"
        + section(1, vec(types))
        + section(3, vec([b"\0" for _ in bodies]))
        + section(13, vec([b"\0" + u32(t) for t in tags]))
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
