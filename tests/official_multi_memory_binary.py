"""Hash-pinned binary projections of three complete official scripts.

Only each initial module is replaced by its manually reviewed byte encoding.
Every following command/comment is copied verbatim, in order. This is not a
text parser or a general text-to-binary translation and does not claim coverage
of other official scripts or verification of text syntax.
"""
import hashlib
from pathlib import Path
import sys

from binary_fixtures import escaped, section, uleb, vector

SUITE_PIN = "b497cbb853db21be875bd5c81fcc3334168fb0b4"


def binary_module(memories, types, functions):
    """functions = (type index, export name, body excluding locals/end)."""
    bodies = [b"\x00" + code + b"\x0b" for _, _, code in functions]
    return (
        b"\x00asm\x01\x00\x00\x00"
        + section(1, vector(types))
        + section(3, vector([uleb(t) for t, _, _ in functions]))
        + section(5, vector([b"\x00" + uleb(n) for n in memories]))
        + section(7, vector([
            uleb(len(name)) + name.encode("ascii") + b"\x00" + uleb(i)
            for i, (_, name, _) in enumerate(functions)
        ]))
        + section(10, vector([uleb(len(body)) + body for body in bodies]))
    )


# Each table is a direct encoding of all functions in the initial source module:
# memory.size $m -> 3f 04; memory.grow $m -> 40 04;
# $n is memory 2; memory.fill/load8_u in memory_fill0 also select memory 2.
CASES = {
    "memory_size0.wast": (
        "34280de026ac1d919583b866e6e7c722337f6445c157f4bf80895e46f49290a3",
        10, (0, 0, 0, 0, 0), (b"\x60\x00\x01\x7f", b"\x60\x01\x7f\x00"),
        ((0, "size", b"\x3f\x04"), (1, "grow", b"\x20\x00\x40\x04\x1a")),
    ),
    "memory_size1.wast": (
        "7856b32b39b9bf839f90f0f818177d85e8ab704d6933c7b68bd7b90e1829b1fa",
        13, (0, 0, 0, 0, 0), (b"\x60\x00\x01\x7f", b"\x60\x01\x7f\x00"),
        (
            (0, "size", b"\x3f\x04"), (1, "grow", b"\x20\x00\x40\x04\x1a"),
            (0, "sizen", b"\x3f\x02"), (1, "grown", b"\x20\x00\x40\x02\x1a"),
        ),
    ),
    "memory_fill0.wast": (
        "d747201062f410ed64b23ca9687397c33e8f5adbcd4dda54ea742e903922f767",
        15, (0, 0, 1), (b"\x60\x03\x7f\x7f\x7f\x00", b"\x60\x01\x7f\x01\x7f"),
        (
            (0, "fill", b"\x20\x00\x20\x01\x20\x02\xfc\x0b\x02"),
            (1, "load8_u", b"\x20\x00\x2d\x40\x02\x00"),
        ),
    ),
}


def project(paths):
    if len(paths) != len(CASES) or {p.name for p in paths} != CASES.keys():
        raise ValueError("Exactly the three pinned official source scripts are required")
    outputs = []
    for source in paths:
        sha, end_line, memories, types, functions = CASES[source.name]
        data = source.read_bytes()
        if hashlib.sha256(data).hexdigest() != sha:
            raise ValueError(f"Source/projection provenance mismatch: {source}")
        lines = data.decode("utf-8").splitlines(keepends=True)
        if lines[end_line - 1].strip() != ")":
            raise ValueError(f"Initial module boundary mismatch: {source}")
        header = (
            f";; Complete-script binary projection from WasmCert/testsuite {SUITE_PIN}\n"
            f";; Source: proposals/multi-memory/{source.name}; SHA256 {sha}\n"
            f";; Replaced initial module through line {end_line}; all later commands unchanged.\n"
        )
        module = binary_module(memories, types, functions)
        output = header + f"(module binary {escaped(module)})\n" + "".join(lines[end_line:])
        outputs.append((f"official_multi_memory_{source.stem}.wast", output))
    for name, output in outputs:
        Path(name).write_text(output)


if __name__ == "__main__":
    project([Path(p) for p in sys.argv[1:]])
