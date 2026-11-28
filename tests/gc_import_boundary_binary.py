"""Recursive-group identity at the actual function import boundary.

All module contents are literal binaries, not GC text assembled by a tool.
See gc_import_boundary.md for pinned specification/reference provenance.
"""
import pathlib
import re
import subprocess
import sys
import tempfile


def section(kind, payload):
    assert len(payload) < 128
    return bytes([kind, len(payload)]) + payload


def module(group, *, producer=False):
    binary = bytes.fromhex("0061736d01000000")
    binary += section(1, bytes.fromhex(group))
    if producer:
        binary += section(3, bytes.fromhex("0101"))
    else:
        binary += section(2, bytes.fromhex("01017001660001"))
    binary += section(7, bytes.fromhex("0101660000"))
    if producer:
        binary += section(10, bytes.fromhex("0102000b"))
    return binary


def quoted(binary):
    return '"' + "".join(f"\\{b:02x}" for b in binary) + '"'


producer = module("014e025f00600000", producer=True)
same_group = module("014e025f00600000")
other_group = module("014e025e7f00600000")
script = "\n".join([
    f"(module binary {quoted(producer)})",
    '(register "p")',
    f"(module binary {quoted(same_group)})",
    '(assert_return (invoke "f"))',
    f'(assert_unlinkable (module binary {quoted(other_group)}) "incompatible import type")',
    "",
])

if len(sys.argv) == 3 and sys.argv[1] == "--emit":
    pathlib.Path(sys.argv[2]).write_text(script)
    sys.exit(0)

reference = len(sys.argv) == 3 and sys.argv[1] == "--reference"
exe = str(pathlib.Path(sys.argv[2] if reference else sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    path = pathlib.Path(directory) / "canonical_import_boundary.wast"
    path.write_text(script)
    run = subprocess.run(
        [exe, str(path)] if reference else [exe, "--wast", str(path)],
        capture_output=True, text=True,
    )
    output = re.sub(r"\x1b\[[0-9;]*m", "", run.stdout + run.stderr)
    if run.returncode != 0 or (not reference and
                              not re.search(r"Result:\s+5/5\b", output)):
        raise AssertionError(f"exit {run.returncode}: {output!r}")
print("Canonical function import binary boundary: 2/2")
