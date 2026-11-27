"""Exercise the extracted binary module parser and validator, without text."""
import pathlib
import re
import subprocess
import sys
import tempfile


def section(identifier, payload):
    assert len(payload) < 128
    return bytes([identifier, len(payload)]) + payload


header = bytes.fromhex("0061736d01000000")
types = section(1, bytes.fromhex("01600000"))
tag = section(13, bytes.fromhex("010000"))
empty_tags = section(13, b"\0")
global_section = section(6, bytes.fromhex("017f0041000b"))
memory_section = section(5, bytes.fromhex("010000"))
cases = [
    ("one-tag", types + tag, None),
    ("empty-tags", empty_tags, None),
    ("two-tags", types + section(13, bytes.fromhex("0200000000")), None),
    ("tag-before-global", types + tag + global_section, None),
    ("tag-after-memory", types + memory_section + tag, None),
    ("unknown-type", tag, "Module type checking failure:invalid tag type"),
    ("bad-type-index", types + section(13, bytes.fromhex("010001")),
     "Module type checking failure:invalid tag type"),
    ("result-bearing-tag", section(1, bytes.fromhex("016000017f")) + tag,
     "Module type checking failure:invalid tag type"),
    ("nonzero-attribute", types + section(13, bytes.fromhex("010100")),
     "error in parsing module"),
    ("truncated-tag", types + section(13, bytes.fromhex("0100")),
     "error in parsing module"),
    ("duplicate-section", types + tag + tag, "error in parsing module"),
    ("tag-after-global", types + global_section + tag, "error in parsing module"),
    ("size-too-small", types + bytes.fromhex("0d02010000"),
     "error in parsing module"),
    ("size-too-large", types + bytes.fromhex("0d04010000"),
     "error in parsing module"),
    ("extra-payload", types + section(13, bytes.fromhex("01000000")),
     "error in parsing module"),
    ("oversized-index", types + section(13, bytes.fromhex("0100ffffffff10")),
     "error in parsing module"),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory(prefix="wasm-eh-tags-") as directory:
    for name, contents, expected_error in cases:
        path = pathlib.Path(directory, name + ".wasm")
        path.write_bytes(header + contents)
        result = subprocess.run(
            [exe, "--no-exec", str(path)], capture_output=True, text=True
        )
        output = " ".join((result.stdout + result.stderr).split())
        if expected_error is None:
            assert result.returncode == 0, (name, result.returncode, output)
        else:
            assert result.returncode == 123 and expected_error in output, (
                name, result.returncode, output
            )

    # A tag-bearing module must still execute ordinary function bodies.
    function = section(3, bytes.fromhex("0100"))
    exports = section(7, bytes.fromhex("01046d61696e0000"))
    code = section(10, bytes.fromhex("010400412a0b"))
    mixed_types = section(1, bytes.fromhex("026000017f600000"))
    path = pathlib.Path(directory, "tag-and-function.wasm")
    path.write_bytes(
        header + mixed_types + function
        + section(13, bytes.fromhex("010001")) + exports + code
    )
    result = subprocess.run(
        [exe, str(path), "-r", "main"], capture_output=True, text=True
    )
    output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout).strip()
    assert result.returncode == 0 and output == "i32.const 42", (
        result.returncode, result.stdout, result.stderr
    )

print(f"Extracted tag binary tests: {len(cases) + 1}/{len(cases) + 1}")
