"""Wrong-stage failures must not satisfy WAST negative assertions."""
import pathlib
import re
import subprocess
import sys
import tempfile


def section(identifier, payload):
    return bytes([identifier, len(payload)]) + payload


header = bytes.fromhex("0061736d01000000")
types = section(1, bytes.fromhex("01600000"))
malformed = header + b"\xff"
invalid = (
    header + section(1, bytes.fromhex("016000017f"))
    + section(3, bytes.fromhex("0100")) + section(10, bytes.fromhex("0102000b"))
)
unlinkable = header + types + section(2, bytes.fromhex("01016d01660000"))
trapping = (
    header + types + section(3, bytes.fromhex("0100"))
    + section(8, b"\0") + section(10, bytes.fromhex("010300000b"))
)
cases = [
    ("malformed", malformed, 1),
    ("invalid", invalid, 1),
    ("unlinkable", unlinkable, 1),
    ("uninstantiable", trapping, 1),
    ("invalid", malformed, 0),
    ("malformed", invalid, 0),
    ("unlinkable", malformed, 0),
    ("uninstantiable", malformed, 0),
    ("unlinkable", invalid, 0),
    ("uninstantiable", invalid, 0),
    ("invalid", unlinkable, 0),
    ("uninstantiable", unlinkable, 0),
    ("invalid", trapping, 0),
    ("malformed", trapping, 0),
    ("unlinkable", trapping, 0),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory(prefix="wasm-wast-stages-") as directory:
    for index, (stage, binary, expected) in enumerate(cases):
        escaped = "".join(f"\\{b:02x}" for b in binary)
        # The script syntax for uninstantiable modules is assert_trap.
        keyword = "trap" if stage == "uninstantiable" else stage
        path = pathlib.Path(directory, f"{index}.wast")
        path.write_text(
            f'(assert_{keyword} (module binary "{escaped}") "test")\n'
        )
        result = subprocess.run(
            [exe, "--wast", str(path)], capture_output=True, text=True
        )
        summary = re.search(r"Result: (\d+)/(\d+)", result.stdout)
        assert result.returncode == 0 and summary is not None, (
            index, result.returncode, result.stdout, result.stderr
        )
        assert tuple(map(int, summary.groups())) == (expected, 1), (
            index, stage, result.stdout, result.stderr
        )

print(f"WAST assertion stage tests: {len(cases)}/{len(cases)}")
