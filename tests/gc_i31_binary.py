"""Actual GC binary decoding, validation and certified execution regressions.

No text frontend or assembler is used. Every negative case checks both exit
status and the stage diagnostic, not merely whether execution failed.
"""
import pathlib
import re
import subprocess
import sys
import tempfile


def module(body):
    prefix = bytes.fromhex(
        "0061736d01000000 0105016000017f 03020100 "
        "070801046d61696e0000"
    )
    function = bytes([len(body) + 2, 0]) + body + b"\x0b"
    code = b"\x01" + function
    assert len(code) < 128
    return prefix + b"\x0a" + bytes([len(code)]) + code


cases = [
    ("ref_i31_nonnull", "417ffb1cd1", 0, "i32.const 0"),
    ("ref_i31_as_non_null", "417ffb1cd4d1", 0, "i32.const 0"),
    ("ref_i31_drop", "4101fb1c1a412a", 0, "i32.const 42"),
    ("ref_i31_padded_opcode", "417ffb9c00d1", 0, "i32.const 0"),
    ("ref_i31_unreachable", "00fb1c1a4107", 0, "Execution returned a trap"),
    ("ref_i31_missing_operand", "fb1c", 123, "instantiation error:"),
    ("ref_i31_i64_operand", "4201fb1cd1", 123, "instantiation error:"),
    ("ref_i31_wrong_result", "4101fb1c", 123, "instantiation error:"),
    ("ref_i31_truncated_opcode", "fb80", 123, "error in parsing module"),
    ("ref_i31_overflow_opcode", "fb9c80808010", 123, "error in parsing module"),
    ("ref_i31_reserved_opcode", "fb1f", 123, "error in parsing module"),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    for name, body, status, expected in cases:
        path = pathlib.Path(directory) / (name + ".wasm")
        path.write_bytes(module(bytes.fromhex(body)))
        result = subprocess.run(
            [exe, str(path), "-r", "main"], capture_output=True, text=True
        )
        output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
        if result.returncode != status or expected not in output:
            raise AssertionError(
                f"{name}: exit {result.returncode}, expected {status}; {output!r}"
            )
print(f"GC i31 binary runtime regressions: {len(cases)}/{len(cases)}")
