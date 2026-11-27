"""Exercise actual extracted binary parsing, validation and execution.

Fixtures are encoded directly, not passed through the deferred text frontend.
The module has two () -> i32 functions, exports the second as main, and
declares the first for ref.func. Only main's instruction bytes vary.
"""
import pathlib
import re
import subprocess
import sys
import tempfile


def module(body):
    prefix = bytes.fromhex(
        "0061736d01000000 0105016000017f 0303020000 "
        "070801046d61696e0001 09050103000100"
    )
    first = bytes.fromhex("0400412a0b")
    second = bytes([len(body) + 2, 0]) + body + b"\x0b"
    code = b"\x02" + first + second
    assert len(code) < 128
    return prefix + b"\x0a" + bytes([len(code)]) + code


cases = [
    ("function", "d200d4d1", 0, "i32.const 0"),
    ("function_identity", "d200d4d4d1", 0, "i32.const 0"),
    ("null_function", "d070d4d1", 0, "Execution returned a trap"),
    ("null_external", "d06fd4d1", 0, "Execution returned a trap"),
    ("numeric_operand", "4100d4", 123, "instantiation error:"),
    ("missing_operand", "d4", 123, "instantiation error:"),
    ("unreachable", "00d41a4107", 0, "Execution returned a trap"),
    # Genuine invalid operands: these must reach validation, not fail decoding.
    # Positive typed-call validation still depends on closed indexed types.
    ("numeric_call_ref", "41001400", 123, "instantiation error:"),
    ("numeric_return_call_ref", "41001500", 123, "instantiation error:"),
    ("missing_call_ref_operand", "1400", 123, "instantiation error:"),
    ("truncated_call_ref_index", "1480", 123, "error in parsing module"),
    ("overflow_call_ref_index", "148080808010", 123, "error in parsing module"),
    ("branch_function", "0270d200d600d0700bd1", 0, "i32.const 0"),
    ("branch_null_fallthrough", "0270d070d600d0700bd1", 0, "i32.const 1"),
    ("branch_external_null", "026fd06fd600d06f0bd1", 0, "i32.const 1"),
    ("branch_missing_ref_result", "0240d070d6000b4107", 123, "instantiation error:"),
    ("branch_numeric_result", "027fd070d60041070b", 123, "instantiation error:"),
    ("branch_numeric_operand", "02704100d600d0700bd1", 123, "instantiation error:"),
    ("branch_invalid_label", "d070d6014107", 123, "instantiation error:"),
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
print(f"function-reference binary runtime regressions: {len(cases)}/{len(cases)}")
