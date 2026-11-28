"""GC i31 constructors through production sequential global initialization."""
import pathlib
import re
import subprocess
import sys
import tempfile


def section(number, contents):
    assert len(contents) < 128
    return bytes([number, len(contents)]) + contents


def module(globals_hex, body):
    result = bytes.fromhex("0061736d01000000 0105016000017f 03020100")
    result += section(6, bytes.fromhex(globals_hex))
    result += section(7, bytes.fromhex("01046d61696e0000"))
    code = b"\x00" + bytes.fromhex(body) + b"\x0b"
    return result + section(10, bytes([1, len(code)]) + code)


cases = [
    ("unsigned", "01646c00417ffb1c0b", "2300fb1e", 0, "i32.const 2147483647"),
    ("signed", "01646c00417ffb1c0b", "2300fb1d", 0, "i32.const -1"),
    ("arithmetic_before_constructor", "01646c00417f41016afb1c0b", "2300fb1e",
     0, "i32.const 0"),
    ("padded_constructor_opcode", "01646c00417ffb9c000b", "2300fb1d", 0, "i32.const -1"),
    ("preceding_numeric_global", "027f00417f0b646c002300fb1c0b", "2301fb1e",
     0, "i32.const 2147483647"),
    ("preceding_i31_global", "02646c00417ffb1c0b646c0023000b", "2301fb1d",
     0, "i32.const -1"),
    ("mutable_global", "01646c01417ffb1c0b", "4101fb1c24002300fb1e",
     0, "i32.const 1"),
    ("wrong_operand", "01646c00427ffb1c0b", "2300fb1d", 123, "instantiation error:"),
    ("missing_operand", "01646c00fb1c0b", "2300fb1d", 123, "instantiation error:"),
    ("extra_stack_value", "01646c004100417ffb1c0b", "2300fb1d", 123, "instantiation error:"),
    ("wrong_declared_result", "017f00417ffb1c0b", "2300", 123, "instantiation error:"),
    ("mutable_predecessor", "027f01417f0b646c002300fb1c0b", "2301fb1d",
     123, "instantiation error:"),
    ("self_reference", "01646c0023000b", "2300fb1d", 123, "instantiation error:"),
    ("forward_reference", "02646c0023010b646c00417ffb1c0b", "2300fb1d",
     123, "instantiation error:"),
    ("get_is_not_constant", "017f00417ffb1cfb1e0b", "2300",
     123, "instantiation error:"),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    for name, globals_hex, body, status, expected in cases:
        path = pathlib.Path(directory) / (name + ".wasm")
        path.write_bytes(module(globals_hex, body))
        result = subprocess.run([exe, str(path), "-r", "main"], capture_output=True, text=True)
        output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
        matched = expected in output.splitlines() if expected.startswith("i32.const ") else expected in output
        if result.returncode != status or not matched:
            raise AssertionError(f"{name}: exit {result.returncode}, expected {status}; {output!r}")
print(f"GC i31 sequential initializer binary regressions: {len(cases)}/{len(cases)}")
