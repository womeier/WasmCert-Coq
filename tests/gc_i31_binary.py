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
    ("i31_get_null_s", "d06cfb1d", 0, "Execution returned a trap"),
    ("i31_get_null_u", "d06cfb1e", 0, "Execution returned a trap"),
    ("i31_get_wrong_null_heap", "d070fb1d", 123, "instantiation error:"),
    ("i31_get_wrong_external_heap", "d06ffb1e", 123, "instantiation error:"),
    ("i31_get_numeric_operand", "4100fb1d", 123, "instantiation error:"),
    ("i31_get_missing_operand", "fb1e", 123, "instantiation error:"),
    ("i31_get_padded_opcode", "417ffb1cfb9e00", 0, "i32.const 2147483647"),
    ("i31_get_truncated_opcode", "417ffb1cfb9d", 123, "error in parsing module"),
    ("ref_null_not_reference_type", "d0646cfb1d", 123, "error in parsing module"),
]


def signed_leb(n):
    result = []
    while True:
        low = n & 127
        n >>= 7
        if (n == 0 and low < 64) or (n == -1 and low >= 64):
            return bytes(result + [low])
        result.append(low | 128)


for value in [0, 1, -1, 63, 64, -64, -65, 1073741823, 1073741824,
              2147483647, -2147483648, -1073741825]:
    unsigned = value & 0x7fffffff
    signed = unsigned if unsigned < 0x40000000 else unsigned - 0x80000000
    prefix = b"\x41" + signed_leb(value) + b"\xfb\x1c"
    cases.append((f"i31_get_u_{value}", (prefix + b"\xfb\x1e").hex(),
                  0, f"i32.const {unsigned}"))
    cases.append((f"i31_get_s_{value}", (prefix + b"\xfb\x1d").hex(),
                  0, f"i32.const {signed}"))


def section(number, contents):
    assert len(contents) < 128
    return bytes([number, len(contents)]) + contents


def argument_fixture(nullable):
    parameter = b"\x6c" if nullable else b"\x64\x6c"
    types = b"\x02\x60\x01" + parameter + b"\x01\x7f\x60\x00\x01\x7f"
    prefix = bytes.fromhex("0061736d01000000")
    prefix += section(1, types)
    prefix += section(3, bytes.fromhex("020001"))
    prefix += section(7, bytes.fromhex("01046d61696e0001"))
    helper = bytes.fromhex("002000fb1d0b")
    value = bytes.fromhex("d06c" if nullable else "417ffb1c")
    main = b"\x00" + value + bytes.fromhex("10000b")
    return prefix + section(10, b"\x02" + bytes([len(helper)]) + helper +
                            bytes([len(main)]) + main)


def local_fixture():
    prefix = bytes.fromhex(
        "0061736d01000000 0105016000017f 03020100 "
        "070801046d61696e0000"
    )
    body = bytes.fromhex("01016c2000fb1d0b")
    return prefix + section(10, b"\x01" + bytes([len(body)]) + body)


def global_fixture():
    prefix = bytes.fromhex(
        "0061736d01000000 0105016000017f 03020100"
    )
    prefix += section(6, bytes.fromhex("016c00d06c0b"))
    prefix += section(7, bytes.fromhex("01046d61696e0000"))
    body = bytes.fromhex("002300fb1e0b")
    return prefix + section(10, b"\x01" + bytes([len(body)]) + body)


fixtures = {
    "i31_nonnull_argument": argument_fixture(False),
    "i31_nullable_argument": argument_fixture(True),
    "i31_nullable_local": local_fixture(),
    "i31_nullable_global": global_fixture(),
}
cases += [
    ("i31_nonnull_argument", "", 0, "i32.const -1"),
    ("i31_nullable_argument", "", 0, "Execution returned a trap"),
    ("i31_nullable_local", "", 0, "Execution returned a trap"),
    ("i31_nullable_global", "", 0, "Execution returned a trap"),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    for name, body, status, expected in cases:
        path = pathlib.Path(directory) / (name + ".wasm")
        path.write_bytes(fixtures[name] if name in fixtures else module(bytes.fromhex(body)))
        result = subprocess.run(
            [exe, str(path), "-r", "main"], capture_output=True, text=True
        )
        output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
        matched = expected in output.splitlines() if expected.startswith("i32.const ") else expected in output
        if result.returncode != status or not matched:
            raise AssertionError(
                f"{name}: exit {result.returncode}, expected {status}; {output!r}"
            )
print(f"GC i31 binary runtime regressions: {len(cases)}/{len(cases)}")
