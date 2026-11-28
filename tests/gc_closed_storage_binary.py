"""Closed indexed descriptors and producer-context null lowering via the CLI."""
import pathlib
import re
import subprocess
import sys
import tempfile


def leb(n):
    result = bytearray()
    while n >= 128:
        result.append((n & 127) | 128)
        n >>= 7
    result.append(n)
    return bytes(result)


def section(number, payload):
    return bytes([number]) + leb(len(payload)) + payload


def module(types, body, globals_hex="", tables_hex="", locals_hex="00"):
    result = bytes.fromhex("0061736d01000000")
    result += section(1, bytes.fromhex(types))
    result += section(3, bytes.fromhex("0101"))
    if tables_hex:
        result += section(4, bytes.fromhex(tables_hex))
    if globals_hex:
        result += section(6, bytes.fromhex(globals_hex))
    result += section(7, bytes.fromhex("01046d61696e0000"))
    code = bytes.fromhex(locals_hex + body + "0b")
    return result + section(10, b"\x01" + leb(len(code)) + code)


cases = []
for name, types in [
    ("function", "026000006000017f"),
    ("struct", "025f006000017f"),
]:
    cases.extend([
        (name + "_global", module(types, "2300d1", "01630000d0000b"), True),
        (name + "_table_default", module(types, "41002500d1", tables_hex="0163000001"), True),
        (name + "_local_default", module(types, "2000d1", locals_hex="01016300"), True),
        (name + "_instruction", module(types, "d000d1"), True),
        (name + "_unknown_null", module(types, "d0021a4101"), False),
        (name + "_unknown_global_descriptor",
         module(types, "4101", "01630200d0000b"), False),
        (name + "_unknown_local_descriptor",
         module(types, "4101", locals_hex="01016302"), False),
    ])

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    for name, binary, valid in cases:
        path = pathlib.Path(directory) / (name + ".wasm")
        path.write_bytes(binary)
        run = subprocess.run([exe, str(path), "-r", "main"], capture_output=True, text=True)
        output = re.sub(r"\x1b\[[0-9;]*m", "", run.stdout + run.stderr)
        if valid:
            passed = run.returncode == 0 and "i32.const 1" in output.splitlines()
        else:
            passed = run.returncode == 123 and "Module type checking failure:" in " ".join(output.split())
        if not passed:
            raise AssertionError(f"{name}: exit {run.returncode}; {output!r}")
print(f"GC closed storage/null binary regressions: {len(cases)}/{len(cases)}")
