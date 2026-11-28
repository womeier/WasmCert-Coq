"""Binary projection of all assertions in final-spec test/core/local_init.wast.

Source: WebAssembly/spec@04931610158e1ae1c69a3abf49e73984c0d4ddaf.
The module instructions and signatures are encoded directly below, without
the deferred WAT module frontend. Invalid modules must parse and fail validation;
runtime traps, parser errors and crashes cannot satisfy an invalid assertion.
"""
import pathlib
import re
import subprocess
import sys
import tempfile


EXE = str(pathlib.Path(sys.argv[1]).resolve())


def uleb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def vector(items):
    return uleb(len(items)) + b"".join(items)


def section(tag, data):
    return bytes([tag]) + uleb(len(data)) + data


def module(signature, bodies, exports=()):
    data = bytes.fromhex("0061736d01000000")
    data += section(1, vector([bytes.fromhex(signature)]))
    data += section(3, vector([b"\x00"] * len(bodies)))
    if exports:
        entries = []
        for index, name in exports:
            encoded = name.encode()
            entries.append(uleb(len(encoded)) + encoded + b"\x00" + uleb(index))
        data += section(7, vector(entries))
    code = []
    for body in bodies:
        # One non-defaultable extern-reference local in every source function.
        encoded = bytes.fromhex("0101646f" + body + "0b")
        code.append(uleb(len(encoded)) + encoded)
    return data + section(10, vector(code))


def clean(result):
    return re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)


def binary_text(data):
    return '(module binary "' + "".join(f"\\{b:02x}" for b in data) + '")\n'


with tempfile.TemporaryDirectory() as directory:
    root = pathlib.Path(directory)
    signature = "6001646f01646f"  # (ref extern) -> (ref extern)
    first = module(signature, [
        "200021012001",
        "200022011a2001",
        "2000210102646f20010b",
    ], [(0, "get-after-set"), (1, "get-after-tee"), (2, "get-in-block-after-set")])
    last = module(signature, ["200022011a2001"], [(0, "tee-init")])
    script = binary_text(first)
    for name, value in [("get-after-set", 1), ("get-after-tee", 2),
                        ("get-in-block-after-set", 3)]:
        script += f'(assert_return (invoke "{name}" (ref.extern {value})) (ref.extern {value}))\n'
    script += binary_text(last)
    script += '(assert_return (invoke "tee-init" (ref.extern 1)) (ref.extern 1))\n'
    path = root / "local_init_binary.wast"
    path.write_text(script)
    result = subprocess.run([EXE, "--wast", str(path)], capture_output=True, text=True)
    output = clean(result)
    # Both module validations and all four return assertions must succeed.
    if result.returncode != 0 or "Result: 6/6 (100.00%)" not in output:
        raise AssertionError(f"positive local_init projection: {result.returncode}; {output!r}")

    invalid = [
        ("uninit", "600000", "20001a"),
        ("uninit-after-end", "6001646f00",
         "024020002101200022011a0b20011a"),
        ("uninit-in-else", "6001646f00",
         "41000440200021010520010b"),
        ("uninit-from-if", "6001646f00",
         "410004402000210105200021010b20011a"),
    ]
    for name, signature, body in invalid:
        path = root / (name + ".wasm")
        path.write_bytes(module(signature, [body]))
        result = subprocess.run([EXE, str(path)], capture_output=True, text=True)
        output = clean(result)
        if result.returncode != 123 or "Module type checking failure:" not in output:
            raise AssertionError(f"{name}: expected validation rejection; "
                                 f"exit {result.returncode}; {output!r}")

print("Final-spec local_init binary projection: 8/8 assertions "
      "(4 returns, 4 validation rejections; 2 positive module validations)")
