"""Final Wasm3 memarg flag classification, bypassing the stale WAST assertions."""
import pathlib
import subprocess
import sys
import tempfile

exe = sys.argv[1]
header = bytes.fromhex("0061736d01000000010401600000030201000503010001")
cases = [
    # Exactly the five legacy align.wast byte sequences. For 64/65 the old
    # "drop" byte is the offset after explicit memory index zero, so these
    # are still decoded modules, then rejected by validation.
    (f"legacy-flags-{flags}", bytes([flags, 0, 0x1A]), False)
    for flags in (32, 33, 63, 64, 65)
]
cases += [
    ("flags-128", bytes.fromhex("8001001a"), True),
    ("flags-u32-overflow", bytes.fromhex("8080808010001a"), True),
]

with tempfile.TemporaryDirectory(prefix="wasmcert-memarg-") as directory:
    for name, immediate, malformed in cases:
        body = b"\0\x41\0\x28" + immediate + b"\x0b"
        binary = header + b"\x0a" + bytes([len(body) + 2, 1, len(body)]) + body
        path = pathlib.Path(directory, name + ".wasm")
        path.write_bytes(binary)
        result = subprocess.run([exe, "--no-exec", str(path)],
                                capture_output=True, text=True, timeout=20)
        output = result.stdout + result.stderr
        expected = "error in parsing module" if malformed else "Module type checking failure"
        assert result.returncode == 123 and expected in output, (
            name, result.returncode, output
        )

print(f"Extracted final memarg stage tests: {len(cases)}/{len(cases)}")
