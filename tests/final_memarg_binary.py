"""Final u64 memarg syntax with memory32 validation, through the real CLI.

No memory64 feature, text-memory parser, or replacement codec is used.
"""
from binary_fixtures import escaped, section, uleb, vector


def module(instructions):
    body = b"\x00" + instructions + b"\x0b"
    return (
        b"\x00asm\x01\x00\x00\x00"
        + section(1, vector([b"\x60\x00\x00"]))
        + section(3, vector([b"\x00"]))
        + section(5, vector([b"\x00\x01", b"\x00\x01"]))
        + section(10, vector([uleb(len(body)) + body]))
    )


def assertion(kind, instructions):
    print(
        f'({kind} (module binary {escaped(module(instructions))}) '
        '"memory32 static offset")'
    )


address = b"\x41\x00"
scalar = b"\x41\x00"
vec = b"\xfd\x0c" + bytes(16)

for offset in (1 << 32, (1 << 64) - 1):
    for header in (b"\x00", b"\x40\x00", b"\x40\x01"):
        memarg = header + uleb(offset)
        for instruction in (
            address + b"\x28" + memarg + b"\x1a",
            address + scalar + b"\x36" + memarg,
            address + b"\xfd\x00" + memarg + b"\x1a",
            address + vec + b"\xfd\x0b" + memarg,
            address + vec + b"\xfd\x54" + memarg + b"\x00\x1a",
            address + vec + b"\xfd\x58" + memarg + b"\x00",
        ):
            assertion("assert_invalid", instruction)

# A legal ten-byte padded offset with value 2^32 still decodes, then fails
# memory32 validation. Eleven bytes or values beyond u64 are malformed.
assertion(
    "assert_invalid",
    address + b"\x28\x00" + bytes([0x80] * 4 + [0x90] + [0x80] * 4 + [0]) + b"\x1a",
)
for offset in (bytes([0x80] * 10 + [0]), uleb(1 << 64)):
    assertion("assert_malformed", address + b"\x28\x00" + offset + b"\x1a")
