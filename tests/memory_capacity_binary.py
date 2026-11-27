"""Exercise the selected sparse backend through actual binary modules.

These core-i32 fixtures test the existing 4-GiB boundary without an eager
4-GiB host allocation. They are storage regressions, not memory64 conformance.
"""


def uleb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def section(tag, payload):
    return bytes([tag]) + uleb(len(payload)) + payload


def module(instructions, active_data=False):
    body = b"\x00" + instructions + b"\x0b"
    return (
        b"\x00asm\x01\x00\x00\x00"
        + section(1, b"\x01\x60\x00\x01\x7f")
        + section(3, b"\x01\x00")
        + section(5, b"\x01\x01" + uleb(65536) + uleb(65536))
        + section(7, b"\x01\x03run\x00\x00")
        + section(10, b"\x01" + uleb(len(body)) + body)
        + (section(11, b"\x01\x00\x41\x7f\x0b\x01\x2a")
           if active_data else b"")
    )


def emit(instructions, expected, active_data=False):
    binary = module(instructions, active_data)
    escaped = "".join(f"\\{b:02x}" for b in binary)
    print(f'(module binary "{escaped}")')
    if expected == "trap":
        print('(assert_trap (invoke "run") "out of bounds memory access")')
    else:
        print(f'(assert_return (invoke "run") (i32.const {expected}))')


emit(b"\x3f\x00", 65536)
# Last byte of a full i32-addressed memory, initially zero.
emit(b"\x41\x7f\x2d\x00\x00", 0)
# A write and an active segment both address that same last byte.
emit(b"\x41\x7f\x41\x2a\x3a\x00\x00\x41\x7f\x2d\x00\x00", 42)
emit(b"\x41\x7f\x2d\x00\x00", 42, active_data=True)
emit(b"\x41\x7f\x2f\x00\x00", "trap")
emit(b"\x41\x00\x40\x00", 65536)
emit(b"\x41\x01\x40\x00", -1)
