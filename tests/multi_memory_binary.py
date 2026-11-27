"""Binary-only fixtures: do not depend on a multi-memory text frontend."""


def uleb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def vector(items):
    return uleb(len(items)) + b"".join(items)


def section(tag, payload):
    return bytes([tag]) + uleb(len(payload)) + payload


def module(instructions):
    body = b"\x00" + instructions + b"\x0b"
    return (
        b"\x00asm\x01\x00\x00\x00"
        + section(1, vector([b"\x60\x00\x01\x7f"]))
        + section(3, vector([b"\x00"]))
        + section(5, vector([b"\x00\x01"]))
        + section(7, vector([b"\x03run\x00\x00"]))
        + section(10, vector([uleb(len(body)) + body]))
    )


def escaped(data):
    return '"' + "".join(f"\\{b:02x}" for b in data) + '"'


def check(instructions, expected):
    print(f"(module binary {escaped(module(instructions))})")
    print(f'(assert_return (invoke "run") (i32.const {expected}))')


# Flag bit 6 requests an explicit index, even when that index is zero.
arg = b"\x40\x00\x00"
check(b"\x41\x00\x41\x2a\x3a" + arg + b"\x41\x00\x2d" + arg, 42)
check(
    b"\x41\x00\xfd\x0c" + bytes([42] * 16) + b"\xfd\x0b" + arg
    + b"\x41\x00\xfd\x00" + arg + b"\xfd\x16\x00",
    42,
)
# A SIMD lane access uses the same indexed memarg, followed by a byte lane.
check(
    b"\x41\x00\xfd\x0c" + bytes([42] * 16) + b"\xfd\x58" + arg + b"\x00"
    + b"\x41\x00\x2d" + arg,
    42,
)
check(b"\x41\x01\x40\x00\x1a\x3f\x00", 2)

bad_index = module(b"\x41\x00\x28\x40\x01\x00")
print(f'(assert_invalid (module binary {escaped(bad_index)}) "unknown memory")')
reserved_flags = module(b"\x41\x00\x28\x80\x01\x00")
print(f'(assert_malformed (module binary {escaped(reserved_flags)}) "malformed memop flags")')
