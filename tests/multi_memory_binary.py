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


def module(instructions, memories=(1,), imports=(), data=(), data_count=None):
    body = b"\x00" + instructions + b"\x0b"
    return (
        b"\x00asm\x01\x00\x00\x00"
        + section(1, vector([b"\x60\x00\x01\x7f"]))
        + (section(2, vector(imports)) if imports else b"")
        + section(3, vector([b"\x00"]))
        + section(5, vector([b"\x00" + uleb(n) for n in memories]))
        + section(7, vector([b"\x03run\x00\x00"]))
        + (section(12, uleb(data_count)) if data_count is not None else b"")
        + section(10, vector([uleb(len(body)) + body]))
        + (section(11, vector(data)) if data else b"")
    )


def escaped(data):
    return '"' + "".join(f"\\{b:02x}" for b in data) + '"'


def check(instructions, expected, **kwargs):
    print(f"(module binary {escaped(module(instructions, **kwargs))})")
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

# Nonzero memory selection, including isolation of writes and growth.
arg1 = b"\x40\x01\x00"
check(b"\x3f\x01", 2, memories=(1, 2))
check(b"\x41\x01\x40\x01\x1a\x3f\x01\x3f\x00\x6a", 4, memories=(1, 2))
check(b"\x41\x00\x41\x2a\x3a" + arg1 + b"\x41\x00\x2d" + arg1, 42, memories=(1, 1))
check(b"\x41\x00\x41\x2a\x3a" + arg1 + b"\x41\x00\x2d" + arg, 0, memories=(1, 1))
check(
    b"\x41\x00\xfd\x0c" + bytes([42] * 16) + b"\xfd\x0b" + arg1
    + b"\x41\x00\xfd\x00" + arg1 + b"\xfd\x16\x00",
    42, memories=(1, 1),
)
check(
    b"\x41\x00\xfd\x0c" + bytes([42] * 16) + b"\xfd\x0b" + arg1
    + b"\x41\x00\x2d" + arg,
    0, memories=(1, 1),
)

# Two imports of the same host memory alias each other; a definition follows
# both imported indices and must not alias them.
spectest_memory = b"\x08spectest\x06memory\x02\x01\x01\x02"
check(
    b"\x41\x00\x41\x2a\x3a" + arg + b"\x41\x00\x2d" + arg1,
    42, imports=(spectest_memory, spectest_memory),
)
check(
    b"\x41\x00\x41\x2a\x3a" + arg + b"\x41\x00\x2d\x40\x02\x00",
    0, imports=(spectest_memory, spectest_memory),
)

# Active data targets memory 1 even though memory 0 has no pages.
active = b"\x02\x01\x41\x00\x0b\x01\x2a"
check(b"\x41\x00\x2d" + arg1, 42, memories=(0, 1), data=(active,))

# Passive initialization encodes dataidx before memidx.
passive = b"\x01\x01\x2b"
check(
    b"\x41\x00\x41\x00\x41\x01\xfc\x08\x00\x01\x41\x00\x2d" + arg1,
    43, memories=(0, 1), data=(passive,), data_count=1,
)
trapping_init = b"\x41\x00\x41\x00\x41\x02\xfc\x08\x00\x01\x41\x00"
print(f"(module binary {escaped(module(trapping_init, memories=(0, 1), data=(passive,), data_count=1))})")
print('(assert_trap (invoke "run") "out of bounds memory access")')
