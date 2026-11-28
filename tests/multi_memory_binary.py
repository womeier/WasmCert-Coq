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


def module(instructions, memories=(1,), imports=(), data=(), data_count=None, peek=None):
    bodies = [b"\x00" + instructions + b"\x0b"]
    exports = [b"\x03run\x00\x00"]
    if peek is not None:
        bodies.append(b"\x00" + peek + b"\x0b")
        exports.append(b"\x04peek\x00\x01")
    return (
        b"\x00asm\x01\x00\x00\x00"
        + section(1, vector([b"\x60\x00\x01\x7f"]))
        + (section(2, vector(imports)) if imports else b"")
        + section(3, vector([b"\x00" for _ in bodies]))
        + section(5, vector([b"\x00" + uleb(n) for n in memories]))
        + section(7, vector(exports))
        + (section(12, uleb(data_count)) if data_count is not None else b"")
        + section(10, vector([uleb(len(body)) + body for body in bodies]))
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

# Fill selects only the requested memory.
fill1 = b"\x41\x00\x41\x2a\x41\x03\xfc\x0b\x01"
check(fill1 + b"\x41\x02\x2d" + arg1, 42, memories=(0, 1))
check(fill1 + b"\x41\x00\x2d" + arg, 0, memories=(1, 1))

# Cross-memory copy uses source and destination bounds independently.
source = b"\x02\x00\x41\x00\x0b\x04\x01\x02\x03\x04"
copy = b"\x41\x00\x41\x00\x41\x04\xfc\x0a\x01\x00"
check(copy + b"\x41\x03\x2d" + arg1, 4, memories=(1, 1), data=(source,))
check(copy + b"\x41\x00\x2d" + arg, 1, memories=(1, 1), data=(source,))
backward = b"\x41\x01\x41\x00\x41\x03\xfc\x0a\x01\x00"
check(
    backward + b"\x41\x03\x2d" + arg1, 3,
    imports=(spectest_memory, spectest_memory), data=(source,),
)
forward = b"\x41\x00\x41\x01\x41\x03\xfc\x0a\x01\x00"
check(
    forward + b"\x41\x00\x2d" + arg1, 2,
    imports=(spectest_memory, spectest_memory), data=(source,),
)

# An out-of-bounds source must trap before modifying the destination.
target = b"\x02\x01\x41\x00\x0b\x01\x11"
oob_copy = b"\x41\x00\x41\xff\xff\x03\x41\x02\xfc\x0a\x01\x00\x41\x00"
fixture = module(
    oob_copy, memories=(1, 1), data=(target,),
    peek=b"\x41\x00\x2d" + arg1,
)
print(f"(module binary {escaped(fixture)})")
print('(assert_trap (invoke "run") "out of bounds memory access")')
print('(assert_return (invoke "peek") (i32.const 17))')

# Zero length still checks both offsets; exactly the end is allowed.
at_end = b"\x41\x80\x80\x04"
check(at_end + at_end + b"\x41\x00\xfc\x0a\x01\x00\x41\x2a", 42, memories=(1, 1))
past_end = b"\x41\x81\x80\x04"
fixture = module(past_end + at_end + b"\x41\x00\xfc\x0a\x01\x00\x41\x00", memories=(1, 1))
print(f"(module binary {escaped(fixture)})")
print('(assert_trap (invoke "run") "out of bounds memory access")')

for op in (b"\xfc\x0b\x02", b"\xfc\x0a\x02\x00", b"\xfc\x0a\x00\x02"):
    invalid = module(b"\x41\x00\x41\x00\x41\x00" + op + b"\x41\x00", memories=(1, 1))
    print(f'(assert_invalid (module binary {escaped(invalid)}) "unknown memory")')

# Exporting memory 1 and importing it into another module preserves identity.
provider = (
    b"\x00asm\x01\x00\x00\x00"
    + section(5, vector([b"\x00\x00", b"\x00\x01"]))
    + section(7, vector([b"\x01m\x02\x01"]))
)
print(f"(module binary {escaped(provider)})")
print('(register "provider")')
provider_memory = b"\x08provider\x01m\x02\x00\x01"
check(
    b"\x41\x00\x41\x2a\x3a" + arg + b"\x41\x00\x2d" + arg1,
    0, imports=(provider_memory,),
)
check(b"\x41\x00\x2d" + arg, 42, imports=(provider_memory,))

# Active initialization bounds are checked in the selected memory.
active_oob = b"\x02\x00\x41\x00\x0b\x01\x2a"
fixture = module(b"\x41\x00", memories=(0, 1), data=(active_oob,))
print(f'(assert_trap (module binary {escaped(fixture)}) "out of bounds memory access")')

# Every scalar-free SIMD load shape selects memory 1, including extending,
# splatting and zeroing loads. Memory 0 is empty, so misselection traps.
for opcode in (*range(11), 0x5C, 0x5D):
    check(
        b"\x41\x00\xfd" + uleb(opcode) + arg1 + b"\xfd\x16\x00",
        42, memories=(0, 1), data=(active,),
    )
for load_opcode, store_opcode in zip(range(0x54, 0x58), range(0x58, 0x5C)):
    check(
        b"\x41\x00\xfd\x0c" + bytes(16)
        + b"\xfd" + uleb(load_opcode) + arg1 + b"\x00\xfd\x16\x00",
        42, memories=(0, 1), data=(active,),
    )
    check(
        b"\x41\x00\xfd\x0c" + bytes([42] * 16)
        + b"\xfd" + uleb(store_opcode) + arg1 + b"\x00"
        + b"\x41\x00\x2d" + arg1,
        42, memories=(0, 1),
    )

# Bounds must use the selected source and destination, not one shared length.
for memories in ((0, 1), (1, 0)):
    fixture = module(
        b"\x41\x00\x41\x00\x41\x01\xfc\x0a\x01\x00\x41\x00",
        memories=memories,
    )
    print(f"(module binary {escaped(fixture)})")
    print('(assert_trap (invoke "run") "out of bounds memory access")')

# Growing one imported alias is visible through the other, not the definition.
check(
    b"\x41\x01\x40\x00\x1a\x3f\x01\x3f\x02\x6a", 3,
    imports=(spectest_memory, spectest_memory),
)
