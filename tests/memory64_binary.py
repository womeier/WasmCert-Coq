"""Actual binary memory64 validation, initialization, and execution fixtures."""


def uleb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def sleb(n):
    out = bytearray()
    while True:
        byte = n & 127
        n >>= 7
        done = (n == 0 and byte & 64 == 0) or (n == -1 and byte & 64 != 0)
        out.append(byte if done else byte | 128)
        if done:
            return bytes(out)


def vec(xs):
    return uleb(len(xs)) + b"".join(xs)


def sec(tag, payload):
    return bytes([tag]) + uleb(len(payload)) + payload


def i64(n):
    return b"\x42" + sleb(n)


def i32(n):
    return b"\x41" + sleb(n)


wide = 2**32 + 16
mem64 = b"\x05" + uleb(65537) + uleb(65538)
mem32 = b"\x00\x01"


def module(code, memories=(mem64,), result=0x7f, data=(), count=None):
    body = b"\x00" + code + b"\x0b"
    return (
        b"\x00asm\x01\x00\x00\x00"
        + sec(1, b"\x01\x60\x00\x01" + bytes([result]))
        + sec(3, b"\x01\x00")
        + sec(5, vec(memories))
        + sec(7, b"\x01\x03run\x00\x00")
        + (sec(12, uleb(count)) if count is not None else b"")
        + sec(10, vec([uleb(len(body)) + body]))
        + (sec(11, vec(data)) if data else b"")
    )


def escape(binary):
    return '"' + "".join(f"\\{b:02x}" for b in binary) + '"'


def check(code, expected=42, result=0x7f, **kwargs):
    print(f"(module binary {escape(module(code, result=result, **kwargs))})")
    if expected == "trap":
        print('(assert_trap (invoke "run") "out of bounds memory access")')
    else:
        kind = "i64" if result == 0x7e else "i32"
        print(f'(assert_return (invoke "run") ({kind}.const {expected}))')


def reject(phase, code, **kwargs):
    print(f'(assert_{phase} (module binary {escape(module(code, **kwargs))}) "memory64")')


# Size/growth return i64; both memory64 limit flag forms reach the runtime.
check(b"\x3f\x00", 65537, result=0x7e)
check(i64(1) + b"\x40\x00", 65537, result=0x7e)
check(i64(2) + b"\x40\x00", -1, result=0x7e)
check(b"\x3f\x00", 0, result=0x7e, memories=(b"\x04\x00",))
check(b"\x3f\x00", 2**48, result=0x7e,
      memories=(b"\x04" + uleb(2**48),))

# Scalar access and wide static offsets must not alias the low 32 bits.
check(i64(wide) + i32(42) + b"\x3a\x00\x00" + i64(wide) + b"\x2d\x00\x00")
check(i64(0) + i32(42) + b"\x3a\x00" + uleb(wide)
      + i64(wide) + b"\x2d\x00\x00")
check(i64(wide) + i32(42) + b"\x3a\x00\x00" + i64(16) + b"\x2d\x00\x00", 0)
check(i64(-1) + b"\x2d\x00\x00", "trap")
check(i64(0) + b"\x2d\x00" + uleb(2**64 - 1), "trap")
check(i64(-1) + b"\x2d\x00\x01", "trap")
check(i64(-1) + i32(42) + b"\x3a\x00\x00" + i64(-1) + b"\x2d\x00\x00",
      memories=(b"\x04" + uleb(2**48),))
check(i64(-1) + b"\x2f\x00\x00", "trap",
      memories=(b"\x04" + uleb(2**48),))

# SIMD full-vector and lane loads/stores at an actual high address.
v42 = b"\xfd\x0c" + bytes([42] * 16)
check(i64(wide) + v42 + b"\xfd\x0b\x00\x00"
      + i64(wide) + b"\xfd\x00\x00\x00\xfd\x16\x00")
check(i64(wide) + v42 + b"\xfd\x58\x00\x00\x00"
      + i64(wide) + b"\x2d\x00\x00")
check(i64(wide) + i32(42) + b"\x3a\x00\x00"
      + i64(wide) + b"\xfd\x0c" + bytes(16)
      + b"\xfd\x54\x00\x00\x00\xfd\x16\x00")

# Fill uses a wide destination and length; init keeps i32 source/length.
check(i64(wide) + i32(42) + i64(3) + b"\xfc\x0b\x00"
      + i64(wide + 2) + b"\x2d\x00\x00")
check(i64(wide) + i32(0) + i32(1) + b"\xfc\x08\x00\x00"
      + i64(wide) + b"\x2d\x00\x00", data=(b"\x01\x01\x2a",), count=1)
check(i64(wide) + b"\x2d\x00\x00",
      data=(b"\x00" + i64(wide) + b"\x0b\x01\x2a",))

# Copy lengths use the narrower width for mixed-width memories.
check(i64(wide) + i32(42) + b"\x3a\x00\x00"
      + i32(0) + i64(wide) + i32(1) + b"\xfc\x0a\x01\x00"
      + i32(0) + b"\x2d\x40\x01\x00", memories=(mem64, mem32))
check(i32(0) + i32(42) + b"\x3a\x40\x01\x00"
      + i64(wide) + i32(0) + i32(1) + b"\xfc\x0a\x00\x01"
      + i64(wide) + b"\x2d\x00\x00", memories=(mem64, mem32))
for dest in (wide - 1, wide + 1):
    check(i64(wide) + i32(42) + b"\x3a\x00\x00"
          + i64(dest) + i64(wide) + i64(2) + b"\xfc\x0a\x00\x00"
          + i64(dest) + b"\x2d\x00\x00")
check(i64(65537 * 65536) + i32(0) + i64(0) + b"\xfc\x0b\x00" + i32(42))
check(i64(65537 * 65536 + 1) + i32(0) + i64(0) + b"\xfc\x0b\x00"
      + i32(42), "trap")

# Wrong-width operands and offsets are validation failures, not parse failures.
reject("invalid", i32(0) + b"\x2d\x00\x00")
reject("invalid", i64(0) + b"\x2d\x00\x00", memories=(mem32,))
reject("invalid", i32(0) + b"\x2d\x00" + uleb(2**32), memories=(mem32,))
reject("invalid", i64(0) + i32(0) + i32(0) + b"\xfc\x0b\x00" + i32(0))
reject("invalid", i64(0) + i32(0) + i64(0) + b"\xfc\x0a\x00\x01" + i32(0),
       memories=(mem64, mem32))
reject("invalid", i64(0) + b"\x2d\x00\x00",
       data=(b"\x00" + i32(0) + b"\x0b\x00",))
reject("invalid", i32(0), memories=(b"\x04" + uleb(2**48 + 1),))
reject("invalid", i32(0), memories=(b"\x05\x02\x01",))

# u64 decoders reject overflow and excess length in both limits and memargs.
for malformed in (b"\x80" * 9 + b"\x02", b"\x80" * 10 + b"\x00"):
    reject("malformed", i64(0) + b"\x2d\x00" + malformed)
    reject("malformed", i32(0), memories=(b"\x04" + malformed,))
reject("malformed", i32(0), memories=(b"\x06\x00",))
