"""Binary table64 declarations and actual selected-width table execution."""


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
        b = n & 127
        n >>= 7
        done = (n == 0 and b & 64 == 0) or (n == -1 and b & 64 != 0)
        out.append(b if done else b | 128)
        if done:
            return bytes(out)


def vec(xs):
    return uleb(len(xs)) + b"".join(xs)


def sec(tag, data):
    return bytes([tag]) + uleb(len(data)) + data


def i64(n):
    if n >= 2**63:
        n -= 2**64
    return b"\x42" + sleb(n)


def i32(n):
    return b"\x41" + sleb(n)


def tt(width, minimum, maximum=None, ref=0x70):
    return bytes([ref, (4 if width == 64 else 0) + (maximum is not None)]) + \
        uleb(minimum) + (uleb(maximum) if maximum is not None else b"")


t64 = tt(64, 4, 8)
t32 = tt(32, 4, 8)
null = b"\xd0\x70"
func = b"\xd2\x01"
get = b"\x25\x00"
set_ = b"\x26\x00"
is_null = b"\xd1"
fill = b"\xfc\x11\x00"
copy00 = b"\xfc\x0e\x00\x00"
init = b"\xfc\x0c\x00\x00"


def active(offset, functions=(1,)):
    return b"\x00" + offset + b"\x0b" + vec([uleb(f) for f in functions])


def module(code, tables=(t64,), result=0x7f, elements=()):
    bodies = [b"\x00" + code + b"\x0b", b"\x00" + i32(42) + b"\x0b",
              b"\x00" + i64(7) + b"\x0b"]
    return (
        b"\x00asm\x01\x00\x00\x00"
        + sec(1, vec([b"\x60\x00\x01\x7f", b"\x60\x00\x01\x7e"]))
        + sec(3, vec([b"\x01" if result == 0x7e else b"\x00", b"\x00", b"\x01"]))
        + sec(4, vec(tables))
        + sec(7, b"\x01\x03run\x00\x00")
        + sec(9, vec(list(elements) + [b"\x03\x00\x03\x00\x01\x02"]))
        + sec(10, vec([uleb(len(b)) + b for b in bodies]))
    )


def escaped(data):
    return '"' + "".join(f"\\{b:02x}" for b in data) + '"'


def check(code, expected, result=0x7f, **kwargs):
    print(f"(module binary {escaped(module(code, result=result, **kwargs))})")
    if expected == "trap":
        print('(assert_trap (invoke "run") "table access trap")')
    else:
        kind = "i64" if result == 0x7e else "i32"
        print(f'(assert_return (invoke "run") ({kind}.const {expected}))')


def reject(phase, code, **kwargs):
    print(f'(assert_{phase} (module binary {escaped(module(code, **kwargs))}) "table64")')


def declaration_case(table, phase=None):
    """Minimal table-only modules: no unrelated functions or element segments."""
    data = b"\x00asm\x01\x00\x00\x00" + sec(4, vec([table]))
    command = f"(module binary {escaped(data)})"
    print(command if phase is None else f'(assert_{phase} {command} "table type")')


# Original official table.wast commands 14--16: explicit null initializers,
# including the explicit nullable spelling. These must parse AND instantiate.
for size, reference in ((0, b"\x70"), (1, b"\x70"), (1, b"\x63\x70")):
    declaration_case(b"\x40\x00" + reference + b"\x00" + uleb(size) + null + b"\x0b")

# Commands 40--41 and 43--45: parse successfully, then fail VALIDATION.
declaration_case(b"\x40\x00\x63\x70\x00\x01" + i32(0) + b"\x0b", "invalid")
declaration_case(b"\x40\x00\x64\x70\x00\x01\xd0\x6f\x0b", "invalid")
declaration_case(b"\x40\x00\x64\x70\x00\x01" + null + b"\x0b", "invalid")
declaration_case(b"\x64\x70\x00\x00", "invalid")
declaration_case(b"\x64\x6f\x00\x00", "invalid")

# Commands 21--23 are deferred quoted-text validation cases. Their oversized
# table32 fields have NO valid u32 binary encoding: the corresponding bytes
# must fail decoding, not be accepted as invalid modules or truncated to zero.
for minimum, maximum in ((2**32, None), (2**32, 2**32), (0, 2**32)):
    declaration_case(tt(32, minimum, maximum), "malformed")


check(b"\xfc\x10\x00", 4, result=0x7e)
check(null + i64(2) + b"\xfc\x0f\x00", 4, result=0x7e)
check(null + i64(5) + b"\xfc\x0f\x00", -1, result=0x7e)
check(null + i64(-1) + b"\xfc\x0f\x00", -1, result=0x7e)
check(i64(3) + get + is_null, 1)
check(i64(3) + func + set_ + i64(3) + get + is_null, 0)
check(i64(1) + func + i64(3) + fill + i64(3) + get + is_null, 0)
check(i64(4) + null + i64(0) + fill + i32(42), 42)
check(i64(5) + null + i64(0) + fill + i32(42), "trap")
check(i64(3) + func + i64(2) + fill + i32(42), "trap")
for address in (4, 2**32, 2**63, -1):
    check(i64(address) + get + is_null, "trap")
    check(i64(address) + null + set_ + i32(0), "trap")

# Both overlap directions, checking copied non-null references.
for dest in (0, 2):
    check(i64(1) + func + set_ + i64(dest) + i64(1) + i64(2) + copy00
          + i64(dest) + get + is_null, 0)
check(i64(4) + i64(4) + i64(0) + copy00 + i32(42), 42)
check(i64(5) + i64(4) + i64(0) + copy00 + i32(0), "trap")
check(i64(0) + i64(-1) + i64(1) + copy00 + i32(0), "trap")
check(i64(3) + func + set_ + i32(1) + i64(3) + i32(1)
      + b"\xfc\x0e\x01\x00" + i32(1) + b"\x25\x01" + is_null, 0, tables=(t64, t32))
check(i32(3) + func + b"\x26\x01" + i64(1) + i32(3) + i32(1)
      + b"\xfc\x0e\x00\x01" + i64(1) + get + is_null, 0, tables=(t64, t32))

# Passive init has i64 destination but still i32 segment source and count.
passive = b"\x01\x00\x01\x01"
check(i64(2) + i32(0) + i32(1) + init + i64(2) + get + is_null, 0,
      elements=(passive,))
check(i64(0) + i32(1) + i32(1) + init + i32(0), "trap", elements=(passive,))
check(i64(4) + i32(1) + i32(0) + init + i32(42), 42, elements=(passive,))
check(i64(0) + i32(0) + i32(1) + init + b"\xfc\x0d\x00"
      + i64(1) + i32(0) + i32(1) + init + i32(0), "trap", elements=(passive,))
check(i64(1) + b"\x11\x00\x00", 42, elements=(active(i64(1)),))
check(i64(1) + b"\x13\x00\x00", 42, elements=(active(i64(1)),))
check(i64(2) + b"\x11\x00\x00", "trap", elements=(active(i64(1)),))
check(i64(4) + b"\x13\x00\x00", "trap", elements=(active(i64(1)),))
check(i64(0) + b"\x11\x01\x00", "trap", result=0x7e,
      elements=(active(i64(0)),))

# Actual high entries in compact full-capacity storage, without aliasing.
full = tt(64, 2**64 - 1)
check(b"\xfc\x10\x00", -1, result=0x7e, tables=(full,))
check(i64(-2) + func + set_ + i64(-2) + get + is_null, 0, tables=(full,))
check(i64(-1) + get + is_null, "trap", tables=(full,))
check(i64(2**32) + func + set_ + i64(0) + get + is_null, 1, tables=(full,))
check(i64(2**32) + func + i64(2) + fill
      + i64(2**32 + 1) + get + is_null, 0, tables=(full,))
check(i64(2**32) + func + set_ + i64(2**32 + 1) + i64(2**32) + i64(2)
      + copy00 + i64(2**32 + 1) + get + is_null, 0, tables=(full,))
check(i64(2**32) + i32(0) + i32(1) + init
      + i64(2**32) + b"\x11\x00\x00", 42, tables=(full,), elements=(passive,))
check(i64(2**32) + b"\x13\x00\x00", 42, tables=(full,),
      elements=(active(i64(2**32)),))
check(func + i64(2**32) + b"\xfc\x0f\x00\x1a"
      + i64(2**32) + get + is_null, 0, tables=(tt(64, 1),))

reject("invalid", i32(0) + get + is_null)
reject("invalid", i64(0) + get + is_null, tables=(t32,))
reject("invalid", i64(0) + null + i32(0) + fill + i32(0))
reject("invalid", i64(0) + i32(0) + i64(0) + b"\xfc\x0e\x00\x01" + i32(0),
       tables=(t64, t32))
reject("invalid", i64(0) + i64(0) + i32(0) + init + i32(0), elements=(passive,))
reject("invalid", i64(0) + b"\x11\x00\x00", elements=(active(i32(0)),))
reject("invalid", i32(0) + b"\x11\x00\x00")
reject("invalid", i32(0) + b"\x13\x00\x00")
reject("invalid", i32(0), tables=(tt(64, 2, 1),))
reject("invalid", i64(0) + b"\x11\x00\x00", tables=(tt(64, 1, ref=0x6f),))
for malformed in (b"\x80" * 9 + b"\x02", b"\x80" * 10 + b"\x00", b""):
    reject("malformed", i32(0), tables=(b"\x70\x04" + malformed,))
reject("malformed", i32(0), tables=(b"\x70\x06\x00",))

# Active initialization traps at instantiation, not validation or decoding.
print(f'(assert_trap (module binary {escaped(module(i32(0), elements=(active(i64(-1)),)))}) "out of bounds table access")')

# Width-bearing imported types use the same binary grammar and core matcher.
exported_table = (b"\x00asm\x01\x00\x00\x00"
                  + sec(4, vec([tt(64, 2**32 + 1)]))
                  + sec(7, b"\x01\x01t\x01\x00"))
print(f"(module binary {escaped(exported_table)})")
print('(register "M")')


def imported_table(table_type, source=b"M", name=b"t", instructions=None):
    if instructions is None:
        instructions = i64(2**32) + get + is_null
    body = b"\x00" + instructions + b"\x0b"
    return (b"\x00asm\x01\x00\x00\x00"
            + sec(1, b"\x01\x60\x00\x01\x7f")
            + sec(2, vec([uleb(len(source)) + source + uleb(len(name)) + name
                          + b"\x01" + table_type]))
            + sec(3, b"\x01\x00")
            + sec(7, b"\x01\x03run\x00\x00")
            + sec(10, vec([uleb(len(body)) + body])))


print(f"(module binary {escaped(imported_table(tt(64, 2**32 + 1)))})")
print('(assert_return (invoke "run") (i32.const 1))')
# For the wrong-width link check, use an i32 body so the module itself is valid.
wrong_body = b"\x00" + i32(0) + get + is_null + b"\x0b"
wrong_width = (b"\x00asm\x01\x00\x00\x00"
               + sec(1, b"\x01\x60\x00\x01\x7f")
               + sec(2, b"\x01\x01M\x01t\x01" + tt(32, 0))
               + sec(3, b"\x01\x00") + sec(7, b"\x01\x03run\x00\x00")
               + sec(10, vec([uleb(len(wrong_body)) + wrong_body])))
for binary in (wrong_width, imported_table(tt(64, 2**32 + 2)),
               imported_table(tt(64, 0, 2**32 + 1))):
    print(f'(assert_unlinkable (module binary {escaped(binary)}) "incompatible import type")')

print(f"(module binary {escaped(imported_table(tt(64, 10, 20), source=b'spectest', name=b'table64', instructions=i64(9) + get + is_null))})")
print('(assert_return (invoke "run") (i32.const 1))')
