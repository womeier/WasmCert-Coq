"""Script definitions validate binaries without linking or instantiating."""
import sys


def vec(xs):
    return bytes([len(xs)]) + b"".join(xs)


def sec(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


magic = b"\x00asm\x01\x00\x00\x00"
counter = (
    magic
    + sec(1, b"\x01\x60\x00\x01\x7f")
    + sec(3, b"\x02\x00\x00")
    + sec(6, b"\x01\x7f\x01\x41\x00\x0b")
    + sec(7, b"\x02\x03get\x00\x00\x04bump\x00\x01")
    + sec(10, vec([b"\x04\x00\x23\x00\x0b",
                   b"\x0b\x00\x23\x00\x41\x01\x6a\x24\x00\x23\x00\x0b"]))
)
trapping = (magic + sec(1, b"\x01\x60\x00\x00") + sec(3, b"\x01\x00")
            + sec(8, b"\x00") + sec(10, b"\x01\x03\x00\x00\x0b"))
unlinkable = (magic + sec(1, b"\x01\x60\x00\x00")
              + sec(2, b"\x01\x06absent\x01f\x00\x00"))
invalid = magic + sec(3, b"\x01\x00") + sec(10, b"\x01\x02\x00\x0b")
null_results = (
    magic
    + sec(1, vec([b"\x60\x00\x01\x70", b"\x60\x00\x01\x6f", b"\x60\x00\x02\x7f\x70"]))
    + sec(3, b"\x04\x00\x01\x00\x02")
    + sec(7, vec([b"\x02nf\x00\x00", b"\x02ne\x00\x01",
                  b"\x01f\x00\x02", b"\x03mix\x00\x03"]))
    + sec(9, b"\x01\x03\x00\x01\x00")
    + sec(10, vec([b"\x04\x00\xd0\x70\x0b", b"\x04\x00\xd0\x6f\x0b",
                   b"\x04\x00\xd2\x00\x0b", b"\x06\x00\x41\x01\xd0\x70\x0b"]))
)


def module(data, prefix=""):
    escaped = "".join(f"\\{b:02x}" for b in data)
    return f'(module {prefix}binary "{escaped}")'


def expect(target, operation, value):
    print(f'(assert_return (invoke {target}"{operation}") (i32.const {value}))')


mode = sys.argv[1] if len(sys.argv) > 1 else "positive"
if mode == "invalid":
    print(module(invalid, "definition "))
elif mode == "malformed":
    print(module(b"not wasm", "definition "))
elif mode == "unknown":
    print("(module instance $missing)")
elif mode == "trapping":
    print(module(trapping, "definition $T "))
    print("(module instance $T)")
elif mode == "inline":
    print("(func)\n(memory 0)")
elif mode == "nonnull":
    print(module(null_results))
    print('(assert_return (invoke "f") (ref.null))')
elif mode == "unsupported-reference":
    print(module(magic + sec(1, b"\x01\x60\x00\x00")
                 + sec(4, b"\x01\x63\x00\x00\x00")))
else:
    assert mode == "positive"
    print(module(counter, "$initial "))
    expect("$initial ", "bump", 1)
    print(module(trapping, "definition $T "))
    print(module(unlinkable, "definition $U "))
    # Neither definition executes start, links imports, or changes default instance.
    expect("", "get", 1)
    print(module(counter, "definition $D "))
    print("(module instance $A $D)")
    print("(module instance $B $D)")
    expect("$A ", "bump", 1)
    expect("$A ", "get", 1)
    expect("$B ", "get", 0)
    print('(register "B" $B)')
    print("(module instance $D)")
    expect("", "get", 0)
    print("(module instance)")
    expect("", "bump", 1)
    expect("$B ", "get", 0)
    print(module(null_results))
    print('(assert_return (invoke "nf") (ref.null))')
    print('(assert_return (invoke "ne") (ref.null))')
    print('(assert_return (invoke "f") (ref.func))')
    print('(assert_return (invoke "mix") (i32.const 1) (ref.null))')
