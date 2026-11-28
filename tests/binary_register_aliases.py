"""Named binary modules and register aliases must retain the same instance."""
from binary_fixtures import escaped, section, vector

header = b"\x00asm\x01\x00\x00\x00"
types = section(1, vector([b"\x60\x00\x01\x7f"]))
base = (
    header
    + types
    + section(3, vector([b"\x00"]))
    + section(7, vector([b"\x03run\x00\x00"]))
    + section(10, vector([b"\x04\x00\x41\x2a\x0b"]))
)


def imported(name):
    name = name.encode("ascii")
    return (
        header
        + types
        + section(2, vector([bytes([len(name)]) + name + b"\x03run\x00\x00"]))
        + section(7, vector([b"\x03run\x00\x00"]))
    )


def invoke(name):
    print(f'(assert_return (invoke ${name} "run") (i32.const 42))')


print(f"(module $original binary {escaped(base)})")
invoke("original")
for alias in ("first", "second", "third"):
    print(f'(register "{alias}" $original)')
    invoke("original")
for alias in ("first", "second", "third"):
    print(f"(module ${alias}_import binary {escaped(imported(alias))})")
    invoke(alias + "_import")
# Named imports themselves can be registered without losing earlier aliases.
print('(register "fourth" $first_import)')
invoke("first_import")
print(f"(module $fourth_import binary {escaped(imported('fourth'))})")
invoke("fourth_import")
invoke("original")
