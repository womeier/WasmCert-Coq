"""Whole-module framing/order regressions through the production CLI."""
import sys

HEADER = b"\0asm\x01\0\0\0"


def quoted(data):
    return '"' + "".join(f"\\{byte:02x}" for byte in data) + '"'


def malformed(data):
    return f'(assert_malformed (module binary {quoted(data)}) "malformed section")'


# Canonical section order is not numeric: data-count precedes code and data.
ids = [1, 2, 3, 4, 5, 6, 7, 9, 12, 10, 11]
commands = [
    f"(module binary {quoted(HEADER + b''.join(bytes([i, 1, 0]) for i in ids))})"
]
for section_id in [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 10, 11]:
    for wrong_size in [0, 2]:
        commands.append(malformed(HEADER + bytes([section_id, wrong_size, 0])))
for sections in [
    b"\x01\x01\x00\x01\x01\x00",  # duplicate type section
    b"\x0a\x01\x00\x0c\x01\x00",  # data-count after code
    b"\x0b\x01\x00\x01\x01\x00",  # type after data
    b"\x0c\x01\x01\x0b\x01\x00",  # data-count mismatch
    b"\x03\x02\x01\x00",          # missing corresponding code
]:
    commands.append(malformed(HEADER + sections))
assert len(commands) == 30
with open(sys.argv[1], "w") as output:
    output.write("\n".join(commands) + "\n")
