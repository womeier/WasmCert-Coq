"""Feature-appropriate oracles for exactly the 20 unchanged root differences.

Not a replacement root suite and not a claim that the original assertions pass.
The 15 binary modules are copied byte-for-byte from hash-pinned root fixtures.
Only their expected phase changes. Five text modules have reviewed direct
binary equivalents; no general text frontend is implemented.

Final rules: WebAssembly/spec d7aada502455b3d9176ca4cbe48be4724d511d2a,
document/core/binary/instructions.rst: binary-memarg, binary-memory.size/grow;
document/core/valid/instructions.rst: valid-load and indexed memory rules;
document/core/valid/modules.rst: module memory index space.
Offsets here are all tiny u32 values; this does not enable memory64.
"""
import hashlib
from pathlib import Path
import re
import sys

from binary_fixtures import escaped, section, uleb, vector

SUITE_PIN = "b497cbb853db21be875bd5c81fcc3334168fb0b4"
SPEC_PIN = "d7aada502455b3d9176ca4cbe48be4724d511d2a"
HASHES = {
    "memory.wast": "3037e7bd8b7a02d2dc77890858974285b9255a1b48c502270164f572dbacb5dc",
    "imports.wast": "5e08aad601fe76e767a621d18932a07e6df094b768e891422f3a576efcedfa21",
    "binary.wast": "6c88456c854e3ca739d15ac69e10822ed3e491229a636746ea05a4ba0e81af61",
    "align.wast": "ec508960f3bb7532a4bc81650db92ec5cf6dba2765a267399b2b4478f8c5edd1",
}
HEADER = b"\x00asm\x01\x00\x00\x00"


def memory_module(imports=(), memories=()):
    data = HEADER
    if imports:
        entries = []
        for module, name, minimum in imports:
            entries.append(
                uleb(len(module)) + module + uleb(len(name)) + name
                + b"\x02\x00" + uleb(minimum)
            )
        data += section(2, vector(entries))
    if memories:
        data += section(5, vector([b"\x00" + uleb(n) for n in memories]))
    return data


def original_binary(lines, assertion_line):
    """Extract only the known binary literal fragments in these pinned cases."""
    if lines[assertion_line - 1].strip() != "(assert_malformed":
        raise ValueError(f"Original assertion moved: line {assertion_line}")
    if lines[assertion_line].strip() != "(module binary":
        raise ValueError(f"Binary module moved: line {assertion_line + 1}")
    fragments = []
    for line in lines[assertion_line + 1:]:
        if line.strip() == ")":
            break
        code = line.split(";;", 1)[0]
        for fragment in re.findall(r'"([^"]*)"', code):
            tokens = re.findall(r"\\[0-9a-fA-F]{2}|[^\\]", fragment)
            if "".join(tokens) != fragment:
                raise ValueError("Unexpected escape in pinned binary fixture")
            fragments.append(bytes(
                int(t[1:], 16) if t.startswith("\\") else ord(t) for t in tokens
            ))
    else:
        raise ValueError("Missing pinned binary module boundary")
    data = b"".join(fragments)
    if not data.startswith(HEADER):
        raise ValueError("Pinned binary fixture lost its header")
    return data


def command(source, line, data, phase, reason):
    print(f";; {source}:{line}; final phase={phase}; {reason}")
    module = f"(module binary {escaped(data)})"
    if phase == "valid":
        print(module)
    elif phase == "invalid":
        print(f'(assert_invalid {module} "feature-appropriate validation failure")')
    elif phase == "unlinkable":
        print(f'(assert_unlinkable {module} "unknown import")')
    else:
        raise ValueError(phase)


def generate(paths):
    if len(paths) != 4 or {p.name for p in paths} != HASHES.keys():
        raise ValueError("Exactly the four pinned root files are required")
    sources = {}
    for path in paths:
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != HASHES[path.name]:
            raise ValueError(f"Root provenance mismatch: {path}")
        sources[path.name] = data.decode("utf-8").splitlines()
    print(f";; Root source pin {SUITE_PIN}; final-rule oracle pin {SPEC_PIN}")
    print(";; Exactly 20 projections; original files/expectations remain untouched.")
    print(";; Categories: 5 old memory-count restrictions; 10 old reserved bytes;")
    print(";; separately, 5 final-invalid/old-malformed alignment/flag cases.")
    two_mems = memory_module(memories=(0, 0))
    command("memory.wast", 10, two_mems, "valid", "multiple definitions permitted")
    command("memory.wast", 11,
            memory_module(((b"spectest", b"memory", 0),), (0,)),
            "valid", "import+definition permitted; existing spectest import links")
    command("imports.wast", 487,
            memory_module(((b"", b"", 1), (b"", b"", 1))),
            "unlinkable", "two imports validate; missing imports fail only linking")
    command("imports.wast", 491,
            memory_module(((b"", b"", 1),), (0,)),
            "unlinkable", "import+definition validates; missing import fails linking")
    command("imports.wast", 495, two_mems, "valid", "multiple definitions permitted")
    for line in (125, 145, 165, 184, 203, 223, 242, 261, 279, 297):
        nonzero = line in (125, 223)
        command("binary.wast", line, original_binary(sources["binary.wast"], line),
                "invalid" if nonzero else "valid",
                "index 1 is decoded but absent" if nonzero
                else "padded zero is a legal u32 memory index")
    for line in (891, 910, 929, 948, 967):
        reason = ("alignment 32/33/63 exceeds the natural load alignment"
                  if line <= 929 else
                  "flag 40/41 selects memory 0; byte 1a is offset 26, not drop; "
                  "the empty-result function retains i32")
        command("align.wast", line, original_binary(sources["align.wast"], line),
                "invalid", reason)


if __name__ == "__main__":
    generate([Path(p) for p in sys.argv[1:]])
