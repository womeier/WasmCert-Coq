"""Strict, currently failing closed-reference handoff regressions.

These are NOT expected-failure tests: valid modules must validate and linked
scripts must produce their specified results. Run explicitly with the
closed-reference-handoff dune alias. The unchanged official table suite also
keeps the root failures enabled in its original counts.
"""
import argparse
import pathlib
import re
import subprocess
import tempfile


def u32(value):
    result = bytearray()
    while value >= 128:
        result.append((value & 127) | 128)
        value >>= 7
    result.append(value)
    return bytes(result)


def vector(items):
    return u32(len(items)) + b"".join(items)


def section(tag, payload):
    return bytes([tag]) + u32(len(payload)) + payload


def name(value):
    value = value.encode("ascii")
    return u32(len(value)) + value


def module(types, *, functions=(), tables=(), globals=(), imports=(), exports=()):
    result = bytes.fromhex("0061736d01000000") + section(1, vector(types))
    if imports:
        result += section(2, vector(imports))
    if functions:
        result += section(3, vector([u32(index) for index, _ in functions]))
    if tables:
        result += section(4, vector(tables))
    if globals:
        result += section(6, vector(globals))
    if exports:
        result += section(7, vector([name(n) + bytes([kind]) + u32(i)
                                    for n, kind, i in exports]))
    if functions:
        bodies = [b"\x00" + body + b"\x0b" for _, body in functions]
        result += section(10, vector([u32(len(body)) + body for body in bodies]))
    return result


VOID = bytes.fromhex("600000")
GET = bytes.fromhex("60000170")
RESULT_I32 = bytes.fromhex("6000017f")
IMPORTED_GLOBAL = name("M") + name("g") + bytes.fromhex("03640000")


def table(reference, width=32, initializer=None):
    descriptor = reference + bytes([4 if width == 64 else 0, 1])
    return descriptor if initializer is None else b"\x40\x00" + descriptor + initializer + b"\x0b"


def binary(data, definition=False):
    escaped = "".join(f"\\{byte:02x}" for byte in data)
    return f'(module {"definition " if definition else ""}binary "{escaped}")'


def provider(reference=bytes.fromhex("6400"), types=(VOID,)):
    return module(types, functions=[(0, b"")],
                  globals=[reference + bytes.fromhex("00d2000b")],
                  exports=[("g", 3, 0)])


def reduced_cases():
    cases = []

    def definition(label, data, valid=True):
        cases.append((label, binary(data, True), 1 if valid else 0, 1))

    definition("provider_indexed_ref_func_global", provider())
    definition("provider_abstract_ref_func_global_control", provider(bytes.fromhex("6470")))
    definition("provider_source_alias_same_closed_signature",
               provider(bytes.fromhex("6401"), (VOID, VOID)))
    definition("provider_wrong_closed_signature_rejected",
               provider(bytes.fromhex("6401"), (VOID, RESULT_I32)), False)
    for width in (32, 64):
        definition(f"table{width}_indexed_ref_func",
                   module([VOID], functions=[(0, b"")],
                          tables=[table(bytes.fromhex("6400"), width, bytes.fromhex("d200"))]))
        definition(f"table{width}_abstract_ref_func_control",
                   module([VOID], functions=[(0, b"")],
                          tables=[table(bytes.fromhex("6470"), width, bytes.fromhex("d200"))]))
        for reference, label in [(bytes.fromhex("6400"), "exact_indexed"),
                                 (bytes.fromhex("70"), "abstract_supertype")]:
            definition(f"table{width}_imported_global_to_{label}",
                       module([VOID], imports=[IMPORTED_GLOBAL],
                              tables=[table(reference, width, bytes.fromhex("2300"))]))
        for reference, label in [(bytes.fromhex("6300"), "indexed"),
                                 (bytes.fromhex("70"), "abstract_control")]:
            index = bytes.fromhex("4200" if width == 64 else "4100")
            definition(f"table{width}_{label}_getter_as_funcref",
                       module([VOID, GET], functions=[(1, index + bytes.fromhex("2500"))],
                              tables=[table(reference, width)]))

    # Faithful reduction of original table.wast #47--54 (eight commands).
    tables = [table(bytes.fromhex("70")),
              table(bytes.fromhex("70"), initializer=bytes.fromhex("d200")),
              table(bytes.fromhex("6400"), initializer=bytes.fromhex("d200")),
              table(bytes.fromhex("70"), initializer=bytes.fromhex("2300")),
              table(bytes.fromhex("6400"), initializer=bytes.fromhex("2300"))]
    consumer = module([VOID, GET], imports=[IMPORTED_GLOBAL],
                      functions=[(0, b"")] + [(1, b"\x41\x00\x25" + u32(i)) for i in range(5)],
                      tables=tables, exports=[(f"get{i+1}", 0, i+1) for i in range(5)])
    script = [binary(provider()), '(register "M")', binary(consumer)]
    script += [f'(assert_return (invoke "get{i+1}") ({kind}))'
               for i, kind in enumerate(["ref.null"] + ["ref.func"] * 4)]
    cases.append(("official_initializer_dependency_chain", "\n".join(script), 8, 8))

    # Same closed producer signature at a different consumer source index.
    imported_alias = name("M") + name("g") + bytes.fromhex("03640100")
    alias = module([bytes.fromhex("5f00"), VOID, GET], imports=[imported_alias],
                   functions=[(2, bytes.fromhex("42002500"))],
                   tables=[table(bytes.fromhex("6401"), 64, bytes.fromhex("2300"))],
                   exports=[("get", 0, 0)])
    cases.append(("canonical_global_import_reindexed_positive",
                  "\n".join([binary(provider()), '(register "M")', binary(alias),
                             '(assert_return (invoke "get") (ref.func))']), 4, 4))

    incompatible = module([RESULT_I32], imports=[IMPORTED_GLOBAL])
    cases.append(("canonical_global_import_same_raw_index_negative",
                  "\n".join([binary(provider()), '(register "M")',
                             f'(assert_unlinkable {binary(incompatible)} "incompatible import type")']),
                  3, 3))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("interpreter")
    parser.add_argument("--emit", type=pathlib.Path,
                        help="retain scripts and a phase/result report here")
    args = parser.parse_args()
    executable = str(pathlib.Path(args.interpreter).resolve())
    failures = 0
    with tempfile.TemporaryDirectory(prefix="closed-reference-") as temporary:
        output = args.emit or pathlib.Path(temporary)
        output.mkdir(parents=True, exist_ok=True)
        report = []
        for label, script, passed, total in reduced_cases():
            path = output / (label + ".wast")
            path.write_text(script + "\n")
            result = subprocess.run([executable, "--stage", "--wast", str(path)],
                                    capture_output=True, text=True)
            text = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
            if args.emit:
                (output / (label + ".log")).write_text(text)
            summaries = re.findall(r"Result: (\d+)/(\d+)", text)
            correct = result.returncode == 0 and summaries == [(str(passed), str(total))]
            # All fixtures have valid source syntax, including the negative
            # type/link cases. A parser failure must not masquerade as invalid.
            correct = correct and "error in parsing module" not in text
            failures += not correct
            report.append(f'{"PASS" if correct else "FAIL"} {label}: '
                          f'expected {passed}/{total}; actual {summaries}')
        print("\n".join(report))
        print(f"Closed-reference handoff: {len(report)-failures}/{len(report)} "
              "(strict expected semantics, not xfails)")
        if args.emit:
            (output / "report.txt").write_text("\n".join(report) + "\n")
    return int(failures != 0)


if __name__ == "__main__":
    raise SystemExit(main())
