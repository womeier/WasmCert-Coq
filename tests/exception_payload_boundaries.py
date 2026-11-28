#!/usr/bin/env python3
"""Real binary indexed-payload conformance probes, not golden failures.

Every command is retained and must pass for exit 0. The positive indexed cases
currently fail and remain reported failures pending shared runtime/parser
handoff. No quoted-text input, reference engine execution or semantic rewrites.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from exception_projection_tests import u32, vec, sec, load, assertion, literal

HEADER = b"\0asm\x01\0\0\0"
BASE = b"\x60\0\0"
DIFFERENT_BASE = b"\x60\0\x01\x7f"
DUMMY = b"\x60\0\x01\x7e"


def indexed_provider(emit=False):
    # Producer: referenced function type at 0, tag payload (ref null 0) at 1.
    result = HEADER + sec(1, vec([BASE, b"\x60\x01\x63\0\0"]))
    if emit:
        result += sec(3, b"\x01\x01")
    result += sec(13, b"\x01\0\x01")
    exports = [b"\x04main\x04\0"]
    if emit:
        exports.append(b"\x04emit\0\0")
    result += sec(7, vec(exports))
    if emit:
        # The source parameter has exactly the local tag's indexed type.
        code = b"\0\x20\0\x08\0\x0b"
        result += sec(10, vec([u32(len(code)) + code]))
    return result


def indexed_consumer(shift=True, different=False, transport=False):
    # Importer either moves the SAME referenced type to 1 or keeps a DIFFERENT
    # referenced type at 0. Tag identity is resolved through the actual registry.
    types = ([DUMMY, BASE] if shift else [DIFFERENT_BASE if different else BASE])
    referenced = 1 if shift else 0
    payload = b"\x63" + u32(referenced)
    tag_index = len(types)
    types.append(b"\x60\x01" + payload + b"\0")
    imports = [b"\x01p\x04main\x04\0" + u32(tag_index)]
    if transport:
        imports.append(b"\x01p\x04emit\0" + u32(tag_index))
        block_index = len(types)
        types.append(b"\x60\0\x01" + payload)
        main_index = len(types)
        types.append(b"\x60\0\x01\x7f")
    result = HEADER + sec(1, vec(types)) + sec(2, vec(imports))
    if transport:
        result += sec(3, b"\x01" + u32(main_index))
        result += sec(7, b"\x01\x04main\0\x01")
        # A nullable indexed local must be initialized in the producing
        # instance, lowered canonically, passed to the imported emitter and
        # returned by catching the imported tag in a DIFFERENT source map.
        code = (b"\x01\x01" + payload + b"\x02" + u32(block_index)
                + b"\x1f\x40\x01\0\0\0\x20\0\x10\0\x0b\0\x0b\xd1\x0b")
        result += sec(10, vec([u32(len(code)) + code]))
    else:
        result += sec(7, b"\x01\x04main\x04\0")
    return result


def prepare(output, tool=None):
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("output directory must be empty")
    cases = [
        ("same-canonical-different-indices", False,
         indexed_consumer(), "module", False,
         "Must link/re-export; producer referenced index 0, importer index 1."),
        ("different-canonical-same-index", False,
         indexed_consumer(shift=False, different=True), "assert_unlinkable", False,
         "Must parse/validate then reject nominal matching; both source indices are 0."),
        ("same-canonical-indexed-null-transport", True,
         indexed_consumer(transport=True), "module", True,
         "Must link and return i32 1 after canonical local-default lowering, call, throw and catch."),
    ]
    manifest = {"scope": "indexed EH payload boundaries", "cases": []}
    if tool:
        manifest["validator"] = subprocess.check_output([tool, "--version"], text=True).strip()
    for name, emit, consumer, kind, invoke, requirement in cases:
        directory = output / name
        directory.mkdir()
        files = {"producer.wasm": indexed_provider(emit), "consumer.wasm": consumer}
        hashes = {}
        for filename, binary in files.items():
            path = directory / filename
            path.write_bytes(binary)
            hashes[filename] = hashlib.sha256(binary).hexdigest()
            if tool:
                subprocess.run([tool, "validate", str(path)], check=True)
        commands = [load("producer.wasm", "P"),
                    {"type": "register", "name": "P", "as": "p"},
                    load("consumer.wasm") if kind == "module" else
                    {"type": kind, "filename": "consumer.wasm", "module_type": "binary"}]
        if invoke:
            commands.append(assertion("assert_return", [literal(1)]))
        for ordinal, command in enumerate(commands, 1):
            command["provenance"] = {"case": name, "ordinal": ordinal,
                                     "requirement": requirement}
        projection = directory / "projection.json"
        projection.write_text(json.dumps({"source": f"binary-boundary:{name}",
                                         "commands": commands}, indent=2) + "\n")
        manifest["cases"].append({
            "name": name, "requirement": requirement, "hashes": hashes,
            "producer_referenced_source_index": 0,
            "importer_referenced_source_index": 0 if "different-canonical" in name else 1,
            "expected_canonical_equivalent": kind != "assert_unlinkable",
            "expected_consumer_stage": "import matching" if kind == "assert_unlinkable"
                else "successful instantiation and execution" if invoke else "successful instantiation",
            "projection": str(projection.resolve()), "commands": len(commands),
        })
    (output / "provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def run(output, exe):
    manifest = json.loads((output / "provenance.json").read_text())
    passed = total = errors = 0
    for case in manifest["cases"]:
        path = Path(case["projection"])
        process = None
        try:
            for filename, digest in case["hashes"].items():
                if hashlib.sha256((path.parent / filename).read_bytes()).hexdigest() != digest:
                    raise ValueError("fixture binary changed since generation")
            process = subprocess.run([str(exe), str(path)], capture_output=True,
                                     text=True, timeout=120)
            report = json.loads(process.stdout)
            expected = json.loads(path.read_text())["commands"]
            if (report["total"] != case["commands"] or
                    [c["provenance"] for c in report["commands"]] !=
                    [c["provenance"] for c in expected] or
                    report["passed"] != sum(c["passed"] for c in report["commands"]) or
                    process.returncode != (0 if report["passed"] == report["total"] else 1)):
                raise ValueError("result accounting mismatch")
            (path.parent / "results.json").write_text(json.dumps(report, indent=2) + "\n")
            passed += report["passed"]
            total += report["total"]
            print(f"{case['name']}: {report['passed']}/{report['total']}")
            for command in report["commands"]:
                if not command["passed"] or command.get("tag_import_diagnostics"):
                    print(json.dumps(command))
        except (ValueError, KeyError, OSError, subprocess.TimeoutExpired) as error:
            errors += 1
            print(f"{case['name']}: infrastructure failure: {error}; "
                  f"{process.stderr if process else ''}")
    summary = {"passed": passed, "total": total,
               "required": sum(c["commands"] for c in manifest["cases"]),
               "infrastructure_errors": errors}
    (output / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))
    return errors == 0 and passed == summary["required"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--wasm-tools")
    parser.add_argument("--executable", type=Path,
                        default=Path("_build/default/tests/eh_script/eh_script.exe"))
    parser.add_argument("--run-existing", action="store_true")
    args = parser.parse_args()
    if not args.run_existing:
        prepare(args.output.resolve(), args.wasm_tools)
    raise SystemExit(0 if run(args.output.resolve(), args.executable.resolve()) else 1)
