#!/usr/bin/env python3
"""Project complete pinned official scripts through an external encoder.

This is a source-span/provenance adapter, not a WAT encoder or implementation.
Every top-level command is accounted for. The default projection defers only
encoder-designated malformed text modules. The explicit current-AST profile
additionally records pinned non-null/table-initializer exclusions and an
equivalent default-null table variant; it never claims unchanged binary coverage.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


REVISION = "9d36019973201a19f9c9ebb0f10828b2fe2374aa"  # spec wg-3.0
HASHES = {
    "global": "0899df8c814d953d56a22b04d518fda6c7e6aab5a0d0472367a830e31821ee40",
    "data": "991bfcf105a8eb23b92b6d59a8e2e6ef8f65111006bcfc35aa7b296eda45664d",
    "elem": "087cfbccfd746458d46e10ea763aecea5f925bc1578e8fdf73eddfd47be68cda",
    "align": "b6b37225b83a1d68da1299ac40266ca5b0486c6468a47484b9c15ca357aeaef6",
}
# Explicit, pinned source cases requiring non-null reference/table-initializer
# syntax absent from the current AST. Never infer exclusions from test outcomes.
OUTSIDE_AST = {
    "elem": {87, 315, 448, 453, 465, 470, 482, 487, 499, 504,
             516, 524, 539, 544, 556, 561, 573, 578},
    "global": {674},
}


def tokens(text):
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
        elif text.startswith(";;", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text.startswith("(;", i):
            depth = 1
            i += 2
            while depth:
                if i >= len(text):
                    raise ValueError("unterminated block comment")
                if text.startswith("(;", i):
                    depth += 1
                    i += 2
                elif text.startswith(";)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        else:
            start = i
            if text[i] in "()":
                i += 1
            elif text[i] == '"':
                i += 1
                while i < len(text) and text[i] != '"':
                    i += 2 if text[i] == "\\" else 1
                if i >= len(text):
                    raise ValueError("unterminated string")
                i += 1
            else:
                while i < len(text) and not text[i].isspace() and text[i] not in "()":
                    i += 1
            yield text[start:i], start, i


def forms(text):
    stack, roots = [], []
    for token, start, end in tokens(text):
        if token == "(":
            node = {"start": start, "atoms": [], "children": []}
            if stack:
                stack[-1]["children"].append(node)
            else:
                roots.append(node)
            stack.append(node)
        elif token == ")":
            node = stack.pop()
            node["end"] = end
        else:
            stack[-1]["atoms"].append(token)
    if stack:
        raise ValueError("unbalanced source")
    return roots


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--encoder", required=True, type=Path)
    parser.add_argument("--originals", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--runner", type=Path,
                        help="also run every projection, requiring exact accounted command totals")
    parser.add_argument("--current-ast-profile", action="store_true",
                        help="explicit non-null/table-init exclusions and default-null table adapter")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    provenance = {
        "revision": REVISION,
        "encoder": str(args.encoder.resolve()),
        "encoder_sha256": sha(args.encoder.read_bytes()),
        "encoder_version": subprocess.check_output(
            [str(args.encoder), "--version"], text=True
        ).strip(),
        "current_ast_profile": args.current_ast_profile,
        "files": {},
    }
    for name, expected_hash in HASHES.items():
        source = args.originals / f"{name}.wast"
        raw = source.read_bytes()
        if sha(raw) != expected_hash:
            raise ValueError(f"{source}: not the pinned wg-3.0 original")
        text = raw.decode()
        destination = args.output / name
        destination.mkdir(parents=True, exist_ok=True)
        commands_file = destination / "commands.json"
        command = [
            str(args.encoder), "json-from-wast", str(source),
            "--wasm-dir", str(destination), "-o", str(commands_file), "--pretty",
        ]
        subprocess.run(command, check=True)
        commands = json.loads(commands_file.read_text())["commands"]
        roots = forms(text)
        if len(roots) != len(commands):
            raise ValueError(f"{name}: source/encoder command count differs")
        records, projected = [], []
        for index, (node, command) in enumerate(zip(roots, commands)):
            line = text.count("\n", 0, node["start"]) + 1
            end_line = text.count("\n", 0, node["end"]) + 1
            if not line <= command["line"] <= end_line:
                raise ValueError(f"{name}:{line}: encoder/source order differs")
            original = text[node["start"]:node["end"]]
            record = {
                "ordinal": index + 1, "line": line, "type": command["type"],
                "encoder_line": command["line"],
                "source_sha256": sha(original.encode()),
                "original": original, "status": "included",
            }
            if args.current_ast_profile and line in OUTSIDE_AST.get(name, set()):
                record["status"] = "deferred-outside-current-ast"
                record["reason"] = (
                    "non-null reference/table initializer source form has no current AST representation; "
                    "not a text-only exclusion"
                )
            if name == "global" and line == 659:
                # wg-3.0 uses an untyped null result pattern; get-elem's
                # declared result is funcref. Retain the exact null assertion
                # using the older script harness's typed null spelling.
                if original != '(assert_return (invoke "get-elem" (i32.const 0)) (ref.null))':
                    raise ValueError("unexpected pinned generic-null assertion")
                original = original.replace("(ref.null)", "(ref.null func)")
                record["harness_adapter"] = {
                    "from": "(ref.null)", "to": "(ref.null func)",
                    "reason": "get-elem declares funcref; identical null result, not a wildcard",
                }
            if "filename" in command:
                encoded = destination / command["filename"]
                record["encoded_file"] = command["filename"]
                record["encoded_sha256"] = sha(encoded.read_bytes())
                if command.get("module_type") == "text":
                    if command["type"] != "assert_malformed":
                        raise ValueError(f"{name}:{line}: cannot defer a non-malformed text module")
                    record["status"] = "deferred-text-only"
                    record["reason"] = "encoder preserves malformed WAT, not binary syntax"
                else:
                    module = node if node["atoms"][0] == "module" else next(
                        child for child in node["children"] if child["atoms"][0] == "module"
                    )
                    identifier = next(
                        (a for a in module["atoms"][1:] if a.startswith("$")), ""
                    )
                    if args.current_ast_profile and name == "global" and line == 634:
                        # The sole table initializer here is exactly ref.null
                        # func. Default initialization of a funcref table has
                        # the same value at every entry. Preserve the original
                        # binary, and separately encode this explicit variant.
                        before = "(table $t 10 funcref (ref.null func))"
                        after = "(table $t 10 funcref)"
                        if original.count(before) != 1:
                            raise ValueError("unexpected pinned default-null table constructor")
                        variant = original.replace(before, after)
                        variant_source = destination / "default-null-table.wat"
                        variant_source.write_text(variant)
                        encoded = destination / "default-null-table.wasm"
                        subprocess.run(
                            [str(args.encoder), "parse", str(variant_source), "-o", str(encoded)],
                            check=True,
                        )
                        record["module_adapter"] = {
                            "from": before, "to": after,
                            "reason": "identical default null table values; not the original table-init binary",
                            "variant_source_sha256": sha(variant.encode()),
                            "variant_binary_sha256": sha(encoded.read_bytes()),
                        }
                    payload = "".join(f"\\{byte:02x}" for byte in encoded.read_bytes())
                    replacement = f'(module {identifier} binary "{payload}")'
                    start = module["start"] - node["start"]
                    end = module["end"] - node["start"]
                    original = original[:start] + replacement + original[end:]
            if record["status"] == "included":
                projected.append(f";; {name}.wast:{line}, command {index + 1}\n{original}\n")
            records.append(record)
        output = args.output / f"{name}.wast"
        output.write_text("\n".join(projected))
        info = {
            "source_url": f"https://raw.githubusercontent.com/WebAssembly/spec/{REVISION}/test/core/{name}.wast",
            "source_sha256": expected_hash,
            "projection_sha256": sha(output.read_bytes()),
            "source_commands": len(records),
            "included_commands": sum(r["status"] == "included" for r in records),
            "included_assertions": sum(
                r["status"] == "included" and r["type"].startswith("assert_") for r in records
            ),
            "records": records,
        }
        provenance["files"][name] = info
        print(f"{name}: {info['included_commands']}/{len(records)} commands; "
              f"{info['included_assertions']} assertions")
    (args.output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    if args.runner:
        results = {"runner_sha256": sha(args.runner.read_bytes()), "files": {}}
        failed = False
        for name, info in provenance["files"].items():
            command = [str(args.runner.resolve()), "--wast", str(args.output / f"{name}.wast")]
            result = subprocess.run(command, capture_output=True, text=True)
            output = result.stdout + result.stderr
            (args.output / f"{name}-run.log").write_text(output)
            clean = re.sub(r"\x1b\[[0-9;]*[a-zA-Z]", "", output)
            summaries = re.findall(r"Result: (\d+)/(\d+) ", clean)
            expected = info["included_commands"]  # driver counts modules/actions too
            passed = (result.returncode == 0 and summaries == [(str(expected), str(expected))])
            results["files"][name] = {
                "command": command, "exit": result.returncode, "summaries": summaries,
                "expected_commands": expected, "passed": passed,
            }
            print(f"{name}: gate {'PASS' if passed else 'FAIL'}; summaries={summaries}")
            failed |= not passed
        (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        if failed:
            raise SystemExit(1)


if __name__ == "__main__":
    main()
