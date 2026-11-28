#!/usr/bin/env python3
"""Prepare binary-only conformance inputs using wasm-tools json-from-wast.

Test tooling, not an interpreter text frontend. Assertions/actions are copied
verbatim; only module forms are replaced by externally encoded bytes. Text-only
malformed assertions are reported separately, never counted as passes.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


def forms(source):
    """Return parenthesized spans, ignoring strings and nested comments."""
    token = re.compile(r';;[^\n]*|\(;|;\)|"(?:\\.|[^"\\])*"|[()]', re.S)
    stack, spans, comment = [], [], 0
    for match in token.finditer(source):
        word = match.group()
        if word == "(;":
            comment += 1
        elif word == ";)" and comment:
            comment -= 1
        elif not comment:
            if word == "(":
                stack.append(match.start())
            elif word == ")":
                start = stack.pop()
                spans.append((start, match.end(), len(stack)))
    if stack or comment:
        raise ValueError("unbalanced input")
    return sorted(spans)


def convert(tool, source, destination):
    text = source.read_text()
    spans = forms(text)
    top = [(a, b) for a, b, depth in spans if depth == 0]
    with tempfile.TemporaryDirectory(
        prefix="wasmcert-binary-projection-", dir="/tmp/opencode"
    ) as directory:
        directory = Path(directory)
        manifest = directory / "suite.json"
        subprocess.run(
            [tool, "json-from-wast", str(source), "--wasm-dir", str(directory),
             "-o", str(manifest)], check=True
        )
        commands = json.loads(manifest.read_text())["commands"]
        if len(commands) != len(top):
            raise ValueError("JSON/source command count mismatch")
        output, binary, text_only, mapping = [], 0, [], []
        for ordinal, (command, (a, b)) in enumerate(zip(commands, top), 1):
            original = text[a:b]
            entry = {
                "source_command": ordinal,
                "source_line": text.count("\n", 0, a) + 1,
                "kind": command["type"],
                "source_sha256": hashlib.sha256(original.encode()).hexdigest(),
            }
            if "filename" not in command:
                output.append(original)
                entry["projection"] = "verbatim"
                entry["projected_command"] = len(output)
                entry["projected_sha256"] = entry["source_sha256"]
                mapping.append(entry)
                continue
            if command["module_type"] != "binary":
                if command["type"] != "assert_malformed":
                    raise ValueError(f"unsupported text command: {command}")
                text_only.append(command["line"])
                entry["projection"] = "deferred-text-only-malformed"
                entry["original_command"] = original
                mapping.append(entry)
                continue
            modules = [(x, y) for x, y, _ in spans if a <= x < y <= b
                       and re.match(r"\(module(?:\s|\))", text[x:y])]
            if len(modules) != 1:
                raise ValueError("expected exactly one module per command")
            x, y = modules[0]
            name = re.match(r"\(module\s+(\$[^\s()]+)", text[x:y])
            identifier = name[1] + " " if name else ""
            data = (directory / command["filename"]).read_bytes()
            encoded = "".join(f"\\{byte:02x}" for byte in data)
            module = f'(module {identifier}binary "{encoded}")'
            output.append(text[a:x] + module + text[y:b])
            entry["projection"] = "module-replaced-only"
            entry["projected_command"] = len(output)
            entry["projected_sha256"] = hashlib.sha256(output[-1].encode()).hexdigest()
            entry["module_sha256"] = hashlib.sha256(data).hexdigest()
            # Preserve the exact outer assertion/action and module variable;
            # no expectation, assertion kind, or later command is rewritten.
            entry["unchanged_prefix"] = text[a:x]
            entry["unchanged_suffix"] = text[y:b]
            mapping.append(entry)
            binary += 1
        if len(output) + len(text_only) != len(top):
            raise ValueError("a source command was lost")
        destination.write_text(
            f";; Binary projection of {source}\n"
            f";; Text-only malformed assertions excluded at lines: {text_only}\n"
            + "\n".join(output) + "\n"
        )
        print(f"{source}: {len(output)} binary-scope commands, {binary} modules; "
              f"{len(text_only)} text-only assertions outside scope at {text_only}")
        return {
            "source_commands": len(top),
            "binary_scope_commands": len(output),
            "encoded_modules": binary,
            "text_only_malformed_lines": text_only,
            "command_map": mapping,
        }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wasm-tools", default="wasm-tools")
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    convert(args.wasm_tools, args.source, args.destination)
