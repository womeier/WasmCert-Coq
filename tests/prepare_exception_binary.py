#!/usr/bin/env python3
"""Externally encode ALL official final-EH binary-scope script commands.

This is test tooling, not a WasmCert text frontend. Only quoted-text malformed
assertions are deferred, with exact source spans. All other commands, including
unsupported commands, remain in the projection and must receive a verdict.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


def forms(text):
    """Balanced top-level forms; strings and nested comments are opaque."""
    stack, spans, i = [], [], 0
    while i < len(text):
        if text.startswith(";;", i):
            newline = text.find("\n", i)
            i = len(text) if newline == -1 else newline + 1
        elif text.startswith("(;", i):
            depth = 1
            i += 2
            while depth:
                if i == len(text):
                    raise ValueError("unterminated block comment")
                if text.startswith("(;", i):
                    depth += 1
                    i += 2
                elif text.startswith(";)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= len(text):
                raise ValueError("unterminated string")
            i += 1
        elif text[i] == "(":
            stack.append(i)
            i += 1
        elif text[i] == ")":
            if not stack:
                raise ValueError("unmatched closing parenthesis")
            start = stack.pop()
            i += 1
            if not stack:
                spans.append((start, i))
        else:
            i += 1
    if stack:
        raise ValueError("unbalanced script")
    return spans


def prepare(suite, output, tool):
    suite, output = suite.resolve(), output.resolve()
    sources = sorted((suite / "proposals" / "exception-handling").glob("*.wast"))
    if len(sources) != 8:
        raise ValueError(f"expected all eight pinned final-EH files, got {len(sources)}")
    if output == suite or suite in output.parents:
        raise ValueError("output must not be in the source testsuite")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("output must be empty")
    version = subprocess.check_output([tool, "--version"], text=True).strip()
    revision = subprocess.check_output(
        ["git", "-C", str(suite), "rev-parse", "HEAD"], text=True).strip()
    tool_path = Path(shutil.which(tool) or tool).resolve()
    manifest = {"testsuite": revision, "encoder": version,
                "encoder_path": str(tool_path),
                "encoder_sha256": hashlib.sha256(tool_path.read_bytes()).hexdigest(),
                "files": []}
    for source in sources:
        directory = output / source.stem
        directory.mkdir()
        raw = directory / "encoder.json"
        subprocess.run([tool, "json-from-wast", str(source), "--wasm-dir",
                        str(directory), "-o", str(raw)], check=True)
        document = json.loads(raw.read_text())
        text = source.read_text()
        spans = forms(text)
        commands = document["commands"]
        if len(commands) != len(spans):
            raise ValueError(f"{source}: encoder/source command count mismatch")
        retained, deferred, mapping = [], [], []
        for ordinal, (command, (start, end)) in enumerate(zip(commands, spans), 1):
            line = text.count("\n", 0, start) + 1
            end_line = text.count("\n", 0, end) + 1
            # The encoder locates negative module assertions at the inner
            # module, whereas action assertions are located at the wrapper.
            if not line <= command["line"] <= end_line:
                raise ValueError(f"{source}:{line}: encoder/source span mismatch")
            head = re.match(r"\(\s*([^\s()]+)", text[start:end])
            expected = command["type"]
            if head is None or (head[1] != expected and
                                not (expected == "action" and head[1] in ("invoke", "get"))):
                raise ValueError(f"{source}:{line}: encoder/source command kind mismatch")
            provenance = {
                "ordinal": ordinal, "line": line,
                "end_line": end_line, "encoder_line": command["line"],
                "start_byte": len(text[:start].encode()),
                "end_byte": len(text[:end].encode()),
                "sha256": hashlib.sha256(text[start:end].encode()).hexdigest(),
                "type": command["type"],
            }
            if command.get("module_type") == "text":
                if command["type"] != "assert_malformed":
                    raise ValueError(f"non-malformed text command: {command}")
                provenance["reason"] = "deferred text-only malformed module"
                deferred.append(provenance)
                continue
            if "filename" in command:
                if command.get("module_type", "binary") != "binary":
                    raise ValueError(f"unhandled module representation: {command}")
                binary = directory / command["filename"]
                provenance["binary_sha256"] = hashlib.sha256(binary.read_bytes()).hexdigest()
            command["provenance"] = provenance
            retained.append(command)
            mapping.append(provenance)
        (directory / "projection.json").write_text(json.dumps({
            "source": str(source), "commands": retained}, indent=2) + "\n")
        manifest["files"].append({
            "source": str(source),
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "source_commands": len(commands), "binary_scope_commands": len(retained),
            "deferred_text_only_malformed": deferred, "mapping": mapping,
            "projection": str(directory / "projection.json"),
        })
        print(f"{source.name}: retained {len(retained)}/{len(commands)} commands; "
              f"deferred text-only malformed: {[x['line'] for x in deferred]}")
    (output / "provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", type=Path, default=Path("wast_testsuite"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--wasm-tools", default="wasm-tools")
    args = parser.parse_args()
    prepare(args.suite, args.output, args.wasm_tools)
