"""Encode WAST modules externally, preserving every command and assertion.

Use a memory64-capable wasmtime.wat2wasm as the text-to-binary frontend. The
result tests WasmCert's own binary parser/validator/runtime, not Wasmtime's.
Quoted/binary modules and instance directives are retained verbatim. Modern
definition directives are retained too: an unsupported harness must fail,
not silently instantiate or discard them.
"""

import argparse
from pathlib import Path


def tokens(source):
    i = 0
    while i < len(source):
        start = i
        if source[i].isspace():
            i += 1
        elif source.startswith(";;", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end + 1
        elif source.startswith("(;", i):
            depth = 1
            i += 2
            while depth:
                if i == len(source):
                    raise ValueError("unterminated block comment")
                if source.startswith("(;", i):
                    depth += 1
                    i += 2
                elif source.startswith(";)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif source[i] in "()":
            i += 1
            yield source[start:i], start, i
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            if i >= len(source):
                raise ValueError("unterminated string")
            i += 1
            yield source[start:i], start, i
        else:
            while i < len(source) and not source[i].isspace() and source[i] not in "()":
                i += 1
            yield source[start:i], start, i


def convert(source, encode):
    ts = list(tokens(source))
    replacements = []
    i = 0
    while i + 1 < len(ts):
        if ts[i][0] != "(" or ts[i + 1][0] != "module":
            i += 1
            continue
        start = i
        depth = 1
        i += 2
        while i < len(ts) and depth:
            depth += (ts[i][0] == "(") - (ts[i][0] == ")")
            i += 1
        if depth:
            raise ValueError("unterminated module")
        end = i - 1
        header = start + 2
        definition = ts[header][0] == "definition"
        if definition:
            header += 1
        identifier = ""
        if ts[header][0].startswith("$"):
            identifier = ts[header][0] + " "
            header += 1
        if ts[header][0] in ("quote", "binary", "instance"):
            continue
        wat = "(module " + source[ts[header][1]:ts[end][2]]
        binary = encode(wat)
        escaped = "".join(f"\\{b:02x}" for b in binary)
        keyword = "definition " if definition else ""
        replacements.append((ts[start][1], ts[end][2],
                             f'(module {keyword}{identifier}binary "{escaped}")'))
    for start, end, replacement in reversed(replacements):
        source = source[:start] + replacement + source[end:]
    return source, len(replacements)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    # Missing compiler dependencies and encoding errors are hard failures.
    import wasmtime
    result, count = convert(args.input.read_text(), wasmtime.wat2wasm)
    args.output.write_text(result)
    print(f"{args.input}: encoded {count} modules; all WAST commands retained")


if __name__ == "__main__":
    main()
