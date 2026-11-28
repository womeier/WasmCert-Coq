"""Regressions for strict source mapping and the extracted binary-script driver.

No external encoder is required for these hand-built binary harness tests.
Official projections are separate, complete conformance runs, not golden failures.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

from prepare_exception_binary import forms, prepare


def u32(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    return bytes(out + bytes([n]))


def vec(xs):
    return u32(len(xs)) + b"".join(xs)


def sec(tag, payload):
    return bytes([tag]) + u32(len(payload)) + payload


def module(body, result=b"\x7f", imports=b"", tags=False):
    return (
        b"\0asm\x01\0\0\0"
        + sec(1, vec([b"\x60\0" + vec([result]) if result else b"\x60\0\0",
                      b"\x60\0\0"]))
        + (sec(2, imports) if imports else b"")
        + sec(3, b"\x01\0")
        + (sec(13, b"\x01\0\x01") if tags else b"")
        + sec(7, b"\x01\x04main\0" + bytes([bool(imports)]))
        + sec(10, vec([u32(len(body) + 2) + b"\0" + body + b"\x0b"]))
    )


def literal(n):
    return {"type": "i32", "value": str(n)}


def invoke(name=None):
    action = {"type": "invoke", "field": "main", "args": []}
    if name is not None:
        action["module"] = name
    return action


def assertion(kind, expected=None, name=None):
    result = {"type": kind, "action": invoke(name)}
    if expected is not None:
        result["expected"] = expected
    return result


def check_driver(exe, files, commands, passed, failures=()):
    with tempfile.TemporaryDirectory(prefix="eh-projection-regression-") as directory:
        directory = Path(directory)
        for name, data in files.items():
            (directory / name).write_bytes(data)
        for ordinal, command in enumerate(commands, 1):
            command["provenance"] = {"ordinal": ordinal, "line": ordinal}
        projection = directory / "projection.json"
        projection.write_text(json.dumps({"source": "harness-regression", "commands": commands}))
        process = subprocess.run([exe, str(projection)], capture_output=True,
                                 text=True, timeout=30)
        report = json.loads(process.stdout)
        assert report["total"] == len(commands), report
        assert report["passed"] == passed, report
        assert process.returncode == (0 if passed == len(commands) else 1), process
        errors = [c["error"] for c in report["commands"] if not c["passed"]]
        for expected in failures:
            assert any(expected in error for error in errors), (expected, errors)
        assert [c["provenance"]["ordinal"] for c in report["commands"]] == list(
            range(1, len(commands) + 1))


def load(filename, name=None):
    command = {"type": "module", "filename": filename, "module_type": "binary"}
    if name is not None:
        command["name"] = name
    return command


def check_preparer():
    with tempfile.TemporaryDirectory(prefix="eh-projection-source-") as directory:
        directory = Path(directory)
        suite = directory / "suite"
        sources = suite / "proposals" / "exception-handling"
        sources.mkdir(parents=True)
        text = ('(module)\n(assert_malformed (module quote "bad") "bad")\n'
                '(assert_invalid (module) "bad")\n(register "alias")\n')
        for i in range(8):
            (sources / f"{i}.wast").write_text(text)
        tool = directory / "fake-encoder"
        tool.write_text(
            "#!" + sys.executable + "\n"
            "import json,os,pathlib,sys\n"
            "if '--version' in sys.argv: print('fixture encoder'); sys.exit(0)\n"
            "directory=pathlib.Path(sys.argv[sys.argv.index('--wasm-dir')+1])\n"
            "for name in ['m.wasm','bad.wat','invalid.wasm']:\n"
            " (directory/name).write_bytes(b'fixture')\n"
            "commands=[{'type':'module','line':1,'filename':'m.wasm','module_type':'binary'},\n"
            " {'type':'assert_malformed','line':2,'filename':'bad.wat','module_type':'text'},\n"
            " {'type':'assert_invalid','line':3,'filename':'invalid.wasm','module_type':"
            " 'text' if os.getenv('EH_BAD_TEXT') else 'binary'},\n"
            " {'type':'register','line':4,'as':'alias'}]\n"
            "pathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_text("
            "json.dumps({'commands':commands}))\n"
        )
        tool.chmod(0o755)
        original = subprocess.check_output

        def output(args, **kwargs):
            return "fixture-suite-revision\n" if args[0] == "git" else original(args, **kwargs)

        with patch("prepare_exception_binary.subprocess.check_output", side_effect=output):
            manifest = prepare(suite, directory / "projection", str(tool))
            assert sum(e["source_commands"] for e in manifest["files"]) == 32
            assert sum(e["binary_scope_commands"] for e in manifest["files"]) == 24
            for entry in manifest["files"]:
                assert [c["ordinal"] for c in entry["mapping"]] == [1, 3, 4]
                assert [c["line"] for c in entry["deferred_text_only_malformed"]] == [2]
            with patch.dict("os.environ", {"EH_BAD_TEXT": "1"}):
                try:
                    prepare(suite, directory / "bad-projection", str(tool))
                except ValueError as error:
                    assert "non-malformed text command" in str(error)
                else:
                    raise AssertionError("silently deferred a binary-scope assertion")


def main(exe):
    text = ';; ignored (\n(; " ;; (; nested ;) ;) (module binary "\\00(;\\22")\n(register "x")'
    assert [text[a:b] for a, b in forms(text)] == [
        '(module binary "\\00(;\\22")', '(register "x")']
    for malformed in ('(', ')', '(; missing', '"missing'):
        try:
            forms(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted broken form framing: {malformed}")
    check_preparer()

    files = {
        "seven.wasm": module(b"\x41\x07"),
        "answer.wasm": module(b"\x41\x2a"),
        "throw.wasm": module(b"\x08\0", tags=True),
        "trap.wasm": module(b"\0"),
        "invalid.wasm": module(b""),
        "malformed.wasm": b"not wasm",
        "null.wasm": module(b"\xd0\x69", result=b"\x69"),
        "import.wasm": module(b"\x10\0", imports=b"\x01\x01a\x04main\0\0"),
        "unknown.wasm": module(b"\x10\0", imports=b"\x01\x06absent\x04main\0\0"),
    }
    positive = [
        load("seven.wasm", "A"), {"type": "register", "name": "A", "as": "a"},
        load("import.wasm", "B"), assertion("assert_return", [literal(7)], "A"),
        assertion("assert_return", [literal(7)]),
        {"type": "register", "name": "B", "as": "b"},
        load("answer.wasm"), {"type": "register", "name": "A", "as": "again"},
        assertion("assert_return", [literal(42)]),
        load("throw.wasm"), assertion("assert_exception"),
        load("trap.wasm"), assertion("assert_trap"),
        load("null.wasm"), assertion("assert_return", [{"type": "exnref", "value": "null"}]),
        {"type": "assert_invalid", "filename": "invalid.wasm"},
        {"type": "assert_malformed", "filename": "malformed.wasm"},
        {"type": "assert_unlinkable", "filename": "unknown.wasm"},
    ]
    check_driver(exe, files, positive, len(positive))
    negative = [
        load("throw.wasm"), assertion("assert_trap"),
        assertion("assert_return", [literal(7)]),
        load("trap.wasm"), assertion("assert_exception"),
        {"type": "assert_invalid", "filename": "malformed.wasm"},
        {"type": "assert_malformed", "filename": "invalid.wasm"},
        {"type": "assert_unlinkable", "filename": "invalid.wasm"},
        {"type": "assert_unlinkable", "filename": "malformed.wasm"},
        {"type": "assert_unlinkable", "filename": "seven.wasm"},
        {"type": "assert_malformed", "filename": "malformed.wasm", "module_type": "text"},
        {"type": "unsupported-command"},
        load("seven.wasm"), assertion("assert_return", [literal(42)]),
        assertion("assert_return", []),
        assertion("assert_return", [literal(7)]),  # Do not stop after failures.
    ]
    check_driver(exe, files, negative, 4,
                 ["assert_trap got exception", "assert_return got exception",
                  "assert_exception got trap", "before validation",
                  "malformed module unexpectedly parsed", "validation:",
                  "unlinkable module linked", "unsupported command",
                  "not a binary module",
                  "return values mismatch"])
    print(f"EH binary projection harness: {len(positive)} positive commands; "
          f"{len(negative) - 4} deliberate failures detected, continuation checked; framing 5/5")


if __name__ == "__main__":
    main(str(Path(sys.argv[1]).resolve()))
