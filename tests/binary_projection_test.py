"""Projection bookkeeping must not silently drop or rewrite assertions."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from binary_wast import convert, forms


class ProjectionTests(unittest.TestCase):
    def test_command_mapping_and_explicit_text_deferral(self):
        source = """;; ignored ( parentheses
(module $named (func)) (; nested (; comment ;) ;)
(register "alias" $named)
(assert_invalid (module (func (result i32))) "unchanged invalid")
(assert_malformed (module quote "(broken") "text only")
(assert_malformed (module binary "\\\\ff") "unchanged malformed")
(assert_return (invoke $named "f") (i32.const 42))
"""
        commands = [
            {"type": "module", "filename": "m0.wasm", "module_type": "binary"},
            {"type": "register"},
            {"type": "assert_invalid", "filename": "m1.wasm", "module_type": "binary"},
            {"type": "assert_malformed", "filename": "m2.wat", "module_type": "text", "line": 5},
            {"type": "assert_malformed", "filename": "m3.wasm", "module_type": "binary"},
            {"type": "assert_return"},
        ]

        def encode(args, check):
            self.assertTrue(check)
            directory = Path(args[args.index("--wasm-dir") + 1])
            Path(args[args.index("-o") + 1]).write_text(json.dumps({"commands": commands}))
            for name in ("m0.wasm", "m1.wasm", "m3.wasm"):
                (directory / name).write_bytes(b"\x00asm")

        with tempfile.TemporaryDirectory(dir="/tmp/opencode") as tmp:
            src, dst = Path(tmp) / "source.wast", Path(tmp) / "binary.wast"
            src.write_text(source)
            with patch("binary_wast.subprocess.run", side_effect=encode):
                result = convert("fixture-encoder", src, dst)
            self.assertEqual(result["source_commands"], 6)
            self.assertEqual(result["binary_scope_commands"], 5)
            self.assertEqual(result["encoded_modules"], 3)
            self.assertEqual(result["text_only_malformed_lines"], [5])
            output = dst.read_text()
            projected = [output[a:b] for a, b, depth in forms(output) if depth == 0]
            self.assertEqual(len(projected), 5)
            for entry in result["command_map"]:
                if entry["projection"] == "deferred-text-only-malformed":
                    self.assertIn('quote "(broken"', entry["original_command"])
                    self.assertNotIn("projected_command", entry)
                    continue
                command = projected[entry["projected_command"] - 1]
                self.assertEqual(hashlib.sha256(command.encode()).hexdigest(),
                                 entry["projected_sha256"])
                if entry["projection"] == "verbatim":
                    self.assertEqual(entry["source_sha256"], entry["projected_sha256"])
                else:
                    self.assertTrue(command.startswith(entry["unchanged_prefix"]))
                    self.assertTrue(command.endswith(entry["unchanged_suffix"]))
            self.assertIn('(module $named binary ', projected[0])
            self.assertIn('"unchanged invalid"', projected[2])
            self.assertIn('"unchanged malformed"', projected[3])

    def test_non_malformed_text_commands_are_rejected(self):
        with tempfile.TemporaryDirectory(dir="/tmp/opencode") as tmp:
            src, dst = Path(tmp) / "source.wast", Path(tmp) / "binary.wast"
            src.write_text('(module quote "(module)")')

            def encode(args, check):
                Path(args[args.index("-o") + 1]).write_text(json.dumps({"commands": [
                    {"type": "module", "module_type": "text", "filename": "m.wat"}
                ]}))

            with patch("binary_wast.subprocess.run", side_effect=encode):
                with self.assertRaisesRegex(ValueError, "unsupported text command"):
                    convert("fixture-encoder", src, dst)
            self.assertFalse(dst.exists())

    def test_command_count_mismatch_is_rejected(self):
        with tempfile.TemporaryDirectory(dir="/tmp/opencode") as tmp:
            src, dst = Path(tmp) / "source.wast", Path(tmp) / "binary.wast"
            src.write_text('(module) (register "keep")')

            def encode(args, check):
                Path(args[args.index("-o") + 1]).write_text('{"commands":[]}')

            with patch("binary_wast.subprocess.run", side_effect=encode):
                with self.assertRaisesRegex(ValueError, "command count mismatch"):
                    convert("fixture-encoder", src, dst)
            self.assertFalse(dst.exists())


if __name__ == "__main__":
    unittest.main()
