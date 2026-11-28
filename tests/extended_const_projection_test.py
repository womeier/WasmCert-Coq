#!/usr/bin/env python3
"""Source-span adapter regressions; no WebAssembly semantics are implemented."""
import unittest

from extended_const_official_projection import forms, tokens


class SourceSpans(unittest.TestCase):
    def test_nested_comments_strings_and_identifiers(self):
        source = ';; leading\n(module $m (; outer (; nested ;) ;) (data "(;) \\""))\n'
        roots = forms(source)
        self.assertEqual(len(roots), 1)
        self.assertEqual(roots[0]["atoms"], ["module", "$m"])
        self.assertEqual(roots[0]["children"][0]["atoms"], ["data", '"(;) \\""'])
        self.assertEqual(source[roots[0]["start"]:roots[0]["end"]][-1], ")")

    def test_module_assertion_preserves_outer_span(self):
        source = '(assert_invalid\n (module (func)) "message")\n(register "x" $m)'
        roots = forms(source)
        self.assertEqual(len(roots), 2)
        module = roots[0]["children"][0]
        projected = (source[roots[0]["start"]:module["start"]] +
                     '(module binary "\\00asm")' +
                     source[module["end"]:roots[0]["end"]])
        self.assertEqual(projected, '(assert_invalid\n (module binary "\\00asm") "message")')
        self.assertEqual(roots[1]["atoms"], ["register", '"x"', "$m"])

    def test_unterminated_input_is_not_silently_dropped(self):
        for source in ['(module', '(; unclosed', '(module "unterminated']:
            with self.assertRaises(ValueError):
                forms(source)

    def test_comment_tokens_are_not_commands(self):
        self.assertEqual(list(tokens(';; (module)\n(; (assert_invalid) ;)')), [])


if __name__ == "__main__":
    unittest.main()
