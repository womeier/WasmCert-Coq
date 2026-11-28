import unittest

from wast_to_binary import convert


class ConversionTests(unittest.TestCase):
    def encode(self, wat):
        self.assertEqual(wat, "(module (memory i64 1))")
        return b"\x00asm"

    def test_assertion_and_identifier_retained(self):
        source = '(assert_invalid (module $m (memory i64 1)) "reason")'
        output, count = convert(source, self.encode)
        self.assertEqual(count, 1)
        self.assertEqual(output,
                         '(assert_invalid (module $m binary "\\00\\61\\73\\6d") "reason")')

    def test_comments_and_strings_are_not_modules(self):
        source = ';; (module)\n(; (; (module) ;) ;)\n(register "(module)")'
        self.assertEqual(convert(source, self.encode), (source, 0))

    def test_quoted_and_binary_modules_unchanged(self):
        source = '(module quote "(module)")\n(module binary "\\00")'
        self.assertEqual(convert(source, self.encode), (source, 0))

    def test_definition_not_silently_instantiated(self):
        output, count = convert('(module definition $m (memory i64 1))', self.encode)
        self.assertEqual(count, 1)
        self.assertTrue(output.startswith('(module definition $m binary '))

    def test_encoder_errors_propagate(self):
        def fail(_):
            raise ValueError("encoding failed")
        with self.assertRaisesRegex(ValueError, "encoding failed"):
            convert('(module)', fail)


if __name__ == "__main__":
    unittest.main()
