"""Small regression tests for the preflight scanner, not proof verification."""

import unittest

from check_sources import code_only, require


class PreflightTests(unittest.TestCase):
    def test_nested_comments(self):
        self.assertEqual(code_only('a /- x /- y -/ z -/ b').split(), ['a', 'b'])

    def test_line_comment_at_end(self):
        self.assertEqual(code_only('x -- final comment'), 'x ')

    def test_string_escape(self):
        self.assertEqual(code_only('x "a\\\"sorry" y').split(), ['x', 'y'])

    def test_real_token_is_retained(self):
        self.assertIn('sorry', code_only('by /- text -/ sorry'))

    def test_unclosed_comment_fails(self):
        with self.assertRaises(SystemExit):
            code_only('/- unfinished')

    def test_failed_precondition_exits(self):
        with self.assertRaises(SystemExit):
            require(False, 'bad configuration')


if __name__ == '__main__':
    unittest.main()
