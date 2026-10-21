"""Decimal metadata retains exact source values before Real lowering is enabled."""

import ast
import copy
import unittest
from unittest.mock import patch

from algo2lean.frontend import CompileError
from algo2lean import real_literals
from algo2lean.real_literals import RealLiteralError, parse_real_literal, real_literal_ratio
from algo2lean.source_validation import parse_source


def literals(source):
    return [node for node in ast.walk(parse_source(source))
            if isinstance(node, ast.Constant) and type(node.value) is float]


class ExactRealLiteralTests(unittest.TestCase):
    def test_decimal_scientific_and_underscore_spellings_are_exact(self):
        cases = {"0.1": (1, 10), ".5": (1, 2), "1.": (1, 1), "1e3": (1000, 1),
                 "1E-3": (1, 1000), "12_3.4_5e+0_2": (12345, 1), "0.e1000": (0, 1),
                 "0.123456789012345678901": (123456789012345678901, 10 ** 21)}
        for token, ratio in cases.items():
            with self.subTest(token=token):
                self.assertEqual(parse_real_literal(token), ratio)
                self.assertEqual(real_literal_ratio(literals("value = " + token + "\n")[0]), ratio)

    def test_python_float_overflow_and_underflow_do_not_change_exact_values(self):
        large, small = literals("large = 1e309\nsmall = 1e-1000\n")
        self.assertEqual(large.value, float("inf"))
        self.assertEqual(small.value, 0.0)
        self.assertEqual(real_literal_ratio(large), (10 ** 309, 1))
        self.assertEqual(real_literal_ratio(small), (1, 10 ** 1000))

    def test_unary_signs_remain_expression_nodes(self):
        tree = parse_source("negative = -1.25\npositive = +.5\n")
        self.assertIsInstance(tree.body[0].value.op, ast.USub)
        self.assertIsInstance(tree.body[1].value.op, ast.UAdd)
        self.assertEqual(real_literal_ratio(tree.body[0].value.operand), (5, 4))
        self.assertEqual(real_literal_ratio(tree.body[1].value.operand), (1, 2))

    def test_utf8_columns_and_crlf_lines_recover_the_correct_tokens(self):
        nodes = literals('note = "é 🌱"; first = 0.1\r\nsecond = 3.25e-1\r\n')
        self.assertEqual([real_literal_ratio(node) for node in nodes], [(1, 10), (13, 40)])

    def test_metadata_survives_ast_copying(self):
        original = literals("value = 0.1\n")[0]
        self.assertEqual(real_literal_ratio(copy.deepcopy(original)), (1, 10))

    def test_source_spelling_is_required_instead_of_rounded_ast_values(self):
        for node in (ast.parse("0.1", mode="eval").body, ast.Constant(value=float("inf"))):
            with self.subTest(value=node.value), self.assertRaisesRegex(RealLiteralError, "original source text"):
                real_literal_ratio(node)

    def test_token_character_and_exponent_bounds(self):
        self.assertEqual(parse_real_literal("1." + "0" * 1022), (1, 1))
        self.assertEqual(parse_real_literal("1e1024"), (10 ** 1024, 1))
        self.assertEqual(parse_real_literal("1e-1024"), (1, 10 ** 1024))
        for token, expected in (("1." + "0" * 1023, "1024 character"),
                                ("1e1025", "exponent magnitude"),
                                ("1e-1025", "exponent magnitude"),
                                ("1e" + "9" * 1000, "exponent magnitude")):
            with self.subTest(token=token[:24]), self.assertRaisesRegex(RealLiteralError, expected):
                parse_real_literal(token)

    def test_expansion_bound_is_applied_before_constructing_large_values(self):
        with patch.object(real_literals, "MAX_EXPANDED_DIGITS", 10):
            with self.assertRaisesRegex(RealLiteralError, "expands beyond 10"):
                parse_real_literal("1e10")
            with self.assertRaisesRegex(RealLiteralError, "expands beyond 10"):
                parse_real_literal("1e-10")
            self.assertEqual(parse_real_literal("1e9"), (10 ** 9, 1))

    def test_invalid_tokens_cannot_be_interpreted_as_real_literals(self):
        for token in ("", "42", "-0.1", "+1.0", "nan", "inf", "1.2j", "1__2.0", "1_.0", "1._0", "1e_3", "1e", " 0.1"):
            with self.subTest(token=token), self.assertRaises(RealLiteralError):
                parse_real_literal(token)

    def test_bound_diagnostics_point_to_the_literal(self):
        with self.assertRaises(CompileError) as context:
            parse_source("def sample() -> Int:\n    value = 1e1025\n")
        self.assertEqual((context.exception.line, context.exception.column), (2, 13))
        self.assertIn("exponent magnitude", context.exception.message)

    def test_integer_boolean_and_complex_nodes_do_not_receive_real_metadata(self):
        tree = parse_source("integer = 7\nboolean = True\ncomplex_value = 1.5j\n")
        self.assertTrue(all(not hasattr(node, "exact_ratio") for node in ast.walk(tree)))


if __name__ == "__main__":
    unittest.main()
