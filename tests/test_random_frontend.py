"""Typing and effect-preserving lowering of integer draws with an exclusive stop."""

import ast
import textwrap
import unittest

from algo2lean.compiler import Lowerer
from algo2lean.frontend import CompileError, parse_program


def parse(source):
    return parse_program(ast.parse(textwrap.dedent(source)))


def lower(source, name="f"):
    functions, _ = parse(source)
    return Lowerer(functions[name])


def paths(lowered, pc=None):
    """List terminating control-flow paths for the acyclic expressions below."""
    pc = lowered.entry if pc is None else pc
    node = lowered.nodes[pc]
    if node.kind == "return":
        return [[node]]
    if node.kind == "branch":
        following = node.data[1:]
    elif node.kind == "assign":
        following = [node.data[2]]
    elif node.kind in ("random", "call"):
        following = [node.data[3]]
    else:
        raise AssertionError("Unexpected node on an expression path: " + node.kind)
    return [[node] + rest for next_pc in following for rest in paths(lowered, next_pc)]


class RandomFrontendTests(unittest.TestCase):
    def test_integer_bounds_accept_negative_singleton_and_empty_intervals(self):
        # Empty intervals are an execution error, not a source type error.
        for bounds in ("-7, -2", "4, 5", "4, 4", "5, 2", "a - 1, b + 1"):
            with self.subTest(bounds=bounds):
                lowered = lower("def f(a: Int, b: Int) -> Int:\n    return randint(" + bounds + ")\n")
                draws = [node for node in lowered.nodes if node.kind == "random"]
                self.assertEqual(len(draws), 1)
                target, low, high, following = draws[0].data
                self.assertEqual(lowered.field_types[target], "Int")
                self.assertNotEqual(low, high)
                self.assertEqual(lowered.nodes[following].kind, "return")

    def test_requires_exactly_two_positional_arguments(self):
        for expression in ("randint()", "randint(0)", "randint(0, 1, 2)"):
            with self.subTest(expression=expression), self.assertRaisesRegex(CompileError, "expects 2 argument"):
                parse("def f() -> Int:\n    return " + expression + "\n")
        for expression in ("randint(a=0, b=1)", "randint(0, b=1)", "randint(**a)"):
            with self.subTest(expression=expression), self.assertRaisesRegex(CompileError, "Keyword and expanded"):
                parse("def f(a: Int) -> Int:\n    return " + expression + "\n")
        with self.assertRaises(CompileError):
            parse("def f(a: Int) -> Int:\n    return randint(*a, 1)\n")

    def test_bounds_reject_booleans_and_nonintegers(self):
        for bounds in ("True, 1", "0, False", "const(0), 1", "0, None"):
            with self.subTest(bounds=bounds), self.assertRaisesRegex(CompileError, "Expected Int"):
                parse("def f() -> Int:\n    return randint(" + bounds + ")\n")
        with self.assertRaisesRegex(CompileError, "Expected Bool, got Int"):
            parse("def f() -> Bool:\n    return randint(0, 1)\n")

    def test_builtin_name_is_reserved_everywhere(self):
        sources = [
            "def randint() -> Int:\n    return 0\n",
            "def f(randint: Int) -> Int:\n    return randint\n",
            "def f() -> Int:\n    randint = 0\n    return randint\n",
            "class randint:\n    pass\n",
            "class Box:\n    randint: Int\n",
            "class Box:\n    def randint(self) -> Int:\n        return 0\n",
        ]
        for source in sources:
            with self.subTest(source=source), self.assertRaisesRegex(CompileError, "'randint' is reserved"):
                parse(source)

    def test_draws_work_in_integer_expression_positions(self):
        lowered = lower('''
            def identity(x: Int) -> Int:
                return x
            def f(values: Seq, flag: Bool) -> Int:
                x = -randint(-4, 4) + identity(randint(0, 2))
                values[randint(-1, 1)] = randint(x, x + 1)
                for i in range(randint(1, 3)):
                    tick("steps", randint(0, 2))
                while randint(0, 1) == 0:
                    x = randint(0, 1) if flag else randint(2, 3)
                return values[randint(-1, 1)]
        ''')
        self.assertEqual(sum(node.kind == "random" for node in lowered.nodes), 10)

    def test_bound_calls_evaluate_once_left_to_right_before_draw(self):
        lowered = lower('''
            def low(values: Seq) -> Int:
                values[0] = values[0] + 1
                return values[0]
            def high(values: Seq) -> Int:
                values[0] = values[0] + 10
                return values[0]
            def f(values: Seq) -> Int:
                return randint(low(values), high(values))
        ''')
        path, = paths(lowered)
        effects = [node for node in path if node.kind in ("call", "random")]
        self.assertEqual([node.kind for node in effects], ["call", "call", "random"])
        self.assertEqual([node.data[0] for node in effects[:2]], ["low", "high"])
        self.assertEqual(effects[2].data[1:3], tuple("s." + node.data[2] for node in effects[:2]))

    def test_nested_draws_preserve_order_and_feed_outer_draw(self):
        lowered = lower("def f() -> Int:\n    return randint(randint(0, 1), randint(2, 3))\n")
        path, = paths(lowered)
        draws = [node for node in path if node.kind == "random"]
        self.assertEqual(len(draws), 3)
        self.assertEqual(draws[-1].data[1:3], tuple("s." + node.data[0] for node in draws[:2]))
        self.assertEqual(len({node.data[0] for node in draws}), 3)

    def test_identical_source_calls_remain_separate_draws(self):
        lowered = lower("def f() -> Int:\n    return randint(0, 1) + randint(0, 1)\n")
        expression = lowered.function.node.body[0].value
        self.assertIsNone(lowered.pure_expr(expression))
        path, = paths(lowered)
        draws = [node for node in path if node.kind == "random"]
        self.assertEqual(len(draws), 2)
        self.assertNotEqual(draws[0].data[0], draws[1].data[0])

    def test_boolean_short_circuit_skips_draws(self):
        for operator in ("and", "or"):
            with self.subTest(operator=operator):
                lowered = lower("def f(flag: Bool) -> Bool:\n    return flag " + operator + " randint(0, 1) == 0\n")
                counts = {sum(node.kind == "random" for node in path) for path in paths(lowered)}
                self.assertEqual(counts, {0, 1})

    def test_conditional_expression_draws_only_selected_branch(self):
        lowered = lower("def f(flag: Bool) -> Int:\n    return randint(0, 1) if flag else randint(2, 3)\n")
        branches = paths(lowered)
        self.assertEqual(len(branches), 2)
        for path in branches:
            self.assertEqual(sum(node.kind == "random" for node in path), 1)

    def test_chained_comparison_reuses_middle_result_and_skips_last_draw(self):
        lowered = lower("def f() -> Bool:\n    return randint(0, 2) < randint(0, 2) < randint(0, 2)\n")
        counts = {sum(node.kind == "random" for node in path) for path in paths(lowered)}
        self.assertEqual(counts, {2, 3})
        self.assertEqual(sum(node.kind == "random" for node in lowered.nodes), 3)


if __name__ == "__main__":
    unittest.main()
