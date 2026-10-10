"""Explicit mathematical operation counters and their execution interfaces."""

from pathlib import Path
import shutil
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.compiler import CompileError, compile_source
from tests.test_lean import constructor_tactic


ROOT = Path(__file__).resolve().parents[1]
SOURCE = '''def f(x: Int) -> Int:
    # @before
    tick("steps")
    return x
'''


class ClockTests(unittest.TestCase):
    def test_ticks_need_explicit_static_names_and_statement_position(self):
        cases = [
            'tick()',
            'tick("steps", 2, 3)',
            'tick(1)',
            'tick(x)',
            'tick("not a name")',
            'tick("")',
            'tick("123")',
            'tick("étapes")',
            'tick(name="steps")',
            'tick("steps", True)',
            'tick("steps", "one")',
            'x = tick("steps")',
            'return tick("steps")',
            'tick',
        ]
        for statement in cases:
            source = 'def f(x: Int) -> Int:\n    ' + statement + '\n    return x\n'
            with self.subTest(statement=statement), self.assertRaises(CompileError):
                compile_source(source)

    def test_tick_name_is_reserved(self):
        cases = [
            'def tick() -> Int:\n    return 1\n',
            'def f(tick: Int) -> Int:\n    return tick\n',
            'def f() -> Int:\n    tick = 1\n    return tick\n',
            'class tick:\n    pass\n',
        ]
        for source in cases:
            with self.subTest(source=source), self.assertRaises(CompileError):
                compile_source(source)

    def test_clock_names_are_independent_of_source_identifier_reservations(self):
        for name in ("steps", "_comparisons2", "Int", "tick", "class"):
            with self.subTest(name=name):
                compile_source('def f() -> None:\n    tick("' + name + '")\n')

    def test_weighted_ticks_accept_integer_expressions(self):
        for amount in ('0', '1', '3', 'x', 'x + 1', '-1'):
            with self.subTest(amount=amount):
                compile_source('def f(x: Int) -> None:\n    tick("steps", ' + amount + ')\n')

    def test_label_changes_leave_counter_semantics_stable(self):
        before = compile_source(SOURCE, module="ClockExample")
        renamed = compile_source(SOURCE.replace("@before", "@counting"), module="ClockExample")
        removed = compile_source(SOURCE.replace("    # @before\n", ""), module="ClockExample")
        self.assertEqual(before.lean, renamed.lean)
        self.assertEqual(before.lean, removed.lean)
        self.assertIn("f.ReturnsWithCost", before.lean)
        self.assertIn("f.At.before", before.points_lean)
        self.assertNotEqual(before.points_lean, renamed.points_lean)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_costs_calls_recursion_mutation_and_divergence(self):
        source = (ROOT / "tests/proofs/clocks.algo").read_text()
        generated = compile_source(source, filename="clocks.algo")
        proof = (ROOT / "tests/proofs/clocks.lean").read_text()
        checked = check_analysis(
            generated.lean,
            "import " + generated.points_module + "\nopen Algo2LeanGenerated\n"
            + constructor_tactic(generated.lean) + proof,
            generated.module, points_lean=generated.points_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses 'sorry'", checked.output)


if __name__ == "__main__":
    unittest.main()
