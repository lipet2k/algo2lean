"""Kernel-check local random transitions without importing Mathlib."""

import ast
from pathlib import Path
import shutil
import unittest

from algo2lean.checker import check_lean
from algo2lean.compiler import Lowerer, compile_source
from algo2lean.frontend import parse_program
from algo2lean.probability import emit_choices


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class RandomSemanticsTests(unittest.TestCase):
    def check_choices(self, source, extra=""):
        functions, _ = parse_program(ast.parse(source))
        lowered = {name: Lowerer(function) for name, function in functions.items()}
        compiled = compile_source(source)
        lean = "import Algo2LeanLib.Choice\nimport Algo2LeanLib.CallContext\n" + compiled.lean + "\n" + emit_choices(lowered) + extra
        checked = check_lean(lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)

    def test_half_open_negative_singleton_and_empty_intervals(self):
        self.check_choices("def sample(a: Int, b: Int) -> Int:\n    return randint(a, b)\n", """
open Algo2LeanCore
example : (Choice.uniform (-3) 2 id).Allows (1 : Int) := ⟨1, by decide, by decide, rfl⟩
example : ¬ (Choice.uniform (-3) 2 id).Allows (2 : Int) := by
  rintro ⟨value, _, upper, rfl⟩
  exact (Int.lt_irrefl _ upper)
example {after : Int} : (Choice.uniform 4 5 id).Allows after ↔ after = 4 := by
  constructor
  · rintro ⟨value, lower, upper, rfl⟩
    omega
  · rintro rfl
    exact ⟨4, by decide, by decide, rfl⟩
example {a : Int} {after : Int} : ¬ (Choice.uniform a a id).Allows after := by
  intro allowed
  exact (Int.lt_irrefl a) (Choice.uniform_bounds allowed)
""")

    def test_choice_agreement_includes_mutation_and_partial_instructions(self):
        self.check_choices("""def change(a: Seq) -> Int:
    a[0] = a[0] + 1
    return a[0]

def sample(a: Seq, lower: Int, upper: Int) -> Int:
    x = randint(change(a), change(a) + 3)
    a[x] = randint(lower, upper)
    for i in range(lower, upper, randint(-1, 2)):
        tick("work", randint(-2, 4))
        a[i] = x // randint(-1, 2)
    if randint(0, 2) == 0:
        return a[x]
    return 0
""")

    def test_choices_cover_existing_sort_and_nullable_object_instructions(self):
        for filename in ("merge_sort.algo", "classes.algo"):
            with self.subTest(filename=filename):
                self.check_choices((ROOT / "examples" / filename).read_text())


if __name__ == "__main__":
    unittest.main()
