"""Lean kernel validation of generated semantics and nontermination proofs."""

from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.compiler import compile_source
from algo2lean.checker import prepare_lean_environment


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "tests" / "proofs"


def constructor_tactic(lean_source):
    """Build explicit Valid transcripts from the generated Step constructors.

    This supplies finite derivations, not an evaluator or an added axiom.
    Expected outputs and the universal divergence theorems live in fixtures.
    """
    constructors = ["Algo2LeanGenerated.Step." + name for name in
                    re.findall(r"^\s*\|\s+(\w+_pc\w*)\b", lean_source, re.MULTILINE)]
    if not constructors:
        raise AssertionError("No execution relation constructors found")
    valid_inputs = re.findall(r"^def (\S+\.ValidInput)\b", lean_source, re.MULTILINE)
    validate = "(solve | (simp only [" + ", ".join(valid_inputs) + "] <;> decide))"
    alternatives = ["assumption", "rfl", "decide", "exact True.intro", validate,
                    "(apply Exists.intro <;> algo_steps)",
                    "(apply And.intro <;> algo_steps)",
                    "(apply Algo2LeanCore.Valid.single)",
                    "(apply Algo2LeanCore.Valid.cons <;> algo_steps)"]
    alternatives.extend("(apply " + name + " <;> algo_steps)" for name in constructors)
    return "\nset_option maxRecDepth 4096\nset_option maxHeartbeats 8000000\n" + \
        'syntax "algo_steps" : tactic\nmacro_rules\n  | `(tactic| algo_steps) => `(tactic| first\n' + \
        "\n".join("    | " + alternative for alternative in alternatives) + ")\n"


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class LeanSemanticsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean_environment = prepare_lean_environment(timeout=120)

    def check_lean(self, content, name):
        with tempfile.TemporaryDirectory(prefix="algo2lean-proof-") as directory:
            path = Path(directory) / (name + ".lean")
            path.write_text(content, encoding="utf-8")
            result = subprocess.run(
                ["lean", "+v4.26.0", str(path)],
                cwd=str(ROOT), env=self.lean_environment,
                capture_output=True, text=True, timeout=120,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("declaration uses 'sorry'", result.stdout + result.stderr)

    def test_examples_are_accepted_by_lean(self):
        for path in sorted((ROOT / "examples").glob("*.algo")):
            with self.subTest(example=path.name):
                result = compile_source(path.read_text(encoding="utf-8"), filename=str(path))
                self.check_lean(result.lean, path.stem)

    def test_finite_execution_semantics(self):
        source = (PROOFS / "semantics.algo").read_text(encoding="utf-8")
        generated = compile_source(source, filename="semantics.algo").lean
        proofs = (PROOFS / "semantics.lean").read_text(encoding="utf-8")
        self.check_lean(generated + constructor_tactic(generated) + proofs, "semantics")

    def test_pure_expression_semantics(self):
        source = (PROOFS / "pure_expressions.algo").read_text(encoding="utf-8")
        generated = compile_source(source, filename="pure_expressions.algo").lean
        proofs = (PROOFS / "pure_expressions.lean").read_text(encoding="utf-8")
        self.check_lean(generated + constructor_tactic(generated) + proofs, "pure_expressions")

    def test_infinite_loop_has_no_output(self):
        generated = compile_source((PROOFS / "loop.algo").read_text(encoding="utf-8")).lean
        proof = (PROOFS / "loop.lean").read_text(encoding="utf-8")
        self.check_lean(generated + proof, "no_loop_output")

    def test_self_recursion_has_no_output(self):
        generated = compile_source((PROOFS / "recursion.algo").read_text(encoding="utf-8")).lean
        proof = (PROOFS / "recursion.lean").read_text(encoding="utf-8")
        self.check_lean(generated + proof, "no_recursion_output")

    def test_conditional_fixture_exact_characterization(self):
        source = (ROOT / "tests/fixtures/my_func.algo").read_text(encoding="utf-8")
        generated = compile_source(source).lean
        proof = (PROOFS / "my_func.lean").read_text(encoding="utf-8")
        self.check_lean(generated + constructor_tactic(generated) + proof, "my_func_characterization")

    def test_division_by_zero_has_no_output(self):
        source = (PROOFS / "division.algo").read_text(encoding="utf-8")
        generated = compile_source(source).lean
        proof = (PROOFS / "division.lean").read_text(encoding="utf-8")
        self.check_lean(generated + proof, "division_by_zero")

    def test_mutable_heap_and_range_semantics(self):
        source = (PROOFS / "mutable.algo").read_text(encoding="utf-8")
        generated = compile_source(source, filename="mutable.algo").lean
        proof = (PROOFS / "mutable.lean").read_text(encoding="utf-8")
        self.check_lean(generated + constructor_tactic(generated) + proof, "mutable_heap")

    def test_range_zero_step_has_no_output(self):
        source = (PROOFS / "range_zero.algo").read_text(encoding="utf-8")
        generated = compile_source(source, filename="range_zero.algo").lean
        proof = (PROOFS / "range_zero.lean").read_text(encoding="utf-8")
        self.check_lean(generated + proof, "range_zero")

    def test_empty_range_still_evaluates_diverging_bound(self):
        source = (PROOFS / "range_divergence.algo").read_text(encoding="utf-8")
        generated = compile_source(source, filename="range_divergence.algo").lean
        proof = (PROOFS / "range_divergence.lean").read_text(encoding="utf-8")
        self.check_lean(generated + proof, "range_divergence")


if __name__ == "__main__":
    unittest.main()
