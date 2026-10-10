"""Named locations and proofs over the explicit transcript-based semantics."""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.checker import check_lean, prepare_lean_environment
from algo2lean.compiler import CompileError, compile_source
from tests.test_lean import constructor_tactic


ROOT = Path(__file__).resolve().parents[1]
SOURCE = """\
def f(n: Int) -> Int:
    # @assign
    value = 1
    pass
    # @result
    return value
"""


class TranscriptInterfaceTests(unittest.TestCase):
    def test_only_explicit_labels_get_location_interfaces(self):
        result = compile_source(SOURCE)
        points = result.functions[0]["points"]
        self.assertEqual([(p["name"], p["line"], p["column"]) for p in points],
                         [("assign", 3, 5), ("result", 6, 5)])
        self.assertEqual(points[0]["variables"], [{"name": "n", "type": "Int"}])
        self.assertEqual(points[1]["variables"],
                         [{"name": "n", "type": "Int"}, {"name": "value", "type": "Int"}])
        self.assertIn("def f.At.assign", result.points_lean)
        self.assertIn("def f.Local.value", result.points_lean)
        self.assertIn("def f.CallFrom", result.program_lean)
        self.assertNotIn("f.At.line", result.program_lean)
        unlabeled = compile_source("def f(n: Int) -> Int:\n    return n\n")
        self.assertEqual(unlabeled.functions[0]["points"], [])
        self.assertNotIn("def At_", unlabeled.program_lean)
        self.assertNotIn("def local_", unlabeled.program_lean)
        self.assertIn("def f.CallFrom", unlabeled.program_lean)
        self.assertNotIn("def At_", unlabeled.points_lean)
        self.assertNotIn("def local_", unlabeled.points_lean)

    def test_import_and_standalone_share_the_identical_program(self):
        imported = compile_source(SOURCE)
        standalone = compile_source(SOURCE, standalone=True)
        self.assertEqual(imported.program_lean, standalone.program_lean)
        self.assertEqual(imported.lean, "import Algo2Lean\n\n" + imported.program_lean)
        self.assertEqual(standalone.lean, imported.shared_lean + "\n" + imported.program_lean)
        self.assertEqual(imported.shared_lean, (ROOT / "Algo2Lean.lean").read_text())
        for result in (imported, standalone):
            self.assertEqual(result.stats, {
                "program_lines": len(result.program_lean.splitlines()),
                "general_lines": len(result.lean.splitlines()),
                "points_lines": len(result.points_lean.splitlines()),
                "shared_lines": len(result.shared_lean.splitlines()),
                "total_lines": len(result.lean.splitlines()) + len(result.points_lean.splitlines()),
            })

    def test_malformed_labels_are_diagnostics(self):
        cases = [
            "def f() -> Int:\n    # @same\n    pass\n    # @same\n    return 0\n",
            "def f() -> Int:\n    # @123\n    return 0\n",
            "# @orphan\ndef f() -> Int:\n    return 0\n",
            "def f() -> Int:\n    return 0\n    # @unattached\n",
        ]
        for source in cases:
            with self.subTest(source=source):
                with self.assertRaises(CompileError):
                    compile_source(source)
        with self.assertRaises(CompileError):
            compile_source(SOURCE, standalone="false")

    def test_scoped_observations_distinguish_underscore_boundaries(self):
        source = "def f_a(b: Int) -> Int:\n    # @b\n    return b\ndef f(a_b: Int) -> Int:\n    # @a_b\n    return a_b\n"
        result = compile_source(source)
        for name in ("f_a.At.b", "f.At.a_b", "f_a.Local.b", "f.Local.a_b"):
            self.assertIn("def " + name, result.points_lean)
        if shutil.which("lean"):
            checked = check_lean(result.lean, module=result.module,
                points_lean=result.points_lean, timeout=120)
            self.assertTrue(checked.ok, checked.output)

    def test_trailing_labels_explain_how_to_move_them(self):
        cases = [
            "def f() -> Int:\n    return 0  # @ready\n",
            "def f() -> Int:\n    while True:  # @loop\n        pass\n",
            "def f() -> Int:\n    return (\n        0\n    )  # @ready\n",
        ]
        for source in cases:
            with self.subTest(source=source), self.assertRaises(CompileError) as caught:
                compile_source(source)
            self.assertIn("on its own line immediately before the statement", str(caught.exception))
            self.assertIn("before execution", str(caught.exception))
        with self.assertRaises(CompileError) as caught:
            compile_source(cases[0])
        self.assertEqual((caught.exception.line, caught.exception.column), (2, 15))

    def test_labels_must_directly_precede_statements_at_matching_indentation(self):
        for separator in ("\n", "    # ordinary comment\n", "    # @second\n"):
            source = "def f() -> Int:\n    # @ready\n" + separator + "    return 0\n"
            with self.subTest(separator=separator), self.assertRaisesRegex(CompileError, "immediately above"):
                compile_source(source)
        with self.assertRaisesRegex(CompileError, "same indentation"):
            compile_source("def f() -> Int:\n  # @ready\n    return 0\n")
        result = compile_source("def f() -> Int:\n    # explanation\n    # @ready\n    return 0  # ordinary comment\n")
        self.assertEqual(result.functions[0]["points"][0]["line"], 4)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_local_facts_transcripts_and_reusable_summaries(self):
        source = (ROOT / "tests/proofs/transcripts.algo").read_text()
        generated = compile_source(source, filename="transcripts.algo")
        proof = "\n".join((ROOT / "tests/proofs" / name).read_text() for name in
                          ("transcripts.lean", "transcript_divergence.lean"))
        checked = check_analysis(generated.lean,
                                 "import " + generated.points_module + "\nopen Algo2LeanGenerated\n" + constructor_tactic(generated.lean) + proof,
                                 generated.module, points_lean=generated.points_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_source_names_do_not_collide_with_lean_constructors(self):
        source = """\
def invalid(mk: Int, casesOn: Int) -> Int:
    # @result
    return mk + casesOn

def rec(recOn: Int) -> Int:
    return invalid(recOn, 1)
"""
        result = compile_source(source)
        checked = check_lean(result.lean, module=result.module, points_lean=result.points_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_documented_interface_examples(self):
        source = (ROOT / "docs/examples/interface.algo").read_text()
        proof = (ROOT / "docs/examples/interface.lean").read_text()
        result = compile_source(source, filename="interface.algo")
        checked = check_analysis(result.lean, proof, result.module, points_lean=result.points_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_fixed_specification_survives_replaced_point_module(self):
        """Rebuild proof helpers against the same compiled algorithm and goal."""
        source = "def f(n: Int) -> Int:\n    # @assign\n    value = 1\n    # @result\n    return value\n"
        first = compile_source(source, module="FixedAlgorithm")
        second = compile_source("# A new proof layout\n" + source.replace("@assign", "@set").replace("@result", "@ready"),
                                module="FixedAlgorithm")
        self.assertEqual(first.lean, second.lean)
        self.assertNotEqual(first.points_lean, second.points_lean)
        environment = prepare_lean_environment(timeout=120)
        with tempfile.TemporaryDirectory(prefix="algo2lean-fixed-statement-") as directory:
            temporary = Path(directory)
            environment["LEAN_PATH"] = directory + os.pathsep + environment["LEAN_PATH"]

            def build(module, text):
                path = temporary / (module + ".lean")
                path.write_text(text)
                checked = subprocess.run(
                    ["lean", "--root=" + directory, "-o", str(path.with_suffix(".olean")), str(path)],
                    cwd=ROOT, env=environment, capture_output=True, text=True, timeout=120)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                self.assertNotIn("declaration uses `sorry`", checked.stdout + checked.stderr)

            build(first.module, first.lean)
            build("Specification", "import FixedAlgorithm\ndef Correct : Prop := ∀ n, f.Returns n 1\n")
            fixed = {name: (temporary / name).read_bytes() for name in
                     ("FixedAlgorithm.lean", "FixedAlgorithm.olean", "Specification.lean", "Specification.olean")}
            for generated, before, after in ((first, "assign", "result"), (second, "set", "ready")):
                build(generated.points_module, generated.points_lean)
                proof = """import Specification
import FixedAlgorithmPoints
open Algo2LeanCore Algo2LeanGenerated
theorem assignment_sets_one {before after : Configuration}
    (transition : Step before after) (location : f.At.BEFORE before) :
    f.At.AFTER after ∧ f.Local.value after = some 1 := by
  cases transition <;> simp_all [f.At.BEFORE, f.At.AFTER, f.Local.value]
theorem verified : Correct := by
  intro n
  refine ⟨{}, True.intro, ?_⟩
  refine (Reaches.single (Step.f_pc3 _ _ _)).trans ?_
  refine (Reaches.single (Step.f_pc2 _ _ _)).trans ?_
  exact Reaches.single (Step.f_pc1 _ _ _)
""".replace("BEFORE", before).replace("AFTER", after)
                build("Proof", proof)
                for name, content in fixed.items():
                    self.assertEqual((temporary / name).read_bytes(), content)


if __name__ == "__main__":
    unittest.main()
