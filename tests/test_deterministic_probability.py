"""Existing deterministic proofs become reusable probabilistic call contracts."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project, _attach_probability
from algo2lean.project_checker import check_project, project_lean_sources
from algo2lean.public_names import PROBABILITY_MEMBERS
from algo2lean.server import project_response
from editor.analysis_export import request
from scripts.check_chapter4_proofs import audit_assumptions
from tests.test_analysis_export import unpack
from tests import test_probability_export as export_tests

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/deterministic_probability"
RECURSIVE = {
    "left": "from right import recurse\n"
            "def count(n: Int) -> Int:\n"
            "    if n <= 0:\n"
            "        return 0\n"
            "    return recurse(n - 1)\n",
    "right": "from left import count\n"
             "def recurse(n: Int) -> Int:\n"
             "    return count(n)\n",
}


def recursive(randomized=False):
    sources = dict(RECURSIVE)
    if randomized:
        sources["left"] = sources["left"].replace("return 0", "return randint(0, 2)")
    compiled = compile_project("left", root=FIXTURE, sources=sources)
    _attach_probability(compiled, force=True)
    return compiled


class DeterministicProbabilityInterfaceTests(unittest.TestCase):
    def test_bridge_is_optional_and_keeps_original_modules(self):
        original = compile_project("helper", root=FIXTURE)
        mixed = compile_project("client", root=FIXTURE)
        self.assertFalse(any(name.endswith(".Probability") for name in original.files))
        for name, source in original.files.items():
            self.assertEqual(source, mixed.files[name])
        companion = mixed.modules["helper"].probability_lean
        self.assertIn("theorem bump.Call.hasLaw", companion)
        self.assertIn("theorem bump.Call.expectedReturn", companion)
        self.assertNotIn("Call.hasLaw", mixed.entry.probability_lean)
        _attach_probability(original, force=True)
        entries = project_response(original)["functions"][0]["interface_entries"]
        self.assertTrue({"bump.Call.hasLaw", "bump.Call.expectedReturn"}.issubset(
            {entry["name"] for entry in entries if entry["file_kind"] == "probability"}))

    def test_successful_random_trace_does_not_acquire_a_law(self):
        source = ("def sample() -> Int:\n"
                  "    if randint(0, 2) == 0:\n"
                  "        return 0\n"
                  "    while True:\n"
                  "        pass\n")
        compiled = compile_project("main", root=FIXTURE, sources={"main": source})
        self.assertNotIn("Call.hasLaw", compiled.entry.probability_lean)
        self.assertNotIn("Deterministic", compiled.entry.probability_lean)
        self.assertFalse(compiled.entry.facts_lean)

    def test_recursive_facades_have_the_complete_contract_interface(self):
        for randomized in (False, True):
            compiled = recursive(randomized)
            for name, function in (("left", "count"), ("right", "recurse")):
                source = compiled.modules[name].probability_lean
                for member in PROBABILITY_MEMBERS:
                    self.assertIn("abbrev " + function + "." + member + " := @", source)
                self.assertIn("abbrev nextChoice_context", source)
                self.assertEqual("Call.hasLaw" in source, not randomized)

    def test_labels_do_not_change_general_or_probability_definitions(self):
        sources = {name: (FIXTURE / (name + ".algo")).read_text() for name in ("client", "helper")}
        original = compile_project("client", root=FIXTURE, sources=sources)
        sources["helper"] = sources["helper"].replace('    tick', '    # @charge\n    tick')
        labelled = compile_project("client", root=FIXTURE, sources=sources)
        for name, source in original.files.items():
            if not name.endswith(".Points"):
                self.assertEqual(source, labelled.files[name])


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class DeterministicProbabilityCoreTests(unittest.TestCase):
    def test_original_mutation_proof_needs_no_mathlib(self):
        compiled = compile_project("helper", root=FIXTURE)
        sources = project_lean_sources(compiled, analysis_modules=["Algo.helper.Analysis"])
        self.assertFalse(any("Mathlib" in source or "Probability" in source for source in sources.values()))
        checked = check_project(compiled, analysis_module="Algo.helper.Analysis")
        self.assertTrue(checked.ok, checked.output)


@unittest.skipUnless(export_tests.MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class DeterministicProbabilityLeanTests(unittest.TestCase):
    def test_repeated_mutating_calls_and_third_module_reuse(self):
        compiled = compile_project("driver", root=FIXTURE)
        checked = check_project(compiled, analysis_module="Algo.driver.Analysis", timeout=180)
        self.assertTrue(checked.ok, checked.output)
        self.assertIsNone(audit_assumptions(checked.output, (
            "Algo.helper.bump.Call.hasLaw", "ClientAnalysis.sample_hasLaw",
            "ClientAnalysis.expected_updates", "DriverAnalysis.run_hasLaw")))

    def test_recursive_companions_check_with_and_without_randomness(self):
        for randomized in (False, True):
            with self.subTest(randomized=randomized):
                compiled = recursive(randomized)
                proof = ("import Algo.left.Probability\nimport Algo.right.Probability\n"
                         "#check Algo.left.count.HasLaw\n#check Algo.right.recurse.expectedReturn\n")
                if not randomized:
                    proof += ("example {h n final value} (call : Algo.right.recurse.Call h n final value) :\n"
                              "    Algo.right.recurse.HasLaw h n (PMF.pure (final, value)) :=\n"
                              "  Algo.right.recurse.Call.hasLaw call\n")
                checked = check_project(compiled, analysis=proof, timeout=180)
                self.assertTrue(checked.ok, checked.output)

    def test_export_rebuilds_the_bridge_from_sources(self):
        body = {
            "filename": "driver.algo", "source": (FIXTURE / "driver.algo").read_text(),
            "project_sources": {name + ".algo": (FIXTURE / (name + ".algo")).read_text()
                                for name in ("helper", "client", "driver")},
            "project_analyses": {"Algo." + name + ".Analysis":
                                (FIXTURE / "analysis" / (name + ".lean")).read_text()
                                for name in ("helper", "client", "driver")},
            "analysis": (FIXTURE / "analysis/driver.lean").read_text(),
        }
        files = unpack(request("/api/analysis-export", body, project=True))
        self.assertEqual(files["Algo2LeanProbability/Deterministic.lean"],
                         (ROOT / "probability/Algo2LeanProbability/Deterministic.lean").read_bytes())
        export_tests.ProbabilityExportBuildTests.build(self, files, "Algo/driver/Analysis.olean")


if __name__ == "__main__":
    unittest.main()
