"""CLRS sources and analyses exercise the generated probability interface."""

from pathlib import Path
import shutil
import unittest

from algo2lean.editor_examples import load_example_project
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from algo2lean.probability_checker import check_probability_sources

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples/randomized_clrs"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


class RandomizedCLRSTests(unittest.TestCase):
    def test_local_catalog_preserves_sources_and_separate_proofs(self):
        project = load_example_project("randomized_clrs")
        self.assertEqual(project["entry"], "shuffle.algo")
        self.assertEqual(set(project["sources"]), {"shuffle.algo", "hiring.algo", "partition.algo",
            "selection.algo", "quicksort.algo", "coupon_collector.algo"})
        for module in ("shuffle", "hiring", "partition", "selection", "quicksort", "coupon_collector"):
            self.assertIn("Algo." + module + ".Analysis", project["analyses"])
        for entry in project["sources"]:
            compiled = compile_project(entry, root=EXAMPLES)
            self.assertTrue(any(name.endswith(".Probability") for name in compiled.files))

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_probability_contexts_cover_all_source_instructions(self):
        sources = {}
        for entry in load_example_project("randomized_clrs")["sources"]:
            compiled = compile_project(entry, root=EXAMPLES)
            sources.update({name: source for name, source in compiled.files.items()
                            if name.endswith((".Generated", ".Facts", ".Probability"))})
        checked = check_probability_sources(sources, timeout=180)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_shuffle_analysis_matches_generated_program(self):
        compiled = compile_project("shuffle", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.shuffle.Analysis", timeout=180)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_hiring_reuses_shuffle_with_total_runtime_guarantees(self):
        compiled = compile_project("hiring", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.hiring.Analysis", timeout=240)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_partition_law_retains_uniform_rank_and_mutation(self):
        compiled = compile_project("partition", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.partition.Analysis", timeout=240)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_selection_reuses_partition_with_linear_expected_runtime(self):
        compiled = compile_project("selection", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.selection.Analysis", timeout=240)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_quicksort_reuses_partition_with_harmonic_comparison_mean(self):
        compiled = compile_project("quicksort", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.quicksort.Analysis", timeout=240)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_coupon_source_expectation_and_tail(self):
        compiled = compile_project("coupon_collector", root=EXAMPLES)
        checked = check_project(compiled, analysis_module="Algo.coupon_collector.Analysis", timeout=240)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
