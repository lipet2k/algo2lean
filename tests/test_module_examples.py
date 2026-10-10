"""Real .algo imports reuse existing correctness and clock analyses in layers."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples/modules"


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ModuleExamplesTests(unittest.TestCase):
    def test_each_layer_reuses_the_same_component_analysis(self):
        independent = compile_project("increment", root=EXAMPLES)
        original = independent.entry.lean
        for name in ("increment", "twice", "pipeline"):
            with self.subTest(module=name):
                compiled = compile_project(name, root=EXAMPLES)
                self.assertEqual(compiled.modules["increment"].lean, original)
                checked = check_project(compiled, analysis_module="Algo." + name + ".Analysis")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("declaration uses 'sorry'", checked.output)

    def test_combined_costs_apply_to_arbitrary_existing_counters(self):
        compiled = compile_project("pipeline", root=EXAMPLES)
        analysis = """import Algo.pipeline.Analysis
open Algo2LeanGenerated Algo.pipeline

example (value : Int) :
    advance_four.ReturnsWithCost value (value + 4)
      (Clocks.add (Clocks.single "batches" 1) (Clocks.single "increments" 4)) :=
  PipelineAnalysis.output_cost value

example (heap : Heap) (value : Int) :
    ∃ after, advance_four.Run heap value after (value + 4) ∧
      after.clocks "increments" = heap.clocks "increments" + 4 ∧
      after.clocks "batches" = heap.clocks "batches" + 1 ∧
      after.clocks "unrelated" = heap.clocks "unrelated" := by
  obtain ⟨after, execution, effect⟩ := PipelineAnalysis.execution_cost heap value
  refine ⟨after, execution, ?_, ?_, ?_⟩
  · simpa [Clocks.add, Clocks.single] using effect "increments"
  · simpa [Clocks.add, Clocks.single] using effect "batches"
  · simpa [Clocks.add, Clocks.single] using effect "unrelated"

example (heap after : Heap) (value output : Int)
    (execution : advance_four.Run heap value after output) :
    output = value + 4 ∧ Heap.cost heap after "increments" = 4 := by
  obtain ⟨result, effect⟩ := PipelineAnalysis.correct execution
  refine ⟨result, ?_⟩
  simpa [Clocks.add, Clocks.single] using congrFun effect.cost "increments"
"""
        checked = check_project(compiled, analysis=analysis, analysis_module="ModuleExampleClient")
        self.assertTrue(checked.ok, checked.output)

    def test_a_changed_import_invalidates_the_original_proof(self):
        changed = (EXAMPLES / "increment.algo").read_text(encoding="utf-8").replace("value + 1", "value + 2")
        compiled = compile_project("pipeline", root=EXAMPLES, sources={"increment": changed})
        checked = check_project(compiled, analysis_module="Algo.pipeline.Analysis")
        self.assertFalse(checked.ok)
        self.assertIn("Algo/increment/Analysis.lean:", checked.output)


if __name__ == "__main__":
    unittest.main()
