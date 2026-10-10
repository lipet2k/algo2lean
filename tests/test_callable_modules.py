"""Ordinary function parameters share the checked executable import mechanism."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples/modules"


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class CallableModuleTests(unittest.TestCase):
    def test_independent_functions_and_one_generic_client_proof(self):
        combined = compile_project("callable_bindings", root=EXAMPLES)
        for name in ("callable_direct", "callable_staged"):
            with self.subTest(module=name):
                independent = compile_project(name, root=EXAMPLES)
                self.assertEqual(independent.entry.lean, combined.modules[name].lean)
                checked = check_project(independent, analysis_module="Algo." + name + ".Analysis", timeout=60)
                self.assertTrue(checked.ok, checked.output)
        checked = check_project(combined, analysis_module="Algo.callable_bindings.Analysis", timeout=60)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses 'sorry'", checked.output)

    def test_both_instances_have_real_executions_and_exact_heap_effects(self):
        compiled = compile_project("callable_bindings", root=EXAMPLES)
        proof = """import Algo.callable_bindings.Analysis
open Algo2LeanCore Algo2LeanGenerated CallableBindings

example (heap : Heap) (value : Int) :
    CallableClient.twice.Run Direct.code heap value
      (heap.tick "callable_work" 2) (value + 2) ∧
    CallableClient.twice.Run Staged.code heap value
      (heap.tick "callable_work" 4) (value + 2) :=
  ⟨(direct_summary heap value).root, (staged_summary heap value).root⟩

example {before after : Heap} {value result : Int}
    (execution : CallableClient.twice.Run Direct.code before value after result)
    (left right : SeqRef) (alias : left = right) :
    result = value + 2 ∧ after.nextRef = before.nextRef ∧
      after.store left = before.store right ∧ after.objects = before.objects ∧
      after.clocks "callable_work" = before.clocks "callable_work" + 2 ∧
      Heap.cost before after "callable_work" = 2 := by
  obtain ⟨sameHeap, sameResult⟩ := direct_correct execution
  subst after
  subst right
  exact ⟨sameResult, rfl, rfl, rfl, by simp, by simp⟩

example {before after : Heap} {value result : Int}
    (execution : CallableClient.twice.Run Staged.code before value after result)
    (clock : String) (different : clock ≠ "callable_work") :
    Heap.cost before after "callable_work" = 4 ∧ after.clocks clock = before.clocks clock := by
  obtain ⟨sameHeap, _⟩ := staged_correct execution
  subst after
  constructor
  · simp
  · simp [Heap.tick, different]

example (heap : Heap) (value : Int) :
    ∃ state : CallableClient.Configuration Direct.code,
      CallableClient.Step Direct.code
        (.active heap (.imported (Direct.code.entry value) [] .afterFirst) []) state ∧
      state.heap = heap.tick "callable_work" := direct_first_tick heap value
"""
        checked = check_project(compiled, analysis=proof, analysis_module="CallableExternalClient", timeout=60)
        self.assertTrue(checked.ok, checked.output)

    def test_changed_function_behavior_or_charge_rejects_original_proof(self):
        source = (EXAMPLES / "callable_direct.algo").read_text(encoding="utf-8")
        for changed in (source.replace("return value + 1", "return value + 2"),
                        source.replace('tick("callable_work")', 'tick("callable_work", 2)')):
            with self.subTest(source=changed):
                compiled = compile_project("callable_bindings", root=EXAMPLES,
                                           sources={"callable_direct": changed})
                checked = check_project(compiled, analysis_module="Algo.callable_bindings.Analysis", timeout=60)
                self.assertFalse(checked.ok)
                self.assertIn("Algo/callable_direct/Analysis.lean:", checked.output)


if __name__ == "__main__":
    unittest.main()
