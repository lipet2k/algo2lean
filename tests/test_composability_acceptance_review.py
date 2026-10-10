"""Final acceptance checks for partially instantiated reusable module proofs."""

import shutil
import tempfile
import unittest

from algo2lean.modular import compile_project
from algo2lean.project import ProjectError
from algo2lean.project_checker import check_project


SOURCES = {
    'api': """from algo2lean import Interface
class Left(Interface):
    def get(self)->Int: ...
class Right(Interface):
    def get(self)->Int: ...
""",
    'left': """class LeftBox:
    def get(self)->Int:
        tick("left", 2)
        return 10
""",
    'right': """class RightBox:
    def get(self)->Int:
        tick("right", 3)
        return 7
""",
    'generic': """from api import Left, Right
def combine(left:Left,right:Right)->Int:
    x=left.get()
    return x+right.get()
""",
    'partial': """from left import LeftBox
from api import Right
from generic import combine
def partially_bound(left:LeftBox,right:Right)->Int:
    return combine(left,right)
""",
    'main': """from left import LeftBox
from right import RightBox
from partial import partially_bound
def run(left:LeftBox,right:RightBox)->Int:
    return partially_bound(left,right)
""",
}

LEFT_PROOF = """import Algo.left.Generated
open Algo2LeanCore Algo2LeanGenerated
namespace LeftProof
open Algo.left Algo.left.Algo2LeanGenerated
theorem get (heap : Heap) (ref : ObjectRef) (valid : is_LeftBox heap ref) :
    LeftBox.get.Call heap ref (heap.tick "left" 2) 10 := by
  refine ⟨valid,?_⟩
  intro caller
  apply Reaches.prepend (Step.LeftBox_get_pc3 _ _ caller)
  apply Reaches.prepend (Step.LeftBox_get_pc2 _ _ caller)
  exact Reaches.single (Step.LeftBox_get_pc1 _ _ caller)
end LeftProof
"""

GENERIC_PROOF = """import Algo.generic.Generated
open Algo2LeanCore Algo2LeanGenerated
namespace GenericProof
open Algo.generic Algo.generic.Algo2LeanGenerated
theorem calls (dependencies : Dependencies) {before middle after : Heap}
    {left right : ObjectRef} {x y : Int}
    (rightValid : dependencies.Right.valid before right = true)
    (first : Algo.api.Left.get.Call dependencies.Left before left middle x)
    (second : Algo.api.Right.get.Call dependencies.Right middle right after y) :
    combine.Call dependencies before (left,right) after (x+y) := by
  refine ⟨⟨first.1,rightValid⟩,?_⟩
  intro caller
  apply Reaches.prepend (Step.combine_pc10 _ _ caller)
  apply Reaches.prepend (Step.combine_pc9 _ _ caller (by exact first.1))
  apply Reaches.prepend (Step.combine_pc8 _ _ caller)
  apply (ModuleCall.summary (interface_Left_simulates dependencies) _ caller first.2).trans
  apply Reaches.prepend (Step.combine_pc7 _ _ caller)
  apply Reaches.prepend (Step.combine_pc6 _ _ caller)
  apply Reaches.prepend (Step.combine_pc5 _ _ caller)
  apply Reaches.prepend (Step.combine_pc4 _ _ caller (by exact second.1))
  apply Reaches.prepend (Step.combine_pc3 _ _ caller)
  apply (ModuleCall.summary (interface_Right_simulates dependencies) _ caller second.2).trans
  apply Reaches.prepend (Step.combine_pc2 _ _ caller)
  exact Reaches.single (Step.combine_pc1 _ _ caller)
end GenericProof
"""

PARTIAL_PROOF = """import Algo.partial.Generated
import Algo.generic.Analysis
import Algo.left.Analysis
open Algo2LeanCore Algo2LeanGenerated
namespace PartialProof
open Algo.partial Algo.partial.Algo2LeanGenerated
theorem summary (dependencies : Dependencies) (heap after : Heap) (left right : ObjectRef) (value : Int)
    (leftValid : Algo.left.Algo2LeanGenerated.is_LeftBox heap left)
    (rightValid : dependencies.Right.valid heap right = true)
    (rightRun : Algo.api.Right.get.Call dependencies.Right (heap.tick "left" 2) right after value) :
    partially_bound.Call dependencies heap (left,right) after (10+value) := by
  have first := LeftBox_as_Left_summary_get (LeftProof.get heap left leftValid)
  have run := GenericProof.calls (use_generic_0 dependencies) rightValid first rightRun
  refine ⟨⟨leftValid,rightValid⟩,?_⟩
  intro caller
  apply Reaches.prepend (Step.partially_bound_pc4 _ _ caller)
  apply Reaches.prepend (Step.partially_bound_pc3 _ _ caller)
  apply Reaches.prepend (Step.partially_bound_pc2 _ _ caller)
  apply (ModuleCall.summary (import_2_use_generic_0_simulates dependencies) _ caller run.2).trans
  exact Reaches.single (Step.partially_bound_pc1 _ _ caller)
end PartialProof
"""

MAIN_PROOF = """import Algo.main.Facts
import Algo.partial.Analysis
open Algo2LeanCore Algo2LeanGenerated
namespace FinalProof
open Algo.main Algo.main.Algo2LeanGenerated
private theorem right_get (heap : Heap) (ref : ObjectRef)
    (valid : Algo.right.Algo2LeanGenerated.is_RightBox heap ref) :
    Algo.right.RightBox.get.Call heap ref (heap.tick "right" 3) 7 := by
  refine ⟨valid,?_⟩
  intro caller
  apply Reaches.prepend (Algo.right.Algo2LeanGenerated.Step.RightBox_get_pc3 _ _ caller)
  apply Reaches.prepend (Algo.right.Algo2LeanGenerated.Step.RightBox_get_pc2 _ _ caller)
  exact Reaches.single (Algo.right.Algo2LeanGenerated.Step.RightBox_get_pc1 _ _ caller)

theorem summary (heap : Heap) (left right : ObjectRef) (valid : run.ValidInput heap (left,right)) :
    run.Call heap (left,right) ((heap.tick "left" 2).tick "right" 3) 17 := by
  have rightRun := RightBox_as_Right_summary_get (right_get (heap.tick "left" 2) right valid.2)
  have run := PartialProof.summary use_partial_0 heap _ left right 7 valid.1
    (by simpa [use_partial_0,RightBox_as_Right] using valid.2) rightRun
  refine ⟨valid,?_⟩
  intro caller
  apply Reaches.prepend (Step.run_pc4 _ _ caller)
  apply Reaches.prepend (Step.run_pc3 _ _ caller)
  apply Reaches.prepend (Step.run_pc2 _ _ caller)
  apply (ModuleCall.summary import_4_use_partial_0_simulates _ caller run.2).trans
  exact Reaches.single (Step.run_pc1 _ _ caller)

theorem every_execution (heap after : Heap) (left right : ObjectRef) (output : Int)
    (execution : run.Run heap (left,right) after output) :
    output = 17 ∧ after = ((heap.tick "left" 2).tick "right" 3) ∧
      Heap.cost heap after "left" = 2 ∧ Heap.cost heap after "right" = 3 := by
  obtain ⟨rfl,rfl⟩ := execution.eq_of_call (summary heap left right execution.1)
  simp [Heap.cost,Heap.tick]
#print axioms every_execution
end FinalProof

namespace PrefixProof
open Algo2LeanCore Algo2LeanGenerated Algo.main Algo.main.Algo2LeanGenerated
/-- The final caller can stop while the first backend is still executing. -/
theorem interior_prefix (heap : Heap) (left right : ObjectRef)
    (valid : run.ValidInput heap (left,right)) :
    ∃ state, Reaches Step (run.initial heap (left,right)) state ∧
      state.heap = heap.tick "left" 2 := by
  apply Exists.intro
  case h =>
    constructor
    · apply Reaches.prepend (Step.run_pc4 _ _ [])
      apply Reaches.prepend (Step.run_pc3 _ _ [])
      apply Reaches.prepend (Step.run_pc2 _ _ [])
      apply Reaches.prepend (Step.import_4_use_partial_0 _ _ _ _ _ _
        (Algo.partial.Algo2LeanGenerated.Step.partially_bound_pc4 _ _ []))
      apply Reaches.prepend (Step.import_4_use_partial_0 _ _ _ _ _ _
        (Algo.partial.Algo2LeanGenerated.Step.partially_bound_pc3 _ _ []))
      apply Reaches.prepend (Step.import_4_use_partial_0 _ _ _ _ _ _
        (Algo.partial.Algo2LeanGenerated.Step.partially_bound_pc2 _ _ []))
      apply Reaches.prepend (Step.import_4_use_partial_0 _ _ _ _ _ _
        (Algo.partial.Algo2LeanGenerated.Step.import_2_use_generic_0 _ _ _ _ _ _
          (Algo.generic.Algo2LeanGenerated.Step.combine_pc10 _ _ [])))
      apply Reaches.prepend (Step.import_4_use_partial_0 _ _ _ _ _ _
        (Algo.partial.Algo2LeanGenerated.Step.import_2_use_generic_0 _ _ _ _ _ _
          (Algo.generic.Algo2LeanGenerated.Step.combine_pc9 _ _ [] (by
            simpa [Algo.generic.Algo2LeanGenerated.is__a2l_import_0_Left,
            Algo.partial.use_generic_0,Algo.partial.LeftBox_as_Left] using valid.1))))
      apply Reaches.prepend (Step.import_4_use_partial_0 _ _ _ _ _ _
        (Algo.partial.Algo2LeanGenerated.Step.import_2_use_generic_0 _ _ _ _ _ _
          (Algo.generic.Algo2LeanGenerated.Step.combine_pc8 _ _ [])))
      exact Reaches.single (Step.import_4_use_partial_0 _ _ _ _ _ _
        (Algo.partial.Algo2LeanGenerated.Step.import_2_use_generic_0 _ _ _ _ _ _
          (Algo.generic.Algo2LeanGenerated.Step.interface_Left _ _ _ _ _ _
            (InterfaceAdapter.Step.imported _ _ _ _ _ _
              (Algo.left.Algo2LeanGenerated.Step.LeftBox_get_pc3 _ _ [])))))
    · rfl
end PrefixProof
"""


class InterfaceNamespaceReviewTests(unittest.TestCase):
    def test_interface_cannot_overwrite_the_generated_machine_namespace(self):
        with tempfile.TemporaryDirectory() as root:
            with self.assertRaisesRegex(ProjectError, "reserved") as raised:
                compile_project("api", root=root, sources={
                    "api": "from algo2lean import Interface\n"
                           "class Algo2LeanGenerated(Interface):\n"
                           "    def get(self) -> Int: ...\n"})
            self.assertEqual(raised.exception.line, 2)
            self.assertTrue(raised.exception.file.endswith("api.algo"))


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class PartialLinkingAcceptanceTests(unittest.TestCase):
    def test_partial_binding_reuses_proofs_costs_and_real_prefixes(self):
        proofs = {"Algo.left.Analysis": LEFT_PROOF,
                  "Algo.generic.Analysis": GENERIC_PROOF,
                  "Algo.partial.Analysis": PARTIAL_PROOF}
        with tempfile.TemporaryDirectory() as root:
            generic = compile_project("generic", root=root, sources=SOURCES)
            partial = compile_project("partial", root=root, sources=SOURCES)
            complete = compile_project("main", root=root, sources=SOURCES)
            self.assertEqual({slot.name for slot in generic.entry.dependencies}, {"Left", "Right"})
            self.assertEqual({slot.name for slot in partial.entry.dependencies}, {"Right"})
            self.assertFalse(complete.entry.dependencies)
            for original in (generic, partial):
                for attribute in ("lean", "points_lean", "facts_lean"):
                    self.assertEqual(getattr(original.entry, attribute),
                                     getattr(complete.modules[original.project.entry], attribute))
                checked = check_project(original, proof_sources=proofs, check_facts=True,
                    analysis_module="Algo." + original.project.entry + ".Analysis")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("warning", checked.output)
            checked = check_project(complete, analysis=MAIN_PROOF,
                                    proof_sources=proofs, check_facts=True)
            self.assertTrue(checked.ok, checked.output)
            self.assertNotIn("warning", checked.output)
            self.assertIn("depends on axioms: [propext, Quot.sound]", checked.output)
            # The final backend's implementation can change without changing the
            # generic or partially instantiated definitions/proof source. Its old
            # concrete cost proof must then be rejected, including on a warm cache.
            changed = dict(SOURCES, right=SOURCES["right"].replace(
                'tick("right", 3)', 'tick("right", 5)'))
            rebuilt = compile_project("main", root=root, sources=changed)
            self.assertEqual(partial.entry.lean, rebuilt.modules["partial"].lean)
            stale = check_project(rebuilt, analysis=MAIN_PROOF,
                                  proof_sources=proofs, check_facts=True)
            self.assertFalse(stale.ok, "A changed concrete charge must invalidate its old cost proof")
            self.assertIn("Algo/main/Analysis.lean:", stale.output)


if __name__ == "__main__":
    unittest.main()
