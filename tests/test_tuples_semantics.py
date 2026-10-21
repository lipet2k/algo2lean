"""Lean checks immutable tuple storage, shared references, and reusable calls."""

from pathlib import Path
import shutil
import tempfile
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.checker import check_lean
from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from tests.test_lean import constructor_tactic


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "tests/proofs"

HELPER_SOURCE = """\
def adjacent(value: Int) -> Tuple[Int, Int]:
    return value, value + 1
"""

CLIENT_SOURCE = """\
from helper import adjacent

def gap(value: Int) -> Int:
    first, second = adjacent(value)
    return second - first
"""

HELPER_PROOF = """\
import Algo.helper.Generated
open Algo2LeanCore Algo2LeanGenerated

namespace TupleHelper

-- A reusable source-facing contract retains the caller's actual heap.
theorem adjacent_call (heap : Heap) (value : Int) :
    Algo.helper.adjacent.Call heap value heap (value, value + 1) := by
  open Algo.helper.Algo2LeanGenerated in
    refine ⟨trivial, ?_⟩
    intro caller
    apply Reaches.prepend (Step.adjacent_pc2 _ _ caller)
    exact Reaches.single (Step.adjacent_pc1 _ _ caller)

end TupleHelper
"""

CLIENT_PROOF = """\
import Algo.client.Generated
import Algo.helper.Analysis
open Algo2LeanCore Algo2LeanGenerated

namespace TupleClient

-- Only the caller's transitions are inspected; the helper proof is reused.
theorem gap_call (heap : Heap) (value : Int) :
    Algo.client.gap.Call heap value heap 1 := by
  have call : Algo.client.gap.Call heap value heap ((value + 1) - value) := by
    open Algo.client.Algo2LeanGenerated in
      refine ⟨trivial, ?_⟩
      intro caller
      apply Reaches.prepend (Step.gap_pc6 _ _ caller)
      apply Reaches.prepend (Step.gap_pc5 _ _ caller)
      apply (ModuleCall.summary import_0_simulates _ caller
        (TupleHelper.adjacent_call heap value).2).trans
      apply Reaches.prepend (Step.gap_pc4 _ _ caller)
      apply Reaches.prepend (Step.gap_pc3 _ _ caller)
      apply Reaches.prepend (Step.gap_pc2 _ _ caller)
      exact Reaches.single (Step.gap_pc1 _ _ caller)
  have difference : (value + 1) - value = 1 := by omega
  simpa only [difference] using call

end TupleClient
"""


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class TupleSemanticsTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
    def test_downloaded_tuple_analysis_builds_with_its_own_shared_library(self):
        from editor.analysis_export import request
        from tests.test_analysis_export import AnalysisExportBuildTests, payload, unpack
        source = "def pair(value: Int) -> Tuple[Int, Bool]:\n    return value, True\n"
        proof = ("import TupleDownloadGenerated\n"
                 "example : Int → (Int × Bool) → Prop := pair.Returns\n")
        files = unpack(request("/api/analysis-export", payload(
            source=source, filename="tuple_download.algo", analysis=proof)))
        self.assertIn("Algo2LeanLib/Tuple.lean", files)
        AnalysisExportBuildTests.build(self, files, Path("Proof.lean"))

    def test_storage_aliases_and_effectful_unpacking(self):
        source = (PROOFS / "tuples.algo").read_text(encoding="utf-8")
        generated = compile_source(source, filename="tuples.algo", module="TuplesGenerated")
        proof = "import TuplesGenerated\n" + constructor_tactic(generated.lean)
        proof += (PROOFS / "tuples.lean").read_text(encoding="utf-8")
        checked = check_analysis(generated.lean, proof, generated.module, timeout=120)
        self.assertTrue(checked.ok, checked.output)

    def test_codec_shape_and_nested_nullable_roundtrips(self):
        checked = check_lean((PROOFS / "tuples_codec.lean").read_text(encoding="utf-8"),
                             module="TupleCodecTest", timeout=60)
        self.assertTrue(checked.ok, checked.output)

    def test_imported_tuple_contract_is_reused_unchanged(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-tuple-import-") as directory:
            sources = {"helper": HELPER_SOURCE, "client": CLIENT_SOURCE}
            helper = compile_project("helper", root=directory, sources=sources)
            client = compile_project("client", root=directory, sources=sources)
            self.assertEqual(helper.entry.lean, client.modules["helper"].lean)
            independent = check_project(helper, analysis=HELPER_PROOF,
                                        analysis_module="Algo.helper.Analysis", timeout=60)
            self.assertTrue(independent.ok, independent.output)
            combined = check_project(client, analysis=CLIENT_PROOF,
                                     analysis_module="Algo.client.Analysis",
                                     proof_sources={"Algo.helper.Analysis": HELPER_PROOF}, timeout=60)
            self.assertTrue(combined.ok, combined.output)


if __name__ == "__main__":
    unittest.main()
