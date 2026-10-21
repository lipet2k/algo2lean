"""Matrix contracts compose through repeated source calls and portable exports."""

import io
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import zipfile

from algo2lean.checker import after_import_header, redirect_imports
from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from algo2lean.server import project_archive
from scripts.check_chapter4_proofs import audit_assumptions


ROOT = Path(__file__).resolve().parents[1]
CASES = (
    ("matrix_multiply", "matrix_multiply", "MatrixMultiplyAnalysis",
     "n", "n", "MatrixMultiplyAnalysis.product {a} {b} n", "MatrixMultiplyAnalysis.costs n"),
    ("matrix_recursive", "matrix_recursive", "MatrixRecursiveAnalysis",
     "depth", "(2^depth)", "MatrixRecursiveAnalysis.matrixProduct {a} {b} (2^depth)",
     "MatrixRecursiveAnalysis.costs depth"),
    ("matrix_strassen", "strassen", "MatrixStrassenVerified",
     "depth", "(2^depth)", "StrassenValues.strassenValue depth {a} {b}",
     "MatrixStrassenExecution.costs depth"),
)


def repeated_call_project(root, case):
    module, function, namespace, parameter, size, model, costs = case
    source = (ROOT / "examples" / (module + ".algo")).read_text()
    caller = (
        f"from {module} import {function}\n"
        "def twice(a: Seq[Seq[Int]], b: Seq[Seq[Int]], n: Int) -> Seq[Seq[Int]]:\n"
        f"    c = {function}(a, b, n)\n"
        f"    return {function}(c, b, n)\n"
    )
    compilation = compile_project("client", root=root, sources={module: source, "client": caller})
    standalone = compile_source(source, filename=module + ".algo")
    analysis = (ROOT / "examples/analysis" / (module + ".lean")).read_text()
    # Only the import header and opening namespace change. Reuse every existing
    # definition and proof body without modifying it for this caller.
    analysis, redirected = redirect_imports(analysis, {
        standalone.module: f"Algo.{module}.Generated",
        standalone.points_module: f"Algo.{module}.Points",
    })
    assert redirected
    position = after_import_header(analysis)
    analysis = (analysis[:position] + f"\nopen Algo.{module} Algo.{module}.Algo2LeanGenerated\n"
                + analysis[position:])
    first_product = "(" + model.format(a="av", b="bv") + ")"
    twice_product = model.format(a=first_product, b="bv")
    proof = f"""import Algo.{module}.Analysis
import Algo.client.Generated

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
open Algo.client Algo.client.Algo2LeanGenerated

namespace MatrixCaller

/-- Both calls reuse the same unchanged contract, with the real intermediate
heap. Correctness, fresh output rows and all counter increments compose. -/
theorem reused (heap : Heap) (a b : CollectionRef) (av bv : Values) ({parameter} : Nat)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result,
      twice.Call heap (a, b, ({size} : Nat)) after result ∧
      Stored after result ({twice_product}) ∧ Extends heap after ∧
      FreshRows heap after result {size} ∧
      heap.Increments after (Clocks.add ({costs}) ({costs})) := by
  obtain ⟨middle, c, first, storedC, frame1, _, _, _, cost1⟩ :=
    {namespace}.call heap a b av bv {parameter} sa sb
  obtain ⟨after, result, second, stored, frame2, _, _, fresh, cost2⟩ :=
    {namespace}.call middle c b {first_product} bv {parameter} storedC (sb.mono frame1)
  refine ⟨after, result, ⟨⟨sa.1, sb.1⟩, ?_⟩, stored, frame1.trans frame2,
    fresh.before_mono frame1.nextRef, cost1.trans cost2⟩
  intro stack
  apply Reaches.prepend (Step.twice_pc10 ..)
  apply Reaches.prepend (Step.twice_pc9 ..)
  apply Reaches.prepend (Step.twice_pc8 ..)
  apply Reaches.prepend (Step.twice_pc7 ..)
  apply (ModuleCall.summary import_0_simulates _ stack first.2).trans
  apply Reaches.prepend (Step.twice_pc6 ..)
  apply Reaches.prepend (Step.twice_pc5 ..)
  apply Reaches.prepend (Step.twice_pc4 ..)
  apply Reaches.prepend (Step.twice_pc3 ..)
  apply Reaches.prepend (Step.twice_pc2 ..)
  apply (ModuleCall.summary import_0_simulates _ stack second.2).trans
  exact Reaches.single (Step.twice_pc1 _ _ _ stored.1)

end MatrixCaller
#print axioms {namespace}.call
#print axioms {namespace}.correctness_and_running_time
#print axioms MatrixCaller.reused
"""
    proofs = {f"Algo.{module}.Analysis": analysis, "Algo.client.Analysis": proof}
    return compilation, proofs


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class MatrixContractTests(unittest.TestCase):
    def test_repeated_imported_calls_reuse_correctness_storage_and_costs(self):
        for case in CASES:
            with self.subTest(algorithm=case[0]), tempfile.TemporaryDirectory() as directory:
                compilation, proofs = repeated_call_project(Path(directory), case)
                result = check_project(compilation, proof_sources=proofs,
                                       analysis_module="Algo.client.Analysis", timeout=300)
                self.assertTrue(result.ok, result.output)
                targets = (case[2] + ".call", case[2] + ".correctness_and_running_time",
                           "MatrixCaller.reused")
                self.assertIsNone(audit_assumptions(result.output, targets), result.output)

    @unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
    def test_exported_project_reuses_all_matrix_libraries_without_mathlib(self):
        source = "def identity(x: Int) -> Int:\n    return x\n"
        proof = """import Algo.main.Generated
import Algo2LeanExamples.MatrixMultiply
import Algo2LeanExamples.MatrixRecursive
import Algo2LeanExamples.MatrixStrassen

example := MatrixMultiplyAnalysis.call
example := MatrixRecursiveAnalysis.call
example := MatrixStrassenVerified.call
#print axioms MatrixMultiplyAnalysis.correctness_and_running_time
#print axioms MatrixRecursiveAnalysis.correctness_and_running_time
#print axioms MatrixStrassenVerified.correctness_and_running_time
"""
        with tempfile.TemporaryDirectory(prefix="algo2lean-matrix-export-") as directory:
            root = Path(directory)
            compilation = compile_project("main", root=root, sources={"main": source})
            archive = project_archive(compilation, {"Algo.main.Analysis": proof})
            with zipfile.ZipFile(io.BytesIO(archive)) as zipped:
                self.assertNotIn("EXPORT_DIAGNOSTICS.txt", zipped.namelist())
                self.assertIn("Algo2LeanLib/MatrixHeap.lean", zipped.namelist())
                self.assertNotIn(b"mathlib", zipped.read("lakefile.toml").lower())
                zipped.extractall(root)
            environment = dict(os.environ)
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            result = subprocess.run([shutil.which("lake"), "build", "Algo.main.Analysis"],
                                    cwd=root, env=environment, capture_output=True,
                                    text=True, timeout=300)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            self.assertTrue((root / ".lake/build/lib/lean/Algo/main/Analysis.olean").is_file())
            self.assertNotIn("declaration uses 'sorry'", output)
