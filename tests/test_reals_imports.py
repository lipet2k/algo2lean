"""Reuse independently checked Real and Std-only contracts across module boundaries."""

from pathlib import Path
import shutil
import tempfile
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "tests/proofs"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean").is_file())

SOURCES = {
    "halves": "def half(x: Real) -> Real:\n    return x / 2\n",
    "scale": "from halves import half\ndef scale(n: Int) -> Real:\n    return half(n)\n",
    "integer": """def increment(values: Seq, index: Int) -> Int:
    values[index] = values[index] + 1
    tick("work")
    return values[index]
""",
    "realclient": """from integer import increment
def preserve(data: Seq[Real], values: Seq, index: Int) -> Real:
    increment(values, index)
    return data[0]
""",
}


def proof(name):
    return (PROOFS / ("reals_import_" + name + ".lean")).read_text(encoding="utf-8")


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class IntegerContractTests(unittest.TestCase):
    def test_integer_contract_checks_without_mathlib(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-integer-contract-") as directory:
            project = compile_project("integer", root=directory, sources=SOURCES)
            self.assertNotIn("Algo2LeanReal", project.entry.lean)
            source = proof("integer")
            self.assertNotIn("Algo2LeanReal", source)
            checked = check_project(project, analysis=source,
                analysis_module="Algo.integer.Analysis", timeout=90)
            self.assertTrue(checked.ok, checked.output)


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class RealImportContractTests(unittest.TestCase):
    def test_real_contract_is_checked_independently_and_reused_by_integer_caller(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-real-contract-") as directory:
            helper = compile_project("halves", root=directory, sources=SOURCES)
            caller = compile_project("scale", root=directory, sources=SOURCES)
            self.assertEqual(helper.entry.lean, caller.modules["halves"].lean)
            helper_proof = proof("helper")
            checked = check_project(helper, analysis=helper_proof,
                analysis_module="Algo.halves.Analysis", timeout=120)
            self.assertTrue(checked.ok, checked.output)
            checked = check_project(caller, analysis=proof("client"),
                analysis_module="Algo.scale.Analysis",
                proof_sources={"Algo.halves.Analysis": helper_proof}, timeout=120)
            self.assertTrue(checked.ok, checked.output)

    def test_original_integer_contract_preserves_real_storage_and_clock_costs(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-real-preservation-") as directory:
            helper = compile_project("integer", root=directory, sources=SOURCES)
            caller = compile_project("realclient", root=directory, sources=SOURCES)
            self.assertEqual(helper.entry.lean, caller.modules["integer"].lean)
            checked = check_project(caller, analysis=proof("preservation"),
                analysis_module="Algo.realclient.Analysis",
                proof_sources={"Algo.integer.Analysis": proof("integer")}, timeout=120)
            self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
