"""Finite container contracts remain reusable through independent imports."""

from pathlib import Path
import shutil
import tempfile
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "tests/proofs"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())

HELPER = """\
def put(values: Dict[Int, Int], key: Int, value: Int) -> None:
    values[key] = value
"""

CLIENT = """\
from helper import put

def run(values: Dict[Int, Int], key: Int, value: Int) -> Int:
    put(values, key, value)
    return values[key]
"""

SAFETY = """\
def read(values: Dict[Int, Int], key: Int) -> Int:
    return values[key]

def remove(values: Dict[Int, Int], key: Int) -> None:
    del values[key]

def clone(values: Dict[Int, Int]) -> Dict[Int, Int]:
    return copy(values)
"""


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class FiniteCollectionsImportTests(unittest.TestCase):
    def test_mutually_recursive_modules_share_finite_collection_types(self):
        sources = {
            "first": """from second import visit
def mark(n: Int, seen: Set[Int], values: Dict[Int, Int]) -> Int:
    if n <= 0:
        return len(seen) + len(values)
    seen.add(n)
    values[n] = n
    return visit(n - 1, seen, values)
""",
            "second": """from first import mark
def visit(n: Int, seen: Set[Int], values: Dict[Int, Int]) -> Int:
    if n <= 0:
        return values.get(n, 0)
    seen.discard(n)
    return mark(n - 1, seen, values)
""",
        }
        with tempfile.TemporaryDirectory(prefix="algo2lean-finite-cycle-") as directory:
            first = compile_project("first", root=directory, sources=sources)
            second = compile_project("second", root=directory, sources=sources)
            self.assertEqual(first.files, second.files)
            checked = check_project(first, check_facts=True, timeout=90)
            self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
    def test_imported_random_dictionary_keeps_checked_probability_semantics(self):
        sources = {
            "helper": """def draw() -> Dict[Int, Int]:
    return {0: randint(0, 2)}
""",
            "client": """from helper import draw
def sample() -> Bool:
    data = copy(draw())
    seen = {randint(0, 2)}
    seen.add(data[0])
    return 1 in seen
""",
        }
        with tempfile.TemporaryDirectory(prefix="algo2lean-finite-probability-") as directory:
            project = compile_project("client", root=directory, sources=sources)
            checked = check_project(project, analysis="import Algo.client.Probability\n",
                                    analysis_module="FiniteProbabilityTest", timeout=120)
            self.assertTrue(checked.ok, checked.output)

    def test_missing_keys_fail_and_copy_returns_fresh_contents(self):
        proof = (PROOFS / "finite_collection_imports_safety.lean").read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory(prefix="algo2lean-finite-safety-") as directory:
            project = compile_project("safety", root=directory, sources={"safety": SAFETY})
            checked = check_project(project, analysis=proof,
                                    analysis_module="Algo.safety.Analysis", timeout=90)
            self.assertTrue(checked.ok, checked.output)

    def test_imported_dictionary_call_contract_is_reused_unchanged(self):
        helper_proof = (PROOFS / "finite_collection_imports_helper.lean").read_text(encoding="utf-8")
        client_proof = (PROOFS / "finite_collection_imports_client.lean").read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory(prefix="algo2lean-finite-import-") as directory:
            sources = {"helper": HELPER, "client": CLIENT}
            helper = compile_project("helper", root=directory, sources=sources)
            client = compile_project("client", root=directory, sources=sources)
            self.assertEqual(helper.entry.lean, client.modules["helper"].lean)
            independent = check_project(helper, analysis=helper_proof,
                                        analysis_module="Algo.helper.Analysis", timeout=90)
            self.assertTrue(independent.ok, independent.output)
            combined = check_project(client, analysis=client_proof,
                                     analysis_module="Algo.client.Analysis",
                                     proof_sources={"Algo.helper.Analysis": helper_proof}, timeout=90)
            self.assertTrue(combined.ok, combined.output)


if __name__ == "__main__":
    unittest.main()
