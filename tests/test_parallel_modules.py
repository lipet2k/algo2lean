"""Imported parallel contracts retain real storage, costs, and access evidence."""

from pathlib import Path
import shutil
import unittest

from algo2lean import CompileError
from algo2lean.modular import compile_project
from algo2lean.parallel_modules import attach_parallel
from algo2lean.project_checker import check_project, project_lean_sources
from algo2lean.server import project_response
from editor.analysis_export import request
from scripts.check_parallel_examples import unexpected_axioms
from tests.test_analysis_export import unpack
from tests import test_probability_export as export_tests

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/parallel_imports"


class ParallelModuleInterfaceTests(unittest.TestCase):
    def test_optional_companions_and_source_facing_metadata(self):
        compiled = compile_project("driver", root=FIXTURE)
        client = compiled.modules["client"]
        self.assertNotIn("Algo2LeanLib.Parallel", client.lean)
        self.assertNotIn("def parallelNext", client.lean)
        self.assertIn("Algo.helper.Algo2LeanGenerated.parallelNext".replace("helper", "«helper»"),
                      client.parallel_lean)
        self.assertNotIn("private def choice_write", client.parallel_lean)
        self.assertNotIn("write_pc4", client.parallel_lean)
        metadata = project_response(compile_project("client", root=FIXTURE))
        self.assertEqual({item["name"] for item in metadata["functions"]}, {"pair", "serial"})
        for function in metadata["functions"]:
            parallel = [entry for entry in function["interface_entries"] if ".ParallelCall" in entry["name"]]
            self.assertEqual(len(parallel), 2)
            self.assertTrue(all(entry["file_kind"] == "parallel" for entry in parallel))

    def test_imported_random_function_cannot_be_a_parallel_child(self):
        with self.assertRaisesRegex(CompileError, "deterministic"):
            compile_project("main", root=FIXTURE, sources={
                "helper": "def sample() -> Int:\n    return randint(0, 2)\n",
                "main": "from helper import sample\ndef pair() -> Tuple[Int, Int]:\n"
                        "    return fork_join(sample(), sample())\n",
            })

    def test_ordinary_module_has_no_parallel_dependency_until_requested(self):
        compiled = compile_project("main", root=FIXTURE, sources={"main": "def f(n: Int) -> Int:\n    return n\n"})
        original = dict(compiled.files)
        self.assertFalse(compiled.entry.parallel_module)
        attach_parallel(compiled, force=True)
        for name, source in original.items():
            self.assertEqual(source, compiled.files[name])

    def test_labels_preserve_import_adapters_and_contracts(self):
        sources = {name: (FIXTURE / (name + ".algo")).read_text() for name in ("helper", "client", "driver")}
        original = compile_project("driver", root=FIXTURE, sources=sources)
        sources["client"] = sources["client"].replace("    return fork_join", "    # @children\n    return fork_join")
        labelled = compile_project("driver", root=FIXTURE, sources=sources)
        for name, source in original.files.items():
            if not name.endswith(".Points"):
                self.assertEqual(source, labelled.files[name])


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ParallelModuleLeanTests(unittest.TestCase):
    def test_imported_mutation_cost_and_access_contract_needs_only_std(self):
        compiled = compile_project("client", root=FIXTURE)
        sources = project_lean_sources(compiled, analysis_modules=["Algo.client.Analysis"])
        self.assertFalse(any("Mathlib" in source or "Probability" in source for source in sources.values()))
        checked = check_project(compiled, analysis_module="Algo.client.Analysis")
        self.assertTrue(checked.ok, checked.output)
        self.assertFalse(unexpected_axioms(checked.output), checked.output)

    def test_recursive_parallel_facades_and_further_import(self):
        compiled = compile_project("client", root=FIXTURE, sources={
            "left": "from right import leaf\ndef run(n: Int) -> Tuple[Int, Int]:\n"
                    "    return fork_join(leaf(n), leaf(n))\n",
            "right": "from left import run\ndef leaf(n: Int) -> Int:\n"
                     "    if n <= 0:\n        return 0\n"
                     "    pair = run(n - 1)\n    return pair[0]\n",
            "client": "from left import run\ndef call(n: Int) -> Tuple[Int, Int]:\n    return run(n)\n",
        })
        proof = """import Algo.client.Parallel
import Algo.left.Parallel
import Algo.right.Parallel
example {h n final value cost access}
    (call : Algo.client.call.ParallelCall h n final value cost access) :
    Algo.client.call.Call h n final value := call.call
#check Algo.left.run.ParallelCall.call
#check Algo.right.leaf.ParallelCall.call
"""
        checked = check_project(compiled, analysis=proof)
        self.assertTrue(checked.ok, checked.output)


@unittest.skipUnless(export_tests.MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ParallelProbabilityTests(unittest.TestCase):
    def test_two_imports_with_different_results_share_the_call_law_interface(self):
        compiled = compile_project("main", root=FIXTURE, sources={
            "number": "def increment(x: Int) -> Int:\n    return x + 1\n"
                      "def unrelated() -> Int:\n    return randint(0, 2)\n",
            "boolean": "def positive(x: Int) -> Bool:\n    return x > 0\n",
            "main": "from number import increment\nfrom boolean import positive\n"
                    "def pair(x: Int) -> Tuple[Int, Bool]:\n"
                    "    return fork_join(increment(x), positive(x))\n",
        })
        proof = """import Algo.main.Parallel
import Algo.main.Probability
example {heap input final output cost access}
    (parallel : Algo.main.pair.ParallelCall heap input final output cost access) :
    Algo.main.pair.HasLaw heap input (PMF.pure (final, output)) :=
  parallel.call.hasLaw
"""
        checked = check_project(compiled, analysis=proof, timeout=180)
        self.assertTrue(checked.ok, checked.output)

    def test_randomized_caller_reuses_parallel_contract_and_counter_effects(self):
        compiled = compile_project("driver", root=FIXTURE)
        checked = check_project(compiled, analysis_module="Algo.driver.Analysis", timeout=180)
        self.assertTrue(checked.ok, checked.output)
        self.assertFalse(unexpected_axioms(checked.output), checked.output)

    def test_export_rebuilds_all_three_contract_layers(self):
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
        self.assertEqual(files["Algo2LeanLib/ParallelModules.lean"],
                         (ROOT / "Algo2LeanLib/ParallelModules.lean").read_bytes())
        export_tests.ProbabilityExportBuildTests.build(self, files, "Algo/driver/Analysis.olean")


if __name__ == "__main__":
    unittest.main()
