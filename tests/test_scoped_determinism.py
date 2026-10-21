"""Determinism follows reachable calls, not the source file containing them."""

from pathlib import Path
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from algo2lean.server import project_response
from algo2lean.compiler import compile_source
from algo2lean.analysis import check_analysis
from algo2lean.module_facts import emit_facts
from tests.test_deterministic_probability import FIXTURE, RECURSIVE
from tests.test_probability_export import MATHLIB_READY


MIXED = {
    "helper": """def increment(n: Int) -> Int:
    return n + 1
def sample() -> Int:
    return randint(0, 2)
def indirectly_random() -> Int:
    return sample()
""",
    "client": """from helper import increment, sample
def twice(n: Int) -> Int:
    return increment(increment(n))
def random_client() -> Int:
    return sample()
""",
}


class ScopedDeterminismTests(unittest.TestCase):
    def test_only_transitively_deterministic_functions_have_adapters(self):
        compiled = compile_project("client", root=FIXTURE, sources=MIXED)
        self.assertEqual(compiled.modules["helper"].deterministic_functions, {"increment"})
        self.assertEqual(compiled.entry.deterministic_functions, {"twice"})
        for module in compiled.modules.values():
            for name in module.functions:
                self.assertEqual("theorem " + name + ".Call.hasLaw" in module.probability_lean,
                                 name in module.deterministic_functions)
        metadata = project_response(compiled)
        for function in metadata["functions"]:
            names = {entry["name"] for entry in function["interface_entries"]}
            self.assertEqual(function["name"] + ".Call.hasLaw" in names, function["name"] == "twice")

    def test_labels_do_not_change_the_certificate(self):
        original = compile_project("client", root=FIXTURE, sources=MIXED)
        labelled = dict(MIXED)
        labelled["helper"] = labelled["helper"].replace("    return n + 1", "    # @incremented\n    return n + 1")
        changed = compile_project("client", root=FIXTURE, sources=labelled)
        for name, source in original.files.items():
            if not name.endswith(".Points"):
                self.assertEqual(source, changed.files[name])


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ScopedDeterminismLeanTests(unittest.TestCase):
    def test_single_file_uses_the_same_adapter(self):
        for namespace in (None, "Mixed"):
            compiled = compile_source(MIXED["helper"], filename="helper.algo", namespace=namespace)
            prefix = "Mixed." if namespace else ""
            proof = "import HelperGeneratedProbability\nexample {h n final value} " \
                    "(call : " + prefix + "increment.Call h n final value) :\n    " + prefix + \
                    "increment.HasLaw h n (PMF.pure (final, value)) :=\n  " + prefix + \
                    "increment.Call.hasLaw call\n"
            checked = check_analysis(compiled.lean, proof, compiled.module,
                                     probability_lean=compiled.probability_lean, timeout=180)
            self.assertTrue(checked.ok, checked.output)

    def test_kernel_rejects_a_falsely_admitted_random_function(self):
        compiled = compile_project("helper", root=FIXTURE, sources=MIXED)
        compiled.entry.deterministic_functions.add("sample")
        compiled.entry.facts_lean = emit_facts(compiled.entry)
        checked = check_project(compiled, analysis="import Algo.helper.Facts\n")
        self.assertFalse(checked.ok, "The call graph is a proposal, not a trusted determinism axiom.")

    def test_imported_mixed_module_and_transitive_rejection(self):
        compiled = compile_project("client", root=FIXTURE, sources=MIXED)
        proof = """import Algo.client.Probability
example {heap input final output} (call : Algo.client.twice.Call heap input final output) :
    Algo.client.twice.HasLaw heap input (PMF.pure (final, output)) :=
  Algo.client.twice.Call.hasLaw call
example {heap input final output expectedHeap expected}
    (run : Algo.client.twice.Run heap input final output)
    (call : Algo.client.twice.Call heap input expectedHeap expected) :
    final = expectedHeap ∧ output = expected := Algo.client.twice.Run.eq_of_call run call
"""
        checked = check_project(compiled, analysis=proof, timeout=180)
        self.assertTrue(checked.ok, checked.output)

    def test_original_mutation_and_cost_proofs_survive_unrelated_randomness(self):
        sources = {name: (FIXTURE / (name + ".algo")).read_text() for name in ("helper", "client", "driver")}
        sources["helper"] += "\ndef unrelated() -> Int:\n    return randint(0, 9)\n"
        compiled = compile_project("driver", root=FIXTURE, sources=sources)
        proof = """import Algo.helper.Probability
import Algo.helper.Analysis
example (heap : Algo2LeanGenerated.Heap) (a : Algo2LeanGenerated.SeqRef)
    (valid : a < heap.nextRef) :
    Algo.helper.bump.HasLaw heap a
      (PMF.pure (HelperAnalysis.updated heap a, heap.read a 0 + 1)) :=
  Algo.helper.bump.Call.hasLaw (HelperAnalysis.bump_call heap a valid)
"""
        checked = check_project(compiled, analysis=proof, timeout=180)
        self.assertTrue(checked.ok, checked.output)

    def test_recursive_mixed_group_and_external_caller(self):
        sources = dict(RECURSIVE)
        sources["left"] += "\ndef unrelated() -> Int:\n    return randint(0, 9)\n"
        sources["client"] = "from right import recurse\ndef run(n: Int) -> Int:\n    return recurse(n)\n"
        compiled = compile_project("client", root=FIXTURE, sources=sources)
        self.assertEqual(compiled.modules["left"].deterministic_functions, {"count"})
        proof = """import Algo.client.Probability
import Algo.left.Probability
import Algo.right.Probability
example {heap input final output} (call : Algo.right.recurse.Call heap input final output) :
    Algo.right.recurse.HasLaw heap input (PMF.pure (final, output)) :=
  Algo.right.recurse.Call.hasLaw call
example {heap input final output} (call : Algo.client.run.Call heap input final output) :
    Algo.client.run.HasLaw heap input (PMF.pure (final, output)) :=
  Algo.client.run.Call.hasLaw call
"""
        checked = check_project(compiled, analysis=proof, timeout=180)
        self.assertTrue(checked.ok, checked.output)

    def test_shared_recursive_wrapper_can_end_with_an_unsafe_facade(self):
        sources = {
            "left": "from right import sample\ndef identity(n: Int) -> Int:\n    return n\n"
                    "def indirect() -> Int:\n    return sample()\n",
            "right": "from left import identity\ndef sample() -> Int:\n"
                     "    return identity(randint(0, 2))\n",
            "client": "from left import identity\nfrom right import sample\n"
                      "def safe(n: Int) -> Int:\n    return identity(n)\n"
                      "def unsafe() -> Int:\n    return sample()\n",
        }
        compiled = compile_project("client", root=FIXTURE, sources=sources)
        self.assertFalse(compiled.modules["right"].facts_module)
        proof = """import Algo.client.Probability
example {h n final value} (call : Algo.client.safe.Call h n final value) :
    Algo.client.safe.HasLaw h n (PMF.pure (final, value)) := call.hasLaw
"""
        checked = check_project(compiled, analysis=proof, timeout=180)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
