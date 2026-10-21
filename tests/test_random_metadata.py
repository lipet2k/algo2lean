"""The probability panel describes only emitted, accurately typed declarations."""

import tempfile
import unittest
from unittest.mock import patch

from algo2lean.analysis import check_analysis
from algo2lean.checker import LeanSetupError
from algo2lean.compiler import CompileError, compile_source
from algo2lean.modular import compile_project
from algo2lean.probability_checker import _installed_dependencies
from algo2lean.public_names import PROBABILITY_MEMBERS
from algo2lean.server import project_response
from tests.test_interface_metadata import entries, signature_checks


SOURCE = '''class Box:
    value: Int
    def __init__(self, value: Int) -> None:
        self.value = value
    def draw(self) -> Int:
        return randint(self.value, self.value + 1)

def choose(values: Seq) -> Seq:
    # @sample
    values[0] = randint(0, 2)
    return values

def object_identity(value: Box | None) -> Box | None:
    return value

def items(values: Seq[Box | None]) -> Seq[Box | None]:
    return values
'''
PURE_FUNCTIONS = {"Box___init__", "Box", "object_identity", "items"}


class RandomMetadataTests(unittest.TestCase):
    def test_companion_entries_have_exact_arities_and_raw_or_value_types(self):
        compiled = compile_source(SOURCE)
        functions = {function["name"]: entries(function) for function in compiled.functions}
        choose = functions["choose"]
        self.assertEqual(choose["choose.outcome"]["signature"],
                         "choose.outcome : Configuration → Option (Heap × (SeqRef))")
        self.assertEqual(choose["choose.law"]["signature"],
                         "choose.law (heap : Heap) (input : SeqRef) : MeasureTheory.Measure (Algo2LeanProbability.Run Configuration)")
        self.assertEqual(choose["choose.returnProbability"]["signature"],
                         "choose.returnProbability (heap : Heap) (input : SeqRef) (post : Heap → SeqRef → Prop) : ENNReal")
        self.assertEqual(choose["choose.outputProbability"]["signature"],
                         "choose.outputProbability (input : Seq) (output : Seq) : ENNReal")
        self.assertEqual(choose["choose.terminationProbability"]["signature"],
                         "choose.terminationProbability (heap : Heap) (input : SeqRef) : ENNReal")
        self.assertEqual(choose["choose.expectedCost"]["signature"],
                         "choose.expectedCost (heap : Heap) (input : SeqRef) (clock : String) : ENNReal")
        self.assertEqual(choose["choose.costProbability"]["signature"],
                         "choose.costProbability (heap : Heap) (input : SeqRef) (clock : String) (threshold : ENNReal) : ENNReal")
        self.assertEqual(choose["choose.HasLaw"]["signature"],
                         "choose.HasLaw (heap : Heap) (input : SeqRef) (distribution : PMF (Heap × (SeqRef))) : Prop")
        self.assertEqual(choose["choose.expectedReturn"]["signature"],
                         "choose.expectedReturn (heap : Heap) (input : SeqRef) (reward : Heap → SeqRef → ENNReal) : ENNReal")
        for function in compiled.functions:
            probabilities = [entry for entry in function["interface_entries"] if entry["category"] == "probability"]
            members = PROBABILITY_MEMBERS + (
                ("Call.hasLaw", "Call.expectedReturn") if function["name"] in PURE_FUNCTIONS else ())
            self.assertEqual({entry["name"] for entry in probabilities},
                             {function["lean_name"] + "." + member for member in members})
            self.assertTrue(all(entry["file_kind"] == "probability" for entry in probabilities))
            self.assertTrue(all(entry["meaning"] and all(arg["meaning"] for arg in entry["arguments"])
                                for entry in probabilities))
        self.assertIn("Box.draw.law", functions["Box_draw"])
        self.assertIn("Box.law", functions["Box"])
        self.assertIn("Heap ×", functions["items"]["items.outputProbability"]["signature"])
        self.assertIn("possible", choose["choose.Returns"]["meaning"])
        self.assertIn("possible", choose["choose.Call"]["meaning"])
        self.assertIn("almost-sure", choose["choose.Call"]["meaning"])
        self.assertIn("infinite", choose["choose.expectedCost"]["meaning"])

    def test_metadata_and_labels_do_not_change_general_or_probability_definitions(self):
        compiled = compile_source(SOURCE)
        with patch("algo2lean.public_names.interface_metadata", return_value={}):
            stripped = compile_source(SOURCE)
        revised = compile_source(SOURCE.replace("# @sample", "# @draw"))
        for other in (stripped, revised):
            self.assertEqual(compiled.lean, other.lean)
            self.assertEqual(compiled.probability_lean, other.probability_lean)
        self.assertNotEqual(compiled.points_lean, revised.points_lean)
        for old, new in zip(compiled.functions, revised.functions):
            self.assertEqual([entry for entry in old["interface_entries"] if entry["file_kind"] == "probability"],
                             [entry for entry in new["interface_entries"] if entry["file_kind"] == "probability"])

    def test_unavailable_companions_do_not_advertise_probability_entries(self):
        deterministic = compile_source("def f() -> Int:\n    return 0\n").functions[0]
        self.assertFalse(any(entry["category"] == "probability" for entry in deterministic["interface_entries"]))
        self.assertEqual(entries(deterministic)["f.Returns"]["meaning"], "The function completes with this returned value.")
        sources = {
            "api": "from algo2lean import Interface\nclass Source(Interface):\n    def get(self) -> Int: ...\n",
            "main": "from api import Source\ndef sample(source: Source) -> Int:\n    return source.get() + randint(0, 2)\n",
        }
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project("main", root=directory, sources=sources)
        response = project_response(compiled)
        self.assertTrue(response["randomized"])
        self.assertFalse(response["probability_lean"])
        self.assertFalse(any(entry["category"] == "probability" for function in response["functions"]
                             for entry in function["interface_entries"]))
        self.assertIn("possible", entries(response["functions"][0])["sample.Call"]["meaning"])

    def test_project_probability_entries_point_to_the_companion(self):
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project("main", root=directory, sources={"main": SOURCE})
        response = project_response(compiled)
        for function in response["functions"]:
            probabilities = [entry for entry in function["interface_entries"] if entry["file_kind"] == "probability"]
            self.assertEqual(len(probabilities), len(PROBABILITY_MEMBERS) +
                             (2 if function["name"] in PURE_FUNCTIONS else 0))
            self.assertTrue(all(entry["category"] == "probability" for entry in probabilities))

    def test_probability_names_are_checked_only_when_the_companion_is_emitted(self):
        for name in PROBABILITY_MEMBERS:
            source = "class Box:\n    def " + name + "(self) -> Int:\n        return 0\n"
            with self.subTest(name=name):
                compile_source(source)
                with self.assertRaisesRegex(CompileError, "probability declaration"):
                    compile_source(source + "\ndef sample() -> Int:\n    return randint(0, 2)\n")

    def test_probability_signatures_and_named_arguments_check_in_lean(self):
        try:
            _installed_dependencies({"Analysis": "import Algo2LeanProbability.Observations\n"})
        except LeanSetupError as error:
            self.skipTest(str(error))
        compiled = compile_source("def roll(limit: Int) -> Int:\n    return randint(0, limit)\n", module="RandomMetadata")
        functions = [{**function, "interface_entries": [entry for entry in function["interface_entries"]
                                                       if entry["file_kind"] == "probability"]}
                     for function in compiled.functions]
        analysis = ("import RandomMetadataProbability\nnoncomputable section\n"
                    "attribute [local instance] Classical.propDecidable\n"
                    "open Algo2LeanGenerated\n" + signature_checks(functions))
        checked = check_analysis(compiled.lean, analysis, compiled.module,
                                 points_lean=compiled.points_lean, probability_lean=compiled.probability_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)
        mixed = compile_source(SOURCE, module="MixedMetadata")
        functions = [{**function, "interface_entries": [entry for entry in function["interface_entries"]
                                                       if entry["file_kind"] == "probability"]}
                     for function in mixed.functions]
        analysis = ("import MixedMetadataProbability\nnoncomputable section\n"
                    "attribute [local instance] Classical.propDecidable\n"
                    "open Algo2LeanGenerated\n" + signature_checks(functions))
        checked = check_analysis(mixed.lean, analysis, mixed.module,
                                 probability_lean=mixed.probability_lean, timeout=180)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
