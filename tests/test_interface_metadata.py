"""The interface browser describes exactly the declarations Lean accepts."""

import json
import shutil
import tempfile
import unittest
from unittest.mock import patch

from algo2lean.checker import check_lean
from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from algo2lean.server import project_response


SOURCE = '''class Box:
    value: Int
    def __init__(self, value: Int) -> None:
        self.value = value
    def get(self) -> Int:
        return self.value

def scalar(value: Int) -> Int:
    tick("work")
    return value + 1

def same(values: Seq) -> Seq:
    # @before
    values[0] = values[0]
    # @after
    return values

def object_identity(value: Box) -> Box:
    return value

def items(values: Seq[Box | None]) -> Seq[Box | None]:
    # @items
    return values

def empty() -> None:
    return

def lemma(theorem: Seq) -> Seq:
    # @by
    return theorem
'''


def entries(function):
    return {entry["name"]: entry for entry in function["interface_entries"]}


def signature_checks(functions):
    """Check displayed types and real named arguments, including implicit ones.

    Anonymous arrows (location predicates and local getters) remain unapplied;
    the displayed signature must retain their actual function type.
    """
    checks = []
    for function in functions:
        for entry in function["interface_entries"]:
            declaration = entry["signature"].removeprefix(entry["name"])
            arguments = ["(%s := %s)" % (arg["name"], arg["name"])
                         for arg in entry["arguments"] if not arg["anonymous"]]
            checks.append("example" + declaration + " := " + entry["name"] + " " + " ".join(arguments))
    return "\n".join(checks) + "\n"


class InterfaceMetadataTests(unittest.TestCase):
    def test_entries_group_real_declarations_and_deduplicate_observations(self):
        compiled = compile_source(SOURCE)
        functions = {function["name"]: function for function in compiled.functions}
        same = entries(functions["same"])
        self.assertEqual(len(same), len(functions["same"]["interface_entries"]))
        self.assertEqual([name for name in same if ".Local." in name], ["same.Local.values"])
        self.assertEqual([name for name in same if ".Element." in name], ["same.Element.values"])
        self.assertEqual(same["same.Call"]["file_kind"], "core")
        self.assertEqual(same["same.At.before"]["file_kind"], "points")
        self.assertEqual(same["same.At.before"]["category"], "location")
        point = functions["same"]["points"][0]
        self.assertEqual((same["same.At.before"]["line"], same["same.At.before"]["column"]),
                         (point["line"], point["column"]))
        self.assertEqual(same["same.Local.values"]["signature"],
                         "same.Local.values : Configuration → Option SeqRef")
        self.assertEqual(entries(functions["items"])["items.Element.values"]["signature"],
                         "items.Element.values (state : Configuration) (index : Int) : Option (Option Ref_Box)")
        self.assertIn("Box.get.Call", entries(functions["Box_get"]))
        self.assertIn("Box.Call", entries(functions["Box"]))
        self.assertIn("«lemma».At.«by»", entries(functions["lemma"]))
        self.assertTrue(all(entry["meaning"] and all(arg["meaning"] for arg in entry["arguments"])
                            for function in compiled.functions for entry in function["interface_entries"]))
        json.dumps(compiled.functions)

    def test_absent_cost_and_facts_apis_are_not_advertised(self):
        function = compile_source("def f() -> Int:\n    return 0\n").functions[0]
        names = entries(function)
        self.assertNotIn("f.ReturnsWithCost", names)
        self.assertNotIn("f.ReturnsWithCost.returns", names)
        self.assertNotIn("f.Returns.withCost", names)
        self.assertNotIn("f.Run.eq_of_call", names)
        self.assertEqual(names["f.ValidInput"]["signature"], "f.ValidInput (_h : Heap) (_input : Unit) : Prop")
        self.assertEqual(names["f.load"]["signature"], "f.load (_input : Unit) : Heap × (Unit)")

    def test_metadata_cannot_change_generated_lean_and_labels_only_change_points(self):
        original = compile_source(SOURCE)
        with patch("algo2lean.public_names.interface_metadata", return_value={}):
            without_metadata = compile_source(SOURCE)
        self.assertEqual(original.lean, without_metadata.lean)
        self.assertEqual(original.points_lean, without_metadata.points_lean)
        revised = compile_source(SOURCE.replace("# @before", "# @renamed"))
        self.assertEqual(original.lean, revised.lean)
        self.assertNotEqual(original.points_lean, revised.points_lean)
        for old, new in zip(original.functions, revised.functions):
            self.assertEqual([entry for entry in old["interface_entries"] if entry["file_kind"] == "core"],
                             [entry for entry in new["interface_entries"] if entry["file_kind"] == "core"])


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class InterfaceMetadataLeanTests(unittest.TestCase):
    def assert_checked(self, checked):
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)

    def test_every_standalone_signature_and_named_argument_checks_in_lean(self):
        for namespace in (None, "Wrapped"):
            with self.subTest(namespace=namespace):
                compiled = compile_source(SOURCE, filename="metadata.algo", namespace=namespace)
                proof = "\nopen Algo2LeanGenerated\n"
                if namespace:
                    proof += "open Wrapped Wrapped.Algo2LeanGenerated\n"
                proof += signature_checks(compiled.functions)
                self.assert_checked(check_lean(compiled.lean, module=compiled.module,
                    points_lean=compiled.points_lean + proof, timeout=120))

    def test_project_generic_dependency_and_facts_signatures_check_in_lean(self):
        sources = {
            "api": "from algo2lean import Interface\nclass Counter(Interface):\n    def get(self) -> Int: ...\n",
            "client": '''from api import Counter

def read(queue: Counter) -> Int:
    # @read
    return queue.get()

def scalar(value: Int) -> Int:
    # @return
    return value

def empty() -> None:
    return
''',
        }
        with tempfile.TemporaryDirectory(prefix="algo2lean-interface-metadata-") as directory:
            compiled = compile_project("client", root=directory, sources=sources)
            before = dict(compiled.files)
            response = project_response(compiled)
            self.assertEqual(compiled.files, before)
            functions = {function["name"]: function for function in response["functions"]}
            read, scalar = entries(functions["read"]), entries(functions["scalar"])
            self.assertIn("(dependencies : Dependencies)", read["read.ValidInput"]["signature"])
            self.assertNotIn("dependencies", read["read.load"]["signature"])
            self.assertNotIn("dependencies", scalar["scalar.ValidInput"]["signature"])
            self.assertIn("(dependencies : Dependencies)", scalar["scalar.Call"]["signature"])
            self.assertEqual(read["read.Run.eq_of_call"]["file_kind"], "facts")
            self.assertIn("{dependencies : Dependencies} (facts : DependencyFacts dependencies)",
                          read["read.Run.eq_of_call"]["signature"])
            self.assertIn("read.ReturnsWithCost", read)
            proof = """import Algo.client.Points
import Algo.client.Facts
open Algo2LeanGenerated Algo.client Algo.client.Algo2LeanGenerated
""" + signature_checks(response["functions"])
            self.assert_checked(check_project(compiled, analysis=proof))

    def test_concrete_project_facts_have_no_extra_dependency_parameters(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-interface-concrete-") as directory:
            compiled = compile_project("concrete", root=directory, sources={"concrete": SOURCE})
            functions = project_response(compiled)["functions"]
            for function in functions:
                fact = entries(function)[function["lean_name"] + ".Run.eq_of_call"]
                self.assertEqual(fact["file_kind"], "facts")
                self.assertNotIn("dependencies", fact["signature"])
                self.assertNotIn("(facts :", fact["signature"])
            proof = """import Algo.concrete.Points
import Algo.concrete.Facts
open Algo2LeanGenerated Algo.concrete Algo.concrete.Algo2LeanGenerated
""" + signature_checks(functions)
            self.assert_checked(check_project(compiled, analysis=proof))


if __name__ == "__main__":
    unittest.main()
