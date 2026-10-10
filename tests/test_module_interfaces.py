"""Generic algorithms retain one compiled body across concrete interface bindings."""

from pathlib import Path
import shutil
import tempfile
import unittest

from algo2lean.modular import compile_project
from algo2lean.project import ProjectError
from algo2lean.project_checker import check_project


API = """from algo2lean import Interface
class Counter(Interface):
    def get(self) -> Int: ...
    def put(self, value: Int) -> None: ...
"""
CLIENT = """from api import Counter

def bump(q: Counter) -> Int:
    # @read
    value = q.get()
    q.put(value + 1)
    return value
"""
BACKEND = """class Storage:
    value: Int
    def __init__(self) -> None:
        self.value = 0
    def get(self) -> Int:
        tick("reads")
        return self.value
    def put(self, value: Int) -> None:
        tick("writes")
        self.value = value
"""
WRAPPER = """from backend import Storage
from client import bump

def run() -> Int:
    q = Storage()
    return bump(q)
"""


class InterfaceBindingValidationTests(unittest.TestCase):
    def test_storing_a_concrete_interface_conversion_is_rejected(self):
        source = """from backend import Storage
from api import Counter

def invalid() -> Int:
    item: Counter = Storage()
    return item.get()
"""
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ProjectError, "storing an interface conversion"):
                compile_project("wrapper", root=directory,
                    sources={"api": API, "backend": BACKEND, "wrapper": source})

    def test_missing_methods_and_mismatched_signatures_have_source_errors(self):
        cases = [
            (BACKEND.replace("def get(", "def other("), "does not implement"),
            (BACKEND.replace("value: Int) -> None", "value: Bool) -> None").replace(
                "self.value = value", "self.value = 0"), "incompatible signature"),
        ]
        with tempfile.TemporaryDirectory() as directory:
            for backend, expected in cases:
                with self.subTest(expected=expected), self.assertRaisesRegex(ProjectError, expected) as raised:
                    compile_project("wrapper", root=directory,
                        sources={"api": API, "client": CLIENT, "backend": backend, "wrapper": WRAPPER})
                self.assertTrue(raised.exception.file.endswith("wrapper.algo"))


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class GenericInterfaceLeanTests(unittest.TestCase):
    def check(self, sources, entry="wrapper", **options):
        with tempfile.TemporaryDirectory(prefix="algo2lean-generic-interface-") as directory:
            compiled = compile_project(entry, root=directory, sources=sources)
            checked = check_project(compiled, check_facts=True, **options)
            self.assertTrue(checked.ok, checked.output)
            self.assertNotIn("declaration uses `sorry`", checked.output)
            return compiled

    def test_generic_client_and_concrete_wrapper_check_separately(self):
        sources = {"api": API, "client": CLIENT, "backend": BACKEND, "wrapper": WRAPPER}
        client = self.check(sources, entry="client")
        wrapper = self.check(sources)
        self.assertEqual(client.entry.lean, wrapper.modules["client"].lean)
        self.assertEqual(client.entry.facts_lean, wrapper.modules["client"].facts_lean)
        self.assertTrue(client.entry.dependencies)
        self.assertFalse(wrapper.entry.dependencies)
        self.assertIn("structure DependencyFacts", client.entry.facts_lean)
        self.assertIn("facts.«Counter».step_next", client.entry.facts_lean)
        self.assertEqual(wrapper.entry.facts_lean.count('import «Algo».«backend».«Facts»'), 1)
        self.assertIn("Storage_as_Counter_facts", wrapper.entry.facts_lean)

    def test_one_generic_module_can_have_two_concrete_instances(self):
        other = BACKEND.replace("Storage", "OtherStorage").replace("self.value = 0", "self.value = 100")
        wrapper = """from backend import Storage, OtherStorage
from client import bump

def run() -> Int:
    first = Storage()
    second = OtherStorage()
    left = bump(first)
    return left + bump(second)
"""
        compiled = self.check({"api": API, "client": CLIENT, "backend": BACKEND + "\n" + other,
                               "wrapper": wrapper})
        self.assertEqual(len(compiled.entry.bindings), 2)
        self.assertEqual(len(compiled.entry.environments), 2)
        frames = {call.frame for call in compiled.entry.imports.values() if call.environment}
        self.assertEqual(len(frames), 2)
        self.assertNotIn("def next_bump", compiled.entry.facts_lean)

    def test_recursive_generic_forwarding_and_labels_preserve_core(self):
        middle = """from api import Counter
from client import bump

def repeat(q: Counter, count: Int) -> Int:
    if count <= 0:
        return q.get()
    value = bump(q)
    return repeat(q, count - 1)
"""
        wrapper = WRAPPER.replace("from client import bump", "from middle import repeat").replace("bump(q)", "repeat(q, 3)")
        sources = {"api": API, "client": CLIENT, "middle": middle, "backend": BACKEND, "wrapper": wrapper}
        compiled = self.check(sources)
        self.assertTrue(compiled.modules["middle"].dependencies)
        self.assertTrue(compiled.modules["middle"].environments)
        changed = self.check(dict(sources, client=CLIENT.replace("# @read", "# @observe")))
        for name in compiled.modules:
            self.assertEqual(compiled.modules[name].lean, changed.modules[name].lean)
            self.assertEqual(compiled.modules[name].facts_lean, changed.modules[name].facts_lean)
        self.assertNotEqual(compiled.modules["client"].points_lean, changed.modules["client"].points_lean)

    def test_multiple_interfaces_with_same_short_name_remain_distinct(self):
        api = "from algo2lean import Interface\nclass Counter(Interface):\n    def get(self) -> Int: ...\n"
        client = """from a_b import Counter as Left
from a.b import Counter as Right

def total(left: Left, right: Right) -> Int:
    return left.get() + right.get()
"""
        wrapper = """from backend import Storage
from client import total

def run() -> Int:
    q = Storage()
    return total(q, q)
"""
        compiled = self.check({"a_b": api, "a.b": api, "client": client,
                               "backend": BACKEND, "wrapper": wrapper})
        slots = list(compiled.modules["client"].dependencies.values())
        self.assertEqual(len(slots), 2)
        self.assertEqual(len({slot.field for slot in slots}), 2)
        self.assertEqual(len({slot.local_name for slot in slots}), 2)
        self.assertEqual(len(compiled.entry.bindings), 2)

    def test_signature_compatibility_does_not_prove_behavioral_laws(self):
        backend = """class Storage:
    def __init__(self) -> None:
        return
    def get(self) -> Int:
        return 7
    def put(self, value: Int) -> None:
        return
"""
        sources = {"api": API, "client": CLIENT, "backend": backend, "wrapper": WRAPPER}
        analysis = """import Algo.wrapper.Facts
open Algo2LeanCore Algo2LeanGenerated Algo.backend

namespace BadBackendCheck

theorem actual (heap : Heap) (ref : ObjectRef) (valid : Storage.get.ValidInput heap ref) :
    Storage.get.Call heap ref heap 7 := by
  open Algo.backend.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.Storage_get_pc2 _ _ caller)
    exact Reaches.single (Step.Storage_get_pc1 _ _ caller)

example (heap after : Heap) (ref : ObjectRef)
    (execution : Storage.get.Run heap ref after 0) : False := by
  have equal := execution.eq_of_call (actual heap ref execution.1)
  omega

end BadBackendCheck
"""
        with tempfile.TemporaryDirectory(prefix="algo2lean-bad-interface-") as directory:
            compiled = compile_project("wrapper", root=directory, sources=sources)
            valid = check_project(compiled, check_facts=True, analysis=analysis)
            self.assertTrue(valid.ok, valid.output)
            invalid = check_project(compiled, analysis=analysis + "\nexample (heap : Heap) (ref : ObjectRef)\n"
                "    (valid : Storage.get.ValidInput heap ref) : Storage.get.Call heap ref heap 0 :=\n"
                "  BadBackendCheck.actual heap ref valid\n")
            self.assertFalse(invalid.ok, "A signature match must not supply a false operation contract")
            self.assertIn("Type mismatch", invalid.output)

    def test_kernel_rejects_a_generic_certificate_that_skips_interface_steps(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-bad-generic-facts-") as directory:
            compiled = compile_project("wrapper", root=directory,
                sources={"api": API, "client": CLIENT, "backend": BACKEND, "wrapper": WRAPPER})
            client = compiled.modules["client"]
            changed = client.facts_lean.replace("facts.«Counter».next (.active h frame inner)",
                                               "(fun state => state) (.active h frame inner)")
            self.assertNotEqual(client.facts_lean, changed)
            client.facts_lean = changed
            rejected = check_project(compiled, check_facts=True)
            self.assertFalse(rejected.ok, "Interface transitions must agree with the supplied executable code")
            self.assertIn("Algo/client/Facts.lean:", rejected.output)


if __name__ == "__main__":
    unittest.main()
