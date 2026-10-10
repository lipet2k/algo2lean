"""Interface declarations and concrete adapters retain independently proved code."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.checker import check_lean, prepare_lean_environment
from algo2lean.interfaces import (check_binding, collect_interfaces, emit_binding,
                                 emit_binding_facts, emit_interface)
from algo2lean.modular import compile_project
from algo2lean.project import ProjectError, Symbol, load_project


ROOT = Path(__file__).resolve().parents[1]
INTERFACE = """from algo2lean import Interface
class Counter(Interface):
    def get(self) -> Int: ...
    def put(self, value: Int) -> None: ...
    def sequence(self, value: Seq) -> Seq: ...
    def self_ref(self) -> Counter: ...
"""
BACKEND = """class Storage:
    value: Int
    def __init__(self) -> None:
        self.value = 0
    def get(self) -> Int:
        tick("reads")
        return self.value
    def put(self, value: Int) -> None:
        self.value = value
    def sequence(self, value: Seq) -> Seq:
        return value
    def self_ref(self) -> Storage:
        return self
"""


class InterfaceSignatureTests(unittest.TestCase):
    def parse(self, source=INTERFACE, **sources):
        with tempfile.TemporaryDirectory() as directory:
            project = load_project("api", root=directory, sources=dict(sources, api=source))
            return project, collect_interfaces(project)

    def test_signatures_have_canonical_class_and_alias_identity(self):
        project, interfaces = self.parse("""from algo2lean import Interface as Marker
from model import Node as Item
class Reader(Marker):
    def read(self, values: Seq[Item | None]) -> Item: ...
""", model="class Node:\n    value: Int\n")
        info = interfaces[Symbol("api", "Reader", "interface")]
        self.assertEqual(info.methods["read"].parameters, (("values", "Seq[model.Node?]"),))
        self.assertEqual(info.methods["read"].return_type, "model.Node")
        self.assertEqual(project.resolve("api", "Item"), Symbol("model", "Node", "class"))

    def test_invalid_declarations_have_source_diagnostics(self):
        cases = [
            ("    value: Int\n", "method signatures only"),
            ("    def get(self) -> Int:\n        return 1\n", "only ..."),
            ("    def __init__(self) -> None: ...\n", "constructors"),
            ("    def get(value: Int) -> Int: ...\n", "self"),
            ("    def get(self, value) -> Int: ...\n", "explicit type annotations"),
            ("    def get(self, value: Int = 1) -> Int: ...\n", "without defaults"),
            ("    def get(self) -> Int: ...\n    def get(self) -> Int: ...\n", "Duplicate interface method"),
        ]
        for body, message in cases:
            with self.subTest(body=body), self.assertRaisesRegex(ProjectError, message):
                self.parse("from algo2lean import Interface\nclass Counter(Interface):\n" + body)

    def test_binding_requires_all_matching_method_signatures(self):
        _, interfaces = self.parse()
        info = next(iter(interfaces.values()))
        with tempfile.TemporaryDirectory() as directory:
            good = compile_project("backend", root=directory, sources={"backend": BACKEND}).entry
            self.assertEqual(set(check_binding(info, good, "Storage").methods),
                             {"get", "put", "sequence", "self_ref"})
            for changed, diagnostic in ((BACKEND.replace("def get(", "def other("), "does not implement"),
                                        (BACKEND.replace("value: Int) -> None", "value: Bool) -> None").replace(
                                            "self.value = value", "self.value = 0"), "incompatible signature")):
                bad = compile_project("backend", root=directory, sources={"backend": changed}).entry
                with self.assertRaisesRegex(ProjectError, diagnostic):
                    check_binding(info, bad, "Storage")


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class InterfaceCheckingTests(unittest.TestCase):
    def test_summary_clock_divergence_and_optional_determinism_core(self):
        proof = (ROOT / "tests/proofs/interface.lean").read_text(encoding="utf-8")
        checked = check_lean(proof, module="InterfaceCoreTest", timeout=60)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)

    def test_generated_binding_and_summary_transfers_are_checked(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-interface-") as directory:
            info = next(iter(collect_interfaces(load_project("api", root=directory,
                sources={"api": INTERFACE})).values()))
            backend = compile_project("backend", root=directory, sources={"backend": BACKEND}).entry
            binding = check_binding(info, backend, "Storage")
            sources = [
                (backend.lean_module, backend.lean),
                (backend.facts_module, backend.facts_lean),
                ("Algo.api.Generated", "import Algo2LeanLib.Interface\nnamespace Algo.api\n"
                 "open _root_.Algo2LeanGenerated\n" + emit_interface(info) + "\nend Algo.api\n"),
                ("Binding", "import Algo.api.Generated\nimport Algo.backend.Generated\n"
                 "open Algo2LeanGenerated\n" + emit_binding(binding, name="counter")),
                ("BindingFacts", "import Binding\nimport Algo.backend.Facts\n"
                 + emit_binding_facts(binding, name="counter")),
            ]
            environment = prepare_lean_environment(modules=("Algo2LeanLib.Interface",))
            environment["LEAN_PATH"] = directory + os.pathsep + environment["LEAN_PATH"]
            for name, source in sources:
                path = Path(directory).joinpath(*name.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding="utf-8")
                result = subprocess.run(
                    ["lean", "--root=" + directory, "-o", str(path.with_suffix(".olean")), str(path)],
                    cwd=ROOT, env=environment, capture_output=True, text=True, timeout=60)
                output = result.stdout + result.stderr
                self.assertEqual(result.returncode, 0, name + "\n" + output)
                self.assertNotIn("declaration uses `sorry`", output)


if __name__ == "__main__":
    unittest.main()
