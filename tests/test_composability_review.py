"""Independent review regressions for static interface identity and binding names."""

import shutil
import tempfile
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ComposabilityReviewTests(unittest.TestCase):
    def check(self, sources):
        with tempfile.TemporaryDirectory(prefix="algo2lean-binding-review-") as root:
            compiled = compile_project("main", root=root, sources=sources)
            checked = check_project(compiled, check_facts=True, timeout=60)
            self.assertTrue(checked.ok, checked.output)
            return compiled

    def test_numbered_binding_collision_never_overwrites_an_earlier_interface(self):
        sources = {
            "api": """from algo2lean import Interface
class I(Interface):
    def get(self) -> Int: ...
class I_2(Interface):
    def get(self) -> Int: ...
""",
            "a": "class A:\n    def get(self) -> Int:\n        return 1\n",
            "b": "class A:\n    def get(self) -> Int:\n        return 2\n",
            "client1": "from api import I\ndef f(q: I) -> Int:\n    return q.get()\n",
            "client2": "from api import I_2\ndef f(q: I_2) -> Int:\n    return q.get()\n",
            "main": """from a import A
from b import A as B
from client1 import f as one
from client2 import f as two
def run(a: A, b: B) -> Int:
    x = two(a)
    y = one(a)
    z = one(b)
    return x + y + z
""",
        }
        compiled = self.check(sources)
        self.assertEqual(len(compiled.entry.bindings), 3)
        self.assertEqual({(binding.interface.name, binding.backend.name)
                          for binding in compiled.entry.bindings.values()},
                         {("I_2", "a"), ("I", "a"), ("I", "b")})

    def test_lean_keyword_interface_names_keep_namespaces_and_slots_valid(self):
        for name in ("by", "where", "end", "namespace"):
            with self.subTest(name=name):
                self.check({
                    "api": "from algo2lean import Interface\nclass %s(Interface):\n"
                           "    def get(self) -> Int: ...\n" % name,
                    "client": "from api import %s\ndef read(q: %s) -> Int:\n"
                              "    return q.get()\n" % (name, name),
                    "backend": "class Storage:\n    def get(self) -> Int:\n        return 1\n",
                    "main": "from backend import Storage\nfrom client import read\n"
                            "def run(q: Storage) -> Int:\n    return read(q)\n",
                })


if __name__ == "__main__":
    unittest.main()
