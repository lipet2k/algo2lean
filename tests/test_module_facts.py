"""Optional determinism certificates are checked against real module boundaries."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.checker import prepare_lean_environment
from algo2lean.modular import compile_project
from algo2lean.module_facts import emit_facts


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ModuleFactsTests(unittest.TestCase):
    def check_project(self, sources, *, entry="main", corrupt_facts=False):
        with tempfile.TemporaryDirectory(prefix="algo2lean-module-facts-") as directory:
            project = compile_project(entry, root=directory, sources=sources)
            environment = prepare_lean_environment(modules=("Algo2LeanLib.Modules",))
            environment["LEAN_PATH"] = directory + os.pathsep + environment["LEAN_PATH"]
            for module in project.modules.values():
                facts = emit_facts(module)
                if corrupt_facts and module.name == entry:
                    # A next-state certificate must not fabricate an extra tick.
                    changed = facts.replace("Algo2LeanCore.resumeConfig h",
                                            'Algo2LeanCore.resumeConfig (h.tick "fabricated")', 1)
                    self.assertNotEqual(changed, facts)
                    facts = changed
                for name, source in ((module.lean_module, module.lean),
                                     ("Algo." + module.name + ".Facts", facts)):
                    path = Path(directory).joinpath(*name.split(".")).with_suffix(".lean")
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(source, encoding="utf-8")
                    result = subprocess.run(
                        ["lean", "--root=" + directory, "-o", str(path.with_suffix(".olean")), str(path)],
                        cwd=ROOT, env=environment, capture_output=True, text=True, timeout=60)
                    output = result.stdout + result.stderr
                    if corrupt_facts and module.name == entry and name.endswith(".Facts"):
                        self.assertNotEqual(result.returncode, 0,
                                            "The kernel must reject a fabricated clock effect")
                        return
                    self.assertEqual(result.returncode, 0, name + "\n" + output)
                    self.assertNotIn("declaration uses `sorry`", output)
            return project

    def test_recursive_transitive_calls_and_reexports(self):
        project = self.check_project({
            "base": 'def f(n: Int) -> Int:\n    if n <= 0:\n        return 0\n'
                    '    tick("steps")\n    return f(n - 1)\n',
            "bridge": "from base import f as selected\n",
            "middle": "import bridge\n\ndef g(n: Int) -> Int:\n    return bridge.selected(n)\n",
            "main": "import base as b\nfrom base import f as alias\nimport middle\n\n"
                    "def run(n: Int) -> Bool:\n    a = const(0)\n    a[-3] = b.f(alias(n))\n"
                    "    return middle.g(a[-3]) == 0\n",
        })
        facts = emit_facts(project.entry)
        self.assertEqual(facts.count("import «Algo».«base».«Facts»"), 1)
        self.assertEqual(facts.count("import «Algo».«middle».«Facts»"), 1)
        self.assertNotIn("next_f (", facts, "Imported instruction projections belong in the original module")

    def test_guarded_objects_typed_sequences_and_heap_operations(self):
        source = (ROOT / "tests/proofs/typed_sequences.algo").read_text(encoding="utf-8")
        self.check_project({"main": source})

    def test_kernel_rejects_wrong_next_state_certificate(self):
        self.check_project({"main": "def answer() -> Int:\n    return 42\n"}, corrupt_facts=True)


if __name__ == "__main__":
    unittest.main()
