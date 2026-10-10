"""Separate compilation must preserve source identity and checked proof reuse."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import textwrap
import unittest

from algo2lean.checker import prepare_lean_environment
from algo2lean.modular import compile_project
from algo2lean.project import ProjectError, Symbol


ROOT = Path(__file__).resolve().parents[1]
INCREMENT = "def increment(x: Int) -> Int:\n    return x + 1\n"
ANSWER = 'def answer() -> Int:\n    tick("work", 3)\n    return 42\n'
NODE = '''class Node:
    value: Int
    next: Node | None
    def __init__(self, value: Int, next: Node | None) -> None:
        self.value = value
        self.next = next
    def read(self) -> Int:
        return self.value
'''


def clean_sources(sources):
    return {name: textwrap.dedent(source).lstrip("\n") for name, source in sources.items()}


class ModularCompilationTests(unittest.TestCase):
    def compile(self, entry, sources):
        with tempfile.TemporaryDirectory(prefix="algo2lean-module-source-") as root:
            return compile_project(entry, root=root, sources=clean_sources(sources))

    def test_all_import_forms_compile_to_same_canonical_call(self):
        variants = (
            ("import library", "library.increment"),
            ("import library as lib", "lib.increment"),
            ("from library import increment", "increment"),
            ("from library import increment as inc", "inc"),
        )
        outputs = []
        for declaration, function in variants:
            with self.subTest(declaration=declaration):
                compiled = self.compile("client", {"library": INCREMENT,
                    "client": declaration + "\ndef run(x: Int) -> Int:\n    return " + function + "(x)\n"})
                self.assertEqual(set(compiled.entry.functions), {"run"})
                self.assertEqual(len(compiled.entry.imports), 1)
                call = next(iter(compiled.entry.imports.values()))
                self.assertEqual((call.module, call.name), ("library", "increment"))
                self.assertIn("Algo.«library».entry_increment", compiled.entry.lean)
                self.assertNotIn("structure State_increment", compiled.entry.lean)
                outputs.append(compiled.entry.lean)
        self.assertEqual(outputs, [outputs[0]] * len(outputs))

    def test_new_callers_do_not_change_existing_module_output(self):
        standalone = self.compile("library", {"library": INCREMENT})
        sources = {"library": INCREMENT,
            "first": "from library import increment\ndef first(x: Int) -> Int:\n    return increment(x)\n",
            "second": "import library as lib\ndef second(x: Int) -> Int:\n    return lib.increment(lib.increment(x))\n",
            "application": "import first\nimport second\ndef run(x: Int) -> Int:\n    return first.first(second.second(x))\n"}
        composition = self.compile("application", sources)
        for attribute in ("lean", "points_lean", "facts_lean"):
            self.assertEqual(getattr(standalone.entry, attribute), getattr(composition.modules["library"], attribute))
        first = self.compile("first", sources)
        self.assertEqual(first.entry.lean, composition.modules["first"].lean)
        self.assertEqual(first.entry.points_lean, composition.modules["first"].points_lean)

    def test_labels_change_only_their_points_file(self):
        sources = {"library": INCREMENT,
            "client": "from library import increment\ndef run(x: Int) -> Int:\n    # @before\n    return increment(x)\n"}
        original = self.compile("client", sources)
        changed = self.compile("client", dict(sources, client=sources["client"].replace("# @before", "# @renamed")))
        self.assertEqual(original.entry.lean, changed.entry.lean)
        self.assertNotEqual(original.entry.points_lean, changed.entry.points_lean)
        labeled_library = self.compile("client", dict(sources, library=INCREMENT.replace("    return", "    # @result\n    return")))
        self.assertEqual(original.entry.lean, labeled_library.entry.lean)
        self.assertEqual(original.modules["library"].lean, labeled_library.modules["library"].lean)
        self.assertNotEqual(original.modules["library"].points_lean, labeled_library.modules["library"].points_lean)

    def test_reexports_and_diamond_imports_delegate_to_one_original(self):
        compiled = self.compile("client", {
            "library": INCREMENT,
            "left": "from library import increment as selected\n",
            "right": "import library as original\n",
            "client": "from left import selected\nfrom right import original\ndef run(x: Int) -> Int:\n    return selected(original.increment(x))\n",
        })
        self.assertEqual(list(compiled.modules), ["library", "left", "right", "client"])
        self.assertEqual(len(compiled.entry.imports), 1)
        self.assertEqual(next(iter(compiled.entry.imports.values())).module, "library")
        self.assertFalse(compiled.modules["left"].functions)
        self.assertFalse(compiled.modules["right"].functions)
        self.assertEqual(compiled.entry.lean.count("theorem import_0_simulates"), 1)

    def test_dotted_module_and_quoted_class_annotations_use_original_types(self):
        compiled = self.compile("client", {
            "pkg.models": NODE,
            "client": '''
                import pkg.models as model
                def read(n: "model.Node") -> Int:
                    return n.read()
                def head(nodes: Seq[model.Node | None]) -> model.Node | None:
                    return nodes[0]
            ''',
        })
        imported = next(name for name, origin in compiled.entry.class_origins.items()
                        if origin == Symbol("pkg.models", "Node", "class"))
        self.assertEqual(compiled.entry.functions["read"].parameters, [("n", imported)])
        self.assertEqual(compiled.entry.functions["head"].parameters, [("nodes", "Seq[" + imported + "?]")])
        self.assertEqual(compiled.entry.classes[imported].runtime_tag, "pkg.models.Node")
        self.assertIn("import Algo.pkg.models.Generated", compiled.entry.lean)

    def test_distinct_same_named_classes_do_not_become_interchangeable(self):
        sources = {"one": NODE, "two": NODE,
            "client": "from one import Node as First\nfrom two import Node as Second\ndef wrong(n: First) -> Second:\n    return n\n"}
        with self.assertRaisesRegex(ProjectError, "Expected"):
            self.compile("client", sources)

    def test_transitive_class_signatures_keep_defining_module_identity(self):
        compiled = self.compile("client", {
            "models": NODE,
            "library": "from models import Node\ndef first(nodes: Seq[Node | None]) -> Node | None:\n    return nodes[0]\n",
            "client": "from models import Node\nfrom library import first\ndef run(n: Node) -> Node | None:\n    nodes: Seq[Node | None] = const(None)\n    nodes[0] = n\n    return first(nodes)\n",
        })
        origins = [origin for origin in compiled.entry.class_origins.values()
                   if origin.name == "Node"]
        self.assertEqual(origins, [Symbol("models", "Node", "class")])
        called = next(call for call in compiled.entry.imports.values() if call.name == "first")
        node_type = compiled.entry.functions["run"].parameters[0][1]
        self.assertEqual(called.function.return_type, node_type + "?")
        self.assertEqual(called.function.parameters, [("nodes", "Seq[" + node_type + "?]")])

    def test_imported_call_arguments_are_evaluated_left_to_right(self):
        compiled = self.compile("client", {
            "library": "def mark(a: Seq, value: Int) -> Int:\n    a[0] = value\n    return value\ndef pair(a: Int, b: Int) -> Int:\n    return a * 10 + b\n",
            "client": "from library import mark, pair\ndef run(a: Seq) -> Int:\n    return pair(mark(a, 1), mark(a, 2))\n",
        })
        lowerer = compiled.entry.lowered["run"]
        pc, assignments, events = lowerer.entry, {}, []
        while lowerer.nodes[pc].kind != "return":
            node = lowerer.nodes[pc]
            if node.kind == "assign":
                target, value, pc, _ = node.data
                assignments[target] = value
            else:
                self.assertEqual(node.kind, "call")
                name, arguments, target, pc, _ = node.data
                call = compiled.entry.imports[name]
                values = [assignments.get(argument.removeprefix("s."), argument) for argument in arguments]
                events.append((call.name, values))
        self.assertEqual([name for name, _ in events], ["mark", "mark", "pair"])
        self.assertEqual(events[0][1][-1], "(1 : Int)")
        self.assertEqual(events[1][1][-1], "(2 : Int)")

    def test_runtime_cost_surface_survives_imports_and_repeated_calls(self):
        compiled = self.compile("client", {"library": ANSWER,
            "client": "from library import answer\ndef run() -> Int:\n    first = answer()\n    return first + answer()\n"})
        self.assertEqual(compiled.entry.clocks, ("work",))
        self.assertIn("def run.ReturnsWithCost", compiled.entry.lean)
        self.assertIn("Heap.cost loaded.1 finalHeap", compiled.entry.lean)
        self.assertEqual(sum(node.kind == "call" for node in compiled.entry.lowered["run"].nodes), 2)

    def test_transitive_recursive_calls_keep_separate_frames(self):
        compiled = self.compile("last", {
            "recursive": "def count(n: Int) -> Int:\n    if n <= 0:\n        return 0\n    return 1 + count(n - 1)\n",
            "middle": "from recursive import count\ndef twice(n: Int) -> Int:\n    return count(n) + count(n)\n",
            "last": "import middle\ndef run(n: Int) -> Int:\n    return middle.twice(n)\n",
        })
        self.assertFalse(compiled.modules["recursive"].imports)
        self.assertEqual({call.module for call in compiled.modules["middle"].imports.values()}, {"recursive"})
        self.assertEqual({call.module for call in compiled.entry.imports.values()}, {"middle"})
        self.assertNotIn("State_count", compiled.entry.lean)
        self.assertIn("Algo.«middle».entry_twice", compiled.entry.lean)

    def test_imported_type_errors_identify_the_callers_source_line(self):
        with self.assertRaises(ProjectError) as raised:
            self.compile("client", {"library": INCREMENT,
                "client": "from library import increment\ndef run() -> Int:\n    return increment(True)\n"})
        self.assertEqual(raised.exception.line, 3)
        self.assertTrue(raised.exception.file.endswith("client.algo"))


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ModularCheckingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.environment = prepare_lean_environment(modules=("Algo2LeanLib.Modules",), timeout=120)

    def check_project(self, entry, sources, proofs=()):
        with tempfile.TemporaryDirectory(prefix="algo2lean-module-test-") as directory:
            compiled = compile_project(entry, root=directory, sources=clean_sources(sources))
            environment = dict(self.environment)
            environment["LEAN_PATH"] = directory + os.pathsep + environment["LEAN_PATH"]
            for name, source in list(compiled.files.items()) + list(proofs):
                path = Path(directory).joinpath(*name.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding="utf-8")
                result = subprocess.run(["lean", "--root=" + directory, "-o", str(path.with_suffix(".olean")), str(path)],
                    cwd=ROOT, env=environment, capture_output=True, text=True, timeout=90)
                self.assertEqual(result.returncode, 0, name + "\n" + result.stdout + result.stderr)
                self.assertNotIn("declaration uses `sorry`", result.stdout + result.stderr)
            return compiled

    def test_all_import_forms_reexports_diamond_and_recursive_calls_check(self):
        self.check_project("client", {
            "pkg.library": "def count(n: Int) -> Int:\n    if n <= 0:\n        return 0\n    return 1 + count(n - 1)\n",
            "left": "from pkg.library import count as selected\n",
            "right": "import pkg.library as selected\n",
            "client": '''
                import pkg.library
                import pkg.library as lib
                from pkg.library import count
                from pkg.library import count as recurse
                from left import selected
                from right import selected as original
                def run(n: Int) -> Int:
                    return pkg.library.count(n) + lib.count(n) + count(n) + recurse(n) + selected(n) + original.count(n)
            ''',
        })

    def test_imported_objects_typed_collections_allocation_and_aliases_check(self):
        self.check_project("client", {
            "models": NODE,
            "library": "from models import Node\ndef first(nodes: Seq[Node | None]) -> Node | None:\n    return nodes[-1]\n",
            "client": '''
                from models import Node
                from library import first
                def run() -> Node | None:
                    nodes: Seq[Node | None] = const(None)
                    alias = nodes
                    alias[-1] = Node(7, None)
                    return first(nodes)
            ''',
        })

    def test_previously_proved_summary_and_cost_are_reused_through_two_callers(self):
        library_proof = '''import Algo.library.Generated
open Algo2LeanCore Algo2LeanGenerated
namespace LibraryProof
open Algo.library Algo.library.Algo2LeanGenerated
theorem answer (heap : Heap) : Algo.library.answer.Call heap () (heap.tick "work" 3) 42 := by
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.answer_pc3 _ _ _)
  apply Reaches.prepend (Step.answer_pc2 _ _ _)
  exact Reaches.single (Step.answer_pc1 _ _ _)
end LibraryProof
'''
        client_proof = '''import LibraryProof
import Algo.client.Generated
open Algo2LeanCore Algo2LeanGenerated
namespace ClientProof
open Algo.client Algo.client.Algo2LeanGenerated
theorem run (heap : Heap) : Algo.client.run.Call heap () (heap.tick "work" 3) 42 := by
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.run_pc2 _ _ _)
  refine Reaches.trans (ModuleCall.summary import_0_simulates _ caller (LibraryProof.answer heap).2) ?_
  exact Reaches.single (Step.run_pc1 _ _ _)
end ClientProof
'''
        final_proof = '''import ClientProof
import Algo.final.Generated
open Algo2LeanCore Algo2LeanGenerated
namespace FinalProof
open Algo.final Algo.final.Algo2LeanGenerated
theorem run (heap : Heap) : Algo.final.run.Call heap () (heap.tick "work" 3) 42 := by
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.run_pc2 _ _ _)
  refine Reaches.trans (ModuleCall.summary import_1_simulates _ caller (ClientProof.run heap).2) ?_
  exact Reaches.single (Step.run_pc1 _ _ _)
example (heap : Heap) : ∃ after,
    Algo.final.run.Call heap () after 42 ∧ Heap.cost heap after "work" = 3 :=
  ⟨heap.tick "work" 3, run heap, Heap.cost_tick_same heap "work" 3⟩
example (heap : Heap) (initial : heap.clocks "work" = 11) :
    (heap.tick "work" 3).clocks "work" = 14 := by simp [initial]
end FinalProof
'''
        repeated_proof = '''import LibraryProof
import Algo.repeated.Generated
open Algo2LeanCore Algo2LeanGenerated
namespace RepeatedProof
open Algo.repeated Algo.repeated.Algo2LeanGenerated
theorem run (heap : Heap) :
    Algo.repeated.run.Call heap () ((heap.tick "work" 3).tick "work" 3) 84 := by
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.run_pc6 _ _ _)
  refine Reaches.trans (ModuleCall.summary import_0_simulates _ caller (LibraryProof.answer heap).2) ?_
  apply Reaches.prepend (Step.run_pc5 _ _ _)
  apply Reaches.prepend (Step.run_pc4 _ _ _)
  apply Reaches.prepend (Step.run_pc3 _ _ _)
  refine Reaches.trans (ModuleCall.summary import_0_simulates _ caller (LibraryProof.answer (heap.tick "work" 3)).2) ?_
  apply Reaches.prepend (Step.run_pc2 _ _ _)
  exact Reaches.single (Step.run_pc1 _ _ _)
example (heap : Heap) : ∃ after,
    Algo.repeated.run.Call heap () after 84 ∧ Heap.cost heap after "work" = 6 := by
  refine ⟨_, run heap, ?_⟩
  simp only [Heap.tick_add, Heap.cost_tick_same]
end RepeatedProof
'''
        self.check_project("application", {
            "library": ANSWER,
            "client": "from library import answer\ndef run() -> Int:\n    return answer()\n",
            "final": "import client\ndef run() -> Int:\n    return client.run()\n",
            "repeated": "from library import answer\ndef run() -> Int:\n    first = answer()\n    return first + answer()\n",
            "application": "import final\nimport repeated\n",
        }, (("LibraryProof", library_proof), ("ClientProof", client_proof), ("FinalProof", final_proof),
            ("RepeatedProof", repeated_proof)))


if __name__ == "__main__":
    unittest.main()
