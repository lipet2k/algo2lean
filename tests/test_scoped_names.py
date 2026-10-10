"""Source-scoped Lean names remain usable across proof and module boundaries."""

import shutil
import tempfile
import unittest

from algo2lean.checker import check_lean
from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


SOURCE = '''class Counter:
    value: Int
    def __init__(self, value: Int) -> None:
        self.value = value
    def add(self, amount: Int) -> Int:
        self.value = self.value + amount
        return self.value

def increment(value: Int) -> Int:
    tick("work")
    return value + 1

def same(a: Seq) -> Seq:
    # @ready
    return a

def identity(q: Counter) -> Counter:
    return q

def lemma(theorem: Seq) -> Seq:
    # @by
    return theorem
'''

LEGACY_PREFIXES = {
    "Returns": "is_Output_",
    "ReturnsWithCost": "is_OutputWithCost_",
    "Run": "is_Execution_",
    "Call": "is_Summary_",
    "CallFrom": "is_SummaryFrom_",
    "ValidTranscript": "is_Transcript_",
    "ValidHeapTranscript": "is_HeapTranscript_",
    "ValidInput": "validInputs_",
    "initial": "initial_",
    "load": "load_",
}


def interface_checks(functions, prefix=""):
    """Check every primary declaration without depending on parameter shapes."""
    return "\n".join(
        "#check @%s%s.%s" % (prefix, scoped, member)
        for scoped, _ in functions
        for member in LEGACY_PREFIXES
    ) + "\n"


def assert_no_legacy_declarations(test, *sources):
    for source in sources:
        test.assertNotRegex(source,
            r"(?m)^(?:def|abbrev|theorem) (?:is_(?:Output|OutputWithCost|Execution|Summary|SummaryFrom|Transcript|HeapTranscript)_|validInputs_|initial_|load_|At_|local_|element_)")


SCALAR_CALL = '''
namespace ScopedProof

theorem increment_call (heap : Heap) (value : Int) :
    increment.Call heap value (heap.tick "work") (value + 1) := by
  refine ⟨trivial, ?_⟩
  intro caller
  apply Reaches.prepend (Step.increment_pc3 _ _ caller)
  apply Reaches.prepend (Step.increment_pc2 _ _ caller)
  exact Reaches.single (Step.increment_pc1 _ _ caller)

example (heap : Heap) (value : Int) :
    increment.Run heap value (heap.tick "work") (value + 1) :=
  (increment_call heap value).run

theorem increment_cost (value : Int) :
    increment.ReturnsWithCost value (value + 1) (Clocks.single "work" 1) := by
  refine ⟨({} : Heap).tick "work", (increment_call {} value).run, ?_⟩
  change Heap.cost ({} : Heap) (({} : Heap).tick "work") = _
  rw [← Heap.charge_single, Heap.cost_charge]

example (value : Int) : increment.Returns value (value + 1) :=
  (increment_cost value).returns

example (value : Int) :
    ∃ costs, increment.ReturnsWithCost value (value + 1) costs :=
  (increment_cost value).returns.withCost

-- The three public output shapes must all support the same cost bridge.
example {input output costs} (run : same.ReturnsWithCost input output costs) :
    same.Returns input output := run.returns
example {input output} (run : same.Returns input output) :
    ∃ costs, same.ReturnsWithCost input output costs := run.withCost
example {input output costs} (run : identity.ReturnsWithCost input output costs) :
    identity.Returns input output := run.returns
example {input output} (run : identity.Returns input output) :
    ∃ costs, identity.ReturnsWithCost input output costs := run.withCost

example (heap after : Heap) (ref : SeqRef)
    (call : same.Call heap ref after ref) : same.Run heap ref after ref := call.run
example (heap after : Heap) (ref : Ref_Counter)
    (call : identity.Call heap ref after ref) : identity.Run heap ref after ref := call.run

end ScopedProof
'''

POINTS = '''
#check same.At.ready
#check same.Local.a
#check same.Element.a
#check «lemma».At.«by»
#check «lemma».Local.«theorem»
#check «lemma».Element.«theorem»

-- Locations and observations need only the supplied local state.
example (heap : Heap) (ref : SeqRef) : same.At.ready (same.initial heap ref) := by
  trivial
example (heap : Heap) (ref : SeqRef) :
    same.Local.a (same.initial heap ref) = some ref := rfl
example (heap : Heap) (ref : SeqRef) (index : Int) :
    same.Element.a (same.initial heap ref) index = some (heap.read ref index) := rfl
'''

API = '''from algo2lean import Interface
class Counter(Interface):
    def get(self) -> Int: ...
    def put(self, value: Int) -> None: ...
'''
CLIENT = '''from api import Counter

def bump(q: Counter) -> Int:
    # @read
    value = q.get()
    q.put(value + 1)
    return value
'''
BACKEND = '''class Storage:
    value: Int
    def __init__(self) -> None:
        self.value = 0
    def get(self) -> Int:
        return self.value
    def put(self, value: Int) -> None:
        tick("writes")
        self.value = value
'''
WRAPPER = '''from backend import Storage
from client import bump as advance

def run() -> Int:
    queue = Storage()
    return advance(queue)
'''


class ScopedNameStabilityTests(unittest.TestCase):
    def test_label_changes_only_change_the_points_module(self):
        changed = SOURCE.replace("# @ready", "# @observed").replace("# @by", "# @then")
        original_single = compile_source(SOURCE, filename="scoped.algo")
        changed_single = compile_source(changed, filename="scoped.algo")
        self.assertEqual(original_single.lean, changed_single.lean)
        self.assertNotEqual(original_single.points_lean, changed_single.points_lean)
        with tempfile.TemporaryDirectory() as directory:
            original = compile_project("scoped", root=directory, sources={"scoped": SOURCE})
            revised = compile_project("scoped", root=directory, sources={"scoped": changed})
        self.assertEqual(original.entry.lean, revised.entry.lean)
        self.assertEqual(original.entry.facts_lean, revised.entry.facts_lean)
        self.assertNotEqual(original.entry.points_lean, revised.entry.points_lean)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ScopedNameLeanTests(unittest.TestCase):
    def assert_checked(self, checked):
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses 'sorry'", checked.output)

    def test_standalone_primary_names_methods_constructors_and_escaped_names(self):
        functions = [("increment", "increment"), ("same", "same"),
                     ("identity", "identity"), ("«lemma»", "lemma"),
                     ("Counter", "Counter"), ("Counter.add", "Counter_add"),
                     ("Counter.__init__", "Counter___init__")]
        for namespace in (None, "Wrapped"):
            with self.subTest(namespace=namespace):
                compiled = compile_source(SOURCE, filename="scoped.algo", namespace=namespace)
                assert_no_legacy_declarations(self, compiled.lean, compiled.points_lean)
                analysis = "\nopen Algo2LeanCore Algo2LeanGenerated\n"
                if namespace:
                    analysis += "open Wrapped Wrapped.Algo2LeanGenerated\n"
                analysis += interface_checks(functions, namespace + "." if namespace else "")
                analysis += SCALAR_CALL + POINTS
                self.assert_checked(check_lean(compiled.lean, module=compiled.module,
                    points_lean=compiled.points_lean + analysis, timeout=120))

    def test_removed_flat_names_are_not_accepted_by_lean(self):
        compiled = compile_source(SOURCE, filename="scoped.algo")
        removed = [prefix + "same" for prefix in LEGACY_PREFIXES.values()] + [
            "At_same_ready", "local_same_a", "element_same_a",
            "is_Summary_Counter_add", "is_Summary_Counter",
        ]
        analysis = "\n" + "\n".join("#check " + name for name in removed) + "\n"
        checked = check_lean(compiled.lean, module=compiled.module,
            points_lean=compiled.points_lean + analysis, timeout=120)
        self.assertFalse(checked.ok, checked.output)
        for name in removed:
            self.assertIn("Unknown identifier `" + name + "`", checked.output)

    def test_same_method_name_in_different_scopes_and_lone_underscore(self):
        source = '''class Left:
    def __init__(self) -> None:
        return
    def add(self) -> Int:
        return 1
class Right:
    def __init__(self) -> None:
        return
    def add(self) -> Int:
        return 2
def add(value: Int) -> Int:
    return value + 3
def _(value: Int) -> Int:
    # @_
    return value
'''
        compiled = compile_source(source, filename="scope_collisions.algo")
        analysis = '''
#check Left.add.Call
#check Right.add.Call
#check add.Call
#check «_».Call
#check «_».At.«_»
#check «_».Local.value
'''
        self.assert_checked(check_lean(compiled.lean, module=compiled.module,
            points_lean=compiled.points_lean + analysis, timeout=120))

    def test_root_identifier_and_keyword_labels_use_importable_metadata_names(self):
        cases = {
            "function": '''def _root_(value: Seq) -> Seq:
    # @_root_
    return value
''',
            "local": '''def keep(_root_: Seq) -> Seq:
    # @def
    return _root_
''',
            "class_method": '''class _root_:
    def __init__(self) -> None:
        return
    def _root_(self) -> Int:
        return 0
''',
        }
        for name, source in cases.items():
            with self.subTest(placement=name):
                compiled = compile_source(source, filename="reserved_" + name + ".algo")
                analysis = "\n"
                assert_no_legacy_declarations(self, compiled.lean, compiled.points_lean)
                for function in compiled.functions:
                    analysis += "#check @%s.Call\n" % function["lean_name"]
                    analysis += "#check @%s\n" % function["output_relation"]
                    for point in function["points"]:
                        analysis += "#check @%s\n" % point["relation"]
                if name == "local":
                    analysis += "#check keep.Local.«_root_·»\n#check keep.Element.«_root_·»\n"
                self.assert_checked(check_lean(compiled.lean, module=compiled.module,
                    points_lean=compiled.points_lean + analysis, timeout=120))

    def test_project_facts_support_primary_run_dot_eq_of_call(self):
        analysis = '''import Algo.scoped.Points
import Algo.scoped.Facts
open Algo2LeanCore Algo2LeanGenerated Algo.scoped Algo.scoped.Algo2LeanGenerated
'''
        analysis += interface_checks([("increment", "increment"), ("same", "same"),
            ("identity", "identity"), ("Counter.add", "Counter_add"), ("Counter", "Counter")],
            "Algo.scoped.")
        analysis += SCALAR_CALL + POINTS + '''
example (heap after : Heap) (value output : Int)
    (run : increment.Run heap value after output) :
    after = heap.tick "work" ∧ output = value + 1 :=
  run.eq_of_call (ScopedProof.increment_call heap value)
'''
        with tempfile.TemporaryDirectory(prefix="algo2lean-scoped-") as directory:
            compiled = compile_project("scoped", root=directory, sources={"scoped": SOURCE})
            assert_no_legacy_declarations(self, compiled.entry.lean,
                compiled.entry.points_lean, compiled.entry.facts_lean)
            self.assert_checked(check_project(compiled, analysis=analysis))

    def test_generic_primary_names_retain_dependency_parameters_and_optional_facts(self):
        analysis = '''import Algo.wrapper.Facts
import Algo.client.Points
open Algo2LeanCore Algo2LeanGenerated
'''
        analysis += interface_checks([("bump", "bump")], "Algo.client.")
        analysis += '''
#check Algo.api.Counter.get.Call
#check Algo.api.Counter.put.Call
#check Algo.client.bump.At.read
#check Algo.client.bump.Local.q

example (dependencies : Algo.client.Dependencies) (heap after : Heap)
    (ref : ObjectRef) (output : Int)
    (call : Algo.client.bump.Call dependencies heap ref after output) :
    Algo.client.bump.Run dependencies heap ref after output := call.run

example (dependencies : Algo.client.Dependencies)
    (facts : Algo.client.DependencyFacts dependencies)
    (heap after expectedHeap : Heap) (ref : ObjectRef) (output expected : Int)
    (run : Algo.client.bump.Run dependencies heap ref after output)
    (call : Algo.client.bump.Call dependencies heap ref expectedHeap expected) :
    after = expectedHeap ∧ output = expected := run.eq_of_call facts call

example (dependencies : Algo.client.Dependencies) {input output costs}
    (run : Algo.client.bump.ReturnsWithCost dependencies input output costs) :
    Algo.client.bump.Returns dependencies input output := run.returns

example (dependencies : Algo.client.Dependencies) {input output}
    (run : Algo.client.bump.Returns dependencies input output) :
    ∃ costs, Algo.client.bump.ReturnsWithCost dependencies input output costs := run.withCost

-- Import aliases do not change the defining module's public identity.
#check Algo.backend.Storage.get.Call
#check Algo.wrapper.run.Call
'''
        sources = {"api": API, "client": CLIENT, "backend": BACKEND, "wrapper": WRAPPER}
        with tempfile.TemporaryDirectory(prefix="algo2lean-scoped-generic-") as directory:
            generic = compile_project("client", root=directory, sources=sources)
            wrapper = compile_project("wrapper", root=directory, sources=sources)
            self.assertEqual(generic.entry.lean, wrapper.modules["client"].lean)
            self.assertEqual(generic.entry.facts_lean, wrapper.modules["client"].facts_lean)
            self.assert_checked(check_project(wrapper, analysis=analysis))

    def test_imported_scoped_proof_is_reusable_without_recompiling_its_algorithm(self):
        sources = {
            "lib.increment": 'def increment(value: Int) -> Int:\n    tick("work")\n    return value + 1\n',
            "caller": 'from lib.increment import increment as advance\n\ndef twice(value: Int) -> Int:\n    return advance(advance(value))\n',
        }
        library_proof = '''import Algo.lib.increment.Generated
open Algo2LeanCore Algo2LeanGenerated Algo.lib.increment Algo.lib.increment.Algo2LeanGenerated
namespace ExistingProof
theorem summary (heap : Heap) (value : Int) :
    increment.Call heap value (heap.tick "work") (value + 1) := by
  refine ⟨trivial, ?_⟩
  intro caller
  apply Reaches.prepend (Step.increment_pc3 _ _ caller)
  apply Reaches.prepend (Step.increment_pc2 _ _ caller)
  exact Reaches.single (Step.increment_pc1 _ _ caller)
end ExistingProof
'''
        analysis = '''import Algo.caller.Facts
import Algo.lib.increment.Analysis
open Algo2LeanGenerated

example (heap : Heap) (value : Int) :
    Algo.lib.increment.increment.Call heap value (heap.tick "work") (value + 1) :=
  ExistingProof.summary heap value

example (heap after : Heap) (value output : Int)
    (run : Algo.lib.increment.increment.Run heap value after output) :
    after = heap.tick "work" ∧ output = value + 1 :=
  run.eq_of_call (ExistingProof.summary heap value)

#check Algo.caller.twice.Returns
'''
        with tempfile.TemporaryDirectory(prefix="algo2lean-scoped-import-") as directory:
            original = compile_project("lib.increment", root=directory, sources=sources)
            caller = compile_project("caller", root=directory, sources=sources)
            self.assertEqual(original.entry.lean, caller.modules["lib.increment"].lean)
            self.assert_checked(check_project(caller, analysis=analysis,
                proof_sources={"Algo.lib.increment.Analysis": library_proof}))


if __name__ == "__main__":
    unittest.main()
