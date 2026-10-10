"""Cross-module proof reuse must be checked against both actual compilations."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.checker import prepare_lean_environment
from algo2lean.compiler import compile_source
from algo2lean.embedding import emit_embedding
from algo2lean.frontend import CompileError


ROOT = Path(__file__).resolve().parents[1]
SIMPLE = 'def increment(x: Int) -> Int:\n    return x + 1\n'
CLIENT = '\ndef caller(x: Int) -> Int:\n    return increment(x)\n'


class EmbeddingValidationTests(unittest.TestCase):
    def test_missing_or_changed_behavior_is_rejected(self):
        cases = [
            ('def other(x: Int) -> Int:\n    return x\n', 'missing'),
            (SIMPLE.replace('x + 1', 'x + 2') + CLIENT, 'changed'),
            (SIMPLE.replace('x: Int', 'x: Bool').replace('x + 1', '1'), 'changed'),
        ]
        for target, message in cases:
            with self.subTest(target=target), self.assertRaisesRegex(CompileError, message):
                emit_embedding(SIMPLE, target)

    def test_labels_and_positions_do_not_change_the_certificate(self):
        labeled = '\n# A separate location map\n' + SIMPLE.replace('    return', '    # @result\n    return')
        self.assertEqual(emit_embedding(SIMPLE, SIMPLE + CLIENT), emit_embedding(labeled, SIMPLE + CLIENT))
        self.assertEqual(emit_embedding(SIMPLE, SIMPLE + CLIENT), emit_embedding(SIMPLE, labeled + CLIENT))

    def test_function_names_containing_pc_do_not_confuse_transition_numbers(self):
        source = SIMPLE.replace('increment', 'increment_pc987')
        target = source + CLIENT.replace('increment', 'increment_pc987')
        certificate = emit_embedding(source, target)
        self.assertIn('theorem summary_increment_pc987', certificate)

    def test_class_schema_changes_are_rejected(self):
        source = 'class Cell:\n    value: Int\n    def __init__(self) -> None:\n        self.value = 0\n'
        target = source.replace('value: Int', 'value: Bool').replace('self.value = 0', 'self.value = False')
        with self.assertRaisesRegex(CompileError, "class 'Cell'.*changed"):
            emit_embedding(source, target)

    def test_stored_fibonacci_adapter_matches_current_source_and_emitter(self):
        source = (ROOT / 'examples/fibonacci_heap.algo').read_text(encoding='utf-8')
        target = (ROOT / 'examples/dijkstra_fibonacci.algo').read_text(encoding='utf-8')
        expected = emit_embedding(source, target,
            source_module='Algo2LeanExamples.FibonacciHeapGenerated',
            target_module='DijkstraFibonacciGenerated',
            source_namespace='FibonacciHeapLibrary', namespace='FibonacciQueueEmbedding')
        actual = (ROOT / 'examples/analysis/support/FibonacciHeapIntoDijkstra.lean').read_text(encoding='utf-8')
        self.assertEqual(actual, expected,
            'Regenerate the checked adapter when its source component, target, or emitter changes')

    def test_stored_graph_adapters_match_current_sources_and_emitter(self):
        source = (ROOT / 'examples/graph.algo').read_text(encoding='utf-8')
        for stem, module, namespace in (
                ('dijkstra', 'DijkstraGenerated', 'GraphIntoDijkstra'),
                ('dijkstra_fibonacci', 'DijkstraFibonacciGenerated', 'GraphIntoDijkstraFibonacci')):
            with self.subTest(backend=stem):
                target = (ROOT / ('examples/' + stem + '.algo')).read_text(encoding='utf-8')
                expected = emit_embedding(source, target,
                    source_module='Algo2LeanExamples.GraphGenerated', target_module=module,
                    source_namespace='GraphLibrary', namespace=namespace)
                actual = (ROOT / ('examples/analysis/support/' + namespace + '.lean')).read_text(encoding='utf-8')
                self.assertEqual(actual, expected,
                    'Regenerate the graph adapter when its source component, target, or emitter changes')

    def test_names_are_validated_and_qualified_imports_supported(self):
        for bad in ('../Escape', 'A; import Bad', 'A..B', 'A.\nBad', ''):
            with self.subTest(bad=bad), self.assertRaises(CompileError):
                emit_embedding(SIMPLE, SIMPLE + CLIENT, source_module=bad)
        for kwargs in ({'source_namespace': 'A.B'}, {'namespace': None},
                       {'source_namespace': 'Same', 'target_namespace': 'Same'}):
            with self.subTest(kwargs=kwargs), self.assertRaises(CompileError):
                emit_embedding(SIMPLE, SIMPLE + CLIENT, **kwargs)
        result = emit_embedding(SIMPLE, SIMPLE + CLIENT, source_module='Examples.Component')
        self.assertIn('import «Examples».«Component»', result)
        self.assertIn('theorem summary_increment', result)
        self.assertNotIn('sorry', result)
        self.assertNotIn('axiom', result)


@unittest.skipUnless(shutil.which('lean'), 'Lean 4 is not installed')
class EmbeddingCheckingTests(unittest.TestCase):
    def check_modules(self, modules, *, rejected_module=None):
        environment = prepare_lean_environment(modules=('Algo2LeanLib.Embedding',))
        with tempfile.TemporaryDirectory(prefix='algo2lean-embedding-test-') as directory:
            environment['LEAN_PATH'] = directory + os.pathsep + environment['LEAN_PATH']
            for name, source in modules:
                path = Path(directory).joinpath(*name.split('.')).with_suffix('.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding='utf-8')
                result = subprocess.run(
                    ['lean', '--root=' + directory, '-o', str(path.with_suffix('.olean')), str(path)],
                    cwd=ROOT, env=environment, capture_output=True, text=True, timeout=90)
                if name == rejected_module:
                    self.assertNotEqual(result.returncode, 0, "A mismatched compiled target must reject the certificate")
                    return
                self.assertEqual(result.returncode, 0, name + '\n' + result.stdout + result.stderr)
                self.assertNotIn("declaration uses `sorry`", result.stdout)

    def check_embedding(self, source, target, *, source_module='LibraryGenerated',
                        source_namespace='Library', target_namespace=None):
        modules = [
            (source_module, compile_source(source, module=source_module.split('.')[-1],
                                           namespace=source_namespace).lean),
            ('ApplicationGenerated', compile_source(target, module='ApplicationGenerated',
                                                     namespace=target_namespace).lean),
            ('Embedding', emit_embedding(source, target, source_module=source_module,
                                         source_namespace=source_namespace, target_namespace=target_namespace)),
        ]
        self.check_modules(modules)

    def test_classes_calls_loops_aliases_collections_and_ticks(self):
        source = '''class Counter:
    value: Int
    def __init__(self, n: Int) -> None:
        self.value = n
    def add(self, n: Int) -> Int:
        self.value = self.value + n
        tick("work", 2)
        return self.value

def work(a: Seq, n: Int) -> Int:
    c = Counter(0)
    cells: Seq[Counter | None] = const(None)
    cells[0] = c
    alias = a
    i = 0
    while i < n:
        alias[i] = c.add(i)
        i = i + 1
    return c.value
'''
        target = source + '\ndef caller(n: Int) -> Int:\n    a = const(0)\n    return work(a, n)\n'
        self.check_embedding(source, target, target_namespace='Application')

    def test_recursive_single_function_handles_extra_result_constructors(self):
        source = '''def recurse(n: Int) -> Int:
    if n <= 0:
        return 0
    return recurse(n - 1)
'''
        target = source + '\ndef extra() -> Bool:\n    return True\n'
        self.check_embedding(source, target, source_module='Examples.Recursive')

    def test_previously_proved_summary_is_reused_with_its_clock_effect(self):
        source = 'def answer() -> Int:\n    tick("work", 3)\n    return 42\n'
        target = source + '\ndef caller() -> Int:\n    return answer()\n'
        proof = '''import LibraryGenerated
open Algo2LeanCore Algo2LeanGenerated
namespace LibraryProof
open Library Library.Algo2LeanGenerated
theorem answer (heap : Heap) : Library.answer.Call heap () (heap.tick "work" 3) 42 := by
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.answer_pc3 _ _ _)
  apply Reaches.prepend (Step.answer_pc2 _ _ _)
  exact Reaches.single (Step.answer_pc1 _ _ _)
end LibraryProof
'''
        reuse = '''import LibraryProof
import Embedding
open Algo2LeanGenerated
example (heap : Heap) : answer.Call heap () (heap.tick "work" 3) 42 :=
  LibraryEmbedding.summary_answer (LibraryProof.answer heap)
'''
        self.check_modules([
            ('LibraryGenerated', compile_source(source, module='LibraryGenerated', namespace='Library').lean),
            ('ApplicationGenerated', compile_source(target, module='ApplicationGenerated').lean),
            ('LibraryProof', proof),
            ('Embedding', emit_embedding(source, target)),
            ('Reuse', reuse),
        ])

    def test_kernel_rejects_a_certificate_against_different_compiled_behavior(self):
        target = SIMPLE + CLIENT
        self.check_modules([
            ('LibraryGenerated', compile_source(SIMPLE, module='LibraryGenerated', namespace='Library').lean),
            ('ApplicationGenerated', compile_source(target.replace('x + 1', 'x + 2'), module='ApplicationGenerated').lean),
            ('Embedding', emit_embedding(SIMPLE, target)),
        ], rejected_module='Embedding')

    def test_real_fibonacci_heap_is_embedded_in_dijkstra(self):
        source = (ROOT / 'examples/fibonacci_heap.algo').read_text(encoding='utf-8')
        target = (ROOT / 'examples/dijkstra_fibonacci.algo').read_text(encoding='utf-8')
        self.check_embedding(source, target, source_module='Examples.FibonacciHeapGenerated',
                             source_namespace='FibonacciHeapLibrary')
