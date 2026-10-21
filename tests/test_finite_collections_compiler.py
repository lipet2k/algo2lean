"""Finite container generation preserves ordinary imports and shared references."""

from pathlib import Path
import unittest

from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project


class FiniteCollectionCompilerTests(unittest.TestCase):
    def test_operations_compile_with_shared_optional_runtime(self):
        source = (Path(__file__).parent / 'proofs/finite_collections.algo').read_text()
        result = compile_source(source, module='FiniteCollectionsGenerated')
        self.assertTrue(result.lean.startswith('import Algo2LeanLib.FiniteCollections\n'))
        self.assertNotIn('Mathlib', result.lean)
        self.assertIn('DictType Int (Option Ref_Cell)', result.lean)
        self.assertIn('SetType (Ref_Cell × Bool)', result.lean)
        self.assertIn('«dict[Int, Int]».valid', result.lean)

    def test_plain_input_output_retains_heap_and_collection_identity(self):
        result = compile_source('def identity(values: Dict[Int, Bool]) -> Dict[Int, Bool]:\n    return values\n')
        self.assertEqual(result.functions[0]['lean_input_type'], 'Heap × (CollectionRef)')
        self.assertEqual(result.functions[0]['lean_output_type'], 'Heap × (CollectionRef)')

    def test_labels_leave_container_definitions_identical(self):
        source = 'def example() -> Set[Int]:\n    # @create\n    values = {1, 2}\n    return values\n'
        self.assertEqual(compile_source(source).lean, compile_source(source.replace('@create', '@new')).lean)

    def test_imported_aliases_preserve_container_tags_and_module_bytes(self):
        sources = {
            'nodes': 'class Node:\n    key: Int\ndef one(n: Node) -> Dict[Node, Int]:\n    return {n: 1}\n',
            'client': 'from nodes import Node as Vertex, one\ndef run(n: Vertex) -> Dict[Vertex, Int]:\n    return one(n)\n',
        }
        result = compile_project('client', sources=sources)
        self.assertEqual(result.modules['nodes'].lean, compile_project('nodes', sources=sources).entry.lean)
        self.assertIn('keyName := "nodes.Node"', result.entry.lean)

    def test_standalone_resolves_shared_finite_runtime(self):
        result = compile_source('def empty() -> Dict[Int, Bool]:\n    return {}\n', standalone=True)
        self.assertEqual(result.lean.count('inductive ObjectValue'), 1)
        self.assertIn('structure DictType', result.lean)
        self.assertNotIn('import Algo2Lean', result.lean)


if __name__ == '__main__':
    unittest.main()
