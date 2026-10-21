"""Tuple interfaces preserve source shape, reference sharing, and module identity."""

import unittest

from algo2lean import compile_source
from algo2lean.modular import compile_project


class TupleCompilerTests(unittest.TestCase):
    def test_public_values_and_explicit_reference_heaps(self):
        result = compile_source('''
def pure(pair: Tuple[Int, Bool], n: Int) -> Tuple[Bool, Int]:
    return pair[1], n

def refs(pair: Tuple[Seq, Int]) -> Tuple[Seq, Int]:
    return pair
''')
        pure, refs = result.functions
        self.assertEqual(pure['lean_input_type'], '(Int × Bool) × Int')
        self.assertEqual(pure['lean_output_type'], '(Bool × Int)')
        self.assertEqual(refs['lean_input_type'], 'Heap × ((SeqRef × Int))')
        self.assertEqual(refs['lean_output_type'], 'Heap × ((SeqRef × Int))')
        self.assertIn('import Algo2LeanLib.Tuple', result.lean)
        self.assertNotIn('Mathlib', result.lean)

    def test_labels_do_not_change_general_tuple_definitions(self):
        source = '''
def pair(x: Int) -> Tuple[Int, Bool]:
    # @result
    return x, True
'''
        first = compile_source(source)
        second = compile_source(source.replace('@result', '@answer'))
        self.assertEqual(first.lean, second.lean)
        self.assertNotEqual(first.points_lean, second.points_lean)

    def test_tuple_storage_names_are_not_underscore_flattened(self):
        source = '''
class Tuple_Int_Bool:
    x: Int
def tuples() -> Seq[Tuple[Int, Bool]]:
    return const((1, True))
def objects(value: Tuple_Int_Bool) -> Seq[Tuple_Int_Bool]:
    return const(value)
'''
        result = compile_source(source)
        self.assertIn('def «seq[Tuple[Int, Bool]]»', result.lean)
        self.assertIn('def seq_Tuple_Int_Bool', result.lean)

    def test_standalone_includes_shared_tuple_support(self):
        result = compile_source('def f() -> Tuple[Int]:\n    return (3,)\n', standalone=True)
        self.assertIn('structure Tuple1', result.lean)
        self.assertNotIn('import Algo2Lean', result.lean)
        self.assertEqual(result.lean.count('inductive ObjectValue'), 1)

    def test_imported_aliases_preserve_tuple_class_identity(self):
        sources = {
            'nodes': 'class Node:\n    key: Int\ndef pair(n: Node) -> Tuple[Node, Bool]:\n    return n, True\n',
            'client': 'from nodes import Node as Vertex, pair\ndef run(n: Vertex) -> Tuple[Vertex, Bool]:\n    return pair(n)\n',
        }
        result = compile_project('client', sources=sources)
        self.assertIn('Tuple[', result.entry.functions['run'].return_type)
        self.assertEqual(result.modules['nodes'].lean,
                         compile_project('nodes', sources=sources).entry.lean)

    def test_recursive_groups_retain_tuple_signatures(self):
        sources = {
            'even': 'from odd import odd\ndef even(n: Int) -> Tuple[Int, Bool]:\n    if n <= 0:\n        return n, True\n    return odd(n - 1)\n',
            'odd': 'from even import even\ndef odd(n: Int) -> Tuple[Int, Bool]:\n    if n <= 0:\n        return n, False\n    return even(n - 1)\n',
        }
        even = compile_project('even', sources=sources)
        odd = compile_project('odd', sources=sources)
        for name in even.modules:
            self.assertEqual(even.modules[name].lean, odd.modules[name].lean)


if __name__ == '__main__':
    unittest.main()
