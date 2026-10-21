"""Exact Real code integrates with independent modules, interfaces, and exports."""

from pathlib import Path
import shutil
import tempfile
import unittest

from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean.probability_checker import check_mathlib_sources
from algo2lean.project_checker import check_project

ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which('lake') and
    (ROOT / 'probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean').is_file())


class RealCompilerTests(unittest.TestCase):
    def test_exact_literals_optional_dependency_and_public_values(self):
        result = compile_source('def value(x: Int) -> Tuple[Real, Real]:\n    return 0.1 + x, 1e-1000\n')
        self.assertIn('import Algo2LeanReal', result.lean)
        self.assertNotIn('import Algo2LeanProbability', result.lean)
        self.assertIn('(1 / 10 : Real)', result.lean)
        self.assertIn('(1 / ' + '1' + '0' * 1000 + ' : Real)', result.lean)
        self.assertEqual(result.functions[0]['lean_output_type'], '(Real × Real)')
        plain = compile_source('def identity(n: Int) -> Int:\n    return n\n')
        self.assertNotIn('Algo2LeanReal', plain.lean)
        self.assertNotIn('noncomputable', plain.lean)

    def test_real_private_expressions_and_labels_select_backend(self):
        source = 'def positive() -> Bool:\n    # @test\n    return 0.1 > 0\n'
        first = compile_source(source)
        second = compile_source(source.replace('@test', '@renamed'))
        self.assertEqual(first.lean, second.lean)
        self.assertIn('import Algo2LeanReal', first.lean)
        # Finite-container locals expose references, without sequence-only getters.
        containers = compile_source('def f(values: Dict[Int, Int], seen: Set[Int]) -> Int:\n    # @observe\n    return len(values) + len(seen)\n')
        self.assertIn('f.Local.values', containers.points_lean)
        self.assertNotIn('f.Element.', containers.points_lean)

    def test_imported_definitions_do_not_depend_on_caller_types(self):
        sources = {
            'integer': 'def identity(x: Int) -> Int:\n    return x\n',
            'real': 'from integer import identity\ndef value(x: Int) -> Real:\n    return identity(x) / 2\n',
        }
        integer = compile_project('integer', sources=sources)
        caller = compile_project('real', sources=sources)
        self.assertEqual(integer.entry.lean, caller.modules['integer'].lean)
        self.assertNotIn('Algo2LeanReal', integer.entry.lean)


@unittest.skipUnless(MATHLIB_READY, 'The optional pinned Mathlib cache is not installed')
class RealGeneratedLeanTests(unittest.TestCase):
    def check(self, compiled, **options):
        result = check_project(compiled, check_facts=True, timeout=180, **options)
        self.assertTrue(result.ok, result.output)

    def test_deterministic_real_modules_points_and_facts(self):
        source = (ROOT / 'tests/proofs/reals.algo').read_text()
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project('reals', root=directory, sources={'reals': source})
            self.check(compiled)

    def test_real_recursive_modules_are_entry_independent(self):
        sources = {
            'first': 'from second import visit\ndef sample(n: Int, x: Real) -> Real:\n    if n <= 0:\n        return 0.1 + x\n    return visit(n - 1, x / 2)\n',
            'second': 'from first import sample\ndef visit(n: Int, x: Real) -> Real:\n    # @entry\n    return sample(n, x)\n',
        }
        with tempfile.TemporaryDirectory() as directory:
            first = compile_project('first', root=directory, sources=sources)
            second = compile_project('second', root=directory, sources=sources)
            self.assertEqual(first.files, second.files)
            self.check(first)

    def test_real_abstract_interface_and_transitive_integer_result(self):
        sources = {
            'api': 'from algo2lean import Interface\nclass Value(Interface):\n    def get(self) -> Real: ...\n',
            'client': 'from api import Value\ndef positive(value: Value) -> Bool:\n    return value.get() > 0.1\n',
            'backend': 'class Box:\n    value: Real\n    def __init__(self) -> None:\n        self.value = 0.5\n    def get(self) -> Real:\n        return self.value\n',
            'wrapper': 'from backend import Box\nfrom client import positive\ndef answer() -> Int:\n    value = Box()\n    return 1 if positive(value) else 0\n',
            'outer': 'from wrapper import answer\ndef result() -> Int:\n    return answer()\n',
        }
        with tempfile.TemporaryDirectory() as directory:
            self.check(compile_project('outer', root=directory, sources=sources))

    def test_recursive_interface_signature_selects_real_and_tuple_support(self):
        sources = {
            'first': 'from algo2lean import Interface\nfrom second import Other\nclass Value(Interface):\n    def get(self) -> Tuple[Real]: ...\ndef one() -> Int:\n    return 1\n',
            'second': 'from algo2lean import Interface\nfrom first import Value\nclass Other(Interface):\n    def get(self) -> Int: ...\n',
        }
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project('first', root=directory, sources=sources)
            implementation, = compiled.implementation_modules.values()
            self.assertIn('import Algo2LeanReal', implementation.lean)
            self.check(compiled)

    def test_real_random_choices_imported_three_layers(self):
        sources = {
            'sampling': 'def draw() -> Real:\n    return randint(0, 2) / 2\n',
            'client': 'from sampling import draw\ndef repeat() -> Tuple[Real, Real]:\n    return draw(), draw()\n',
            'outer': 'from client import repeat\ndef positive() -> Bool:\n    return repeat()[0] > 0.1\n',
        }
        with tempfile.TemporaryDirectory() as directory:
            result = compile_project('outer', root=directory, sources=sources)
            self.check(result, analysis='import Algo.outer.Probability\n', analysis_module='RealProbabilityTest')

    def test_standalone_and_namespaced_real_generation(self):
        source = 'def divide(n: Real) -> Real:\n    # @entry\n    return n / 2\n'
        compiled = compile_source(source, module='RealStandalone', standalone=True, namespace='Standalone')
        self.assertNotIn('import Algo2Lean', compiled.lean)
        self.assertEqual(compiled.lean.count('inductive ObjectValue'), 1)
        checked = check_mathlib_sources({'RealStandalone': compiled.lean,
                                        'RealStandalonePoints': compiled.points_lean}, timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == '__main__':
    unittest.main()
