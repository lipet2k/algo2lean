"""The same generic correctness and cost proof links two concrete backends."""
from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project

ROOT = Path(__file__).resolve().parents[1] / 'examples' / 'interfaces'

@unittest.skipUnless(shutil.which('lean'), 'Lean 4 is not installed')
class InterfaceExamplesTests(unittest.TestCase):
    def test_a_linked_component_is_reused_unchanged_by_an_external_consumer(self):
        names = ['direct', 'counter', 'increment', 'use_direct']
        proofs = {name: (ROOT / 'analysis' / (name + '.lean')).read_bytes() for name in names}
        compiled = {name: compile_project(name, root=ROOT).entry for name in names}
        project = compile_project('consumer.advance_twice', root=ROOT)
        checked = check_project(project, analysis=(
            'import Algo.consumer.advance_twice.Analysis\n'
            '#print axioms CounterConsumerAnalysis.summary\n'
            '#print axioms CounterConsumerAnalysis.correct\n'), analysis_module='Algo.Audit.Analysis')
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn('sorryAx', checked.output)
        for name in names:
            self.assertEqual(project.modules[name].lean, compiled[name].lean)
            self.assertEqual((ROOT / 'analysis' / (name + '.lean')).read_bytes(), proofs[name])
        for line in checked.output.splitlines():
            if 'depends on axioms' in line:
                for axiom in line.split('[', 1)[-1].rstrip(']').split(','):
                    self.assertIn(axiom.strip(), {'propext', 'Classical.choice', 'Quot.sound'})

    def test_both_concrete_contracts_reuse_generic_analysis(self):
        generic = (ROOT / 'analysis/increment.lean').read_bytes()
        for backend in ['direct', 'negated']:
            name = 'use_' + backend
            project = compile_project(name, root=ROOT)
            checked = check_project(project, analysis=(ROOT / 'analysis' / (name + '.lean')).read_text())
            self.assertTrue(checked.ok, checked.output)
            self.assertEqual((ROOT / 'analysis/increment.lean').read_bytes(), generic)
        both = compile_project('both', root=ROOT)
        checked = check_project(both, check_facts=True)
        self.assertTrue(checked.ok, checked.output)

    def test_concrete_theorems_have_no_contract_axiom(self):
        for backend, prefix in [('direct', 'Direct'), ('negated', 'Negated')]:
            name = 'use_' + backend
            project = compile_project(name, root=ROOT)
            proof = (f'import Algo.{name}.Analysis\n'
                     f'#print axioms {prefix}ClientAnalysis.correct\n'
                     f'#print axioms {prefix}ClientAnalysis.summary\n')
            checked = check_project(project, analysis=proof, analysis_module='Algo.Audit.Analysis')
            self.assertTrue(checked.ok, checked.output)
            self.assertNotIn('sorryAx', checked.output)
            for line in checked.output.splitlines():
                if 'depends on axioms' in line:
                    for axiom in line.split('[', 1)[-1].rstrip(']').split(','):
                        self.assertIn(axiom.strip(), {'propext', 'Classical.choice', 'Quot.sound'})

if __name__ == '__main__':
    unittest.main()
