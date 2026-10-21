"""Kernel-checked finite-container behavior and complete package exports."""

from pathlib import Path
import shutil
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.compiler import compile_source
from tests.test_lean import constructor_tactic


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which('lean'), 'Lean 4 is not installed')
class FiniteCollectionSemanticsTests(unittest.TestCase):
    def test_aliases_copies_nested_storage_and_evaluation_order(self):
        source = (ROOT / 'tests/proofs/finite_collections.algo').read_text()
        compiled = compile_source(source, module='FiniteCollectionsGenerated')
        proof = 'import FiniteCollectionsGenerated\n' + constructor_tactic(compiled.lean)
        proof += (ROOT / 'tests/proofs/finite_collections.lean').read_text()
        checked = check_analysis(compiled.lean, proof, compiled.module, timeout=180)
        self.assertTrue(checked.ok, checked.output)

    @unittest.skipUnless(shutil.which('lake'), 'Lake is not installed')
    def test_download_contains_the_finite_collection_runtime(self):
        from editor.analysis_export import request
        from tests.test_analysis_export import AnalysisExportBuildTests, payload, unpack
        source = 'def empty() -> Dict[Int, Bool]:\n    return {}\n'
        proof = ('import FiniteDownloadGenerated\n'
                 'open Algo2LeanGenerated\n'
                 'example : Unit → (Heap × CollectionRef) → Prop := empty.Returns\n')
        files = unpack(request('/api/analysis-export', payload(
            source=source, filename='finite_download.algo', analysis=proof)))
        self.assertIn('Algo2LeanLib/FiniteCollections.lean', files)
        self.assertIn('Algo2LeanLib/Tuple.lean', files)
        AnalysisExportBuildTests.build(self, files, Path('Proof.lean'))


if __name__ == '__main__':
    unittest.main()
