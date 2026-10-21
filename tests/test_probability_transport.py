"""Probability contracts survive unrelated result tags in imported modules."""

from pathlib import Path
import shutil
import unittest

from algo2lean.modular import compile_project
from algo2lean.probability_checker import check_probability_sources


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/probability_calls"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ProbabilityTransportTests(unittest.TestCase):
    def test_multiple_callee_result_tags_reuse_original_contract(self):
        sampler = (FIXTURE / "sampler.algo").read_text(encoding="utf-8")
        sampler += "\ndef other() -> Bool:\n    return True\n"
        compiled = compile_project("client", root=FIXTURE, sources={
            "client": (FIXTURE / "client.algo").read_text(encoding="utf-8"),
            "sampler": sampler,
        })
        sources = {name: source for name, source in compiled.files.items()
                   if name.endswith((".Generated", ".Facts", ".Probability"))}
        sources["Algo.sampler.Analysis"] = (FIXTURE / "analysis/sampler.lean").read_text(encoding="utf-8")
        sources["ModuleTransportAnalysis"] = (ROOT / "tests/proofs/probability_module_transport.lean").read_text(encoding="utf-8")
        checked = check_probability_sources(sources, timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
