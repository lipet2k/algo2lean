"""Proof-check path rewards, runtime moments, and charged random draws."""

from pathlib import Path
import shutil
import unittest

from algo2lean.compiler import compile_source
from algo2lean.probability_checker import check_probability_sources


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ProbabilityObservationsTests(unittest.TestCase):
    def test_complete_path_rewards_and_runtime_tails(self):
        proof = (ROOT / "tests/proofs/probability_observations.lean").read_text(encoding="utf-8")
        checked = check_probability_sources({"ObservationsAnalysis": proof}, timeout=120)
        self.assertTrue(checked.ok, checked.output)

    def test_generated_charged_draw_joint_reward_and_runtime_moment(self):
        compiled = compile_source(
            'def charged_draw() -> Int:\n'
            '    value = randint(0, 4)\n'
            '    tick("work", value)\n'
            '    return value\n', module="ChargedDraw")
        proof = (ROOT / "tests/proofs/probability_charged_draw.lean").read_text(encoding="utf-8")
        checked = check_probability_sources({
            "ChargedDraw": compiled.lean,
            "ChargedDrawProbability": compiled.probability_lean,
            "ChargedDrawAnalysis": proof,
        }, timeout=120)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
