"""Probability companions stay visible and distinct from ordinary Lean checks."""

import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from algo2lean.browser import _MemoryHandler, request
from algo2lean.checker import CheckResult
from algo2lean.compiler import compile_source


ROOT = Path(__file__).resolve().parents[1]
SOURCE = "def roll() -> Int:\n    return randint(1, 7)\n"


class RandomDeliveryTests(unittest.TestCase):
    def body(self, response):
        self.assertEqual(response["status"], 200, response)
        return response["body"]

    def cli(self, *arguments):
        return subprocess.run([sys.executable, "-m", "algo2lean", *map(str, arguments)],
                              cwd=ROOT, capture_output=True, text=True, timeout=40)

    def test_single_file_response_preserves_probability_companion(self):
        native = compile_source(SOURCE, filename="dice.algo")
        data = self.body(request("/api/compile", {"source": SOURCE, "filename": "dice.algo"}))
        self.assertTrue(data["randomized"])
        self.assertEqual(data["probability_module"], "DiceGeneratedProbability")
        self.assertEqual(data["probability_lean"], native.probability_lean)
        self.assertEqual(data["probability_diagnostic"], "")
        self.assertNotIn("import Algo2LeanProbability", data["lean"])

    def test_generation_hashes_cover_probability_companion(self):
        data = self.body(request("/api/generation", {"source": SOURCE, "filename": "dice.algo"}))
        name = "DiceGeneratedProbability.lean"
        content = data["files"][name].encode("utf-8")
        self.assertEqual(data["manifest"]["outputs"][name], {
            "sha256": hashlib.sha256(content).hexdigest(), "bytes": len(content),
        })

    def test_project_response_exposes_canonical_companion_without_facts(self):
        data = self.body(request("/api/compile", {
            "source": SOURCE, "filename": "main.algo", "project_sources": {"main.algo": SOURCE},
        }, project=True))
        self.assertTrue(data["randomized"])
        self.assertEqual(data["probability_module"], "Algo.main.Probability")
        self.assertEqual(data["probability_lean"], data["project_files"]["Algo.main.Probability"])
        self.assertNotIn("Algo.main.Facts", data["project_files"])

    def test_checking_definitions_does_not_claim_probability_checked(self):
        with patch.object(_MemoryHandler, "_check_generated", return_value=CheckResult(True, True, "Lean accepted")):
            data = self.body(request("/api/check", {"source": SOURCE}))
        self.assertTrue(data["ok"])
        self.assertFalse(data["probability_checked"])
        self.assertIn("separate checking", data["output"])

    def test_probability_diagnostic_is_separate_from_source_errors(self):
        result = compile_source(SOURCE)
        result.probability_diagnostic = "Probability semantics need a concrete interface implementation."
        with patch("algo2lean.server.compile_source", return_value=result):
            data = self.body(request("/api/compile", {"source": SOURCE}))
        self.assertTrue(data["ok"])
        self.assertEqual(data["diagnostics"], [])
        self.assertEqual(data["probability_diagnostic"], result.probability_diagnostic)

    def test_analysis_receives_the_matching_probability_companion(self):
        with patch.object(_MemoryHandler, "_check_analysis", return_value=CheckResult(True, True, "Lean accepted")) as check:
            data = self.body(request("/api/analyze", {
                "source": SOURCE, "filename": "dice.algo", "analysis": "import DiceGeneratedProbability\n",
            }))
        self.assertEqual(check.call_args.kwargs["probability_lean"], data["probability_lean"])
        self.assertEqual(check.call_args.kwargs["points_lean"], data["points_lean"])

    def test_cli_exports_probability_sibling_and_preserves_unchanged_text(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, output = root / "dice.algo", root / "Dice.lean"
            source.write_text(SOURCE)
            result = self.cli("compile", source, "-o", output)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((root / "DicePoints.lean").is_file())
            companion = root / "DiceProbability.lean"
            self.assertEqual(companion.read_text(), compile_source(SOURCE, module="Dice").probability_lean)
            self.assertIn("separate checking", result.stderr)
            self.assertEqual(source.read_text(), SOURCE)
            timestamp = companion.stat().st_mtime_ns
            repeated = self.cli("compile", source, "-o", output)
            self.assertEqual(repeated.returncode, 0, repeated.stderr)
            self.assertEqual(companion.stat().st_mtime_ns, timestamp)

    def test_cli_probability_alias_preflight_prevents_partial_overwrites(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, output = root / "dice.algo", root / "Dice.lean"
            points, companion = root / "DicePoints.lean", root / "DiceProbability.lean"
            source.write_text(SOURCE)
            output.write_text("existing core")
            points.write_text("existing points")
            for target in (source, output, points):
                with self.subTest(target=target.name):
                    companion.symlink_to(target)
                    result = self.cli("compile", source, "-o", output)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(source.read_text(), SOURCE)
                    self.assertEqual(output.read_text(), "existing core")
                    self.assertEqual(points.read_text(), "existing points")
                    companion.unlink()

    def test_project_cli_exports_optional_probability_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "main.algo"
            source.write_text(SOURCE)
            result = self.cli("compile", source, "--project", root, "--output-dir", root / "build")
            self.assertEqual(result.returncode, 0, result.stderr)
            module = root / "build" / "Algo" / "main"
            self.assertTrue((module / "Generated.lean").is_file())
            self.assertTrue((module / "Probability.lean").is_file())
            self.assertFalse((module / "Facts.lean").exists())


if __name__ == "__main__":
    unittest.main()
