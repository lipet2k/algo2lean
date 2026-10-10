"""Local exact-generation checks regenerate rather than trusting a manifest."""

import base64
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from algo2lean.browser import request
from algo2lean.verification import verify_generated


ROOT = Path(__file__).resolve().parents[1]
SOURCE = "def f(x: Int) -> Int:\n    # @result\n    return x + 1\n"


class VerificationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="algo2lean-verification-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.source = self.root / "example.algo"
        self.source.write_text(SOURCE, encoding="utf-8")
        self.output = self.root / "generated"
        self.output.mkdir()

    def bundle(self, payload=None, project=False):
        payload = payload or {"filename": self.source.name, "source": SOURCE}
        result = request("/api/generation", {**payload, "archive": True}, project=project)
        self.assertEqual(result["status"], 200)
        with zipfile.ZipFile(io.BytesIO(base64.b64decode(result["body"]))) as archive:
            archive.extractall(self.output)

    def test_downloaded_generation_folder_matches_without_lean(self):
        self.bundle()
        with patch("subprocess.run", side_effect=AssertionError("Lean must not run")):
            result = verify_generated(self.source, self.output)
        self.assertTrue(result["exact"])
        self.assertEqual(result["compared"], 3)

    def test_missing_extra_and_changed_files_are_reported(self):
        self.bundle()
        (self.output / "ExampleGeneratedPoints.lean").unlink()
        (self.output / "ExampleGenerated.lean").write_text("-- replaced\n")
        (self.output / "unexpected.lean").write_text("-- extra\n")
        (self.output / "generation.json").write_text('{"claimed_match": true}')
        result = verify_generated(self.source, self.output)
        self.assertFalse(result["exact"])
        self.assertEqual(result["missing"], ["ExampleGeneratedPoints.lean"])
        self.assertEqual(result["extra"], ["unexpected.lean"])
        self.assertEqual(result["different"], ["ExampleGenerated.lean"])

    def test_supplied_libraries_are_compared_and_paths_are_exact(self):
        self.bundle()
        library = self.output / "Algo2Lean.lean"
        library.write_bytes(library.read_bytes() + b"\n")
        (self.output / "wrong").mkdir()
        (self.output / "ExampleGeneratedPoints.lean").rename(self.output / "wrong/ExampleGeneratedPoints.lean")
        result = verify_generated(self.source, self.output)
        self.assertEqual(result["different"], ["Algo2Lean.lean"])
        self.assertEqual(result["missing"], ["ExampleGeneratedPoints.lean"])
        self.assertEqual(result["extra"], ["wrong/ExampleGeneratedPoints.lean"])

    def test_project_generation_bundle_matches_its_full_generated_set(self):
        caller = "from helper import f\n\ndef caller(x: Int) -> Int:\n    return f(x)\n"
        self.source.write_text(caller)
        (self.root / "helper.algo").write_text(SOURCE)
        self.bundle({"filename": self.source.name, "source": caller,
                     "project_sources": {self.source.name: caller, "helper.algo": SOURCE}}, project=True)
        self.assertFalse((self.output / "Algo.lean").exists())
        result = verify_generated(self.source, self.output, project_root=self.root)
        self.assertTrue(result["exact"], result)

    def test_cli_exit_status_and_current_source_changes(self):
        self.bundle()
        command = [sys.executable, "-m", "algo2lean", "verify", str(self.source), str(self.output)]
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Exact match", result.stdout)
        self.source.write_text(SOURCE.replace("x + 1", "x + 2"))
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 1)
        self.assertIn("Different contents: ExampleGenerated.lean", result.stdout)

    def test_standalone_is_an_explicit_generation_setting(self):
        self.bundle({"filename": self.source.name, "source": SOURCE, "standalone": True})
        self.assertTrue(verify_generated(self.source, self.output, standalone=True)["exact"])
        self.assertFalse(verify_generated(self.source, self.output)["exact"])


if __name__ == "__main__":
    unittest.main()
