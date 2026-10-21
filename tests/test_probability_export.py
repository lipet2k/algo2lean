"""Randomized downloads include their exact probability semantics and dependencies."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from algo2lean.browser import request as compiler_request
from algo2lean.compiler import compile_source
from algo2lean.editor_examples import load_example_project
from editor.analysis_export import request
from scripts.build_site import compiler_files
from tests.test_analysis_export import unpack


ROOT = Path(__file__).resolve().parents[1]
SOURCE = "def die() -> Int:\n    return randint(1, 7)\n"
ANALYSIS = "import DieGeneratedProbability\nnoncomputable example : Unit → Int → ENNReal := die.outputProbability\n"
BODY = {"source": SOURCE, "filename": "die.algo", "analysis": ANALYSIS,
        "analysis_filename": "Proof.lean"}
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


def composed_call_body():
    fixture = ROOT / "tests/fixtures/probability_calls"
    return {"filename": "driver.algo", "source": (fixture / "driver.algo").read_text(),
            "project_sources": {name + ".algo": (fixture / (name + ".algo")).read_text()
                                for name in ("sampler", "client", "driver")},
            "project_analyses": {"Algo." + name + ".Analysis":
                (fixture / "analysis" / (name + ".lean")).read_text()
                for name in ("sampler", "client", "driver")},
            "analysis": (fixture / "analysis/driver.lean").read_text()}


class ProbabilityExportTests(unittest.TestCase):
    def assert_complete(self, files):
        self.assertIn("Algo2LeanProbability.lean", files)
        self.assertIn("Algo2LeanLib/Choice.lean", files)
        self.assertIn(b'[[require]]\nname = "mathlib"', files["lakefile.toml"])
        self.assertIn(b"lake exe cache get", b"\n".join(value for key, value in files.items() if key.endswith(".md")))
        self.assertNotIn("lake-manifest.json", files)
        self.assertFalse(any(".lake/" in name for name in files))

    def test_generation_and_analysis_archives_include_probability_sources(self):
        generation = unpack(compiler_request("/api/generation", {**BODY, "archive": True}))
        analysis = unpack(request("/api/analysis-export", BODY))
        compiled = compile_source(SOURCE, filename="die.algo")
        for files in (generation, analysis):
            self.assert_complete(files)
            self.assertEqual(files["DieGeneratedProbability.lean"], compiled.probability_lean.encode())
        self.assertEqual(analysis["Proof.lean"], ANALYSIS.encode())
        self.assertIn(b'defaultTargets = ["Proof"]', analysis["lakefile.toml"])

    def test_project_imports_export_their_probability_dependencies(self):
        caller = "from die import die\ndef roll() -> Int:\n    return die()\n"
        body = {"source": caller, "filename": "main.algo",
                "project_sources": {"main.algo": caller, "die.algo": SOURCE},
                "analysis": "import Algo.main.Probability\n#check Algo.main.roll.outputProbability\n"}
        files = unpack(request("/api/analysis-export", body, project=True))
        self.assert_complete(files)
        self.assertIn("Algo/die/Probability.lean", files)
        self.assertIn("Algo/main/Probability.lean", files)
        self.assertNotIn("Algo/main/Facts.lean", files)

    def test_deterministic_mathlib_analysis_can_opt_in_without_random_syntax(self):
        body = {**BODY, "source": "def die() -> Int:\n    return 6\n",
                "analysis": "import DieGenerated\nimport Mathlib.Data.Nat.Basic\n"}
        files = unpack(request("/api/analysis-export", body))
        self.assertIn(b'[[require]]\nname = "mathlib"', files["lakefile.toml"])
        self.assertNotIn("Algo2LeanProbability.lean", files)
        self.assertNotIn("Algo2LeanLib/Choice.lean", files)
        self.assertNotIn("DieGeneratedProbability.lean", files)

    def test_browser_bundle_has_optional_sources_but_no_mathlib_cache(self):
        files = compiler_files(ROOT)
        self.assertIn("probability/Algo2LeanProbability.lean", files)
        self.assertIn("probability/lakefile.toml", files)
        self.assertFalse(any(".lake/" in name for name in files))

    def test_total_cost_bridge_exports_its_complete_optional_imports(self):
        body = {**BODY, "analysis": "import Algo2LeanProbability.CallObservations\n" + ANALYSIS}
        files = unpack(request("/api/analysis-export", body))
        for module in ("Algo2LeanProbability.lean", "Algo2LeanProbability/Call.lean",
                       "Algo2LeanProbability/Observations.lean", "Algo2LeanProbability/CallObservations.lean"):
            self.assertEqual(files[module], (ROOT / "probability" / module).read_bytes())

    def test_nested_call_analysis_exports_shared_composition_rules(self):
        files = unpack(request("/api/analysis-export", composed_call_body(), project=True))
        self.assert_complete(files)
        for name in ("sampler", "client", "driver"):
            self.assertIn("Algo/" + name + "/Analysis.lean", files)
        for module in ("Call", "CallTransport", "CallContext"):
            path = "Algo2LeanProbability/" + module + ".lean"
            self.assertEqual(files[path], (ROOT / "probability" / path).read_bytes())


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ProbabilityExportBuildTests(unittest.TestCase):
    def build(self, files, target):
        with tempfile.TemporaryDirectory(prefix="algo2lean-probability-export-") as directory:
            root = Path(directory)
            for name, contents in files.items():
                exported_path = root / name
                exported_path.parent.mkdir(parents=True, exist_ok=True)
                exported_path.write_bytes(contents)
            # Reuse only the externally installed Mathlib packages. Every
            # Algo2Lean module is rebuilt from the downloaded source archive.
            manifest = json.loads((ROOT / "probability/lake-manifest.json").read_text())
            manifest["name"] = "algo2lean_analysis"
            manifest["packages"] = [p for p in manifest["packages"] if p["name"] != "algo2lean"]
            for package in manifest["packages"]:
                link = root / ".lake/packages" / package["name"]
                link.parent.mkdir(parents=True, exist_ok=True)
                link.symlink_to(ROOT / "probability/.lake/packages" / package["name"], target_is_directory=True)
            (root / "lake-manifest.json").write_text(json.dumps(manifest))
            environment = dict(os.environ)
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            checked = subprocess.run([shutil.which("lake"), "--no-cache", "build"],
                cwd=root, env=environment, capture_output=True, text=True, timeout=180)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertTrue((root / ".lake/build/lib/lean" / target).is_file())

    def test_download_builds_without_repository_sources_on_lean_path(self):
        self.build(unpack(request("/api/analysis-export", BODY)), "Proof.olean")

    def test_nested_contract_download_builds_in_isolation(self):
        files = unpack(request("/api/analysis-export", composed_call_body(), project=True))
        self.build(files, "Algo/driver/Analysis.olean")

    def test_coupon_runtime_download_builds_with_shared_reward_rules(self):
        project = load_example_project("randomized_clrs")
        body = {"filename": "coupon_collector.algo",
                "source": project["sources"]["coupon_collector.algo"],
                "project_sources": project["sources"],
                "project_analyses": project["analyses"],
                "analysis": project["analyses"]["Algo.coupon_collector.Analysis"]}
        files = unpack(request("/api/analysis-export", body, project=True))
        for module in ("CallRewards", "CallObservations", "Observations"):
            path = "Algo2LeanProbability/" + module + ".lean"
            self.assertEqual(files[path], (ROOT / "probability" / path).read_bytes())
        self.build(files, "Algo/coupon_collector/Analysis.olean")


if __name__ == "__main__":
    unittest.main()
