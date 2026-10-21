"""The local values-and-collections project opens and exports all dependencies."""

import base64
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from algo2lean.browser import request
from algo2lean.editor_examples import EXAMPLES, load_example_project, project_examples
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean").is_file())


class AdditionalTypeExamplesTests(unittest.TestCase):
    def test_project_is_discoverable_without_compilation(self):
        with patch("algo2lean.editor_examples.compile_project", side_effect=AssertionError("Catalog must stay cheap")):
            entry, = [entry for entry in project_examples() if entry["project_id"] == "additional_types"]
        self.assertEqual(entry["name"], "Values and collections")
        self.assertEqual(entry["filename"], "main.algo")
        self.assertEqual(entry["folder"], "additional_types")
        self.assertIn("exact real arithmetic", entry["description"])
        catalog = request("/api/examples")["body"]["examples"]
        self.assertTrue(any(item.get("project_id") == "additional_types" for item in catalog))
        self.assertTrue(any(item.get("filename") == "merge_sort.algo" for item in catalog))

    def test_each_source_opens_independently_and_preserves_narrow_imports(self):
        bundle = load_example_project("additional_types")
        self.assertEqual(bundle["entry"], "main.algo")
        self.assertEqual(set(bundle["sources"]), {"main.algo", "histogram.algo", "visited.algo", "centroid.algo"})
        with tempfile.TemporaryDirectory() as directory:
            for path, text in bundle["sources"].items():
                with self.subTest(path=path):
                    self.assertEqual(text, (EXAMPLES / "additional_types" / path).read_text())
                    compiled = compile_project(path, root=directory, sources=bundle["sources"])
                    imports = "\n".join(compiled.files.values())
                    self.assertNotIn("Algo2LeanProbability", imports)
                    if path in {"histogram.algo", "visited.algo"}:
                        self.assertNotIn("Algo2LeanReal", imports)
                        self.assertIn("Algo2LeanLib.FiniteCollections", imports)
                    else:
                        self.assertIn("Algo2LeanReal", imports)

    def test_project_download_preserves_sources_and_shared_real_libraries(self):
        bundle = load_example_project("additional_types")
        body = {"source": bundle["sources"][bundle["entry"]], "filename": bundle["entry"],
                "project_sources": bundle["sources"], "project_analyses": bundle["analyses"]}
        response = request("/api/project-export", body, project=True)
        self.assertEqual(response["status"], 200, response)
        with zipfile.ZipFile(io.BytesIO(base64.b64decode(response["body"]))) as archive:
            names = set(archive.namelist())
            self.assertNotIn("EXPORT_DIAGNOSTICS.txt", names)
            for filename, source in bundle["sources"].items():
                self.assertEqual(archive.read("source/" + filename).decode(), source)
                self.assertIn("Algo/" + Path(filename).stem + "/Generated.lean", names)
            self.assertTrue({"Algo2LeanReal.lean", "Algo2Lean.lean", "Algo2LeanLib/Tuple.lean",
                             "Algo2LeanLib/FiniteCollections.lean", "lakefile.toml", "lean-toolchain"}.issubset(names))
            self.assertNotIn("Algo2LeanProbability.lean", names)
            self.assertIn(b'name = "mathlib"', archive.read("lakefile.toml"))


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Real Mathlib cache is not installed")
class AdditionalTypeExamplesLeanTests(unittest.TestCase):
    def test_composed_project_and_isolated_download_check(self):
        bundle = load_example_project("additional_types")
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project(bundle["entry"], root=directory, sources=bundle["sources"])
            checked = check_project(compiled, timeout=120)
            self.assertTrue(checked.ok, checked.output)
        body = {"source": bundle["sources"][bundle["entry"]], "filename": bundle["entry"],
                "project_sources": bundle["sources"], "project_analyses": bundle["analyses"]}
        response = request("/api/project-export", body, project=True)
        self.assertEqual(response["status"], 200, response)
        with tempfile.TemporaryDirectory(prefix="algo2lean-values-export-") as directory:
            root = Path(directory)
            with zipfile.ZipFile(io.BytesIO(base64.b64decode(response["body"]))) as archive:
                archive.extractall(root)
            # Only external Mathlib dependencies may reuse installed artifacts.
            # All Algo2Lean modules are rebuilt from the downloaded sources.
            manifest = json.loads((ROOT / "probability/lake-manifest.json").read_text())
            manifest["name"] = "algo2lean_project"
            manifest["packages"] = [package for package in manifest["packages"] if package["name"] != "algo2lean"]
            for package in manifest["packages"]:
                target = root / ".lake/packages" / package["name"]
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(ROOT / "probability/.lake/packages" / package["name"], target_is_directory=True)
            (root / "lake-manifest.json").write_text(json.dumps(manifest))
            environment = dict(os.environ)
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            count = int(environment.get("GIT_CONFIG_COUNT", "0"))
            environment.update({"GIT_CONFIG_COUNT": str(count + 1),
                                "GIT_CONFIG_KEY_%d" % count: "protocol.allow",
                                "GIT_CONFIG_VALUE_%d" % count: "never"})
            built = subprocess.run([shutil.which("lake"), "--no-cache", "build"],
                cwd=root, env=environment, capture_output=True, text=True, timeout=180)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            self.assertTrue((root / ".lake/build/lib/lean/Algo/main/Generated.olean").is_file())
            self.assertTrue((root / ".lake/build/lib/lean/Algo2LeanReal.olean").is_file())


if __name__ == "__main__":
    unittest.main()
