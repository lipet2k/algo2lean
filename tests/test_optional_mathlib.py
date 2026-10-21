"""Real-only support selects Mathlib without packaging probability semantics."""

import base64
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest
from unittest.mock import patch
import zipfile

from algo2lean import browser, probability_checker as backend, probability_support as support
from algo2lean.analysis import check_analysis
from algo2lean.checker import CheckResult, LeanSetupError, check_lean
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project
from editor.analysis_export import request as analysis_request
from scripts.build_site import compiler_files


ROOT = Path(__file__).resolve().parents[1]
SOURCE = "def identity(x: Int) -> Int:\n    return x\n"
REAL_IMPORT = "import Algo2LeanReal\n"
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean").is_file())


def unpack(response):
    if isinstance(response, bytes):
        contents = response
    else:
        if response["status"] != 200:
            raise AssertionError(response)
        contents = base64.b64decode(response["body"])
    with zipfile.ZipFile(io.BytesIO(contents)) as archive:
        return {name: archive.read(name) for name in archive.namelist()}


class OptionalLibraryTests(unittest.TestCase):
    def test_capability_detection_and_narrow_source_selection(self):
        cases = [
            ("import Algo2Lean\n-- import Algo2LeanReal\n", False, ()),
            (REAL_IMPORT, True, ("Algo2LeanReal",)),
            ("import Algo2LeanProbability\n", True, ("Algo2LeanProbability",)),
            ("import Mathlib.Data.Real.Basic\n", True, ()),
            (REAL_IMPORT + "import Algo2LeanProbability\n", True,
             ("Algo2LeanProbability", "Algo2LeanReal")),
        ]
        for source, mathlib, names in cases:
            with self.subTest(source=source):
                self.assertEqual(support.needs_mathlib([source]), mathlib)
                self.assertEqual(backend.needs_mathlib(source), mathlib)
                self.assertEqual(support.needs_probability([source]), mathlib)
                self.assertEqual(backend.needs_probability(source), mathlib)
                self.assertEqual(support.required_libraries(iter([source])), names)
                self.assertEqual(set(support.optional_sources([source])), {name + ".lean" for name in names})

    def test_optional_source_dependencies_are_closed_without_duplicates(self):
        with tempfile.TemporaryDirectory() as directory:
            probability = Path(directory) / "probability"
            probability.mkdir()
            (probability / "Algo2LeanReal.lean").write_text("import Algo2LeanProbability\n")
            (probability / "Algo2LeanProbability.lean").write_text("import Algo2LeanReal\n")
            with patch.object(support, "ROOT", Path(directory)):
                self.assertEqual(support.required_libraries([REAL_IMPORT]),
                                 ("Algo2LeanProbability", "Algo2LeanReal"))

    def test_real_preflight_does_not_require_probability_mathlib_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            mathlib = project / ".lake/packages/mathlib"
            mathlib.mkdir(parents=True)
            (mathlib / "lakefile.lean").write_text("-- installed dependency\n")
            for name in ("lakefile.toml", "lean-toolchain"):
                (project / name).write_text("present\n")
            (project / "lake-manifest.json").write_text(json.dumps({"packages": [
                {"name": "mathlib", "type": "git", "configFile": "lakefile.lean"}]}))
            basic = mathlib / ".lake/build/lib/lean/Mathlib/Data/Real/Basic.olean"
            basic.parent.mkdir(parents=True)
            basic.write_bytes(b"cached")
            with patch.object(backend, "PROBABILITY_ROOT", project):
                libraries = backend._installed_dependencies({"Analysis": REAL_IMPORT})
                self.assertEqual(set(libraries), {"Algo2LeanReal.lean"})
                with self.assertRaisesRegex(LeanSetupError, "do not download"):
                    backend._installed_dependencies({"Analysis": "import Algo2LeanProbability\n"})
                with self.assertRaisesRegex(LeanSetupError, "do not download"):
                    backend._installed_dependencies({"Analysis": "import Mathlib.Data.Nat.Basic\n"})

    def test_optional_submodules_include_their_exact_source_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            probability = Path(directory) / "probability"
            (probability / "Algo2LeanProbability").mkdir(parents=True)
            (probability / "Algo2LeanProbability.lean").write_text("import Mathlib.Data.Nat.Basic\n")
            (probability / "Algo2LeanProbability/Call.lean").write_text("import Algo2LeanProbability\n")
            (probability / "Algo2LeanProbability/Unused.lean").write_text("import Algo2LeanReal\n")
            source = "import Algo2LeanProbability.Call\n"
            with patch.object(support, "ROOT", Path(directory)):
                self.assertTrue(support.needs_mathlib([source]))
                self.assertEqual(support.required_libraries([source]),
                                 ("Algo2LeanProbability", "Algo2LeanProbability.Call"))
                self.assertEqual(set(support.optional_sources([source])),
                                 {"Algo2LeanProbability.lean", "Algo2LeanProbability/Call.lean"})
                self.assertEqual(list(backend._ordered_sources({"Analysis": source})), ["Analysis"])

    def test_requested_build_targets_do_not_include_probability_by_default(self):
        for source, libraries, targets in [
            (REAL_IMPORT, {"Algo2LeanReal.lean": "import Algo2LeanLib.Tuple\n"}, ["Algo2LeanReal"]),
            ("import Algo2LeanProbability.Call\n", {"Algo2LeanProbability/Call.lean": ""},
             ["Algo2LeanProbability.Call"]),
            ("import Mathlib.Data.Real.Basic\n", {}, ["Mathlib.Data.Real.Basic"]),
        ]:
            calls = []

            def run(command, environment, deadline, **kwargs):
                calls.append(command)
                output = json.dumps({"lean": "/lean", "environment": {"LEAN_PATH": "/cached"}}) if "env" in command else ""
                return subprocess.CompletedProcess(command, 0, output, "")

            with self.subTest(source=source), \
                    patch.object(backend, "_installed_dependencies", return_value=libraries), \
                    patch.object(backend.shutil, "which", side_effect=lambda name: "/lake" if name == "lake" else None), \
                    patch.object(backend, "_run", side_effect=run), \
                    patch.object(backend, "prepare_lean_environment", return_value={"LEAN_PATH": "/current"}):
                backend._prepare({"Analysis": source}, time.monotonic() + 30)
            self.assertEqual(calls[0], ["/lake", "--no-cache", "build", *targets])

    def test_generated_and_analysis_imports_select_optional_checker(self):
        accepted = CheckResult(True, True, "optional checked")
        with patch.object(backend, "check_mathlib_sources", return_value=accepted) as check:
            self.assertEqual(check_lean(REAL_IMPORT, module="Generated"), accepted)
            self.assertEqual(check.call_args.args[0], {"Generated": REAL_IMPORT})
            self.assertEqual(check_lean("core", module="Generated", points_lean=REAL_IMPORT), accepted)
            self.assertEqual(check.call_args.args[0], {"Generated": "core", "GeneratedPoints": REAL_IMPORT})
            self.assertEqual(check_analysis(REAL_IMPORT, "import Generated\n", "Generated"), accepted)
            self.assertEqual(check.call_args.args[0]["Generated"], REAL_IMPORT)
            self.assertEqual(check_analysis("core", REAL_IMPORT, "Generated"), accepted)
            self.assertNotIn("GeneratedProbability", check.call_args.args[0])

    def test_real_project_import_is_supported_and_uses_optional_checker(self):
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project("main", root=directory, sources={"main": SOURCE})
            with patch.object(backend, "check_mathlib_sources", return_value=CheckResult(True, True, "checked")) as check, \
                    patch("algo2lean.project_checker.shutil.which", return_value="/lean"):
                checked = check_project(compiled, analysis=REAL_IMPORT)
        self.assertTrue(checked.ok, checked.output)
        self.assertIn(REAL_IMPORT, check.call_args.args[0].values())

    def test_optional_library_names_cannot_be_shadowed_by_proofs(self):
        with patch.object(backend, "_prepare") as prepare:
            checked = backend.check_mathlib_sources({"Algo2LeanReal": "example : True := True.intro\n"})
        self.assertFalse(checked.ok)
        self.assertIn("conflicts with a Lean library", checked.output)
        prepare.assert_not_called()


class OptionalExportTests(unittest.TestCase):
    def assert_real_package(self, files):
        self.assertIn("Algo2LeanReal.lean", files)
        self.assertIn("Algo2LeanLib/Tuple.lean", files)
        self.assertNotIn("Algo2LeanProbability.lean", files)
        self.assertNotIn("Algo2LeanLib/Choice.lean", files)
        self.assertIn(b'name = "Algo2LeanReal"', files["lakefile.toml"])
        self.assertIn(support.mathlib_requirement().encode(), files["lakefile.toml"])

    def test_analysis_export_only_adds_required_optional_library(self):
        body = {"source": SOURCE, "filename": "identity.algo", "analysis_filename": "Proof.lean",
                "analysis": "import IdentityGenerated\n" + REAL_IMPORT + "#check Real\n"}
        files = unpack(analysis_request("/api/analysis-export", body))
        self.assert_real_package(files)
        self.assertIn(b"lake exe cache get", files["README.md"])
        body["analysis"] = "import IdentityGenerated\nimport Mathlib.Data.Real.Basic\n"
        direct = unpack(analysis_request("/api/analysis-export", body))
        self.assertNotIn("Algo2LeanReal.lean", direct)
        self.assertNotIn("Algo2LeanProbability.lean", direct)
        self.assertIn(support.mathlib_requirement().encode(), direct["lakefile.toml"])

    def test_project_export_supports_real_and_direct_mathlib_proofs(self):
        body = {"source": SOURCE, "filename": "main.algo", "project_sources": {"main.algo": SOURCE},
                "analysis": "import Algo.main.Generated\n" + REAL_IMPORT + "#check Real\n"}
        files = unpack(analysis_request("/api/analysis-export", body, project=True))
        self.assert_real_package(files)
        self.assertIn("MATHLIB.md", files)
        body["analysis"] = "import Algo.main.Generated\nimport Mathlib.Data.Real.Basic\n"
        direct = unpack(analysis_request("/api/analysis-export", body, project=True))
        self.assertNotIn("Algo2LeanReal.lean", direct)
        self.assertNotIn("Algo2LeanProbability.lean", direct)
        self.assertIn(support.mathlib_requirement().encode(), direct["lakefile.toml"])

    def test_generated_archive_records_only_required_shared_libraries(self):
        body = {"source": SOURCE, "filename": "identity.algo"}
        compiled = browser.request("/api/compile", body)["body"]
        # Exercise dependency packaging before source Real lowering is required.
        compiled["lean"] = REAL_IMPORT + compiled["lean"]
        generated = browser.generation(body, compiled)
        self.assertIn("Algo2LeanReal.lean", generated["manifest"]["libraries"])
        self.assertNotIn("Algo2LeanProbability.lean", generated["manifest"]["libraries"])
        files = unpack(browser._generation_archive(generated, body, compiled, False))
        self.assert_real_package(files)

    def test_browser_bundle_contains_optional_sources_but_no_dependency_cache(self):
        files = compiler_files(ROOT)
        self.assertEqual(files["probability/Algo2LeanReal.lean"], (ROOT / "probability/Algo2LeanReal.lean").read_bytes())
        self.assertIn("probability/Algo2LeanProbability.lean", files)
        self.assertNotIn("probability/lake-manifest.json", files)
        self.assertFalse(any(".lake" in name.split("/") for name in files))


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Real Mathlib cache is not installed")
class RealLibraryLeanTests(unittest.TestCase):
    def test_exact_real_analysis_checks_with_narrow_library(self):
        checked = backend.check_mathlib_sources({"RealAnalysis": REAL_IMPORT + """
noncomputable section
example (x : Real) : x + 0 = x := add_zero x
example : Real × Int := ((1 : Real) / 2, 7)
"""})
        self.assertTrue(checked.ok, checked.output)
        self.assertIn("Mathlib modules and analysis", checked.output)


if __name__ == "__main__":
    unittest.main()
