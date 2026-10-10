"""The editor project API resolves only explicitly supplied browser files."""

import http.client
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import threading
import unittest
from unittest.mock import patch
import zipfile

from algo2lean.checker import CheckResult
from algo2lean.server import EditorHandler, MAX_SOURCE_BYTES, ThreadingHTTPServer


HELPER = "def increment(value: Int) -> Int:\n    return value + 1\n"
MAIN = "from helper import increment\n\ndef caller(value: Int) -> Int:\n    return increment(value)\n"
PROOF = "import Algo.main.Generated\n#check Algo.main.caller.Returns\n"


class ProjectServerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.server = ThreadingHTTPServer(("127.0.0.1", 0), EditorHandler)
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        cls.thread.join(timeout=3)

    def request(self, path, payload, *, project=True, headers=None):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port, timeout=30)
        request_headers = {"Content-Type": "application/json"}
        if project:
            request_headers["X-Algo2Lean-Project"] = "1"
        request_headers.update(headers or {})
        connection.request("POST", path, json.dumps(payload), request_headers)
        response = connection.getresponse()
        data, status, content_type = response.read(), response.status, response.getheader("Content-Type")
        connection.close()
        return status, data, content_type

    def payload(self, **changes):
        return {"filename": "main.algo", "source": MAIN,
                "project_sources": {"main.algo": MAIN, "helper.algo": HELPER}, **changes}

    def post(self, path="/api/compile", **changes):
        status, data, _ = self.request(path, self.payload(**changes))
        return status, json.loads(data)

    def test_compile_keeps_module_boundaries_and_selected_unsaved_source(self):
        changed = MAIN.replace("caller", "renamed_caller")
        status, response = self.post(source=changed)
        self.assertEqual(status, 200)
        self.assertTrue(response["ok"])
        self.assertEqual(response["module"], "Algo.main.Generated")
        self.assertEqual(response["points_module"], "Algo.main.Points")
        self.assertIn("renamed_caller.Returns", response["lean"])
        self.assertNotIn("inductive Step", response["points_lean"])
        self.assertEqual([module["name"] for module in response["project_modules"]], ["helper", "main"])
        self.assertIn("Algo.helper.Generated", response["project_files"])
        self.assertIn("Algo.main.Facts", response["project_files"])
        self.assertNotIn("def increment.Returns", response["lean"])
        self.assertEqual(response["functions"][0]["name"], "renamed_caller")

    def test_check_passes_compilation_and_proofs_without_selecting_analysis(self):
        proofs = {"Algo.helper.Analysis": "import Algo.helper.Generated\n"}
        with patch("algo2lean.project_checker.check_project", return_value=CheckResult(True, True, "checked")) as check:
            status, response = self.post("/api/check", project_analyses=proofs)
        self.assertEqual(status, 200)
        self.assertTrue(response["ok"])
        compiled, = check.call_args.args
        self.assertEqual(compiled.project.entry, "main")
        self.assertEqual(compiled.project.source_overlays["helper.algo"], HELPER)
        self.assertEqual(check.call_args.kwargs, {"proof_sources": proofs, "analysis_module": None})

    def test_analyze_uses_active_proof_and_preserves_imported_file_diagnostics(self):
        output = ("Algo/helper/Analysis.lean:7:3: error: first proof failed\n"
                  "Algo/main/Analysis.lean:11:0: error(lean.unknownIdentifier): unknown theorem\n")
        with patch("algo2lean.project_checker.check_project", return_value=CheckResult(False, True, output)) as check:
            status, response = self.post("/api/analyze", analysis=PROOF,
                project_analyses={"Algo.main.Analysis": "old editor text", "Algo.helper.Analysis": "import Algo.helper.Generated\n"})
        self.assertEqual(status, 200)
        self.assertFalse(response["ok"])
        self.assertEqual(response["scope"], "analysis")
        self.assertEqual(check.call_args.kwargs["analysis_module"], "Algo.main.Analysis")
        self.assertEqual(check.call_args.kwargs["proof_sources"]["Algo.main.Analysis"], PROOF)
        self.assertEqual([(item["module"], item["line"], item["column"])
                          for item in response["analysis_diagnostics"]], [("helper", 7, 4), ("main", 11, 1)])

    def test_missing_dependencies_identify_the_source_file(self):
        with patch("algo2lean.project_checker.check_project") as check:
            status, response = self.post("/api/check", project_sources={"main.algo": MAIN})
        self.assertEqual(status, 400)
        self.assertFalse(response["ok"])
        self.assertEqual(response["diagnostics"][0]["file"], "main.algo")
        self.assertIn("helper", response["diagnostics"][0]["message"])
        check.assert_not_called()

    def test_project_api_requires_explicit_header(self):
        for path in ("/api/compile", "/api/check", "/api/analyze", "/api/project-export"):
            with self.subTest(path=path):
                status, raw, _ = self.request(path, self.payload(analysis=PROOF), project=False)
                self.assertEqual(status, 400)
                self.assertIn("X-Algo2Lean-Project", json.loads(raw)["message"])

    def test_paths_and_disk_roots_cannot_escape_the_browser_project(self):
        for name in ("../helper.algo", "/tmp/helper.algo", "../project/helper.algo"):
            with self.subTest(name=name):
                status, response = self.post(project_sources={"main.algo": MAIN, name: HELPER})
                self.assertEqual(status, 400)
                self.assertIn("relative .algo filenames", response["diagnostics"][0]["message"])
        with tempfile.TemporaryDirectory(prefix="algo2lean-unselected-") as directory:
            (Path(directory) / "helper.algo").write_text(HELPER, encoding="utf-8")
            status, response = self.post(root=directory, project_root=directory, project_sources={"main.algo": MAIN})
        self.assertEqual(status, 400)
        self.assertIn("was not found", response["diagnostics"][0]["message"])

    def test_invalid_project_shapes_are_rejected_before_checking(self):
        for changes in ({"project_sources": {}}, {"project_sources": []},
                        {"project_sources": {"main.algo": 1}}, {"project_analyses": []},
                        {"project_analyses": {"../Proof": "import Std\n"}},
                        {"project_analyses": {"Algo.helper.Analysis": 1}}, {"standalone": True}):
            with self.subTest(changes=changes), patch("algo2lean.project_checker.check_project") as check:
                status, response = self.post("/api/check", **changes)
                self.assertEqual(status, 400)
                self.assertFalse(response["ok"])
                check.assert_not_called()

    def test_source_size_limit_includes_the_current_unsaved_buffer(self):
        over_limit = HELPER + "\n# " + "α" * (MAX_SOURCE_BYTES // 2)
        self.assertGreater(len(over_limit.encode("utf-8")), MAX_SOURCE_BYTES)
        with patch("algo2lean.project_checker.check_project") as check:
            status, response = self.post("/api/check", source=over_limit)
        self.assertEqual(status, 413)
        self.assertFalse(response["ok"])
        check.assert_not_called()

    def test_invalid_active_analysis_is_scoped_to_analysis(self):
        for analysis in (None, "", "  ", "example : True := by\x00"):
            with self.subTest(analysis=analysis):
                status, response = self.post("/api/analyze", analysis=analysis)
                self.assertEqual(status, 400)
                self.assertEqual(response["scope"], "analysis")
                self.assertTrue(response["analysis_diagnostics"])

    def test_busy_checker_and_missing_lean_are_readable(self):
        with patch("algo2lean.server.LEAN_SLOTS") as slots:
            slots.acquire.return_value = False
            status, response = self.post("/api/analyze", analysis=PROOF)
        self.assertEqual(status, 429)
        self.assertEqual(response["scope"], "analysis")
        slots.release.assert_not_called()
        with patch("algo2lean.project_checker.check_project", return_value=CheckResult(False, False, "Lean not installed")):
            status, response = self.post("/api/check")
        self.assertEqual(status, 200)
        self.assertFalse(response["available"])
        self.assertEqual(response["output"], "Lean not installed")

    def test_untrusted_project_posts_are_rejected_before_compilation(self):
        with patch("algo2lean.modular.compile_project") as compile_mock:
            for headers in ({"Origin": "https://example.org"}, {"Host": "example.org"}, {"Sec-Fetch-Site": "cross-site"}):
                with self.subTest(headers=headers):
                    status, _, _ = self.request("/api/compile", self.payload(), headers=headers)
                    self.assertEqual(status, 403)
        compile_mock.assert_not_called()

    def test_export_contains_sources_proofs_and_shared_lean_modules(self):
        status, raw, content_type = self.request("/api/project-export", self.payload(
            analysis=PROOF, project_analyses={"Algo.helper.Analysis": "import Algo.helper.Generated\n"}))
        self.assertEqual(status, 200)
        self.assertEqual(content_type, "application/zip")
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            names = set(archive.namelist())
            self.assertTrue({"Algo/main/Generated.lean", "Algo/main/Points.lean", "Algo/main/Facts.lean",
                             "Algo/helper/Generated.lean", "Algo/main/Analysis.lean", "Algo/helper/Analysis.lean",
                             "Algo2Lean.lean", "Algo2LeanLib/Modules.lean", "source/main.algo", "source/helper.algo",
                             "lakefile.toml", "lean-toolchain", "LICENSE"}.issubset(names))
            self.assertEqual(archive.read("source/main.algo").decode(), MAIN)
            self.assertEqual(archive.read("Algo/main/Analysis.lean").decode(), PROOF)
            self.assertTrue(archive.read("Algo2Lean.lean").startswith(b"import Std"))
            license = (Path(__file__).resolve().parents[1] / "LICENSE").read_bytes()
            self.assertEqual(archive.read("LICENSE"), license)
            self.assertIn(b"/-\n" + license + b"-/", archive.read("Algo2Lean.lean"))
            self.assertIn(b"does not assign a license to your algorithm or proof", archive.read("README.md"))
            self.assertFalse(any(name.startswith("/") or ".." in Path(name).parts for name in names))

    def test_export_preserves_unfinished_sources_and_active_proofs(self):
        for source in ("def incomplete(\n", "from missing import helper\n" + HELPER):
            with self.subTest(source=source):
                status, raw, content_type = self.request("/api/project-export", self.payload(
                    source=source, analysis="", project_analyses={"Algo.main.Analysis": "old proof", "Algo.helper.Analysis": "unfinished proof"}))
                self.assertEqual(status, 200)
                self.assertEqual(content_type, "application/zip")
                with zipfile.ZipFile(io.BytesIO(raw)) as archive:
                    self.assertEqual(archive.read("source/main.algo").decode(), source)
                    self.assertEqual(archive.read("source/helper.algo").decode(), HELPER)
                    self.assertEqual(archive.read("source/analysis/main.lean"), b"")
                    self.assertEqual(archive.read("source/analysis/helper.lean"), b"unfinished proof")
                    self.assertIn(b"draft backup", archive.read("README.md"))
                    self.assertTrue(archive.read("EXPORT_DIAGNOSTICS.txt"))
                    self.assertNotIn(b"algo2lean-editor-project-", archive.read("EXPORT_DIAGNOSTICS.txt"))
                    self.assertNotIn("lakefile.toml", archive.namelist())
                    self.assertFalse(any(name.startswith("Algo/") for name in archive.namelist()))

    def test_export_preserves_drafts_when_a_proof_import_is_missing(self):
        proof = "import Algo.unwritten.Analysis\nexample : True := .intro\n"
        status, raw, content_type = self.request("/api/project-export", self.payload(analysis=proof))
        self.assertEqual((status, content_type), (200, "application/zip"))
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            self.assertEqual(archive.read("source/main.algo").decode(), MAIN)
            self.assertEqual(archive.read("source/analysis/main.lean").decode(), proof)
            self.assertIn(b"Algo.unwritten.Analysis", archive.read("EXPORT_DIAGNOSTICS.txt"))
            self.assertIn(b"Generated Lean build files are unavailable", archive.read("README.md"))
            self.assertNotIn("lakefile.toml", archive.namelist())

    def test_draft_export_still_rejects_unsafe_paths_case_collisions_and_size_limits(self):
        changes = [
            {"project_sources": {"main.algo": MAIN, "../outside.algo": HELPER}},
            {"project_sources": {"main.algo": MAIN, "while.algo": HELPER}},
            {"project_sources": {"main.algo": MAIN, "Main.algo": HELPER}},
            {"project_analyses": {"Algo.Main.Analysis": "-- proof"}},
            {"project_analyses": {"../outside": "-- proof"}},
            {"source": "x" * (MAX_SOURCE_BYTES + 1)},
            {"analysis": "-- current", "project_analyses": {f"Algo.proof_{index}.Analysis": "-- proof" for index in range(256)}},
        ]
        with patch("algo2lean.modular.compile_project") as compile_mock:
            for change in changes:
                with self.subTest(change=list(change)):
                    status, raw, content_type = self.request("/api/project-export", self.payload(**change))
                    self.assertIn(status, {400, 413})
                    self.assertIn("application/json", content_type)
                    self.assertFalse(json.loads(raw)["ok"])
        compile_mock.assert_not_called()

    @unittest.skipUnless(shutil.which("lake"), "Lean's Lake build tool is not installed")
    def test_exported_proof_only_algorithm_closure_builds_independently(self):
        extra = "from helper import increment\ndef extra(value: Int) -> Int:\n    return increment(value)\n"
        proof = ("import Algo.extra.Generated\nimport Algo.extra.Facts\n"
                 "example : Int → Int → Prop := Algo.extra.extra.Returns\n")
        analysis = "import Algo.main.Generated\nimport Algo.extra.Analysis\n"
        status, raw, content_type = self.request("/api/project-export", self.payload(
            project_sources={"main.algo": MAIN, "helper.algo": HELPER, "extra.algo": extra,
                             "unused.algo": "An unfinished, unused source file."},
            project_analyses={"Algo.extra.Analysis": proof}, analysis=analysis))
        self.assertEqual(status, 200, raw)
        self.assertEqual(content_type, "application/zip")
        with tempfile.TemporaryDirectory(prefix="algo2lean-export-check-") as directory:
            with zipfile.ZipFile(io.BytesIO(raw)) as archive:
                names = set(archive.namelist())
                self.assertTrue({"Algo/extra/Generated.lean", "Algo/extra/Facts.lean", "Algo/extra/Analysis.lean",
                                 "source/extra.algo", "source/analysis/extra.lean"}.issubset(names))
                self.assertNotIn("Algo/unused/Generated.lean", names)
                self.assertFalse(any(name.startswith("/") or ".." in Path(name).parts for name in names))
                archive.extractall(directory)
            environment = os.environ.copy()
            environment.pop("LEAN_PATH", None)
            checked = subprocess.run(["lake", "build", "Algo.main.Analysis"], cwd=directory, env=environment,
                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_analysis_can_reuse_a_proof_only_algorithm_from_browser_sources(self):
        extra = "from helper import increment\ndef extra(value: Int) -> Int:\n    return increment(value)\n"
        proof = "import Algo.extra.Generated\nimport Algo.extra.Facts\n#check Algo.extra.extra.Run.eq_of_call\n"
        status, response = self.post("/api/analyze",
            project_sources={"main.algo": MAIN, "helper.algo": HELPER, "extra.algo": extra},
            project_analyses={"Algo.extra.Analysis": proof},
            analysis="import Algo.main.Generated\nimport Algo.extra.Analysis\n")
        self.assertEqual(status, 200)
        self.assertTrue(response["ok"], response.get("output", response))

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_pipeline_checks_from_browser_sources_and_proofs(self):
        root = Path(__file__).resolve().parents[1] / "examples/modules"
        sources = {name + ".algo": (root / (name + ".algo")).read_text(encoding="utf-8")
                   for name in ("increment", "twice", "pipeline")}
        proofs = {"Algo." + name + ".Analysis": (root / "analysis" / (name + ".lean")).read_text(encoding="utf-8")
                  for name in ("increment", "twice", "pipeline")}
        status, response = self.post("/api/analyze", filename="pipeline.algo", source=sources["pipeline.algo"],
            project_sources=sources, project_analyses=proofs, analysis=proofs["Algo.pipeline.Analysis"])
        self.assertEqual(status, 200)
        self.assertTrue(response["ok"], response.get("output", response))
        self.assertEqual(response["analysis_diagnostics"], [])


if __name__ == "__main__":
    unittest.main()
