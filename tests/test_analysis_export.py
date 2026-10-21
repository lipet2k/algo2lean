"""Analysis bundles build from their own sources, without repository imports."""

import base64
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

from algo2lean.browser import request as compiler_request
from algo2lean.compiler import compile_source
from algo2lean.server import MAX_ANALYSIS_BYTES, MAX_ANALYSIS_REQUEST_BYTES, ThreadingHTTPServer
from editor.analysis_export import request
from editor.server import EditorHandler


ROOT = Path(__file__).resolve().parents[1]
SOURCE = "def identity(x: Int) -> Int:\n    # @result\n    return x\n"
PROOF = ("import IdentityGeneratedPoints\nopen Algo2LeanGenerated\n"
         "example : Int → Int → Prop := identity.Returns\n"
         "example : Configuration → Prop := identity.At.result\n")
HELPER = "def increment(x: Int) -> Int:\n    return x + 1\n"
CALLER = "from helper import increment\n\ndef caller(x: Int) -> Int:\n    return increment(x)\n"


def payload(**changes):
    return {"source": SOURCE, "filename": "identity.algo", "analysis": PROOF,
            "analysis_filename": "Proof.lean", **changes}


def project_payload(**changes):
    return {"source": CALLER, "filename": "main.algo",
            "project_sources": {"main.algo": CALLER, "helper.algo": HELPER},
            "project_analyses": {"Algo.helper.Analysis": "import Algo.helper.Generated\n"
                                 "theorem reusable : True := True.intro\n"},
            "analysis": "import Algo.main.Points\nimport Algo.helper.Analysis\n"
                        "example : True := reusable\n", **changes}


def unpack(response):
    if response["status"] != 200:
        raise AssertionError(response)
    if response["content_type"] != "application/zip" or response.get("encoding") != "base64":
        raise AssertionError(response)
    with zipfile.ZipFile(io.BytesIO(base64.b64decode(response["body"], validate=True))) as archive:
        return {name: archive.read(name) for name in archive.namelist()}


class AnalysisExportTests(unittest.TestCase):
    def test_standalone_preserves_exact_source_proof_and_compiler_output(self):
        body = payload(source="# café\r\n" + SOURCE.replace("\n", "\r\n"),
                       analysis="-- unchanged α\r\n" + PROOF.replace("\n", "\r\n"))
        files = unpack(request("/api/analysis-export", body))
        compiled = compile_source(body["source"], filename=body["filename"])
        self.assertEqual(files["Proof.lean"], body["analysis"].encode())
        self.assertEqual(files["source/identity.algo"], body["source"].encode())
        self.assertEqual(files["IdentityGenerated.lean"], compiled.lean.encode())
        self.assertEqual(files["IdentityGeneratedPoints.lean"], compiled.points_lean.encode())
        self.assertEqual(files["LICENSE"], (ROOT / "LICENSE").read_bytes())
        self.assertEqual(files["lean-toolchain"], (ROOT / "lean-toolchain").read_bytes())
        self.assertIn(b'defaultTargets = ["Proof"]', files["lakefile.toml"])
        self.assertIn(b"does not check the proof", files["README.md"])
        self.assertIn(b"does not assign a license", files["README.md"])
        self.assertEqual(request("/api/analysis-export", body), request("/api/analysis-export", body))

    def test_shared_example_libraries_include_transitive_sources_and_lake_root(self):
        body = payload(analysis="import IdentityGenerated\nimport Algo2LeanExamples.Factorial\n"
                       "#check FactorialAnalysis.output\n")
        files = unpack(request("/api/analysis-export", body))
        self.assertIn("Algo2LeanExamples/Factorial.lean", files)
        self.assertIn("Algo2LeanExamples/FactorialGenerated.lean", files)
        self.assertIn("Algo2Lean.lean", files)
        self.assertIn(b'[[lean_lib]]\nname = "Algo2LeanExamples"', files["lakefile.toml"])

    def test_recursive_packaged_support_sources_are_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            support = Path(directory) / "examples/analysis/support"
            support.mkdir(parents=True)
            first = "import ExportSupportB\nexample : True := True.intro\n"
            second = "import IdentityGeneratedPoints\n#check identity.At.result\n"
            (support / "ExportSupportA.lean").write_text(first)
            (support / "ExportSupportB.lean").write_text(second)
            with patch("algo2lean.analysis.ROOT", Path(directory)):
                files = unpack(request("/api/analysis-export", payload(analysis="import ExportSupportA\n")))
            self.assertEqual(files["ExportSupportA.lean"], first.encode())
            self.assertEqual(files["ExportSupportB.lean"], second.encode())

    def test_project_preserves_frozen_export_sources_and_selects_active_proof(self):
        body = project_payload(analysis="import Algo.main.Points\nimport Algo.helper.Analysis\n"
                               "import Algo2LeanExamples.Factorial\nexample : True := reusable\n")
        before = unpack(compiler_request("/api/project-export", body, project=True))
        files = unpack(request("/api/analysis-export", body, project=True))
        for name, contents in before.items():
            if name not in {"lakefile.toml", "README.md"}:
                self.assertEqual(files[name], contents, name)
        self.assertEqual(files["Algo/main/Analysis.lean"], body["analysis"].encode())
        self.assertIn(b'defaultTargets = ["Algo.main.Analysis"]', files["lakefile.toml"])
        self.assertIn(b'[[lean_lib]]\nname = "Algo2LeanExamples"', files["lakefile.toml"])

    def test_missing_imports_or_failed_compilation_never_return_a_successful_bundle(self):
        cases = [(False, payload(analysis="import MissingProof\n")),
                 (False, payload(analysis="import MissingLibrary\n")),
                 (False, payload(analysis="import Algo2LeanExamples.NotAnExample\n")),
                 (False, payload(analysis="import Proof\n")),
                 (False, payload(source="def broken(\n")),
                 (True, project_payload(source="def broken(\n")),
                 (True, project_payload(analysis="import Algo.missing.Analysis\n")),
                 (True, project_payload(analysis="import MissingLibrary\n"))]
        for project, body in cases:
            with self.subTest(project=project, body=body):
                response = request("/api/analysis-export", body, project=project)
                self.assertEqual(response["status"], 400, response)
                self.assertFalse(response["body"]["ok"])
                self.assertEqual(response["content_type"], "application/json; charset=utf-8")

    def test_archive_paths_and_module_collisions_are_rejected(self):
        for name in ("../Proof.lean", "/tmp/Proof.lean", "folder/Proof.lean", "Proof\\Other.lean",
                     "bad-name.lean", "two words.lean", "Proof.lean/", "Lean.lean", "Std.lean",
                     "Algo2Lean.lean", "Algo2LeanLib.lean", "IdentityGenerated.lean", "identitygeneratedpoints.lean"):
            with self.subTest(name=name):
                self.assertEqual(request("/api/analysis-export", payload(analysis_filename=name))["status"], 400)
        body = project_payload(project_sources={"../main.algo": CALLER})
        self.assertEqual(request("/api/analysis-export", body, project=True)["status"], 400)
        body = project_payload(project_sources={"main.algo": CALLER, "helper.algo": HELPER, "Helper.algo": HELPER})
        self.assertEqual(request("/api/analysis-export", body, project=True)["status"], 400)

    def test_text_limits_invalid_characters_and_project_flag_are_validated(self):
        for analysis in (None, 7, "", " ", "a\x00", "a\ud800", "a" * (MAX_ANALYSIS_BYTES + 1)):
            with self.subTest(analysis=str(analysis)[:20]):
                self.assertEqual(request("/api/analysis-export", payload(analysis=analysis))["status"], 400)
        self.assertEqual(request("/api/analysis-export", payload(), project=1)["status"], 400)
        self.assertEqual(request("/api/analysis-export", [])["status"], 400)
        self.assertEqual(request("/api/analysis-export", {**payload(), "padding": "a" * MAX_ANALYSIS_REQUEST_BYTES})["status"], 413)
        self.assertEqual(request("/api/analysis-export", project_payload())["status"], 400)
        response = request("/api/analysis-export", payload(standalone=True))
        self.assertEqual(response["status"], 400)
        self.assertIn("separate generated modules", response["body"]["message"])

    def test_export_does_not_run_lean_and_all_other_routes_keep_frozen_behavior(self):
        with patch("subprocess.run", side_effect=AssertionError("export must not execute Lean")):
            unpack(request("/api/analysis-export", payload(analysis="import IdentityGenerated\nnot valid Lean\n")))
        self.assertEqual(request("/api/compile", {"source": SOURCE}), compiler_request("/api/compile", {"source": SOURCE}))
        self.assertEqual(request("/api/capabilities")["body"]["analysis_export_protocol"], 1)
        for path in ("/api/analysis-export?extra=1", "https://example.org/api/analysis-export", "/../analysis_export.py"):
            self.assertNotEqual(request(path, payload())["status"], 200)


@unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
class AnalysisExportBuildTests(unittest.TestCase):
    def build(self, files, selected_path):
        with tempfile.TemporaryDirectory(prefix="algo2lean-export-build-") as directory:
            root = Path(directory)
            for name, contents in files.items():
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(contents)
            environment = dict(os.environ)
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            completed = subprocess.run([shutil.which("lake"), "build"], cwd=root, env=environment,
                                       capture_output=True, text=True, timeout=180)
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            self.assertTrue((root / ".lake/build/lib/lean" / selected_path).with_suffix(".olean").is_file(),
                            "The default Lake target must build the selected analysis.")

    def test_standalone_points_build_without_repository_search_paths(self):
        self.build(unpack(request("/api/analysis-export", payload())), Path("Proof.lean"))

    def test_shared_example_builds_without_repository_search_paths(self):
        proof = "import IdentityGeneratedPoints\nimport Algo2LeanExamples.Factorial\n" + PROOF.split("\n", 1)[1]
        self.build(unpack(request("/api/analysis-export", payload(analysis=proof))), Path("Proof.lean"))

    def test_project_imported_analysis_builds_as_default_target(self):
        self.build(unpack(request("/api/analysis-export", project_payload(), project=True)),
                   Path("Algo/main/Analysis.lean"))


class AnalysisExportServerTests(unittest.TestCase):
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

    def http(self, method, path, body=None, headers=None):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port, timeout=10)
        connection.request(method, path, body, headers or {})
        response = connection.getresponse()
        result = response.status, response.getheader("Content-Type"), response.read()
        connection.close()
        return result

    def test_local_service_serves_current_assets_capabilities_and_zip(self):
        for path in ("/", "/interface.js", "/analysis_export.py"):
            self.assertEqual(self.http("GET", path)[0], 200)
        status, _, data = self.http("GET", "/api/capabilities")
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(data)["analysis_export_protocol"], 1)
        status, content_type, data = self.http("POST", "/api/analysis-export", json.dumps(payload()),
                                               {"Content-Type": "application/json"})
        self.assertEqual(status, 200)
        self.assertEqual(content_type, "application/zip")
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            self.assertEqual(archive.read("Proof.lean"), PROOF.encode())

    def test_export_keeps_local_origin_and_request_size_restrictions(self):
        for headers in ({"Origin": "https://example.org"}, {"Sec-Fetch-Site": "cross-site"}, {"Host": "example.org"}):
            status, _, _ = self.http("POST", "/api/analysis-export", json.dumps(payload()),
                                      {"Content-Type": "application/json", **headers})
            self.assertEqual(status, 403)
        self.assertEqual(self.http("POST", "/api/analysis-export", "{}", {"Content-Type": "text/plain"})[0], 415)
        self.assertEqual(self.http("POST", "/api/analysis-export", "{", {"Content-Type": "application/json"})[0], 400)
        self.assertEqual(self.http("POST", "/api/analysis-export", "", {"Content-Type": "application/json",
                                                                               "Content-Length": str(MAX_ANALYSIS_REQUEST_BYTES + 1)})[0], 413)


if __name__ == "__main__":
    unittest.main()
