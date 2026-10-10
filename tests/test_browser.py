"""Browser and native compilation share exact outputs and validation."""

import base64
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from algo2lean.browser import ROOT, request
from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project


SOURCE = "def identity(x: Int) -> Int:\n    # @result\n    return x\n"
HELPER = "def increment(x: Int) -> Int:\n    tick(\"work\", 2)\n    return x + 1\n"
CALLER = "from helper import increment as inc\n\ndef twice(x: Int) -> Int:\n    # @call\n    return inc(inc(x))\n"


class BrowserTests(unittest.TestCase):
    def project_body(self, **changes):
        return {"filename": "main.algo", "source": CALLER,
                "project_sources": {"main.algo": CALLER, "helper.algo": HELPER}, **changes}

    def body(self, response):
        self.assertEqual(response["status"], 200, response)
        self.assertEqual(response["content_type"], "application/json; charset=utf-8")
        return response["body"]

    def archive(self, response):
        self.assertEqual(response["status"], 200, response)
        self.assertEqual(response["content_type"], "application/zip")
        self.assertEqual(response["encoding"], "base64")
        raw = base64.b64decode(response["body"], validate=True)
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            return {name: archive.read(name).decode("utf-8") for name in archive.namelist()}

    def test_single_file_matches_native_compiler_byte_for_byte(self):
        for filename in ("merge_sort.algo", "classes.algo", "mutable_sequences.algo", "weighted_ticks.algo"):
            source = (ROOT / "examples" / filename).read_text(encoding="utf-8")
            with self.subTest(filename=filename):
                native = compile_source(source, filename=filename)
                result = self.body(request("/api/compile", {"filename": filename, "source": source}))
                for key in ("lean", "program_lean", "points_lean", "shared_lean", "module", "points_module", "functions", "stats"):
                    self.assertEqual(result[key], getattr(native, key))

    def test_standalone_generation_matches_native(self):
        native = compile_source(SOURCE, filename="test.algo", standalone=True)
        data = self.body(request("/api/generation", {"filename": "test.algo", "source": SOURCE, "standalone": True}))
        self.assertEqual(data["files"][native.module + ".lean"], native.lean)
        self.assertEqual(data["files"][native.points_module + ".lean"], native.points_lean)
        self.assertTrue(data["manifest"]["options"]["standalone"])
        self.assertIn("Algo2Lean.lean", data["manifest"]["libraries"])
        license = (ROOT / "LICENSE").read_text(encoding="utf-8")
        self.assertIn("/-\n" + license + "-/", native.lean)
        self.assertIn("/-\n" + license + "-/", data["libraries"]["Algo2Lean.lean"])

    def test_generation_uses_the_same_default_filename_as_the_editor(self):
        for project in (False, True):
            payload = {"source": SOURCE}
            if project:
                payload["project_sources"] = {"untitled.algo": SOURCE}
            data = self.body(request("/api/generation", payload, project=project))
            self.assertEqual(list(data["manifest"]["sources"]), ["untitled.algo"])
            self.assertEqual(data["manifest"]["options"]["entry"], "untitled.algo")

    def test_imports_match_native_and_unsaved_source_is_used(self):
        changed = CALLER.replace("twice", "updated")
        payload = self.project_body(source=changed)
        with tempfile.TemporaryDirectory() as directory:
            native = compile_project("main.algo", root=directory,
                                     sources={**payload["project_sources"], "main.algo": changed})
        data = self.body(request("/api/compile", payload, project=True))
        self.assertEqual(data["project_files"], native.files)
        self.assertEqual(data["lean"], native.entry.lean)
        self.assertIn("updated.Returns", data["lean"])
        self.assertIn("Algo.main.Facts", data["project_files"])

    def test_generation_manifest_covers_only_dependency_closure(self):
        payload = self.project_body()
        payload["project_sources"]["unused.algo"] = SOURCE
        payload["source"] = CALLER.replace("twice", "changed")
        data = self.body(request("/api/generation", payload, project=True))
        manifest = data["manifest"]
        self.assertEqual(set(manifest["sources"]), {"main.algo", "helper.algo"})
        self.assertEqual(manifest["sources"]["main.algo"]["sha256"],
                         hashlib.sha256(payload["source"].encode()).hexdigest())
        self.assertEqual(manifest["schema_version"], 1)
        self.assertEqual(manifest["options"]["mode"], "project")
        self.assertEqual(manifest["options"]["entry"], "main.algo")
        self.assertEqual(manifest["lean_toolchain"], (ROOT / "lean-toolchain").read_text().strip())
        self.assertEqual(set(manifest["outputs"]), set(data["files"]))
        self.assertIn("Algo/main/Facts.lean", data["files"])
        self.assertIn("Algo2LeanLib/Modules.lean", data["libraries"])
        for category, contents in (("outputs", data["files"]), ("libraries", data["libraries"])):
            for name, source in contents.items():
                encoded = source.encode("utf-8")
                self.assertEqual(manifest[category][name], {"sha256": hashlib.sha256(encoded).hexdigest(), "bytes": len(encoded)})

    def test_manifest_is_repeatable_and_separate_from_label_stable_core(self):
        payload = {"filename": "identity.algo", "source": SOURCE}
        first = self.body(request("/api/generation", payload))
        self.assertEqual(first, self.body(request("/api/generation", payload)))
        second = self.body(request("/api/generation", {**payload, "source": SOURCE.replace("@result", "@return_value")}))
        core = "IdentityGenerated.lean"
        points = "IdentityGeneratedPoints.lean"
        self.assertEqual(first["files"][core], second["files"][core])
        self.assertEqual(first["manifest"]["outputs"][core], second["manifest"]["outputs"][core])
        self.assertNotEqual(first["manifest"]["outputs"][points], second["manifest"]["outputs"][points])
        self.assertNotEqual(first["manifest"]["sources"], second["manifest"]["sources"])
        self.assertNotIn("source_sha256", first["files"][core])

    def test_source_identity_preserves_exact_unicode_and_newlines(self):
        source = "# café\r\n" + SOURCE.replace("\n", "\r\n")
        payload = {"filename": "/private/user/identity.algo", "source": source}
        data = self.body(request("/api/generation", payload))
        self.assertEqual(list(data["manifest"]["sources"]), ["identity.algo"])
        self.assertEqual(data["manifest"]["sources"]["identity.algo"],
                         {"sha256": hashlib.sha256(source.encode()).hexdigest(), "bytes": len(source.encode())})
        self.assertNotIn("/private/user", json.dumps(data["manifest"]))

    def test_generation_archive_is_deterministic_and_complete(self):
        for project, payload in ((False, {"source": SOURCE, "filename": "identity.algo"}),
                                 (True, self.project_body())):
            with self.subTest(project=project):
                data = self.body(request("/api/generation", payload, project=project))
                response = request("/api/generation", {**payload, "archive": True}, project=project)
                self.assertEqual(response, request("/api/generation", {**payload, "archive": True}, project=project))
                files = self.archive(response)
                self.assertEqual(json.loads(files["generation.json"]), data["manifest"])
                self.assertEqual({name for name in files if name.endswith(".lean")},
                                 set(data["files"]) | set(data["libraries"]),
                                 "The downloaded generated folder must verify against its own file map.")
                for name, source in {**data["files"], **data["libraries"]}.items():
                    self.assertEqual(files[name], source)
                self.assertEqual(files["source/" + payload["filename"]], payload["source"])
                self.assertIn("lakefile.toml", files)
                self.assertIn("lean-toolchain", files)
                self.assertEqual(files["LICENSE"], (ROOT / "LICENSE").read_text(encoding="utf-8"))
                self.assertIn("does not assign a license to your algorithm or proof", files["README.md"])
                self.assertNotIn("analysis", files)

    def test_project_export_preserves_existing_draft_backup_behavior(self):
        payload = self.project_body(source="def broken(\n", analysis="-- unfinished proof\n")
        files = self.archive(request("/api/project-export", payload, project=True))
        self.assertEqual(files["source/main.algo"], payload["source"])
        self.assertEqual(files["source/analysis/main.lean"], payload["analysis"])
        self.assertIn("EXPORT_DIAGNOSTICS.txt", files)

    def test_checker_requests_never_run_native_checker_or_subprocess(self):
        with patch("algo2lean.server.check_lean", side_effect=AssertionError("native checker")), \
             patch("algo2lean.server.check_analysis", side_effect=AssertionError("native checker")), \
             patch("algo2lean.project_checker.check_project", side_effect=AssertionError("native checker")), \
             patch("subprocess.run", side_effect=AssertionError("subprocess")):
            for path in ("/api/check", "/api/analyze"):
                for project, payload in ((False, {"source": SOURCE, "analysis": "-- proof\n"}),
                                         (True, self.project_body(analysis="-- proof\n"))):
                    with self.subTest(path=path, project=project):
                        data = self.body(request(path, payload, project=project))
                        self.assertFalse(data["available"])
                        self.assertFalse(data["ok"])
                        self.assertIn("locally", data["output"])
                        self.assertIn("lean", data)

    def test_routes_and_catalog_need_no_socket(self):
        with patch("socket.socket", side_effect=AssertionError("socket")), \
             patch("subprocess.run", side_effect=AssertionError("subprocess")):
            capabilities = self.body(request("/api/capabilities"))
            self.assertEqual(capabilities["project_protocol"], 1)
            self.assertFalse(capabilities["lean_check"])
            self.assertTrue(capabilities["browser_compiler"])
            self.assertTrue(self.body(request("/api/examples"))["examples"])
            self.assertTrue(self.body(request("/api/publication"))["title"])
            self.assertEqual(request("/CITATION.cff")["status"], 200)
            self.assertEqual(request("/api/example-project/missing")["status"], 404)

    def test_browser_preserves_source_and_project_validation(self):
        for payload in ({"source": "import os\n"}, {"source": "def broken(\n"},
                        {"source": SOURCE, "standalone": "yes"}, {"source": 5}):
            with self.subTest(payload=payload):
                response = request("/api/compile", payload)
                self.assertEqual(response["status"], 400)
                self.assertFalse(response["body"]["ok"])
        for name in ("../helper.algo", "/tmp/helper.algo", "dir/../helper.algo"):
            payload = self.project_body(project_sources={"main.algo": CALLER, name: HELPER})
            self.assertEqual(request("/api/generation", payload, project=True)["status"], 400)
        self.assertEqual(request("/api/compile", self.project_body())["status"], 400)
        self.assertEqual(request("/api/generation", self.project_body(project_sources={"main.algo": CALLER}), project=True)["status"], 400)
        self.assertEqual(request("/api/analyze", {"source": SOURCE, "analysis": ""})["status"], 400)

    def test_unknown_paths_cannot_read_release_files(self):
        for path in ("/publication.json", "/../publication.json", "/api/example-project/../publication.json", "/algo2lean/compiler.py", "/"):
            self.assertEqual(request(path)["status"], 404)
        for path in ("https://example.org/api/compile", "/api/compile?extra=true", None):
            self.assertEqual(request(path, {"source": SOURCE})["status"], 400)


if __name__ == "__main__":
    unittest.main()
