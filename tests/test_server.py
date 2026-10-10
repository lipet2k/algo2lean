import http.client
import json
from pathlib import Path
import threading
import unittest
from unittest.mock import patch

from algo2lean.checker import CheckResult, check_lean
from algo2lean.server import (EditorHandler, MAX_ANALYSIS_BYTES, MAX_ANALYSIS_REQUEST_BYTES,
                             ThreadingHTTPServer, analysis_diagnostics)


SOURCE = "def identity(x: Int) -> Int:\n    return x\n"


class ServerTests(unittest.TestCase):
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

    def request(self, method, path, body=None, headers=None):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port, timeout=5)
        connection.request(method, path, body=body, headers=headers or {})
        response = connection.getresponse()
        data = response.read()
        status = response.status
        connection.close()
        return status, data

    def post(self, path="/api/compile", source=SOURCE, **options):
        status, data = self.request("POST", path, json.dumps({"source": source, **options}), {"Content-Type": "application/json"})
        return status, json.loads(data)

    def test_editor_assets_and_examples(self):
        for path in ["/", "/app.js", "/drafts.js", "/interface.js", "/proof-outline.js", "/code-search.js", "/code-search.css", "/styles.css"]:
            with self.subTest(path=path):
                status, data = self.request("GET", path)
                self.assertEqual(status, 200)
                self.assertTrue(data)
        status, data = self.request("GET", "/api/examples")
        self.assertEqual(status, 200)
        examples = json.loads(data)["examples"]
        self.assertGreaterEqual(len(examples), 4)
        self.assertTrue(all(example["source"] and example["filename"].endswith(".algo") for example in examples))
        factorial = next(example for example in examples if example["filename"] == "factorial.algo")
        self.assertNotIn("my_func.algo", [example["filename"] for example in examples])
        self.assertEqual(factorial["module"], "FactorialGenerated")
        self.assertTrue(factorial["analysis"].startswith("import FactorialGenerated"))
        self.assertEqual(factorial["points_module"], "FactorialGeneratedPoints")

    def test_compile(self):
        status, data = self.post()
        self.assertEqual(status, 200)
        self.assertTrue(data["ok"])
        self.assertIn("identity.Returns", data["lean"])
        self.assertEqual(data["functions"][0]["name"], "identity")
        self.assertEqual(data["lean"], "import Algo2Lean\n\n" + data["program_lean"])
        self.assertEqual(data["module"], "UntitledGenerated")
        self.assertEqual(data["points_module"], "UntitledGeneratedPoints")
        self.assertTrue(data["points_lean"].startswith("import «UntitledGenerated»\n"))
        self.assertEqual(data["stats"], {
            "program_lines": len(data["program_lean"].splitlines()),
            "shared_lines": len(data["shared_lean"].splitlines()),
            "general_lines": len(data["lean"].splitlines()),
            "points_lines": len(data["points_lean"].splitlines()),
            "total_lines": len(data["lean"].splitlines()) + len(data["points_lean"].splitlines()),
        })

    def test_standalone_export_and_label_metadata(self):
        source = "def identity(x: Int) -> Int:\n    # @result\n    return x\n"
        status, data = self.post(source=source, standalone=True)
        self.assertEqual(status, 200)
        self.assertEqual(data["lean"], data["shared_lean"] + "\n" + data["program_lean"])
        point = data["functions"][0]["points"][0]
        self.assertEqual((point["name"], point["line"], point["relation"]),
                         ("result", 3, "identity.At.result"))
        self.assertIn("identity.At.result", data["points_lean"])
        self.assertNotIn("identity.At.result", data["lean"])

    def test_label_edits_only_change_points_output(self):
        _, first = self.post(source=SOURCE.replace("return x", "# @first\n    return x"))
        _, second = self.post(source=SOURCE.replace("return x", "# @second\n    return x"))
        self.assertEqual(first["lean"], second["lean"])
        self.assertEqual(first["program_lean"], second["program_lean"])
        self.assertEqual(first["module"], second["module"])
        self.assertNotEqual(first["points_lean"], second["points_lean"])

    def test_compile_diagnostic(self):
        status, data = self.post(source="def broken(x: Int) -> Int:\n    return missing\n")
        self.assertEqual(status, 400)
        self.assertFalse(data["ok"])
        self.assertEqual(data["diagnostics"][0]["line"], 2)

    def test_invalid_source_characters_return_diagnostics(self):
        for character in ["\x00", "\ud800"]:
            with self.subTest(character=repr(character)):
                status, data = self.post(source=SOURCE + character)
                self.assertEqual(status, 400)
                self.assertFalse(data["ok"])
                self.assertTrue(data["diagnostics"][0]["message"])

    def test_check_reports_missing_lean_without_losing_generated_output(self):
        with patch("algo2lean.server.check_lean", return_value=CheckResult(False, False, "Lean not installed")):
            status, data = self.post("/api/check")
        self.assertEqual(status, 200)
        self.assertFalse(data["ok"])
        self.assertFalse(data["available"])
        self.assertIn("identity.Returns", data["lean"])

    def test_check_success(self):
        with patch("algo2lean.server.check_lean", return_value=CheckResult(True, True, "Lean accepted")) as check:
            status, data = self.post("/api/check")
        self.assertEqual(status, 200)
        self.assertTrue(data["ok"])
        self.assertTrue(data["available"])
        self.assertEqual(check.call_args.args, (data["lean"],))
        self.assertEqual(check.call_args.kwargs, {"module": data["module"], "points_lean": data["points_lean"]})

    def test_analysis_checks_a_separate_module_and_returns_its_locations(self):
        proof = "import IdentityGenerated\nexample : False := by decide\n"
        message = "Analysis.lean:2:27: error: tactic 'decide' failed\nFalse is not true\n"
        with patch("algo2lean.server.check_analysis", return_value=CheckResult(False, True, message)) as check:
            status, data = self.post("/api/analyze", filename="identity.algo", analysis=proof)
        self.assertEqual(status, 200)
        self.assertFalse(data["ok"])
        self.assertEqual(data["scope"], "analysis")
        self.assertEqual(data["module"], "IdentityGenerated")
        self.assertEqual(data["analysis_diagnostics"][0]["line"], 2)
        self.assertEqual(data["analysis_diagnostics"][0]["column"], 28)
        self.assertIn("identity.Returns", data["lean"])
        self.assertEqual(check.call_args.args, (data["lean"], proof, "IdentityGenerated"))
        self.assertEqual(check.call_args.kwargs, {"points_lean": data["points_lean"]})

    def test_analysis_validation_and_missing_lean(self):
        for analysis in (None, 2, "", " " * 4, "bad\x00", "bad\ud800",
                         "x" * (MAX_ANALYSIS_BYTES + 1),
                         "α" * (MAX_ANALYSIS_BYTES // 2) + "x"):
            with self.subTest(analysis=repr(analysis)[:30]):
                status, data = self.post("/api/analyze", analysis=analysis)
                self.assertEqual(status, 400)
                self.assertFalse(data["ok"])
                self.assertEqual(data["scope"], "analysis")
                self.assertTrue(data["analysis_diagnostics"])
                self.assertNotIn("diagnostics", data)
        with patch("algo2lean.server.check_analysis", return_value=CheckResult(False, False, "Lean not installed")):
            status, data = self.post("/api/analyze", analysis="import UntitledGenerated\n")
        self.assertEqual(status, 200)
        self.assertFalse(data["available"])
        self.assertEqual(data["analysis_diagnostics"], [])

    def test_analysis_accepts_the_bundled_dijkstra_proof(self):
        examples = Path(__file__).resolve().parents[1] / "examples"
        source = (examples / "dijkstra.algo").read_text(encoding="utf-8")
        proof = (examples / "analysis" / "dijkstra.lean").read_text(encoding="utf-8")
        with patch("algo2lean.server.check_analysis", return_value=CheckResult(True, True, "Lean accepted")) as check:
            status, data = self.post("/api/analyze", source=source,
                                     filename="dijkstra.algo", analysis=proof)
        self.assertEqual(status, 200)
        self.assertTrue(data["ok"])
        self.assertEqual(data["scope"], "analysis")
        self.assertEqual(check.call_args.args, (data["lean"], proof, "DijkstraGenerated"))
        self.assertEqual(check.call_args.kwargs, {"points_lean": data["points_lean"]})

    def test_analysis_accepts_its_utf8_size_boundary(self):
        for proof in ("x" * MAX_ANALYSIS_BYTES, "α" * (MAX_ANALYSIS_BYTES // 2)):
            with self.subTest(multibyte=proof.startswith("α")):
                self.assertEqual(len(proof.encode("utf-8")), MAX_ANALYSIS_BYTES)
                with patch("algo2lean.server.check_analysis", return_value=CheckResult(True, True, "Lean accepted")) as check:
                    status, data = self.post("/api/analyze", analysis=proof)
                self.assertEqual(status, 200)
                self.assertTrue(data["ok"])
                self.assertEqual(check.call_args.args[1], proof)

    def test_analysis_request_errors_do_not_blame_source(self):
        cases = [
            ("{", {"Content-Type": "application/json"}, 400),
            ("{}", {"Content-Type": "text/plain"}, 415),
            ("{}", {"Content-Type": "application/json", "Content-Length": "bad"}, 400),
            ("", {"Content-Type": "application/json", "Content-Length": "0"}, 413),
            ("{}", {"Content-Type": "application/json",
                    "Content-Length": str(MAX_ANALYSIS_REQUEST_BYTES + 1)}, 413),
        ]
        with patch("algo2lean.server.compile_source") as compile_mock, patch("algo2lean.server.check_analysis") as check_mock:
            for body, headers, expected in cases:
                with self.subTest(headers=headers, body=body):
                    status, raw = self.request("POST", "/api/analyze", body, headers)
                    data = json.loads(raw)
                    self.assertEqual(status, expected)
                    self.assertEqual(data["scope"], "analysis")
                    self.assertTrue(data["analysis_diagnostics"])
                    self.assertNotIn("diagnostics", data)
            compile_mock.assert_not_called()
            check_mock.assert_not_called()

    def test_analysis_keeps_the_source_size_limit(self):
        with patch("algo2lean.server.check_analysis") as check:
            status, data = self.post("/api/analyze", source="x" * 200001,
                                     analysis="import UntitledGenerated\n")
        self.assertEqual(status, 400)
        self.assertIn("200,000 character limit", data["diagnostics"][0]["message"])
        self.assertNotIn("analysis_diagnostics", data)
        check.assert_not_called()

    def test_busy_analysis_checker_does_not_blame_source(self):
        with patch("algo2lean.server.LEAN_SLOTS") as slots:
            slots.acquire.return_value = False
            status, data = self.post("/api/analyze", analysis="import UntitledGenerated\n")
        self.assertEqual(status, 429)
        self.assertEqual(data["scope"], "analysis")
        self.assertNotIn("diagnostics", data)
        self.assertIn("already running", data["message"])

    def test_cross_site_top_level_editor_navigation(self):
        headers = {
            "Sec-Fetch-Site": "cross-site",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Dest": "document",
        }
        for path in ["/", "/index.html", "/?example=merge_sort", "/index.html?example=merge_sort"]:
            with self.subTest(path=path):
                status, data = self.request("GET", path, headers=headers)
                self.assertEqual(status, 200)
                self.assertIn(b"<!doctype html>", data.lower())

    def test_cross_site_navigation_still_checks_host_and_origin(self):
        navigation = {
            "Sec-Fetch-Site": "cross-site",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Dest": "document",
        }
        for untrusted in [{"Host": "example.org"}, {"Origin": "https://example.org"}, {"Origin": "null"}]:
            with self.subTest(untrusted=untrusted):
                status, _ = self.request("GET", "/", headers={**navigation, **untrusted})
                self.assertEqual(status, 403)

    def test_cross_site_navigation_does_not_allow_assets_or_apis(self):
        headers = {
            "Sec-Fetch-Site": "cross-site",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Dest": "document",
        }
        for path in ["/api/examples", "/api/compile", "/api/check", "/app.js", "/drafts.js", "/interface.js", "/proof-outline.js", "/code-search.js", "/code-search.css", "/styles.css"]:
            with self.subTest(path=path):
                status, _ = self.request("GET", path, headers=headers)
                self.assertEqual(status, 403)

    def test_cross_site_editor_requests_require_top_level_navigation(self):
        for mode, destination in [
            (None, None), (None, "document"), ("navigate", None),
            ("navigate", "iframe"), ("navigate", "object"), ("navigate", "embed"),
            ("cors", "document"), ("no-cors", "document"),
        ]:
            with self.subTest(mode=mode, destination=destination):
                headers = {"Sec-Fetch-Site": "cross-site"}
                if mode is not None:
                    headers["Sec-Fetch-Mode"] = mode
                if destination is not None:
                    headers["Sec-Fetch-Dest"] = destination
                status, _ = self.request("GET", "/", headers=headers)
                self.assertEqual(status, 403)

    def test_cross_site_posts_are_rejected_before_compilation(self):
        navigation = {
            "Sec-Fetch-Site": "cross-site",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Dest": "document",
        }
        with patch("algo2lean.server.compile_source") as compile_mock, patch("algo2lean.server.check_lean") as check_mock, patch("algo2lean.server.check_analysis") as analysis_mock:
            for path in ["/", "/index.html", "/api/compile", "/api/check", "/api/analyze"]:
                for metadata in [{}, navigation]:
                    with self.subTest(path=path, metadata=metadata):
                        headers = {"Content-Type": "application/json", "Sec-Fetch-Site": "cross-site", **metadata}
                        status, _ = self.request("POST", path, json.dumps({"source": SOURCE}), headers)
                        self.assertEqual(status, 403)
            compile_mock.assert_not_called()
            check_mock.assert_not_called()
            analysis_mock.assert_not_called()

    def test_rejects_external_origins_and_rebinding_hosts(self):
        for headers in [{"Origin": "https://example.org"}, {"Host": "example.org"}, {"Sec-Fetch-Site": "cross-site"}]:
            with self.subTest(headers=headers):
                status, _ = self.request("GET", "/api/examples", headers=headers)
                self.assertEqual(status, 403)

    def test_path_traversal_is_not_served(self):
        for path in ["/../AGENTS.md", "/%2e%2e/AGENTS.md", "/algo2lean/server.py"]:
            with self.subTest(path=path):
                status, _ = self.request("GET", path)
                self.assertEqual(status, 404)

    def test_malformed_requests(self):
        cases = [
            ("{", {"Content-Type": "application/json"}, 400),
            ("[]", {"Content-Type": "application/json"}, 400),
            ('{"source": 1}', {"Content-Type": "application/json"}, 400),
            ('{"source": "", "filename": 2}', {"Content-Type": "application/json"}, 400),
            ('{"source": "", "standalone": "false"}', {"Content-Type": "application/json"}, 400),
            ("{}", {"Content-Type": "text/plain"}, 415),
            ("x" * (256 * 1024 + 1), {"Content-Type": "application/json"}, 413),
        ]
        for body, headers, expected in cases:
            with self.subTest(expected=expected, body=body[:30]):
                status, data = self.request("POST", "/api/compile", body, headers)
                self.assertEqual(status, expected)
                self.assertIn("diagnostics", json.loads(data))


class CheckerTests(unittest.TestCase):
    def test_analysis_locations_with_lean_diagnostic_codes(self):
        diagnostics = analysis_diagnostics(
            "Analysis.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `missing`\n"
            "Analysis.lean:3:0: warning: declaration uses `sorry`\n")
        self.assertEqual(diagnostics, [
            {"line": 2, "column": 8, "message": "Unknown identifier `missing`"},
            {"line": 3, "column": 1, "message": "declaration uses `sorry`"},
        ])

    def test_missing_binary(self):
        with patch("algo2lean.checker.shutil.which", return_value=None):
            result = check_lean("def x := 1")
        self.assertFalse(result.ok)
        self.assertFalse(result.available)


if __name__ == "__main__":
    unittest.main()
