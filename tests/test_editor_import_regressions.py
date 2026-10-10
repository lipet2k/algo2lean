"""Editor imports distinguish a project, a missing folder, and an old server."""

import http.client
import json
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

from algo2lean.checker import LeanSetupError
from algo2lean.compiler import CompileError
from algo2lean.editor_examples import EXAMPLES, example_files
from algo2lean.server import EditorHandler, ThreadingHTTPServer


HELPER = "def increment(value: Int) -> Int:\n    return value + 1\n"
MAIN = "# A separate module.\nfrom helper import increment\ndef caller(value: Int) -> Int:\n    return increment(value)\n"


class ExampleCatalogTests(unittest.TestCase):
    def test_new_examples_are_discovered_after_curated_examples(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-example-order-") as temporary:
            root = Path(temporary)
            for name in ("z_new.algo", "gcd.algo", "a_new.algo", "sum_loop.algo", "notes.md",
                         "dijkstra.algo", "dijkstra_fibonacci.algo", "gcd 2.algo"):
                (root / name).write_text("", encoding="utf-8")
            self.assertEqual([path.name for path in example_files(root)],
                             ["sum_loop.algo", "gcd.algo", "a_new.algo", "z_new.algo"])


class EditorImportRegressionTests(unittest.TestCase):
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

    def request(self, method, path, payload=None, headers=None):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port, timeout=30)
        request_headers = {"Content-Type": "application/json"}
        request_headers.update(headers or {})
        connection.request(method, path, json.dumps(payload) if payload is not None else None,
                           request_headers)
        response = connection.getresponse()
        result = json.loads(response.read())
        status = response.status
        connection.close()
        return status, result

    def test_capabilities_advertise_project_protocol(self):
        status, data = self.request("GET", "/api/capabilities")
        self.assertEqual(status, 200)
        self.assertEqual(data["project_protocol"], 1)

    def test_capabilities_keep_local_request_boundary(self):
        status, _ = self.request("GET", "/api/capabilities",
                                 headers={"Origin": "https://example.com"})
        self.assertEqual(status, 403)

    def test_single_file_import_has_actionable_diagnostic(self):
        for path in ("/api/compile", "/api/check", "/api/analyze"):
            with self.subTest(path=path):
                status, data = self.request("POST", path, {
                    "filename": "main.algo", "source": MAIN,
                    "analysis": "import MainGenerated\n"})
                self.assertEqual(status, 400)
                diagnostic, = data["diagnostics"]
                self.assertIn("Imports are supported", diagnostic["message"])
                self.assertIn("Open project", diagnostic["message"])
                self.assertEqual((diagnostic["line"], diagnostic["column"]), (2, 1))

    def test_interface_import_also_requires_project(self):
        status, data = self.request("POST", "/api/compile", {
            "source": "from algo2lean import Interface\nclass Counter(Interface):\n    def get(self) -> Int: ...\n"})
        self.assertEqual(status, 400)
        self.assertIn("Open project", data["diagnostics"][0]["message"])

    def test_unrelated_source_error_is_not_mislabeled_as_import(self):
        status, data = self.request("POST", "/api/compile", {
            "source": "# import library\ndef bad(x: Int) -> Int:\n    return missing\n"})
        self.assertEqual(status, 400)
        self.assertNotIn("Open project", data["diagnostics"][0]["message"])
        self.assertEqual(data["diagnostics"][0]["line"], 3)

    def test_project_request_compiles_imported_module(self):
        status, data = self.request("POST", "/api/compile", {
            "filename": "main.algo", "source": MAIN,
            "project_sources": {"main.algo": MAIN, "helper.algo": HELPER}},
            {"X-Algo2Lean-Project": "1"})
        self.assertEqual(status, 200)
        self.assertTrue(data["ok"])
        self.assertIn("Algo.helper.Generated", data["project_files"])
        self.assertIn("caller.Returns", data["lean"])

    def test_missing_module_explains_project_folder(self):
        status, data = self.request("POST", "/api/compile", {
            "filename": "main.algo", "source": MAIN,
            "project_sources": {"main.algo": MAIN}},
            {"X-Algo2Lean-Project": "1"})
        self.assertEqual(status, 400)
        diagnostic, = data["diagnostics"]
        self.assertIn("Module 'helper' was not found", diagnostic["message"])
        self.assertIn("folder containing all imported modules", diagnostic["message"])
        self.assertEqual(diagnostic["file"], "main.algo")

    def test_examples_list_exposes_import_projects(self):
        status, data = self.request("GET", "/api/examples")
        self.assertEqual(status, 200)
        examples = data["examples"]
        projects = [item for item in examples if "project_id" in item]
        self.assertEqual([item["project_id"] for item in projects], [
            "modules", "interfaces", "mutual-recursion-imports", "dijkstra"])
        self.assertEqual([item["folder"] for item in projects], [
            "modules", "interfaces", "mutual_recursion", "composable_dijkstra"])
        self.assertEqual(examples[-len(projects):], projects)
        files = [item for item in examples if "project_id" not in item]
        self.assertEqual([item["filename"] for item in files[:5]], [
            "sum_loop.algo", "range_sum.algo", "factorial.algo", "gcd.algo", "mutual_recursion.algo"])
        self.assertEqual([item["filename"] for item in files[-3:]], [
            "matrix_multiply.algo",
            "matrix_recursive.algo", "matrix_strassen.algo"])
        self.assertEqual({item["filename"] for item in files},
                         {path.name for path in EXAMPLES.glob("*.algo")
                          if path.stem.isascii() and path.stem.isidentifier()} -
                         {"dijkstra.algo", "dijkstra_fibonacci.algo"})
        self.assertEqual(len(files), len({item["filename"] for item in files}))
        self.assertTrue(all("sources" not in item for item in projects))
        self.assertNotIn("dijkstra.algo", {item["filename"] for item in files})
        self.assertNotIn("dijkstra_fibonacci.algo", {item["filename"] for item in files})

    def test_example_project_includes_its_imports_and_compiles(self):
        status, project = self.request("GET", "/api/example-project/dijkstra")
        self.assertEqual(status, 200)
        self.assertIn("graph.algo", project["sources"])
        self.assertIn("indexed_heap.algo", project["sources"])
        self.assertIn("fibonacci_heap.algo", project["sources"])
        self.assertIn("Algo.composable_dijkstra.dijkstra_fibonacci.Analysis", project["analyses"])
        self.assertIn("Algo.composable_dijkstra.dijkstra_binary.Analysis", project["analyses"])
        source = project["sources"][project["entry"]]
        status, result = self.request("POST", "/api/compile", {
            "filename": project["entry"], "source": source,
            "project_sources": project["sources"], "project_analyses": project["analyses"]},
            {"X-Algo2Lean-Project": "1"})
        self.assertEqual(status, 200)
        self.assertTrue(result["ok"])
        self.assertIn("Algo.indexed_heap.Generated", result["project_files"])

    def test_unknown_example_project_cannot_read_arbitrary_paths(self):
        for name in ("missing", "../../AGENTS.md", "%2e%2e%2fAGENTS.md"):
            with self.subTest(name=name):
                status, _ = self.request("GET", "/api/example-project/" + name)
                self.assertEqual(status, 404)

    def test_broken_example_source_or_proof_returns_json_diagnostic(self):
        for error in (CompileError("Invalid return annotation.", 3, 1),
                      LeanSetupError("Could not find proof module 'Algo.queue.Analysis'.")):
            with self.subTest(error=type(error).__name__), patch(
                    "algo2lean.editor_examples.load_example_project", side_effect=error):
                status, result = self.request("GET", "/api/example-project/dijkstra")
                self.assertEqual(status, 400)
                self.assertFalse(result["ok"])
                self.assertIn(str(error), result["message"])
                self.assertEqual(result["diagnostics"][0]["message"], result["message"])


if __name__ == "__main__":
    unittest.main()
