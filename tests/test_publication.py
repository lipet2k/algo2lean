"""Public metadata is explicit; generated credit stays deterministic and local."""

from contextlib import redirect_stderr, redirect_stdout
import http.client
import io
import json
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

from algo2lean.__main__ import main
from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean.publication import (ROOT, PublicationError, bibtex, citation_cff, citation_text,
                                   credit_generated, metadata, publication_info)
from algo2lean.server import EditorHandler, ThreadingHTTPServer


PUBLICATION = {
    "title": "Algo2Lean", "version": "0.1.0-dev", "status": "development",
    "authors": [], "creators": [], "contributors": [], "repository_url": None, "doi": None,
}
AUTHOR = {"given_names": "Example", "family_names": "Author", "orcid": None}
SOURCE = "def identity(x: Int) -> Int:\n    # @before_return\n    return x\n"


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="algo2lean-publication-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write_metadata()

    def write_metadata(self, **options):
        self.data = {**PUBLICATION, **options}
        (self.root / "publication.json").write_text(json.dumps(self.data), encoding="utf-8")

    def test_missing_identities_and_destinations_stay_unset(self):
        info = publication_info(self.root)
        for key in ("repository_url", "doi", "citation", "bibtex", "citation_url"):
            self.assertIsNone(info[key])
        self.assertEqual(info["authors"], [])
        self.assertEqual(info["creators"], [])
        self.assertEqual(info["contributors"], [])
        self.assertEqual(info["status"], "development")
        self.assertNotIn("technical_report_url", info)
        self.assertIsNone(citation_cff(self.data))

    def test_creator_contributor_and_citation_roles_are_independent(self):
        contributor = {"given_names": "Another", "family_names": "Person", "orcid": None}
        self.write_metadata(authors=[AUTHOR, contributor], creators=[AUTHOR], contributors=[contributor])
        info = publication_info(self.root)
        self.assertEqual(info["authors"], [AUTHOR, contributor])
        self.assertEqual(info["creators"], [AUTHOR])
        self.assertEqual(info["contributors"], [contributor])
        self.assertIn("Example Author; Another Person", info["citation"])
        self.assertIn("Author, Example and Person, Another", info["bibtex"])
        self.assertEqual(citation_cff(self.data).count("family-names:"), 2)
        self.write_metadata(creators=[AUTHOR], contributors=[contributor])
        info = publication_info(self.root)
        self.assertIsNone(info["citation"])
        self.assertEqual(info["creators"], [AUTHOR])
        self.assertEqual(info["contributors"], [contributor])

    def test_absent_role_lists_do_not_infer_creators_from_authors(self):
        self.write_metadata(authors=[AUTHOR])
        self.data.pop("creators")
        self.data.pop("contributors")
        (self.root / "publication.json").write_text(json.dumps(self.data), encoding="utf-8")
        info = publication_info(self.root)
        self.assertEqual(info["creators"], [])
        self.assertEqual(info["contributors"], [])
        self.assertIsNotNone(info["citation"])

    def test_citation_without_repository_or_doi_is_useful_and_honest(self):
        self.write_metadata(authors=[AUTHOR])
        info = publication_info(self.root)
        self.assertEqual(info["citation_url"], "/CITATION.cff")
        self.assertIn("Example Author", info["citation"])
        self.assertIn("development version", info["citation"])
        self.assertIn("Development version; unreleased", info["bibtex"])
        cff = citation_cff(self.data)
        self.assertIn('family-names: "Author"', cff)
        self.assertIn('version: "0.1.0-dev"', cff)
        for absent in ("doi:", "repository-code:", "date-released:", "orcid:"):
            self.assertNotIn(absent, cff)

    def test_citations_use_only_explicit_metadata(self):
        self.write_metadata(authors=[{**AUTHOR, "orcid": "https://orcid.org/0000-0002-1825-0097"}],
                            repository_url="https://example.org/algo2lean", doi="10.12345/example.1")
        data = metadata(self.root)
        self.assertTrue(citation_text(data).endswith("https://doi.org/10.12345/example.1"))
        self.assertIn("doi = {10.12345/example.1}", bibtex(data))
        self.assertIn('repository-code: "https://example.org/algo2lean"', citation_cff(data))
        self.assertIn('orcid: "https://orcid.org/0000-0002-1825-0097"', citation_cff(data))

    def test_metadata_rejects_injected_lines_or_unsafe_links(self):
        for invalid in ({"title": "Algo2Lean\naxiom bad : False"},
                        {"version": "0.1.0\n"}, {"repository_url": "javascript:alert(1)"},
                        {"repository_url": "https://user:password@example.org"},
                        {"doi": "https://doi.org/10.12345/example"},
                        {"authors": [{**AUTHOR, "orcid": "made-up"}]}):
            with self.subTest(invalid=invalid):
                self.write_metadata(**invalid)
                with self.assertRaises(ValueError):
                    metadata(self.root)

    def test_cff_scalar_quoting_and_bibtex_escaping(self):
        self.write_metadata(authors=[{**AUTHOR, "family_names": 'A: "B" & C_{D}'}])
        cff = citation_cff(self.data)
        family = next(line.split(": ", 1)[1] for line in cff.splitlines() if "family-names:" in line)
        self.assertEqual(json.loads(family), self.data["authors"][0]["family_names"])
        self.assertIn(r"\& C\_\{D\}", bibtex(self.data))

    def test_generated_credit_preserves_imports_and_omits_unset_links(self):
        with patch("algo2lean.publication.ROOT", self.root):
            code = credit_generated("import First\nimport Second\n\ndef value := 1\n")
        self.assertEqual(code, "import First\nimport Second\n-- Generated by Algo2Lean 0.1.0-dev\n\ndef value := 1\n")
        self.write_metadata(repository_url="https://example.org/algo2lean")
        with patch("algo2lean.publication.ROOT", self.root):
            self.assertEqual(credit_generated("def value := 1\n"),
                             "-- Generated by Algo2Lean 0.1.0-dev https://example.org/algo2lean\ndef value := 1\n")

    def test_attribution_and_doi_updates_do_not_change_generated_code(self):
        with patch("algo2lean.publication.ROOT", self.root):
            before = compile_source(SOURCE)
            self.write_metadata(authors=[AUTHOR], creators=[AUTHOR], contributors=[AUTHOR], doi="10.12345/example.1")
            after = compile_source(SOURCE)
        self.assertEqual(before.lean, after.lean)
        self.assertEqual(before.points_lean, after.points_lean)

    def test_invalid_citation_fields_do_not_block_compilation(self):
        with patch("algo2lean.publication.ROOT", self.root):
            original = compile_source(SOURCE)
            for fields in ({"authors": [{**AUTHOR, "orcid": "0000-0002-1825-0097"}]},
                           {"authors": "unfinished"}, {"doi": "not assigned yet"}, {"status": "draft"},
                           {"creators": "unfinished"}, {"contributors": [{**AUTHOR, "orcid": "not supplied"}]}):
                with self.subTest(fields=fields):
                    self.write_metadata(**fields)
                    self.assertEqual(compile_source(SOURCE).lean, original.lean)
                    project = compile_project("identity", root=self.root, sources={"identity": SOURCE})
                    self.assertIn("Generated by Algo2Lean 0.1.0-dev", project.entry.lean)
                    with self.assertRaises(ValueError):
                        metadata(self.root)

    def test_broken_compiler_metadata_has_a_dedicated_setup_error(self):
        path = self.root / "publication.json"
        for content in (None, b'{"broken"', b'\xff', b'[]', b'{"title":"Algo2Lean","version":42}'):
            with self.subTest(content=content), patch("algo2lean.publication.ROOT", self.root):
                if content is None:
                    path.unlink(missing_ok=True)
                else:
                    path.write_bytes(content)
                with self.assertRaises(PublicationError) as caught:
                    compile_source(SOURCE)
                self.assertIn("publication.json", str(caught.exception))
                self.assertIsNotNone(caught.exception.__cause__)

    def test_cli_reports_metadata_setup_errors_without_tracebacks_or_source_locations(self):
        source, proof = self.root / "identity.algo", self.root / "analysis.lean"
        source.write_text(SOURCE, encoding="utf-8")
        proof.write_text("import IdentityGenerated\n", encoding="utf-8")
        path = self.root / "publication.json"
        for content in (None, '{"unfinished"', json.dumps({**PUBLICATION, "version": "bad\nversion"})):
            if content is None:
                path.unlink(missing_ok=True)
            else:
                path.write_text(content, encoding="utf-8")
            for args in (("compile", str(source)), ("analyze", str(source), str(proof)),
                         ("compile", str(source), "--output-dir", str(self.root / "out")),
                         ("analyze", str(source), str(proof), "--project", str(self.root))):
                with self.subTest(content=content, args=args), patch("algo2lean.publication.ROOT", self.root):
                    stdout, stderr = io.StringIO(), io.StringIO()
                    with redirect_stdout(stdout), redirect_stderr(stderr):
                        status = main(args)
                    self.assertEqual(status, 1)
                    self.assertEqual(stdout.getvalue(), "")
                    self.assertIn("Compiler setup error:", stderr.getvalue())
                    self.assertIn("publication.json", stderr.getvalue())
                    self.assertNotIn("Traceback", stderr.getvalue())
                    self.assertNotIn("identity.algo:", stderr.getvalue())
                    self.assertFalse((self.root / "out").exists())

    def test_single_file_credit_is_deterministic_and_label_independent(self):
        with patch("algo2lean.publication.ROOT", self.root):
            for options in ({}, {"standalone": True}, {"namespace": "Example"}):
                with self.subTest(options=options):
                    first = compile_source(SOURCE, filename="identity.algo", **options)
                    repeated = compile_source(SOURCE, filename="identity.algo", **options)
                    renamed = compile_source(SOURCE.replace("before_return", "result"), filename="identity.algo", **options)
                    self.assertEqual(first.lean, repeated.lean)
                    self.assertEqual(first.points_lean, repeated.points_lean)
                    self.assertEqual(first.lean, renamed.lean)
                    self.assertNotEqual(first.points_lean, renamed.points_lean)
                    for output in (first.lean, first.points_lean):
                        self.assertEqual(output.count("-- Generated by Algo2Lean 0.1.0-dev"), 1)
                    self.assertTrue(first.points_lean.startswith("import «IdentityGenerated»\n"))

    def test_every_modular_output_has_credit_without_changing_dependency_identity(self):
        sources = {"library": SOURCE,
                   "main": "import library\ndef run(x: Int) -> Int:\n    return library.identity(x)\n"}
        with patch("algo2lean.publication.ROOT", self.root):
            first = compile_project("main", root=self.root, sources=sources)
            repeated = compile_project("main", root=self.root, sources=sources)
            renamed = compile_project("main", root=self.root,
                                      sources={**sources, "library": SOURCE.replace("before_return", "renamed")})
            alone = compile_project("library", root=self.root, sources={"library": SOURCE})
        self.assertEqual(first.files, repeated.files)
        self.assertEqual(set(first.files), {"Algo.%s.%s" % (name, part)
                                          for name in ("main", "library") for part in ("Generated", "Points", "Facts")})
        for module, output in first.files.items():
            self.assertEqual(output.count("-- Generated by Algo2Lean 0.1.0-dev"), 1)
            self.assertTrue(output.startswith("import "))
            if not module.endswith(".Points"):
                self.assertEqual(output, renamed.files[module])
        for module, output in alone.files.items():
            self.assertEqual(output, first.files[module])

    def test_checked_in_citation_matches_metadata_when_present(self):
        path = ROOT / "CITATION.cff"
        expected = citation_cff(metadata())
        if expected is None:
            self.assertFalse(path.exists(), "Do not publish a citation with unconfirmed authors.")
        else:
            self.assertEqual(path.read_text(encoding="utf-8"), expected)


class PublicationServerTests(unittest.TestCase):
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

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="algo2lean-publication-route-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "publication.json").write_text(json.dumps(PUBLICATION), encoding="utf-8")
        (self.root / "docs").mkdir()
        (self.root / "docs" / "TECHNICAL_REPORT.md").write_text("# Algo2Lean\nDraft technical report.\n", encoding="utf-8")
        self.patch_root = patch("algo2lean.server.ROOT", self.root)
        self.patch_root.start()
        self.addCleanup(self.patch_root.stop)

    def request(self, path, headers=None, body=None):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port, timeout=5)
        if body is not None:
            headers = {"Content-Type": "application/json", **(headers or {})}
        connection.request("POST" if body is not None else "GET", path,
                           body=json.dumps(body) if body is not None else None, headers=headers or {})
        response = connection.getresponse()
        status, headers, data = response.status, dict(response.getheaders()), response.read()
        connection.close()
        return status, headers, data

    def test_publication_and_missing_citation(self):
        status, _, content = self.request("/api/publication")
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(content)["version"], "0.1.0-dev")
        self.assertIsNone(json.loads(content)["citation_url"])
        self.assertNotIn("technical_report_url", json.loads(content))
        self.assertEqual(self.request("/CITATION.cff")[0], 404)

    def test_configured_citation_download_matches_metadata(self):
        data = {**PUBLICATION, "authors": [AUTHOR]}
        (self.root / "publication.json").write_text(json.dumps(data), encoding="utf-8")
        status, headers, content = self.request("/CITATION.cff")
        self.assertEqual(status, 200)
        self.assertEqual(headers["Content-Disposition"], 'attachment; filename="CITATION.cff"')
        self.assertEqual(headers["Content-Type"], "application/yaml; charset=utf-8")
        self.assertEqual(content.decode("utf-8"), citation_cff(data))

    def test_repository_metadata_api_and_download_match_checked_in_citation(self):
        data = metadata(ROOT)
        with patch("algo2lean.server.ROOT", ROOT):
            status, _, content = self.request("/api/publication")
            self.assertEqual(status, 200)
            self.assertEqual(json.loads(content), publication_info(ROOT))
            status, _, content = self.request("/CITATION.cff")
        expected = citation_cff(data)
        if expected is None:
            self.assertEqual(status, 404)
        else:
            self.assertEqual(status, 200)
            self.assertEqual(content, (ROOT / "CITATION.cff").read_bytes())

    def test_private_documents_are_not_served(self):
        for path in ("/technical-report.md", "/docs/TECHNICAL_REPORT.md", "/publication.json",
                     "/../AGENTS.md", "/technical-report.md/../AGENTS.md"):
            self.assertEqual(self.request(path)[0], 404)

    def test_publication_routes_keep_local_request_checks(self):
        for path in ("/api/publication", "/CITATION.cff"):
            self.assertEqual(self.request(path, {"Origin": "https://example.org"})[0], 403)

    def test_malformed_metadata_is_reported_without_its_contents(self):
        (self.root / "publication.json").write_text('{"secret": "not valid"', encoding="utf-8")
        for path in ("/api/publication", "/CITATION.cff"):
            status, _, content = self.request(path)
            self.assertEqual(status, 500)
            self.assertNotIn(b"secret", content)

    def test_invalid_orcid_disables_citation_without_breaking_compiler(self):
        (self.root / "publication.json").write_text(json.dumps({**PUBLICATION,
            "authors": [{**AUTHOR, "orcid": "0000-0002-1825-0097"}]}), encoding="utf-8")
        self.assertEqual(self.request("/api/publication")[0], 500)
        with patch("algo2lean.publication.ROOT", self.root):
            status, _, content = self.request("/api/compile", body={"source": SOURCE})
        self.assertEqual(status, 200)
        self.assertTrue(json.loads(content)["ok"])

    def test_broken_compiler_metadata_is_a_setup_error_for_all_compile_routes(self):
        path = self.root / "publication.json"
        for content in (None, '{"unfinished"', json.dumps({**PUBLICATION, "version": 42})):
            if content is None:
                path.unlink(missing_ok=True)
            else:
                path.write_text(content, encoding="utf-8")
            for route in ("/api/compile", "/api/check", "/api/analyze", "/api/project-export"):
                for project in (False, True):
                    if route == "/api/project-export" and not project:
                        continue
                    body = {"source": SOURCE, "filename": "identity.algo", "analysis": "import IdentityGenerated\n"}
                    headers = {}
                    if project:
                        body["project_sources"] = {"identity.algo": SOURCE}
                        headers["X-Algo2Lean-Project"] = "1"
                    with self.subTest(content=content, route=route, project=project), patch("algo2lean.publication.ROOT", self.root):
                        status, _, response = self.request(route, headers, body)
                    self.assertEqual(status, 503)
                    error = json.loads(response)
                    self.assertEqual(error["scope"], "setup")
                    self.assertIn("Compiler setup error:", error["message"])
                    self.assertIn("publication.json", error["message"])
                    self.assertEqual(error["diagnostics"], [])
                    self.assertEqual(error["analysis_diagnostics"], [])
                    self.assertNotIn("request must", error["message"])


if __name__ == "__main__":
    unittest.main()
