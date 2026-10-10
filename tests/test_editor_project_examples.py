"""Bundled editor examples keep source imports and reusable proof imports intact."""

from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from algo2lean.editor_examples import EXAMPLES, load_example_project, project_examples
from algo2lean.modular import compile_project
from algo2lean.project_checker import check_project, project_lean_sources


class EditorProjectExamplesTests(unittest.TestCase):
    def test_catalog_is_small_and_does_not_compile_or_load_proofs(self):
        with patch("algo2lean.editor_examples.compile_project", side_effect=AssertionError("unexpected compile")):
            entries = project_examples()
        self.assertEqual({entry["project_id"] for entry in entries},
                         {"dijkstra-binary", "dijkstra-fibonacci", "dijkstra-generic"})
        for entry in entries:
            self.assertIn("imports", entry["name"])
            self.assertIn("from ", entry["source"])
            self.assertNotIn("analyses", entry)
            self.assertEqual(entry["source"], (EXAMPLES / entry["filename"]).read_text(encoding="utf-8"))

    def test_only_fixed_example_ids_are_accepted(self):
        for identifier in ("", "dijkstra", "../dijkstra-binary", "/etc/passwd", "dijkstra-binary.algo"):
            with self.subTest(identifier=identifier), self.assertRaises(KeyError):
                load_example_project(identifier)

    def test_all_bundles_resolve_in_an_empty_directory_with_unchanged_proofs(self):
        for identifier in ("dijkstra-binary", "dijkstra-fibonacci", "dijkstra-generic"):
            with self.subTest(identifier=identifier), tempfile.TemporaryDirectory() as directory:
                bundle = load_example_project(identifier)
                self.assertIn(bundle["entry"], bundle["sources"])
                for path, source in bundle["sources"].items():
                    self.assertEqual(source, (EXAMPLES / path).read_text(encoding="utf-8"))
                for module, source in bundle["analyses"].items():
                    path = Path(*module.split(".")[1:-1]).with_suffix(".lean")
                    self.assertEqual(source, (EXAMPLES / "analysis" / path).read_text(encoding="utf-8"))
                compiled = compile_project(bundle["entry"], root=directory, sources=bundle["sources"])
                analysis_module = "Algo." + compiled.project.entry + ".Analysis"
                resolved = project_lean_sources(compiled, proof_sources=bundle["analyses"],
                    analysis_modules=(analysis_module,))
                self.assertEqual({name: text for name, text in resolved.items() if name.endswith(".Analysis")},
                                 bundle["analyses"])
                self.assertIn("Algo.composable_dijkstra.dijkstra.Analysis", bundle["analyses"])
                self.assertIn("Algo.composable_dijkstra.priority_queue.Analysis", bundle["analyses"])
                # Resolving one project includes only its imported analyses,
                # excluding unrelated single-file proofs and alternate heaps.
                if identifier != "dijkstra-fibonacci":
                    self.assertNotIn("fibonacci_heap.algo", bundle["sources"])
                if identifier != "dijkstra-binary":
                    self.assertNotIn("indexed_heap.algo", bundle["sources"])

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_bundled_imports_and_existing_correctness_and_runtime_analyses_check(self):
        for identifier in ("dijkstra-binary", "dijkstra-fibonacci", "dijkstra-generic"):
            with self.subTest(identifier=identifier), tempfile.TemporaryDirectory() as directory:
                bundle = load_example_project(identifier)
                compiled = compile_project(bundle["entry"], root=directory, sources=bundle["sources"])
                checked = check_project(compiled, proof_sources=bundle["analyses"],
                    analysis_module="Algo." + compiled.project.entry + ".Analysis")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("declaration uses 'sorry'", checked.output)


if __name__ == "__main__":
    unittest.main()
