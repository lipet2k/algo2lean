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
                         {"modules", "interfaces", "kruskal", "dijkstra", "mutual-recursion-imports"})
        self.assertEqual({entry["folder"] for entry in entries},
                         {"modules", "interfaces", "kruskal", "dijkstra", "mutual_recursion"})
        self.assertLess([entry["project_id"] for entry in entries].index("kruskal"),
                        [entry["project_id"] for entry in entries].index("dijkstra"))
        kruskal, = [entry for entry in entries if entry["project_id"] == "kruskal"]
        self.assertEqual(kruskal["name"], "Kruskal")
        self.assertEqual(kruskal["filename"], "kruskal.algo")
        self.assertEqual(kruskal["folder"], "kruskal")
        dijkstra, = [entry for entry in entries if entry["project_id"] == "dijkstra"]
        self.assertEqual(dijkstra["name"], "Dijkstra")
        self.assertEqual(dijkstra["filename"], "dijkstra/dijkstra_binary.algo")
        for entry in entries:
            root = EXAMPLES if entry["project_id"] == "dijkstra" else EXAMPLES / entry["folder"]
            self.assertIn("from ", entry["source"])
            self.assertNotIn("analyses", entry)
            self.assertEqual(entry["source"], (root / entry["filename"]).read_text(encoding="utf-8"))

    def test_folder_projects_include_every_module_and_reusable_proof(self):
        for identifier, folder, entry in (
            ("modules", "modules", "pipeline.algo"),
            ("interfaces", "interfaces", "use_direct.algo"),
            ("mutual-recursion-imports", "mutual_recursion", "client.algo"),
            ("kruskal", "kruskal", "kruskal.algo"),
        ):
            with self.subTest(project=identifier), tempfile.TemporaryDirectory() as directory:
                root = EXAMPLES / folder
                bundle = load_example_project(identifier)
                self.assertEqual(bundle["entry"], entry)
                source_paths = {path.relative_to(root).as_posix() for path in root.rglob("*.algo")
                                if all(part.isascii() and part.isidentifier()
                                       for part in path.relative_to(root).with_suffix("").parts)}
                self.assertEqual(set(bundle["sources"]), source_paths)
                for path, source in bundle["sources"].items():
                    self.assertEqual(source, (root / path).read_text(encoding="utf-8"))
                    # Every file offered in the editor is independently selectable.
                    compile_project(path, root=directory, sources=bundle["sources"])
                for module, source in bundle["analyses"].items():
                    path = Path(*module.split(".")[1:-1]).with_suffix(".lean")
                    self.assertEqual(source, (root / "analysis" / path).read_text(encoding="utf-8"))
                compiled = compile_project(entry, root=directory, sources=bundle["sources"])
                resolved = project_lean_sources(compiled, proof_sources=bundle["analyses"],
                    analysis_modules=tuple(bundle["analyses"]))
                self.assertEqual({name: text for name, text in resolved.items() if name.endswith(".Analysis")},
                                 bundle["analyses"])
        self.assertIn("general_sort_then_search.algo", load_example_project("modules")["sources"])
        self.assertIn("Algo.callable_client.Analysis", load_example_project("modules")["analyses"])
        self.assertIn("both.algo", load_example_project("interfaces")["sources"])
        self.assertIn("consumer/advance_twice.algo", load_example_project("interfaces")["sources"])

    def test_recursive_example_preserves_its_source_root_and_reusable_analysis(self):
        bundle = load_example_project("mutual-recursion-imports")
        root = EXAMPLES / "mutual_recursion"
        self.assertEqual(bundle["entry"], "client.algo")
        self.assertEqual(set(bundle["sources"]), {"client.algo", "even.algo", "odd.algo"})
        self.assertEqual(set(bundle["analyses"]), {"Algo.client.Analysis", "Algo.parity.Analysis"})
        for path, text in bundle["sources"].items():
            self.assertEqual(text, (root / path).read_text(encoding="utf-8"))
        for module, text in bundle["analyses"].items():
            path = Path(*module.split(".")[1:-1]).with_suffix(".lean")
            self.assertEqual(text, (root / "analysis" / path).read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project(bundle["entry"], root=directory, sources=bundle["sources"])
            resolved = project_lean_sources(compiled, proof_sources=bundle["analyses"],
                analysis_modules=("Algo.client.Analysis",))
            self.assertEqual({name: text for name, text in resolved.items() if name.endswith(".Analysis")},
                             bundle["analyses"])

    def test_kruskal_bundle_contains_its_four_sources_and_independent_proofs(self):
        bundle = load_example_project("kruskal")
        self.assertEqual(bundle["entry"], "kruskal.algo")
        self.assertEqual(set(bundle["sources"]), {
            "indexed_heap.algo", "union_find.algo", "sort_indices.algo", "kruskal.algo",
        })
        self.assertTrue({
            "Algo.indexed_heap.Analysis", "Algo.union_find.Analysis",
            "Algo.union_find_init.Analysis", "Algo.sort_indices.Analysis",
            "Algo.kruskal_input.Analysis", "Algo.kruskal_scan.Analysis",
        }.issubset(bundle["analyses"]))
        root = EXAMPLES / "kruskal"
        for path, source in bundle["sources"].items():
            self.assertEqual(source, (root / path).read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project(bundle["entry"], root=directory, sources=bundle["sources"])
            self.assertEqual(set(compiled.project.modules),
                             {"indexed_heap", "union_find", "sort_indices", "kruskal"})
            resolved = project_lean_sources(compiled, proof_sources=bundle["analyses"],
                analysis_modules=tuple(bundle["analyses"]))
            self.assertEqual({name: text for name, text in resolved.items() if name.endswith(".Analysis")},
                             bundle["analyses"])

    def test_only_fixed_example_ids_are_accepted(self):
        for identifier in ("", "dijkstra-generic", "dijkstra-binary", "dijkstra-fibonacci",
                           "../dijkstra", "/etc/passwd", "dijkstra.algo"):
            with self.subTest(identifier=identifier), self.assertRaises(KeyError):
                load_example_project(identifier)

    def test_dijkstra_bundle_resolves_both_heaps_with_unchanged_proofs(self):
        bundle = load_example_project("dijkstra")
        self.assertEqual(bundle["entry"], "dijkstra/dijkstra_binary.algo")
        self.assertEqual(set(bundle["sources"]), {
            "dijkstra/dijkstra.algo", "dijkstra/priority_queue.algo",
            "dijkstra/dijkstra_binary.algo", "dijkstra/dijkstra_fibonacci.algo",
            "graph.algo", "indexed_heap.algo", "fibonacci_heap.algo",
        })
        for path, source in bundle["sources"].items():
            self.assertEqual(source, (EXAMPLES / path).read_text(encoding="utf-8"))
        for module, source in bundle["analyses"].items():
            path = Path(*module.split(".")[1:-1]).with_suffix(".lean")
            self.assertEqual(source, (EXAMPLES / "analysis" / path).read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project(bundle["entry"], root=directory, sources=bundle["sources"])
            resolved = project_lean_sources(compiled, proof_sources=bundle["analyses"],
                analysis_modules=tuple("Algo.dijkstra.dijkstra_" + backend + ".Analysis"
                                       for backend in ("binary", "fibonacci")))
            self.assertEqual({name: text for name, text in resolved.items() if name.endswith(".Analysis")},
                             bundle["analyses"])
        self.assertIn("Algo.dijkstra.dijkstra.Analysis", bundle["analyses"])
        self.assertIn("Algo.dijkstra.priority_queue.Analysis", bundle["analyses"])
        self.assertNotIn("Algo.dijkstra.Analysis", bundle["analyses"])
        self.assertNotIn("Algo.dijkstra_fibonacci.Analysis", bundle["analyses"])

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_bundled_imports_and_existing_correctness_and_runtime_analyses_check(self):
        bundle = load_example_project("dijkstra")
        for entry in ("dijkstra", "dijkstra_binary", "dijkstra_fibonacci"):
            with self.subTest(entry=entry), tempfile.TemporaryDirectory() as directory:
                compiled = compile_project("dijkstra/" + entry + ".algo",
                                           root=directory, sources=bundle["sources"])
                checked = check_project(compiled, proof_sources=bundle["analyses"],
                    analysis_module="Algo." + compiled.project.entry + ".Analysis")
                self.assertTrue(checked.ok, checked.output)
                self.assertNotIn("declaration uses `sorry`", checked.output)


if __name__ == "__main__":
    unittest.main()
