"""Project caches follow real imports, source contents, and compiler versions."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from algo2lean.project_checker import check_project


class ProjectCheckerTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="algo2lean-project-check-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name) / "project"
        self.root.mkdir()
        self.repository = Path(self.directory.name) / "repository"
        self.repository.mkdir()
        (self.repository / "Algo2Lean.lean").write_text("import Std\n", encoding="utf-8")
        self.files = {
            "Algo.lib.Generated": "import Algo2Lean\ndef libraryValue := 1\n",
            "Algo.lib.Points": "import Algo.lib.Generated\n",
            "Algo.lib.Facts": "import Algo.lib.Generated\n-- FAIL optional facts\n",
            "Algo.client.Generated": "import Algo.lib.Generated\ndef clientValue := libraryValue\n",
            "Algo.client.Points": "import Algo.client.Generated\n",
        }
        self.compilation = SimpleNamespace(files=self.files,
            project=SimpleNamespace(root=self.root, entry="client"))
        self.version = "Lean (version 4.33.1, test-build)\n"
        self.builds = []
        self.environments = []
        for target, value in [
            ("algo2lean.checker.ROOT", self.repository),
            ("algo2lean.project_checker.shutil.which", lambda _: "/test/bin/lean"),
            ("algo2lean.project_checker.tempfile.gettempdir", lambda: self.directory.name),
        ]:
            context = patch(target, value)
            context.start()
            self.addCleanup(context.stop)
        runner = patch("algo2lean.project_checker.subprocess.run", side_effect=self.run_lean)
        self.runner = runner.start()
        self.addCleanup(runner.stop)

    def run_lean(self, command, **kwargs):
        if "--version" in command:
            return subprocess.CompletedProcess(command, 0, self.version, "")
        build_root = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("--root=")))
        source_path = Path(command[-1])
        source = source_path.read_text(encoding="utf-8")
        name = ".".join(source_path.relative_to(build_root).with_suffix("").parts)
        self.builds.append(name)
        self.environments.append(kwargs["env"])
        self.assertTrue(build_root.name.startswith(".building-"))
        if "-- FAIL" in source:
            return subprocess.CompletedProcess(command, 1, str(source_path) + ":2:0: proof rejected\n", "")
        if "-- NO_OBJECT" not in source:
            Path(command[command.index("-o") + 1]).write_bytes(b"test object")
        output = str(source_path) + ":2:0: warning: declaration uses `sorry`\n" if "-- SORRY" in source else ""
        return subprocess.CompletedProcess(command, 0, output, "")

    def check(self, **kwargs):
        checked = check_project(self.compilation, **kwargs)
        self.assertTrue(checked.ok, checked.output)
        return checked

    def test_core_cache_is_reused_and_optional_facts_are_not_built(self):
        with patch.dict(os.environ, {"LEAN_PATH": "/existing/user/path"}):
            self.check()
            first = list(self.builds)
            self.check()
        self.assertEqual(self.builds, first)
        self.assertEqual(first, ["Algo2Lean", "Algo.lib.Generated", "Algo.lib.Points",
                                 "Algo.client.Generated", "Algo.client.Points"])
        self.assertTrue(all(env["LEAN_PATH"].endswith("/existing/user/path") for env in self.environments))
        facts = check_project(self.compilation, check_facts=True)
        self.assertFalse(facts.ok)
        self.assertIn("Algo/lib/Facts.lean:2:", facts.output)

    def test_labels_and_analysis_edits_leave_generated_definitions_cached(self):
        self.check()
        count = len(self.builds)
        self.files["Algo.lib.Points"] += "-- renamed label\n"
        self.check()
        self.assertEqual(self.builds[count:], ["Algo.lib.Points"])
        analysis = "import Algo.client.Generated\nexample : True := .intro\n"
        self.check(analysis=analysis)
        count = len(self.builds)
        self.check(analysis=analysis + "-- proof edit\n")
        self.assertEqual(self.builds[count:], ["Algo.client.Analysis"])

    def test_changed_transitive_source_rebuilds_every_affected_caller(self):
        self.check()
        count = len(self.builds)
        self.files["Algo.lib.Generated"] += "-- changed library implementation\n"
        self.check()
        self.assertEqual(self.builds[count:], ["Algo.lib.Generated", "Algo.lib.Points",
                                               "Algo.client.Generated", "Algo.client.Points"])
        count = len(self.builds)
        self.version = "Lean (version 4.33.1, changed-build)\n"
        self.check()
        self.assertEqual(self.builds[count:], ["Algo2Lean", "Algo.lib.Generated", "Algo.lib.Points",
                                               "Algo.client.Generated", "Algo.client.Points"])

    def test_requested_disk_proofs_are_transitive_and_other_files_are_ignored(self):
        proofs = self.root / "analysis"
        proofs.mkdir()
        (proofs / "lib.lean").write_text("import Algo.lib.Generated\n", encoding="utf-8")
        (proofs / "client.lean").write_text("import Algo.lib.Analysis\nimport Algo.client.Generated\n", encoding="utf-8")
        (proofs / "unused.lean").write_text("import Algo.missing.Analysis\n-- FAIL\n", encoding="utf-8")
        self.check()
        self.assertFalse(any(name.endswith(".Analysis") for name in self.builds))
        self.check(analysis_module="Algo.client.Analysis")
        self.assertEqual(self.builds[-2:], ["Algo.lib.Analysis", "Algo.client.Analysis"])
        count = len(self.builds)
        (proofs / "lib.lean").write_text("import Algo.lib.Generated\n-- proof edited\n", encoding="utf-8")
        self.check(analysis_module="Algo.client.Analysis")
        self.assertEqual(self.builds[count:], ["Algo.lib.Analysis", "Algo.client.Analysis"])

    def test_in_memory_proofs_and_optional_facts_follow_requested_imports(self):
        self.files["Algo.lib.Facts"] = "import Algo.lib.Generated\n"
        proofs = {"Algo.lib.Analysis": "import Algo.lib.Facts\n",
                  "Algo.unused.Analysis": "import Algo.missing.Analysis\n-- FAIL\n"}
        self.check(analysis="import Algo.lib.Analysis\n", proof_sources=proofs)
        self.assertEqual(self.builds[-3:], ["Algo.lib.Facts", "Algo.lib.Analysis", "Algo.client.Analysis"])
        self.assertNotIn("Algo.unused.Analysis", self.builds)

    def test_multiline_imports_resolve_proofs_and_cannot_bypass_import_policy(self):
        proof = "import\n/- comment -/ Algo.lib.Generated\n"
        self.check(analysis="import -- companion\n Algo.lib.Analysis\n",
                   proof_sources={"Algo.lib.Analysis": proof})
        self.assertEqual(self.builds[-2:], ["Algo.lib.Analysis", "Algo.client.Analysis"])
        checked = check_project(self.compilation, analysis="import\n Mathlib\n")
        self.assertFalse(checked.ok)
        self.assertIn("Unsupported Lean import 'Mathlib'", checked.output)

    def test_shared_source_snapshot_invalidates_only_dependent_modules(self):
        library = self.repository / "Algo2LeanLib"
        library.mkdir()
        (library / "Base.lean").write_text("import Algo2Lean\n", encoding="utf-8")
        (library / "Client.lean").write_text("import Algo2LeanLib.Base\n", encoding="utf-8")
        self.files["Algo.lib.Generated"] = "import Algo2LeanLib.Client\n"
        self.files["Algo.independent.Generated"] = "import Algo2Lean\n"
        self.check()
        count = len(self.builds)
        (library / "Base.lean").write_text("import Algo2Lean\n-- changed shared dependency\n", encoding="utf-8")
        self.check()
        rebuilt = self.builds[count:]
        self.assertIn("Algo.lib.Generated", rebuilt)
        self.assertIn("Algo.client.Generated", rebuilt)
        self.assertNotIn("Algo.independent.Generated", rebuilt)

    def test_cycles_missing_proofs_unsupported_imports_and_unsafe_names_fail(self):
        for analysis, proofs, expected in [
            ("import Algo.missing.Analysis\n", {}, "Could not find proof module"),
            ("import Algo.missing.Generated\n", {}, "No generated Lean module"),
            ("import Mathlib\n", {}, "Unsupported Lean import"),
            ("import Algo.lib.Analysis\n", {"Algo.lib.Analysis": "import Algo.client.Analysis\n"}, "import cycle"),
        ]:
            with self.subTest(expected=expected):
                checked = check_project(self.compilation, analysis=analysis, proof_sources=proofs)
                self.assertFalse(checked.ok)
                self.assertIn(expected, checked.output)
        for module in ("../Proof", "Std", "std", "Algo.client.Generated", "Algo.Lib.Analysis"):
            with self.subTest(module=module):
                checked = check_project(self.compilation, analysis="import Std\n", analysis_module=module)
                self.assertFalse(checked.ok, checked.output)
        self.assertFalse(self.builds)

    def test_companion_paths_cannot_escape_or_ambiguously_select_a_proof(self):
        outside = Path(self.directory.name) / "outside.lean"
        outside.write_text("import Std\n", encoding="utf-8")
        (self.root / "lib.lean").symlink_to(outside)
        rejected = check_project(self.compilation, analysis="import Algo.lib.Analysis\n")
        self.assertFalse(rejected.ok)
        self.assertIn("escapes the project root", rejected.output)
        (self.root / "lib.lean").unlink()
        (self.root / "lib.lean").write_text("import Algo.lib.Generated\n", encoding="utf-8")
        (self.root / "analysis").mkdir()
        (self.root / "analysis/lib.lean").write_text("import Algo.lib.Generated\n", encoding="utf-8")
        rejected = check_project(self.compilation, analysis="import Algo.lib.Analysis\n")
        self.assertFalse(rejected.ok)
        self.assertIn("ambiguous", rejected.output)

    def test_failed_or_incomplete_proofs_are_never_cached(self):
        for marker in ("FAIL", "SORRY", "NO_OBJECT"):
            source = "import Algo.client.Generated\n-- " + marker + "\n"
            with self.subTest(marker=marker):
                first = check_project(self.compilation, analysis=source)
                self.assertFalse(first.ok)
                count = len(self.builds)
                self.assertFalse(check_project(self.compilation, analysis=source).ok)
                self.assertEqual(self.builds[count:], ["Algo.client.Analysis"])
        self.check(analysis="import Algo.client.Generated\n")
        cache = Path(self.directory.name) / "algo2lean-project-cache"
        self.assertFalse(list(cache.glob(".building-*")))

    def test_missing_cached_objects_are_rebuilt(self):
        self.check()
        cache = Path(self.directory.name) / "algo2lean-project-cache"
        next(cache.glob("*/Algo/lib/Generated.olean")).unlink()
        count = len(self.builds)
        self.check()
        self.assertEqual(self.builds[count:], ["Algo.lib.Generated"])

    def test_cached_warnings_are_rechecked_after_diagnostic_format_changes(self):
        analysis = "import Algo.client.Generated\n-- SORRY\n"
        # Simulate an older checker that did not recognize the new warning.
        with patch("algo2lean.checker.has_sorry_warning", return_value=False):
            self.check(analysis=analysis)
        count = len(self.builds)
        rejected = check_project(self.compilation, analysis=analysis)
        self.assertFalse(rejected.ok)
        self.assertIn("incomplete", rejected.output)
        self.assertEqual(self.builds[count:], ["Algo.client.Analysis"])

    def test_concurrent_requests_publish_one_complete_node(self):
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(lambda _: check_project(self.compilation), range(8)))
        self.assertTrue(all(result.ok for result in results), [result.output for result in results])
        self.assertEqual(len(self.builds), 5)

    def test_missing_lean_and_timeout_are_readable_results(self):
        with patch("algo2lean.project_checker.shutil.which", return_value=None):
            absent = check_project(self.compilation)
        self.assertFalse(absent.ok)
        self.assertFalse(absent.available)
        self.assertIn("Lean was not found", absent.output)
        self.runner.side_effect = subprocess.TimeoutExpired(["lean"], 1)
        timed_out = check_project(self.compilation)
        self.assertFalse(timed_out.ok)
        self.assertTrue(timed_out.available)
        self.assertIn("timed out", timed_out.output)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ProjectLeanTests(unittest.TestCase):
    def test_proof_only_algorithm_preserves_the_original_dependency_snapshot(self):
        from algo2lean.modular import compile_project
        from algo2lean.project_checker import _sources
        examples = Path(__file__).resolve().parents[1] / "examples/modules"
        with tempfile.TemporaryDirectory(prefix="algo2lean-proof-only-") as directory:
            root = Path(directory)
            for name in ("increment", "twice"):
                (root / (name + ".algo")).write_text((examples / (name + ".algo")).read_text(), encoding="utf-8")
            (root / "analysis").mkdir()
            (root / "analysis/increment.lean").write_text(
                (examples / "analysis/increment.lean").read_text(), encoding="utf-8")
            (root / "helper.algo").write_text(
                "from increment import increment\ndef helper(value: Int) -> Int:\n    return increment(value)\n",
                encoding="utf-8")
            (root / "unused.algo").write_text("this unused file is invalid", encoding="utf-8")
            (root / "analysis/helper.lean").write_text(
                "import Algo.helper.Generated\nimport Algo.helper.Facts\nimport Algo.increment.Analysis\n"
                "#check IncrementAnalysis.summary\n", encoding="utf-8")
            compiled = compile_project("twice", root=root)
            self.assertNotIn("helper", compiled.modules)
            original = compiled.modules["increment"].lean
            # A later filesystem edit must not silently replace a dependency
            # while compiling the algorithm requested only by the proof.
            (root / "increment.algo").write_text("def broken(:\n", encoding="utf-8")
            analysis = "import Algo.twice.Generated\nimport Algo.helper.Analysis\n"
            selected, _ = _sources(compiled, analysis, None, None, False)
            self.assertEqual(selected["Algo.increment.Generated"], original)
            self.assertIn("Algo.helper.Generated", selected)
            self.assertIn("Algo.helper.Facts", selected)
            self.assertNotIn("Algo.helper.Points", selected)
            self.assertFalse(any("unused" in module for module in selected))
            checked = check_project(compiled, analysis=analysis)
            self.assertTrue(checked.ok, checked.output)

    def test_proof_only_algorithms_use_unsaved_browser_sources_and_stay_lazy(self):
        from algo2lean.modular import compile_project
        from algo2lean.project_checker import _sources
        with tempfile.TemporaryDirectory(prefix="algo2lean-unsaved-proof-") as directory:
            source = "def identity(value: Int) -> Int:\n    return value\n"
            compiled = compile_project("main", root=directory, sources={
                "main.algo": source, "helper.algo": source, "unused.algo": "invalid program",
            })
            self.assertEqual(set(compiled.project.source_overlays), {"main.algo", "helper.algo", "unused.algo"})
            selected, _ = _sources(compiled, None, None, None, False)
            self.assertFalse(any("helper" in module for module in selected))
            proof = "import -- multiline dependency\n Algo.helper.Points\n#check Algo.helper.identity.Returns\n"
            checked = check_project(compiled, analysis="import\n/- companion -/ Algo.helper.Analysis\n",
                proof_sources={"Algo.helper.Analysis": proof})
            self.assertTrue(checked.ok, checked.output)

    def test_proof_only_module_named_algo_keeps_unambiguous_source_paths(self):
        from algo2lean.modular import compile_project
        from algo2lean.project_checker import _sources
        with tempfile.TemporaryDirectory(prefix="algo2lean-module-named-algo-") as directory:
            sources = {
                "main.algo": "from pkg.algo import identity\ndef main(value: Int) -> Int:\n    return identity(value)\n",
                "pkg/algo.algo": "def identity(value: Int) -> Int:\n    return value\n",
                "helper/algo.algo": "from pkg.algo import identity\ndef helper(value: Int) -> Int:\n    return identity(value)\n",
            }
            compiled = compile_project("main", root=directory, sources=sources)
            self.assertEqual(compiled.project.source_overlays, sources)
            proof = "import Algo.helper.algo.Points\n#check Algo.helper.algo.helper.Returns\n"
            selected, _ = _sources(compiled, proof, None, None, False)
            self.assertIn("Algo.helper.algo.Generated", selected)
            self.assertIn("Algo.pkg.algo.Generated", selected)
            self.assertNotIn("Algo.helper.Generated", selected)
            self.assertEqual(selected["Algo.pkg.algo.Generated"], compiled.modules["pkg.algo"].lean)
            checked = check_project(compiled, analysis=proof)
            self.assertTrue(checked.ok, checked.output)

    def test_real_imports_reuse_component_proofs_and_preserve_diagnostics(self):
        with tempfile.TemporaryDirectory(prefix="algo2lean-proof-project-") as directory:
            root = Path(directory)
            files = {
                "Algo.component.Generated": "import Algo2Lean\nnamespace ProjectCheckerExample\ndef value : Nat := 3\nend ProjectCheckerExample\n",
                "Algo.component.Points": "import Algo.component.Generated\n",
                "Algo.component.Facts": "import Algo.component.Generated\nexample : False := by decide\n",
                "Algo.client.Generated": "import Algo.component.Generated\nnamespace ProjectCheckerExample\ndef twice : Nat := value + value\nend ProjectCheckerExample\n",
                "Algo.client.Points": "import Algo.client.Generated\n",
            }
            compilation = SimpleNamespace(files=files, project=SimpleNamespace(root=root, entry="client"))
            proof = "import Algo.component.Generated\ntheorem component_value : ProjectCheckerExample.value = 3 := rfl\n"
            (root / "component.lean").write_text(proof, encoding="utf-8")
            analysis = ("import Algo.client.Generated\nimport Algo.component.Analysis\n"
                        "example : ProjectCheckerExample.twice = 6 := by\n"
                        "  simp [ProjectCheckerExample.twice, component_value]\n")
            accepted = check_project(compilation, analysis=analysis)
            self.assertTrue(accepted.ok, accepted.output)
            facts = check_project(compilation, check_facts=True)
            self.assertFalse(facts.ok)
            self.assertIn("Algo/component/Facts.lean:2:", facts.output)
            rejected = check_project(compilation, analysis=analysis + "example : False := by decide\n")
            self.assertFalse(rejected.ok)
            self.assertIn("Algo/client/Analysis.lean:5:", rejected.output)
            incomplete = check_project(compilation, analysis=analysis + "example : False := by sorry\n")
            self.assertFalse(incomplete.ok)
            self.assertIn("incomplete", incomplete.output)
            # Changing a dependency must invalidate both its imported proof and
            # the downstream client, not reuse their formerly successful objects.
            files["Algo.component.Generated"] = files["Algo.component.Generated"].replace(":= 3", ":= 4")
            stale = check_project(compilation, analysis=analysis)
            self.assertFalse(stale.ok)
            self.assertIn("Algo/component/Analysis.lean:2:", stale.output)


if __name__ == "__main__":
    unittest.main()
