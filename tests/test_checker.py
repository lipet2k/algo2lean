"""Shared Lean library preparation, independent of a local Lean installation."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from algo2lean.checker import (LeanSetupError, after_import_header, check_lean,
                              lean_imports, prepare_lean_environment,
                              redirect_imports, shared_imports)
from algo2lean.compiler import compile_source


class LibraryPreparationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="algo2lean-cache-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name) / "project"
        self.root.mkdir()
        self.source = self.root / "Algo2Lean.lean"
        self.source.write_text("import Std\n", encoding="utf-8")
        self.version = "Lean (version 4.33.1, test-build)\n"
        self.builds = 0
        self.built_modules = []
        self.generated_environments = []
        self.build_failure = False
        self.build_warning = ""
        self.installation_failure = False
        for target, value in [
            ("algo2lean.checker.ROOT", self.root),
            ("algo2lean.checker.shutil.which", lambda _: "/test/bin/lean"),
            ("algo2lean.checker.tempfile.gettempdir", lambda: self.directory.name),
        ]:
            context = patch(target, value)
            context.start()
            self.addCleanup(context.stop)
        runner = patch("algo2lean.checker.subprocess.run", side_effect=self.run_lean)
        self.runner = runner.start()
        self.addCleanup(runner.stop)

    def run_lean(self, command, **kwargs):
        if "--version" in command:
            return subprocess.CompletedProcess(
                command, int(self.installation_failure),
                "" if self.installation_failure else self.version,
                "toolchain unavailable" if self.installation_failure else "",
            )
        if "-o" in command:
            self.builds += 1
            if self.build_failure:
                return subprocess.CompletedProcess(command, 1, "proof rejected", "")
            output = Path(command[command.index("-o") + 1])
            build_root = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("--root=")))
            relative = output.relative_to(build_root).with_suffix(".lean")
            self.assertTrue(build_root.name.startswith(".building-"))
            self.assertEqual((build_root / relative).read_bytes(), (self.root / relative).read_bytes())
            self.built_modules.append(relative.as_posix())
            output.write_bytes(b"test Lean object")
            return subprocess.CompletedProcess(command, 0, self.build_warning, "")
        self.generated_environments.append(kwargs["env"])
        return subprocess.CompletedProcess(command, 0, "", "")

    def test_cache_reuse_preserves_user_search_path(self):
        with patch.dict(os.environ, {"LEAN_PATH": "first" + os.pathsep + "second"}):
            first = prepare_lean_environment()
            second = prepare_lean_environment()
        self.assertEqual(self.builds, 1)
        self.assertEqual(first["LEAN_PATH"], second["LEAN_PATH"])
        self.assertTrue(first["LEAN_PATH"].endswith(os.pathsep + "first" + os.pathsep + "second"))
        self.assertTrue((Path(first["LEAN_PATH"].split(os.pathsep)[0]) / "Algo2Lean.olean").is_file())

    def test_source_and_lean_version_invalidate_cache(self):
        first = prepare_lean_environment()
        self.source.write_text("import Std\ndef changed := 1\n", encoding="utf-8")
        second = prepare_lean_environment()
        self.version = "Lean (version 4.33.1, different-build)\n"
        third = prepare_lean_environment()
        self.assertEqual(self.builds, 3)
        self.assertEqual(len({env["LEAN_PATH"] for env in (first, second, third)}), 3)

    def test_selected_analysis_modules_build_dependencies_and_leave_core_cache_reusable(self):
        library = self.root / "Algo2LeanLib"
        library.mkdir()
        (library / "Base.lean").write_text("import Std\ndef base := 1\n")
        (library / "Client.lean").write_text("import Algo2LeanLib.Base\ndef client := base\n")
        # An unused broken module must never affect unrelated algorithm checks.
        (library / "Unused.lean").write_text("import Algo2LeanLib.Missing\n")
        core = prepare_lean_environment()
        first = prepare_lean_environment(modules=("Algo2LeanLib.Client",))
        self.assertEqual(self.built_modules, ["Algo2Lean.lean", "Algo2Lean.lean",
                         "Algo2LeanLib/Base.lean", "Algo2LeanLib/Client.lean"])
        self.assertEqual(first, prepare_lean_environment(modules=("Algo2LeanLib.Client",)))
        (library / "Base.lean").write_text("import Std\ndef base := 2\n")
        second = prepare_lean_environment(modules=("Algo2LeanLib.Client",))
        self.assertNotEqual(first["LEAN_PATH"], second["LEAN_PATH"])
        self.assertEqual(core, prepare_lean_environment())
        self.assertEqual(self.builds, 7)

    def test_analysis_imports_are_selected_by_checker(self):
        library = self.root / "Algo2LeanLib"
        library.mkdir()
        (library / "Example.lean").write_text("import Std\n")
        checked = check_lean("import Algo2LeanLib.Example\nexample : True := .intro\n")
        self.assertTrue(checked.ok, checked.output)
        self.assertEqual(self.built_modules, ["Algo2Lean.lean", "Algo2LeanLib/Example.lean"])

    def test_import_scan_ignores_comments_and_non_header_text(self):
        self.assertEqual(shared_imports("""/- nested /- import Algo2LeanLib.Bad -/
import Algo2LeanLib.AlsoBad -/
import Algo2Lean
import Algo2LeanLib.Good -- import Algo2LeanLib.Bad
def text := "
import Algo2LeanLib.StringContent
"
"""), ("Algo2Lean", "Algo2LeanLib.Good"))

    def test_import_headers_follow_lean_whitespace_and_stop_before_commands(self):
        source = ("/- leading /- nested -/ comment -/\nprelude\n"
                  "import -- split header\n «Algo2LeanLib».«Base»\n"
                  "import\n/- between tokens -/ Algo2LeanLib.Client\n"
                  "def text := \"import Algo2LeanLib.NotAnImport\"\n")
        self.assertEqual(lean_imports(source), ("Algo2LeanLib.Base", "Algo2LeanLib.Client"))
        redirected, count = redirect_imports(source, {"Algo2LeanLib.Base": "Algo2LeanLib.Replacement"})
        self.assertEqual(count, 1)
        self.assertEqual(redirected, source.replace("«Algo2LeanLib».«Base»", "Algo2LeanLib.Replacement"))
        self.assertEqual(lean_imports("import Init example : True := .intro\n"), ("Init",))
        same_line = "import Init /- trailing comment -/ example : True := .intro\n"
        self.assertEqual(same_line[after_import_header(same_line):], "example : True := .intro\n")
        self.assertEqual(lean_imports("module\npublic\nmeta\nimport\nAlgo.foo.Generated\n"
                                      "import all\nAlgo.bar.Generated\npublic section\n"),
                         ("Algo.bar.Generated", "Algo.foo.Generated"))

    def test_bad_dependencies_fail_before_building(self):
        library = self.root / "Algo2LeanLib"
        library.mkdir()
        (library / "A.lean").write_text("import Algo2LeanLib.B\n")
        (library / "B.lean").write_text("import Algo2LeanLib.A\n")
        for module, message in [("Algo2LeanLib.A", "import cycle"),
                                ("Algo2LeanLib.Absent", "Could not read"),
                                ("../outside", "Invalid shared")]:
            with self.subTest(module=module), self.assertRaisesRegex(LeanSetupError, message):
                prepare_lean_environment(modules=(module,))
        self.assertEqual(self.builds, 0)

    def test_concurrent_requests_share_one_complete_build(self):
        with ThreadPoolExecutor(max_workers=8) as pool:
            environments = list(pool.map(lambda _: prepare_lean_environment(), range(16)))
        self.assertEqual(self.builds, 1)
        self.assertEqual(len({env["LEAN_PATH"] for env in environments}), 1)
        self.assertFalse(any((Path(self.directory.name) / "algo2lean-lean-cache").glob(".building-*")))

    def test_failed_build_is_reported_and_not_cached(self):
        self.build_failure = True
        result = check_lean("import Algo2Lean\n")
        self.assertFalse(result.ok)
        self.assertTrue(result.available)
        self.assertIn("Lean rejected the shared library", result.output)
        self.assertIn("proof rejected", result.output)
        self.assertFalse(self.generated_environments)
        self.build_failure = False
        self.assertTrue(check_lean("import Algo2Lean\n").ok)
        self.assertEqual(self.builds, 2)

    def test_check_passes_prepared_environment_to_lean(self):
        self.assertTrue(check_lean("import Algo2Lean\n").ok)
        environment, = self.generated_environments
        self.assertTrue((Path(environment["LEAN_PATH"].split(os.pathsep)[0]) / "Algo2Lean.olean").is_file())

    def test_unfinished_library_is_rejected_for_both_lean_warning_formats(self):
        for quoted in ("'sorry'", "`sorry`"):
            with self.subTest(quoted=quoted):
                self.build_warning = "Algo2Lean.lean:2:0: warning: declaration uses " + quoted
                result = check_lean("import Algo2Lean\n")
                self.assertFalse(result.ok)
                self.assertIn("Lean rejected the shared library", result.output)
                self.assertFalse(self.generated_environments)
        self.build_warning = ""
        self.assertTrue(check_lean("import Algo2Lean\n").ok)
        self.assertEqual(self.builds, 3)

    def test_standalone_check_needs_no_library_or_build(self):
        self.source.unlink()
        with patch.dict(os.environ, {"LEAN_PATH": "/existing/standalone/path"}):
            result = check_lean("import Std\n-- import Algo2Lean\ndef value := 1\n")
        self.assertTrue(result.ok)
        self.assertEqual(self.builds, 0)
        self.assertEqual(self.runner.call_count, 1)
        self.assertEqual(self.generated_environments[0]["LEAN_PATH"], "/existing/standalone/path")

    def test_missing_lean_is_distinct_from_library_failure(self):
        with patch("algo2lean.checker.shutil.which", return_value=None):
            with self.assertRaises(LeanSetupError) as raised:
                prepare_lean_environment()
        self.assertFalse(raised.exception.available)
        self.assertIn("Lean was not found", str(raised.exception))

    def test_unavailable_toolchain_has_actionable_message(self):
        self.installation_failure = True
        result = check_lean("import Algo2Lean\n")
        self.assertFalse(result.ok)
        self.assertIn("Could not determine the Lean version", result.output)
        self.assertIn("toolchain unavailable", result.output)

    def test_setup_timeout_is_reported(self):
        self.runner.side_effect = subprocess.TimeoutExpired(["lean", "--version"], 1)
        result = check_lean("import Algo2Lean\n", timeout=1)
        self.assertFalse(result.ok)
        self.assertTrue(result.available)
        self.assertIn("timed out", result.output)

    def test_missing_shared_source_is_reported(self):
        self.source.unlink()
        result = check_lean("import Algo2Lean\n")
        self.assertFalse(result.ok)
        self.assertIn("Could not read the shared Lean library", result.output)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class GeneratedModulesTests(unittest.TestCase):
    def test_points_are_checked_as_an_importing_module(self):
        result = compile_source("def identity(x: Int) -> Int:\n    # @result\n    return x\n", module="Identity")
        good = check_lean(result.lean, module=result.module, points_lean=result.points_lean)
        self.assertTrue(good.ok, good.output)
        bad_points = check_lean(result.lean, module=result.module,
            points_lean=result.points_lean + "example : False := by decide\n")
        self.assertFalse(bad_points.ok)
        self.assertIn("IdentityPoints.lean:", bad_points.output)
        # The core must never depend on the named-points file.
        bad_core = check_lean(result.lean + "\n#check identity.At.result\n",
            module=result.module, points_lean=result.points_lean)
        self.assertFalse(bad_core.ok)
        self.assertIn("Identity.lean:", bad_core.output)
        self.assertNotIn("IdentityPoints.lean:", bad_core.output)


if __name__ == "__main__":
    unittest.main()
