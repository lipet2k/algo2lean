from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
SOURCE = "def identity(x: Int) -> Int:\n    return x\n"


class CliTests(unittest.TestCase):
    def run_cli(self, *arguments):
        return subprocess.run([sys.executable, "-m", "algo2lean", *map(str, arguments)], cwd=str(ROOT), capture_output=True, text=True, timeout=40)

    def test_compile_stdout_and_file(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            output = Path(directory) / "output.lean"
            source.write_text(SOURCE)
            result = self.run_cli("compile", source)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("identity.Returns", result.stdout)
            self.assertTrue(result.stdout.startswith("import Algo2Lean\n"))
            saved = self.run_cli("compile", source, "-o", output)
            self.assertEqual(saved.returncode, 0, saved.stderr)
            self.assertEqual(output.read_text(), result.stdout)
            self.assertTrue((Path(directory) / "outputPoints.lean").read_text().startswith("import «output»\n"))
            self.assertEqual(source.read_text(), SOURCE)

    def test_standalone_and_shared_library_exports(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            library = Path(directory) / "Algo2Lean.lean"
            source.write_text(SOURCE)
            standalone = self.run_cli("compile", source, "--standalone")
            self.assertEqual(standalone.returncode, 0, standalone.stderr)
            self.assertIn("inductive Valid", standalone.stdout)
            self.assertNotIn("import Algo2Lean\n", standalone.stdout)
            exported = self.run_cli("library", "-o", library)
            self.assertEqual(exported.returncode, 0, exported.stderr)
            self.assertEqual(library.read_text(), (ROOT / "Algo2Lean.lean").read_text())
            stdout = self.run_cli("library")
            self.assertEqual(stdout.returncode, 0, stdout.stderr)
            self.assertEqual(stdout.stdout, library.read_text())

    def test_shared_library_filename_is_reserved(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            library = Path(directory) / "Algo2Lean.lean"
            source.write_text(SOURCE)
            library.write_text("existing library")
            result = self.run_cli("compile", source, "-o", library)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(library.read_text(), "existing library")

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_check_imported_output(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            source.write_text(SOURCE)
            checked = self.run_cli("compile", source, "--check")
            self.assertEqual(checked.returncode, 0, checked.stderr)
            self.assertTrue(checked.stdout.startswith("import Algo2Lean\n"))

    def test_refuses_to_overwrite_source(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            source.write_text(SOURCE)
            result = self.run_cli("compile", source, "-o", source)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(source.read_text(), SOURCE)

    def test_named_points_are_separate_and_core_timestamp_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            output = Path(directory) / "Identity.lean"
            points = Path(directory) / "IdentityPoints.lean"
            source.write_text(SOURCE.replace("return x", "# @first\n    return x"))
            first = self.run_cli("compile", source, "-o", output)
            self.assertEqual(first.returncode, 0, first.stderr)
            original = output.read_bytes()
            self.assertNotIn("identity.At.first", output.read_text())
            self.assertIn("identity.At.first", points.read_text())
            # An unchanged timestamp confirms that identical output is not rewritten.
            os.utime(output, ns=(1000000000, 1000000000))
            source.write_text(SOURCE.replace("return x", "# @second\n    return x"))
            second = self.run_cli("compile", source, "-o", output)
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual(output.read_bytes(), original)
            self.assertEqual(output.stat().st_mtime_ns, 1000000000)
            self.assertIn("identity.At.second", points.read_text())
            self.assertNotIn("identity.At.first", points.read_text())

    def test_stdout_can_export_points_with_predictable_import(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "identity.algo"
            points = Path(directory) / "IdentityGeneratedPoints.lean"
            source.write_text(SOURCE.replace("return x", "# @result\n    return x"))
            result = self.run_cli("compile", source, "--points-output", points)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(points.read_text().startswith("import «IdentityGenerated»\n"))
            self.assertIn("identity.At.result", points.read_text())
            self.assertNotIn("identity.At.result", result.stdout)
            self.assertIn("IdentityGenerated.lean", result.stderr)

    def test_output_module_names_and_points_location_are_validated(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            source.write_text(SOURCE)
            for name in ("bad-name.lean", "1Bad.lean", "Foo.txt", "Init.lean"):
                with self.subTest(name=name):
                    output = Path(directory) / name
                    result = self.run_cli("compile", source, "-o", output)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse(output.exists())
            for points in (Path(directory) / "Wrong.lean", Path(directory) / "other" / "FooPoints.lean"):
                result = self.run_cli("compile", source, "-o", Path(directory) / "Foo.lean", "--points-output", points)
                self.assertNotEqual(result.returncode, 0)
            self.assertFalse((Path(directory) / "Foo.lean").exists())

    def test_output_aliases_do_not_clobber_source_core_or_library(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            output = Path(directory) / "Foo.lean"
            points = Path(directory) / "FooPoints.lean"
            source.write_text(SOURCE)
            for target in (source, output, ROOT / "Algo2Lean.lean"):
                output.write_text("existing core")
                original = target.read_bytes()
                for hard_link in (False, True):
                    with self.subTest(target=target.name, hard_link=hard_link):
                        if hard_link:
                            os.link(target, points)
                        else:
                            points.symlink_to(target)
                        result = self.run_cli("compile", source, "-o", output)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertEqual(target.read_bytes(), original)
                        self.assertEqual(output.read_text(), "existing core")
                        points.unlink()

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_check_separate_named_module_and_standalone(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            source.write_text(SOURCE.replace("return x", "# @result\n    return x"))
            for options in ([], ["--standalone"]):
                result = self.run_cli("compile", source, "-o", Path(directory) / "Foo.lean", "--check", *options)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("named points", result.stderr)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_lean_keyword_output_filename_uses_escaped_import(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            source.write_text(SOURCE.replace("return x", "# @result\n    return x"))
            result = self.run_cli("compile", source, "-o", Path(directory) / "namespace.lean", "--check")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((Path(directory) / "namespacePoints.lean").read_text().startswith("import «namespace»\n"))

    def test_diagnostic_does_not_clobber_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.algo"
            output = Path(directory) / "output.lean"
            source.write_text("def identity(x: Int) -> Int:\n    return unknown\n")
            output.write_text("existing output")
            result = self.run_cli("compile", source, "-o", output)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(":2:", result.stderr)
            self.assertEqual(output.read_text(), "existing output")


if __name__ == "__main__":
    unittest.main()
