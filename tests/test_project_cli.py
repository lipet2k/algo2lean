"""Project CLI exports preserve canonical modules and user-owned files."""

from contextlib import redirect_stderr, redirect_stdout
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from algo2lean.__main__ import main
from algo2lean.checker import CheckResult
from algo2lean.modular import compile_project


ROOT = Path(__file__).resolve().parents[1]
LIBRARY = "def increment(x: Int) -> Int:\n    return x + 1\n"
CLIENT = "from library import increment\ndef run(x: Int) -> Int:\n    # @call\n    return increment(x)\n"


class ProjectCliTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="algo2lean-cli-project-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.library = self.root / "library.algo"
        self.source = self.root / "main.algo"
        self.library.write_text(LIBRARY)
        self.source.write_text(CLIENT)
        self.output = self.root / "build"

    def run_cli(self, *arguments):
        return subprocess.run([sys.executable, "-m", "algo2lean", *map(str, arguments)],
                              cwd=ROOT, capture_output=True, text=True, timeout=60)

    def test_imports_automatically_select_project_stdout(self):
        result = self.run_cli("compile", self.source)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("import Algo.library.Generated", result.stdout)
        self.assertIn("namespace Algo.«main»", result.stdout)
        self.assertNotIn("structure State_increment", result.stdout)
        self.assertIn("--output-dir", result.stderr)
        self.assertIn("dependencies", result.stderr)

    def test_all_import_forms_work_through_the_cli(self):
        variants = (("import library", "library.increment"),
                    ("import library as lib", "lib.increment"),
                    ("from library import increment", "increment"),
                    ("from library import increment as inc", "inc"))
        outputs = []
        for declaration, function in variants:
            with self.subTest(declaration=declaration):
                self.source.write_text(declaration + "\ndef run(x: Int) -> Int:\n    return " + function + "(x)\n")
                result = self.run_cli("compile", self.source)
                self.assertEqual(result.returncode, 0, result.stderr)
                outputs.append(result.stdout)
        self.assertEqual(outputs, [outputs[0]] * 4)

    def test_explicit_project_root_resolves_dotted_entry_and_sibling_imports(self):
        nested = self.root / "consumers" / "main.algo"
        nested.parent.mkdir()
        nested.write_text(CLIENT)
        result = self.run_cli("compile", nested, "--project", self.root, "--output-dir", self.output)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((self.output / "Algo/consumers/main/Generated.lean").is_file())
        self.assertTrue((self.output / "Algo/library/Generated.lean").is_file())
        default = self.run_cli("compile", nested)
        self.assertNotEqual(default.returncode, 0)
        self.assertIn("was not found", default.stderr)

    def test_output_directory_opts_into_project_mode_for_single_file(self):
        self.source.write_text(LIBRARY)
        result = self.run_cli("compile", self.source, "--output-dir", self.output)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("namespace Algo.«main»", (self.output / "Algo/main/Generated.lean").read_text())
        self.assertEqual(result.stdout, "")

    def test_export_writes_exact_canonical_files_and_preserves_timestamps(self):
        original = compile_project(self.source, root=self.root)
        first = self.run_cli("compile", self.source, "--project", self.root, "--output-dir", self.output)
        self.assertEqual(first.returncode, 0, first.stderr)
        for name, contents in original.files.items():
            path = self.output.joinpath(*name.split(".")).with_suffix(".lean")
            self.assertEqual(path.read_text(), contents)
            os.utime(path, ns=(1000000000, 1000000000))
        self.source.write_text(CLIENT.replace("# @call", "# @renamed"))
        second = self.run_cli("compile", self.source, "--output-dir", self.output)
        self.assertEqual(second.returncode, 0, second.stderr)
        for name in original.files:
            path = self.output.joinpath(*name.split(".")).with_suffix(".lean")
            if name == "Algo.main.Points":
                self.assertIn("run.At.renamed", path.read_text())
                self.assertNotEqual(path.stat().st_mtime_ns, 1000000000)
            else:
                self.assertEqual(path.stat().st_mtime_ns, 1000000000, name)
        self.assertEqual(self.library.read_text(), LIBRARY)
        self.assertEqual(self.source.read_text(), CLIENT.replace("# @call", "# @renamed"))

    def test_legacy_output_flags_have_clear_project_diagnostic(self):
        for options in (("-o", self.output / "Bad.lean"),
                        ("--points-output", self.output / "BadPoints.lean"), ("--standalone",)):
            with self.subTest(options=options):
                result = self.run_cli("compile", self.source, *options)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("use --output-dir", result.stderr)
                self.assertFalse(self.output.exists())

    def test_dependency_error_reports_its_own_file_and_line(self):
        self.library.write_text("def increment(x: Int) -> Int:\n    return missing\n")
        result = self.run_cli("compile", self.source, "--output-dir", self.output)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(str(self.library) + ":2:", result.stderr)
        self.assertFalse(self.output.exists())

    def test_explicit_root_rejects_an_entry_outside_it(self):
        other = self.root / "other"
        other.mkdir()
        result = self.run_cli("compile", self.source, "--project", other)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("inside the project root", result.stderr)

    def test_existing_handwritten_target_blocks_all_writes(self):
        target = self.output / "Algo/main/Points.lean"
        target.parent.mkdir(parents=True)
        target.write_text("-- My handwritten proof\nexample : True := by trivial\n")
        result = self.run_cli("compile", self.source, "--output-dir", self.output)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Refusing to overwrite", result.stderr)
        self.assertFalse((self.output / "Algo/library/Generated.lean").exists())
        self.assertFalse((target.parent / "Generated.lean").exists())
        self.assertIn("My handwritten proof", target.read_text())

    def test_symlinked_or_hardlinked_outputs_cannot_overwrite_user_files(self):
        proof = self.root / "analysis.lean"
        proof.write_text("-- preserved proof\n")
        shared = self.root / "Algo2Lean.lean"
        shared.write_text("-- preserved shared library\n")
        target = self.output / "Algo/main/Generated.lean"
        target.parent.mkdir(parents=True)
        for protected in (self.source, proof, shared):
            for hardlink in (False, True):
                with self.subTest(protected=protected.name, hardlink=hardlink):
                    original = protected.read_bytes()
                    if hardlink:
                        os.link(protected, target)
                    else:
                        target.symlink_to(protected)
                    result = self.run_cli("compile", self.source, "--output-dir", self.output)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(protected.read_bytes(), original)
                    self.assertFalse((self.output / "Algo/library/Generated.lean").exists())
                    target.unlink()

    def test_symlinked_output_directory_component_cannot_escape(self):
        outside = self.root / "elsewhere"
        outside.mkdir()
        self.output.mkdir()
        (self.output / "Algo").symlink_to(outside, target_is_directory=True)
        result = self.run_cli("compile", self.source, "--output-dir", self.output)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("symbolic link", result.stderr)
        self.assertEqual(list(outside.iterdir()), [])

    def test_check_is_before_writes_and_does_not_request_optional_facts(self):
        stdout, stderr = io.StringIO(), io.StringIO()
        with patch("algo2lean.project_checker.check_project", return_value=CheckResult(False, True, "failed check")) as check:
            with redirect_stdout(stdout), redirect_stderr(stderr):
                status = main(["compile", str(self.source), "--output-dir", str(self.output), "--check"])
        self.assertEqual(status, 1)
        self.assertFalse(self.output.exists())
        self.assertEqual(check.call_args.kwargs, {"check_facts": False})
        self.assertIn("failed check", stderr.getvalue())

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_project_check_and_companion_analysis_imports(self):
        proof_dir = self.root / "analysis"
        proof_dir.mkdir()
        (proof_dir / "library.lean").write_text('''import Algo.library.Generated
namespace LibraryProof
theorem nonnegative (n : Nat) : 0 ≤ n := Nat.zero_le n
end LibraryProof
''')
        proof = self.root / "client_proof.lean"
        proof.write_text('''import Algo.main.Generated
import Algo.main.Facts
import Algo.library.Analysis
#check Algo.main.run.Returns
example (n : Nat) : 0 ≤ n := LibraryProof.nonnegative n
''')
        checked = self.run_cli("compile", self.source, "--check", "--output-dir", self.output)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertIn("named points", checked.stderr)
        analyzed = self.run_cli("analyze", self.source, proof, "--project", self.root)
        self.assertEqual(analyzed.returncode, 0, analyzed.stdout + analyzed.stderr)
        self.assertIn("project and analysis", analyzed.stdout)
        automatic = self.run_cli("analyze", self.source, proof)
        self.assertEqual(automatic.returncode, 0, automatic.stdout + automatic.stderr)

    @unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
    def test_code_check_does_not_check_an_unrequested_broken_companion(self):
        (self.root / "library.lean").write_text("this is not a valid Lean proof\n")
        checked = self.run_cli("compile", self.source, "--check")
        self.assertEqual(checked.returncode, 0, checked.stderr)
        proof = self.root / "client_proof.lean"
        proof.write_text("import Algo.library.Analysis\nexample : True := by trivial\n")
        analyzed = self.run_cli("analyze", self.source, proof)
        self.assertNotEqual(analyzed.returncode, 0)
        self.assertIn("Algo.library.Analysis", analyzed.stdout)


if __name__ == "__main__":
    unittest.main()
