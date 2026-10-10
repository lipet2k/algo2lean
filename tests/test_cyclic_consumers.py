"""Recursive source groups retain ordinary editor, export, and verification APIs."""

import base64
from contextlib import redirect_stderr, redirect_stdout
import io
from pathlib import Path
import tempfile
import unittest
import zipfile

from algo2lean.__main__ import main
from algo2lean.browser import request
from algo2lean.checker import lean_imports
from algo2lean.modular import compile_project
from algo2lean.project_checker import project_lean_sources
from algo2lean.verification import verify_generated


SOURCES = {
    "even.algo": (
        "from odd import is_odd\n\n"
        "def is_even(n: Int) -> Bool:\n"
        "    # @test\n"
        "    if n == 0:\n"
        "        return True\n"
        "    return is_odd(n - 1)\n"
    ),
    "odd.algo": (
        "import even\n\n"
        "def is_odd(n: Int) -> Bool:\n"
        "    if n == 0:\n"
        "        return False\n"
        "    return even.is_even(n - 1)\n"
    ),
}


class CyclicConsumerTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="algo2lean-cyclic-consumers-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for filename, source in SOURCES.items():
            (self.root / filename).write_text(source, encoding="utf-8")
        self.compiled = compile_project("even.algo", root=self.root)
        self.payload = {"filename": "even.algo", "source": SOURCES["even.algo"],
                        "project_sources": SOURCES}

    def body(self, route, **updates):
        result = request(route, {**self.payload, **updates}, project=True)
        self.assertEqual(result["status"], 200, result)
        return result["body"]

    def archive(self, route, **updates):
        result = request(route, {**self.payload, **updates}, project=True)
        self.assertEqual(result["status"], 200, result)
        with zipfile.ZipFile(io.BytesIO(base64.b64decode(result["body"]))) as archive:
            return {name: archive.read(name).decode("utf-8") for name in archive.namelist()}

    def test_browser_compilation_preserves_public_modules_and_complete_outputs(self):
        data = self.body("/api/compile")
        self.assertEqual(data["module"], "Algo.even.Generated")
        self.assertEqual(data["points_module"], "Algo.even.Points")
        self.assertEqual(data["project_files"], self.compiled.files)
        self.assertIn(data["implementation_module"], data["project_files"])
        self.assertIn(data["implementation_points_module"], data["project_files"])
        self.assertIn(data["implementation_facts_module"], data["project_files"])
        self.assertEqual({module["filename"] for module in data["project_modules"]}, set(SOURCES))
        self.assertEqual([function["name"] for function in data["functions"]], ["is_even"])
        alternate = self.body("/api/compile", filename="odd.algo", source=SOURCES["odd.algo"])
        self.assertEqual(alternate["project_files"], data["project_files"])
        self.assertEqual(alternate["module"], "Algo.odd.Generated")
        self.assertEqual([function["name"] for function in alternate["functions"]], ["is_odd"])

    def test_generation_manifest_and_archive_include_the_shared_implementation(self):
        data = self.body("/api/generation")
        expected = {name.replace(".", "/") + ".lean": text
                    for name, text in self.compiled.files.items()}
        self.assertEqual(data["files"], expected)
        self.assertEqual(set(data["manifest"]["sources"]), set(SOURCES))
        self.assertEqual(set(data["manifest"]["outputs"]), set(expected))
        files = self.archive("/api/generation", archive=True)
        output = self.root / "generated"
        for name, text in files.items():
            target = output / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
        result = verify_generated(self.root / "even.algo", output, project_root=self.root)
        self.assertTrue(result["exact"], result)
        facade_modules = {module.lean_module for module in self.compiled.modules.values()}
        implementation = next(name for name in self.compiled.files
                              if name.endswith(".Generated") and name not in facade_modules)
        missing = implementation.replace(".", "/") + ".lean"
        (output / missing).unlink()
        result = verify_generated(self.root / "even.algo", output, project_root=self.root)
        self.assertFalse(result["exact"])
        self.assertEqual(result["missing"], [missing])

    def test_project_export_and_checker_order_use_an_acyclic_lean_graph(self):
        analysis = (
            "import Algo.even.Generated\n"
            "import Algo.odd.Points\n"
            "#check Algo.even.is_even.Returns\n"
            "#check Algo.odd.is_odd.Returns\n"
        )
        sources = project_lean_sources(self.compiled,
            proof_sources={"Algo.even.Analysis": analysis},
            analysis_modules=("Algo.even.Analysis",))
        visited = set()
        for name, text in sources.items():
            for dependency in lean_imports(text):
                if dependency in sources:
                    self.assertIn(dependency, visited, (name, dependency))
            visited.add(name)
        files = self.archive("/api/project-export", analysis=analysis)
        self.assertNotIn("EXPORT_DIAGNOSTICS.txt", files)
        for name, text in sources.items():
            self.assertEqual(files[name.replace(".", "/") + ".lean"], text)
        for filename, text in SOURCES.items():
            self.assertEqual(files["source/" + filename], text)

    def test_cli_exports_all_units_and_replaces_its_previous_generated_files(self):
        output = self.root / "compiled"
        command = ["compile", str(self.root / "even.algo"), "--project", str(self.root),
                   "--output-dir", str(output)]
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(main(command), 0, errors.getvalue())
        expected = {name.replace(".", "/") + ".lean": text
                    for name, text in self.compiled.files.items()}
        actual = {path.relative_to(output).as_posix(): path.read_text(encoding="utf-8")
                  for path in output.rglob("*.lean")}
        self.assertEqual(actual, expected)
        changed = SOURCES["even.algo"].replace("return True", "return False")
        (self.root / "even.algo").write_text(changed, encoding="utf-8")
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(main(command), 0, errors.getvalue())
        result = verify_generated(self.root / "even.algo", output, project_root=self.root)
        self.assertTrue(result["exact"], result)


if __name__ == "__main__":
    unittest.main()
