"""Each imported source obeys the same input bounds as single-file compilation."""

import ast
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from algo2lean.compiler import compile_source
from algo2lean.frontend import CompileError
from algo2lean.modular import compile_project
from algo2lean.project import ProjectError, load_project


FUNCTION = "def f(value: Int) -> Int:\n    return value\n"


class ProjectSourceLimitTests(unittest.TestCase):
    def assert_matching_error(self, source, message):
        with self.assertRaisesRegex(CompileError, message) as single:
            compile_source(source)
        with tempfile.TemporaryDirectory() as root:
            with self.assertRaisesRegex(ProjectError, message) as project:
                compile_project("main", root=root,
                    sources={"main": "from library import f\n", "library": source})
            self.assertEqual(Path(project.exception.file), Path(root).resolve() / "library.algo")
            self.assertEqual((single.exception.line, single.exception.column),
                             (project.exception.line, project.exception.column))

    def test_per_file_text_and_ast_limits_apply_to_imported_modules(self):
        self.assert_matching_error("#" + "x" * 200_000 + "\n" + FUNCTION, "200,000 character")
        self.assert_matching_error("def f() -> Int:\n" + "    value = 0\n" * 3100 +
                                   "    return value\n", "12,000 syntax nodes")

    def test_invalid_text_and_type_comments_have_the_same_source_diagnostic(self):
        for source in ("# invalid\n#\x00\n" + FUNCTION, "# invalid\n#\ud800\n" + FUNCTION):
            self.assert_matching_error(source, "invalid text character")
        self.assert_matching_error("def f() -> Int:\n    value = 0 # type: Int\n    return value\n",
                                   "Type comments are not supported")

    def test_parser_resource_errors_are_normalized_in_both_entry_points(self):
        original = ast.parse
        for failure in (RecursionError, MemoryError):
            def failing_parse(source, *args, **kwargs):
                if source == FUNCTION:
                    raise failure
                return original(source, *args, **kwargs)
            with self.subTest(failure=failure.__name__), patch(
                    "algo2lean.source_validation.ast.parse", side_effect=failing_parse):
                self.assert_matching_error(FUNCTION, "resource limit")

    def test_resolver_resource_error_keeps_the_current_module_path(self):
        with tempfile.TemporaryDirectory() as root, patch(
                "algo2lean.project._References.visit", side_effect=RecursionError):
            with self.assertRaisesRegex(ProjectError, "resource limit") as raised:
                load_project("main", root=root, sources={"main": FUNCTION})
            self.assertEqual(Path(raised.exception.file), Path(root).resolve() / "main.algo")

    def test_lowering_resource_errors_keep_the_imported_module_path(self):
        for failure in (RecursionError, MemoryError):
            with self.subTest(failure=failure.__name__), tempfile.TemporaryDirectory() as root, patch(
                    "algo2lean.modular.Lowerer", side_effect=failure):
                with self.assertRaisesRegex(ProjectError, "resource limit") as raised:
                    compile_project("main", root=root,
                        sources={"main": "from library import f\n", "library": FUNCTION})
                self.assertEqual(Path(raised.exception.file), Path(root).resolve() / "library.algo")


if __name__ == "__main__":
    unittest.main()
