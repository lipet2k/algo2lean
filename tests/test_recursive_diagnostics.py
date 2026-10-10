"""Recursive implementation groups report errors in original source files."""

from pathlib import Path
import tempfile
import unittest

from algo2lean.modular import compile_project
from algo2lean.project import ProjectError


FIRST = "import b\ndef first(x: Int) -> Int:\n    return x\n"
COUNTER = "from algo2lean import Interface\nclass Counter(Interface):\n    def get(self) -> Int: ...\n"


class RecursiveDiagnosticTests(unittest.TestCase):
    def assert_source_error(self, sources, message, module, line, column=None):
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-diagnostic-") as root:
            with self.assertRaisesRegex(ProjectError, message) as raised:
                compile_project("a", root=root, sources=sources)
            error = raised.exception
            self.assertEqual(Path(error.file), Path(root).resolve() / (module + ".algo"))
            self.assertEqual(error.line, line)
            if column is not None:
                self.assertEqual(error.column, column)
            return error

    def test_later_member_type_error_uses_original_file_line_and_column(self):
        self.assert_source_error({
            "a": FIRST,
            "b": "import a\n\n# The second source has its own line numbers.\ndef second(x: Int) -> Int:\n    return True\n",
        }, "Expected Int, got Bool", "b", 5, 12)

    def test_third_member_error_survives_sources_without_final_newlines(self):
        self.assert_source_error({
            "a": "import b\ndef first(x: Int) -> Int:\n    return x",
            "b": "import c\n\n# No final newline",
            "c": "import a\n\n\ndef third(x: Int) -> Int:\n    return False",
        }, "Expected Int, got Bool", "c", 5, 12)

    def test_duplicate_point_label_reports_second_member_statement(self):
        self.assert_source_error({
            "a": FIRST,
            "b": "import a\n\ndef second(x: Int) -> Int:\n    # @same\n    y = x\n    # @same\n    return y\n",
        }, "Duplicate source point name 'same' in function 'b.second'", "b", 7, 5)

    def test_diagnostic_name_translation_preserves_longer_source_identifiers(self):
        error = self.assert_source_error({
            "a": FIRST,
            "b": "import a\ndef second(x: Int) -> Int:\n    # @tag__a2l_group_1_second_suffix\n    y = x\n    # @tag__a2l_group_1_second_suffix\n    return y\n",
        }, "in function 'b.second'", "b", 6, 5)
        self.assertIn("'tag__a2l_group_1_second_suffix'", error.message)

    def test_method_diagnostic_uses_class_member_not_internal_function_name(self):
        self.assert_source_error({
            "a": FIRST,
            "b": "import a\nclass Box:\n    def read(self) -> Int:\n        # @same\n        x = 1\n        # @same\n        return x\n",
        }, "in function 'b.Box.read'", "b", 7, 9)

    def test_invalid_label_forms_report_original_comment_location(self):
        cases = [
            ("    return x  # @exit\n", "on its own line", 4, 15),
            ("    # @not-a-name\n    return x\n", "standalone comment", 4, 5),
            ("    # @exit\n\n    return x\n", "immediately above", 4, 5),
        ]
        for body, message, line, column in cases:
            with self.subTest(body=body):
                self.assert_source_error({
                    "a": FIRST,
                    "b": "import a\n\ndef second(x: Int) -> Int:\n" + body,
                }, message, "b", line, column)

    def test_stored_interface_conversion_reports_original_expression(self):
        self.assert_source_error({
            "a": FIRST,
            "b": "import a\nfrom backend import Storage\nfrom api import Counter\n\ndef invalid() -> Int:\n    item: Counter = Storage()\n    return item.get()\n",
            "api": COUNTER,
            "backend": "class Storage:\n    def get(self) -> Int:\n        return 0\n",
        }, "storing an interface conversion", "b", 6, 21)

    def test_unsupported_interface_sequence_reports_function_in_later_member(self):
        self.assert_source_error({
            "a": FIRST,
            "b": "import a\nfrom api import Counter\ndef invalid(items: Seq[Counter]) -> Int:\n    return 0\n",
            "api": COUNTER,
        }, "Sequences of abstract interface references", "b", 3, 1)

    def test_unsupported_interface_fields_report_original_annotation(self):
        for annotation, message in (("Counter", "Abstract interface references"),
                                    ("Seq[Counter]", "Sequences of abstract interface references")):
            with self.subTest(annotation=annotation):
                self.assert_source_error({
                    "a": FIRST,
                    "b": "import a\nfrom api import Counter\nclass Holder:\n    item: %s\n" % annotation,
                    "api": COUNTER,
                }, message, "b", 4, 11)

    def test_quoted_annotation_error_reports_original_annotation(self):
        self.assert_source_error({
            "a": FIRST,
            "b": "import a\n\ndef second(x: \"Unknown\") -> Int:\n    return 0\n",
        }, "A type annotation must be", "b", 3, 15)

    def test_generated_prefixes_cannot_collide_with_source_function_names(self):
        sources = {
            "a": "from b import count as other\ndef g1_count(x: Int) -> Int:\n    return other(x)\ndef count(x: Int) -> Int:\n    return x\n",
            "b": "from a import g1_count\ndef count(x: Int) -> Int:\n    return g1_count(x)\ndef g0_g1_count(x: Int) -> Int:\n    return x\n",
        }
        with tempfile.TemporaryDirectory(prefix="algo2lean-recursive-names-") as root:
            compiled = compile_project("a", root=root, sources=sources)
        implementation = compiled.entry.implementation
        names = [internal for member in compiled.modules.values()
                 for internal in member.implementation_names.values()]
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(set(names), set(implementation.functions))
        self.assertEqual(set(compiled.modules["a"].functions), {"count", "g1_count"})
        self.assertEqual(set(compiled.modules["b"].functions), {"count", "g0_g1_count"})

    def test_generated_function_name_is_not_an_implicit_source_binding(self):
        self.assert_source_error({
            "a": "import b\ndef first(x: Int) -> Int:\n    return g1_second(x)\n",
            "b": "import a\ndef second(x: Int) -> Int:\n    return x\n",
        }, "Unknown function", "a", 3, 12)

    def test_reserved_generated_call_name_is_rejected(self):
        self.assert_source_error({
            "a": "import b\ndef first(x: Int) -> Int:\n    return _a2l_group_1_second(x)\n",
            "b": "import a\ndef second(x: Int) -> Int:\n    return x\n",
        }, "Names beginning _a2l_group_ are reserved", "a", 3, 12)

    def test_reserved_generated_type_name_is_rejected_in_bare_and_quoted_annotations(self):
        for annotation in ("_a2l_group_1_Box", '"_a2l_group_1_Box"'):
            with self.subTest(annotation=annotation):
                self.assert_source_error({
                    "a": "import b\ndef first(x: %s) -> Int:\n    return 0\n" % annotation,
                    "b": "import a\nclass Box:\n    value: Int\n",
                }, "Names beginning _a2l_group_ are reserved", "a", 2, 14)


if __name__ == "__main__":
    unittest.main()
