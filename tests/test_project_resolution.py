"""Static project identities, import boundaries, and editor source overlays."""

import ast
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest.mock import patch

from algo2lean.frontend import CompileError
from algo2lean.project import INTERFACE, ProjectError, Symbol, load_project


FUNCTION = "def f(x: Int) -> Int:\n    return x\n"


class ProjectResolutionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()

    def write(self, name, source):
        path = self.root.joinpath(*name.split(".")).with_suffix(".algo")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(source).lstrip("\n"), encoding="utf-8")
        return path

    def load(self, source, **kwargs):
        self.write("main", source)
        return load_project("main", root=self.root, **kwargs)

    def test_four_import_forms_have_one_canonical_identity(self):
        self.write("sorting", FUNCTION)
        project = self.load('''
            import sorting
            import sorting as sorts
            from sorting import f
            from sorting import f as sort
            def run(x: Int) -> Int:
                return sorting.f(sorts.f(f(sort(x))))
        ''')
        expected = Symbol("sorting", "f", "function")
        for spelling in ("sorting.f", "sorts.f", "f", "sort"):
            self.assertEqual(project.resolve("main", spelling), expected)
        self.assertEqual(project.modules["main"].dependencies, ("sorting",))
        calls = [node for node in ast.walk(project.modules["main"].tree) if isinstance(node, ast.Call)]
        self.assertTrue(all(project.modules["main"].resolved_symbols[id(call.func)] == expected for call in calls))
        self.assertEqual(expected.canonical_name, "sorting.f")

    def test_dotted_modules_and_distinct_same_named_classes(self):
        self.write("first.types", "class Node:\n    value: Int\n")
        self.write("second.types", "class Node:\n    value: Bool\n")
        project = self.load('''
            import first.types
            import second.types as other
            def choose(n: first.types.Node) -> first.types.Node:
                return n
        ''')
        one = project.resolve("main", "first.types.Node")
        two = project.resolve("main", "other.Node")
        self.assertEqual(one.canonical_name, "first.types.Node")
        self.assertNotEqual(one, two)
        self.assertEqual(list(project.modules), ["first.types", "second.types", "main"])

    def test_multiple_dotted_imports_share_prefix(self):
        self.write("pkg.one", FUNCTION)
        self.write("pkg.two", FUNCTION)
        project = self.load("import pkg.one, pkg.two\n" + FUNCTION)
        self.assertEqual(project.resolve("main", "pkg.one.f").module, "pkg.one")
        self.assertEqual(project.resolve("main", "pkg.two.f").module, "pkg.two")
        self.assertNotIn("pkg", project.modules)

    def test_reexports_and_diamond_imports_retain_original_symbol(self):
        self.write("base", FUNCTION)
        self.write("left", "from base import f as selected\n")
        self.write("right", "import base as exported\n")
        project = self.load('''
            from left import selected as a
            from right import exported as b
            def run(x: Int) -> Int:
                return a(b.f(x))
        ''')
        original = project.modules["base"].exports["f"]
        self.assertIs(project.modules["main"].bindings["a"], original)
        self.assertIs(project.resolve("main", "b.f"), original)
        self.assertEqual(project.transitive_dependencies("main"), ("base", "left", "right"))
        self.assertEqual(list(project.modules), ["base", "left", "right", "main"])

    def test_reexported_dotted_namespace(self):
        self.write("pkg.alg", FUNCTION)
        self.write("bridge", "import pkg.alg\n")
        project = self.load("from bridge import pkg\n" + FUNCTION)
        self.assertEqual(project.resolve("main", "pkg.alg.f"), Symbol("pkg.alg", "f", "function"))

    def test_unrelated_caller_import_does_not_expand_dependency_namespace(self):
        self.write("pkg.one", FUNCTION)
        self.write("pkg.two", FUNCTION)
        self.write("middle", "import pkg.one\n" + FUNCTION)
        project = self.load("import pkg.two\nimport middle\n" + FUNCTION)
        self.assertIsNone(project.resolve("middle", "pkg.two.f"))

    def test_quoted_and_nested_annotations_preserve_source_tree(self):
        self.write("types", "class Node:\n    value: Int\n")
        source = '''
            import types as t
            def run(n: "Seq[t.Node | None]") -> t.Node | None:
                return n[0]
        '''
        project = self.load(source)
        module = project.modules["main"]
        self.assertEqual(ast.dump(module.tree), ast.dump(ast.parse(module.source)))
        function = module.tree.body[1]
        quoted = function.args.args[0].annotation
        parsed = module.quoted_annotations[id(quoted)]
        typed = next(node for node in ast.walk(parsed) if isinstance(node, ast.Attribute))
        self.assertEqual(module.resolved_symbols[id(typed)], Symbol("types", "Node", "class"))
        self.assertEqual(typed.lineno, quoted.lineno)

    def test_local_arguments_and_assignments_shadow_imports_in_bodies(self):
        self.write("lib", "class Node:\n    value: Int\n")
        project = self.load('''
            import lib
            def read(lib: lib.Node) -> Int:
                return lib.value
            def create() -> Int:
                lib = 3
                return lib
        ''')
        module = project.modules["main"]
        read = module.tree.body[1]
        self.assertEqual(module.resolved_symbols[id(read.args.args[0].annotation)].kind, "class")
        self.assertNotIn(id(read.body[0].value), module.resolved_symbols)
        self.assertNotIn(id(module.tree.body[2].body[1].value), module.resolved_symbols)

    def test_methods_do_not_acquire_same_named_global_function_identity(self):
        project = self.load('''
            def value() -> Int:
                return 0
            class Box:
                def value(self) -> Int:
                    return 1
        ''')
        module = project.modules["main"]
        self.assertEqual(module.resolved_symbols[id(module.tree.body[0])].canonical_name, "main.value")
        self.assertNotIn(id(module.tree.body[1].body[0]), module.resolved_symbols)

    def test_interface_marker_is_builtin_and_may_be_aliased(self):
        project = self.load('''
            from algo2lean import Interface as Contract
            class Counter(Contract):
                def value(self) -> Int: ...
        ''')
        module = project.modules["main"]
        self.assertEqual(module.bindings["Contract"], INTERFACE)
        self.assertEqual(module.bindings["Counter"], Symbol("main", "Counter", "interface"))
        self.assertEqual(module.dependencies, ())
        self.assertEqual(list(project.modules), ["main"])

    def test_module_qualified_interface_marker(self):
        project = self.load("import algo2lean as a\nclass C(a.Interface):\n    pass\n")
        self.assertEqual(project.modules["main"].exports["C"].kind, "interface")

    def test_only_marker_inheritance_is_accepted(self):
        for source in ("class C(Interface):\n    pass\n", "class A:\n    pass\nclass C(A):\n    pass\n"):
            with self.subTest(source=source), self.assertRaisesRegex(ProjectError, "only base"):
                self.load(source)

    def test_sources_overlay_disk_and_supply_unsaved_dependencies(self):
        self.write("lib", FUNCTION)
        project = load_project(self.root / "main.algo", root=self.root, sources={
            "main.algo": "from lib import replacement\n",
            str(self.root / "lib.algo"): "def replacement() -> Int:\n    return 3\n",
        })
        self.assertEqual(project.resolve("main", "replacement").canonical_name, "lib.replacement")
        self.assertFalse((self.root / "main.algo").exists())
        self.assertEqual((self.root / "lib.algo").read_text(), FUNCTION)
        other = load_project("main", root=self.root, sources={"main": "import pkg.tool\n", "pkg/tool.algo": FUNCTION})
        self.assertIn("pkg.tool", other.modules)

    def test_unresolved_cycle_diagnostic_identifies_importing_file_and_line(self):
        self.write("a", "from b import f\n")
        self.write("b", "# comment\nfrom a import f\n")
        with self.assertRaisesRegex(ProjectError, "Unresolved cyclic re-export") as raised:
            load_project("a", root=self.root)
        self.assertIsInstance(raised.exception, CompileError)
        self.assertEqual(raised.exception.line, 2)
        self.assertEqual(raised.exception.file, str(self.root / "b.algo"))
        self.assertEqual(raised.exception.to_dict()["file"], raised.exception.file)

    def test_missing_import_points_to_import_not_entry(self):
        with self.assertRaisesRegex(ProjectError, "was not found") as raised:
            self.load("# comment\nimport absent\n")
        self.assertEqual(raised.exception.line, 2)
        self.assertEqual(raised.exception.file, str(self.root / "main.algo"))

    def test_imported_syntax_error_points_to_dependency(self):
        self.write("bad", "def nope(\n")
        with self.assertRaises(ProjectError) as raised:
            self.load("import bad\n")
        self.assertEqual(raised.exception.file, str(self.root / "bad.algo"))
        self.assertEqual(raised.exception.line, 1)

    def test_reject_unsupported_import_forms(self):
        for source, message in (
            ("from .lib import f\n", "Relative"),
            ("from lib import *\n", "Wildcard"),
            ("if True:\n    import lib\n", "unconditional"),
            ("def run() -> Int:\n    import lib\n    return 1\n", "unconditional"),
            ("try:\n    import lib\nexcept:\n    pass\n", "unconditional"),
        ):
            with self.subTest(source=source), self.assertRaisesRegex(ProjectError, message):
                self.load(source)

    def test_missing_exports_and_conflicting_aliases(self):
        self.write("one", FUNCTION)
        self.write("two", FUNCTION)
        for source, message in (
            ("from one import missing\n", "does not export"),
            ("from one import f\nfrom two import f\n", "Conflicting binding"),
            ("import one\ndef one() -> Int:\n    return 0\n", "Conflicting binding"),
            ("import one\ndef run() -> Int:\n    return one.missing()\n", "does not export"),
            ("from one import f as Int\n", "reserved"),
        ):
            with self.subTest(source=source), self.assertRaisesRegex(ProjectError, message):
                self.load(source)

    def test_reject_virtual_source_case_collisions_including_namespaces(self):
        for sources in ({"main": FUNCTION, "MAIN": FUNCTION}, {"pkg.a": FUNCTION, "Pkg.b": FUNCTION}):
            with self.subTest(sources=sources), self.assertRaisesRegex(ProjectError, "Case-colliding"):
                load_project("main", root=self.root, sources=sources)

    def test_reject_wrong_disk_path_case(self):
        self.write("library", FUNCTION)
        with self.assertRaisesRegex(ProjectError, "case mismatch"):
            self.load("import Library\n")

    def test_reject_disk_case_collisions_when_filesystem_supports_them(self):
        lower = self.write("lib", FUNCTION)
        upper = self.write("Lib", FUNCTION)
        if lower.samefile(upper):
            self.skipTest("Filesystem does not permit separate case-colliding files")
        with self.assertRaisesRegex(ProjectError, "Case-colliding"):
            self.load("import lib\n")

    def test_reject_entry_and_overlay_paths_outside_root(self):
        with self.assertRaisesRegex(ProjectError, "inside the project root"):
            load_project("../outside.algo", root=self.root)
        with self.assertRaisesRegex(ProjectError, "inside the project root"):
            load_project("main", root=self.root, sources={"../outside.algo": FUNCTION})
        with self.assertRaisesRegex(ProjectError, "inside the project root"):
            load_project(self.root.parent / "outside.algo", root=self.root)

    def test_path_components_cannot_disguise_dotted_module_mapping(self):
        with self.assertRaisesRegex(ProjectError, "ASCII identifiers"):
            load_project(self.root / "pkg.tool.algo", root=self.root)

    def test_reject_file_and_directory_symlink_escapes_even_with_overlay(self):
        with tempfile.TemporaryDirectory() as directory:
            outside = Path(directory).resolve()
            (outside / "payload.algo").write_text(FUNCTION)
            (self.root / "unsafe.algo").symlink_to(outside / "payload.algo")
            (self.root / "linked").symlink_to(outside, target_is_directory=True)
            for name in ("unsafe", "linked.payload"):
                with self.subTest(name=name), self.assertRaisesRegex(ProjectError, "symbolic link"):
                    self.load("import %s\n" % name, sources={name: FUNCTION})

    def test_same_source_cannot_gain_two_identities_through_symlinks(self):
        self.write("original", FUNCTION)
        (self.root / "alias.algo").symlink_to(self.root / "original.algo")
        with self.assertRaisesRegex(ProjectError, "same source path"):
            self.load("import original\nimport alias\n")

    def test_source_is_never_executed_and_host_modules_are_not_imported(self):
        with patch("builtins.exec", side_effect=AssertionError("source executed")):
            project = load_project("main", root=self.root, sources={"main": FUNCTION})
        self.assertIn("main", project.modules)
        with self.assertRaisesRegex(ProjectError, "was not found"):
            self.load("import sys\n")
        with self.assertRaisesRegex(ProjectError, "Only imports"):
            self.load("__import__('os').system('should never run')\n")

    def test_module_count_limit_reports_import_location(self):
        self.write("lib", FUNCTION)
        with self.assertRaisesRegex(ProjectError, "limit of 1") as raised:
            self.load("import lib\n", max_modules=1)
        self.assertEqual(raised.exception.file, str(self.root / "main.algo"))


if __name__ == "__main__":
    unittest.main()
