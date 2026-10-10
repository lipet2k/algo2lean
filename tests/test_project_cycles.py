"""Recursive imports resolve static declarations before function bodies."""

import ast
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from algo2lean.project import INTERFACE, ProjectError, Symbol, load_project


class ProjectCycleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()

    def load(self, sources, entry="a", **kwargs):
        return load_project(entry, root=self.root, sources=sources, **kwargs)

    def test_named_imports_resolve_mutual_calls_before_visiting_bodies(self):
        project = self.load({
            "a": "from b import odd\ndef even(n: Int) -> Bool:\n    return n == 0 or odd(n - 1)\n",
            "b": "from a import even\ndef odd(n: Int) -> Bool:\n    return n != 0 and even(n - 1)\n",
        })
        self.assertEqual(project.compilation_groups, (("a", "b"),))
        for owner, called in (("a", "odd"), ("b", "even")):
            module = project.modules[owner]
            function = next(node for node in module.tree.body if isinstance(node, ast.FunctionDef))
            call = next(node for node in ast.walk(function) if isinstance(node, ast.Call))
            self.assertIs(module.resolved_symbols[id(call.func)], module.bindings[called])
        self.assertEqual(project.transitive_dependencies("a"), ("b",))
        self.assertEqual(project.transitive_dependencies("b"), ("a",))

    def test_dotted_and_aliased_imports_have_entry_independent_group_members(self):
        sources = {
            "pkg.a": "import pkg.b\ndef f(n: Int) -> Int:\n    return pkg.b.g(n)\n",
            "pkg.b": "import pkg.a as peer\ndef g(n: Int) -> Int:\n    return peer.f(n)\n",
        }
        for entry in sources:
            with self.subTest(entry=entry):
                project = self.load(sources, entry=entry)
                self.assertEqual(project.compilation_groups, (("pkg.a", "pkg.b"),))
                self.assertEqual(list(project.modules), ["pkg.a", "pkg.b"])
                self.assertEqual(project.resolve("pkg.a", "pkg.b.g"), Symbol("pkg.b", "g", "function"))
                self.assertEqual(project.resolve("pkg.b", "peer.f"), Symbol("pkg.a", "f", "function"))

    def test_group_dependencies_precede_mutual_group_and_callers(self):
        project = self.load({
            "main": "import a\nimport leaf\n",
            "a": "import b\nimport shared\n",
            "b": "import a\nimport shared\n",
            "shared": "import leaf\n",
            "leaf": "def identity(x: Int) -> Int:\n    return x\n",
        }, entry="main")
        self.assertEqual(project.compilation_groups, (("leaf",), ("shared",), ("a", "b"), ("main",)))
        self.assertEqual(list(project.modules), ["leaf", "shared", "a", "b", "main"])
        self.assertEqual(set(project.transitive_dependencies("a")), {"leaf", "shared", "b"})

    def test_several_components_remain_separate(self):
        project = self.load({
            "a": "import b\nimport c\n",
            "b": "import a\n",
            "c": "import d\n",
            "d": "import c\n",
        })
        self.assertEqual(project.compilation_groups, (("c", "d"), ("a", "b")))

    def test_self_import_preserves_one_declaration(self):
        project = self.load({
            "a": "import a\nfrom a import f as recurse\ndef f(x: Int) -> Int:\n    return recurse(x)\n",
        }, max_modules=1)
        self.assertEqual(project.compilation_groups, (("a",),))
        self.assertEqual(project.modules["a"].dependencies, ("a",))
        self.assertEqual(project.transitive_dependencies("a"), ())
        self.assertIs(project.resolve("a", "recurse"), project.resolve("a", "a.f"))

    def test_reexports_through_cycle_keep_original_symbol(self):
        project = self.load({
            "a": "from b import selected\ndef f(x: Int) -> Int:\n    return selected(x)\n",
            "b": "from c import forwarded as selected\n",
            "c": "from a import f as forwarded\n",
        })
        symbol = project.modules["a"].bindings["f"]
        self.assertIs(project.resolve("a", "selected"), symbol)
        self.assertIs(project.resolve("b", "selected"), symbol)
        self.assertIs(project.resolve("c", "forwarded"), symbol)
        self.assertEqual(project.compilation_groups, (("a", "b", "c"),))

    def test_imported_interface_kind_is_propagated_after_cycle_resolution(self):
        project = self.load({
            "a": "from b import Marker\nclass Contract(Marker):\n    def value(self) -> Int: ...\n",
            "b": "from a import Contract as API\nfrom algo2lean import Interface as Marker\n",
        })
        self.assertEqual(project.resolve("a", "Marker"), INTERFACE)
        self.assertEqual(project.resolve("b", "API"), Symbol("a", "Contract", "interface"))
        declaration = project.modules["a"].tree.body[1]
        self.assertIs(project.resolve("b", "API"), project.modules["a"].resolved_symbols[id(declaration)])

    def test_cycle_does_not_hide_missing_export(self):
        with self.assertRaisesRegex(ProjectError, "Module 'a' does not export 'missing'"):
            self.load({"a": "import b\n", "b": "from a import missing\n"})

    def test_pure_reexport_cycle_has_declaration_diagnostic(self):
        with self.assertRaisesRegex(ProjectError, r"cyclic re-export: .*needs a function, class, or module declaration"):
            self.load({"a": "from b import g as f\n", "b": "from a import f as g\n"})

    def test_deferred_imports_still_reject_conflicting_names(self):
        with self.assertRaisesRegex(ProjectError, "Conflicting binding for 'f'"):
            self.load({
                "a": "from b import f\ndef f(x: Int) -> Int:\n    return x\n",
                "b": "import a\ndef f(x: Int) -> Int:\n    return x\n",
            })

    def test_deferred_alias_cannot_replace_another_import(self):
        for imports in ("from b import f as x\nimport c as x\n",
                        "import c as x\nfrom b import f as x\n",
                        "from b import f as x\nfrom c import f as x\n"):
            with self.subTest(imports=imports), self.assertRaisesRegex(ProjectError, "Conflicting binding for 'x'"):
                self.load({
                    "a": imports,
                    "b": "import a\ndef f(x: Int) -> Int:\n    return x\n",
                    "c": "def f(x: Int) -> Int:\n    return x + 1\n",
                })

    def test_repeated_aliases_to_the_same_declaration_remain_valid(self):
        project = self.load({
            "a": "from b import f\nfrom c import forwarded as f\n",
            "b": "import a\ndef f(x: Int) -> Int:\n    return x\n",
            "c": "from b import f as forwarded\n",
        })
        self.assertIs(project.resolve("a", "f"), project.resolve("c", "forwarded"))

    def test_recursive_imports_do_not_allow_class_inheritance(self):
        for base in ("API", "Marker, API", "Marker, metaclass=API"):
            with self.subTest(base=base), self.assertRaisesRegex(ProjectError, "only base") as raised:
                self.load({
                    "a": "from b import API\n",
                    "b": "import a\nfrom algo2lean import Interface as Marker\nclass API(Marker):\n    pass\nclass Invalid(%s):\n    pass\n" % base,
                })
            self.assertEqual(Path(raised.exception.file), self.root / "b.algo")
            self.assertEqual(raised.exception.line, 5)

    def test_mutually_referential_class_annotations_preserve_source_coordinates(self):
        sources = {
            "a": "from b import B\nclass A:\n    peer: \"B | None\"\n",
            "b": "from a import A\nclass B:\n    peer: \"A | None\"\n",
        }
        project = self.load(sources)
        for name, source in sources.items():
            with self.subTest(name=name):
                module = project.modules[name]
                self.assertEqual(ast.dump(module.tree, include_attributes=True),
                                 ast.dump(ast.parse(source), include_attributes=True))
                quoted = module.tree.body[1].body[0].annotation
                parsed = module.quoted_annotations[id(quoted)]
                target = parsed.left
                self.assertEqual(module.resolved_symbols[id(target)].kind, "class")
                self.assertEqual((target.lineno, target.col_offset), (quoted.lineno, quoted.col_offset))

    def test_local_parameter_shadowing_remains_distinct_from_cyclic_import(self):
        project = self.load({
            "a": "from b import g\ndef f(g: Int) -> Int:\n    return g\n",
            "b": "from a import f\ndef g(x: Int) -> Int:\n    return f(x)\n",
        })
        module = project.modules["a"]
        function = module.tree.body[1]
        self.assertNotIn(id(function.body[0].value), module.resolved_symbols)

    def test_cycle_at_default_module_limit_does_not_overflow(self):
        sources = {"m%d" % i: "import m%d\n" % ((i + 1) % 256) for i in range(256)}
        project = self.load(sources, entry="m0")
        self.assertEqual(len(project.compilation_groups), 1)
        self.assertEqual(set(project.compilation_groups[0]), set(sources))

    def test_module_limit_counts_recursive_modules_once(self):
        sources = {"a": "import b\n", "b": "import a\nimport c\n", "c": "import a\n"}
        with self.assertRaisesRegex(ProjectError, "limit of 2"):
            self.load(sources, max_modules=2)
        self.assertEqual(len(self.load(sources, max_modules=3).modules), 3)

    def test_generated_group_namespace_cannot_be_a_source_module(self):
        for name in ("_a2l_groups", "_a2l_groups.Gabc", "_A2L_GROUPS.Gabc"):
            with self.subTest(name=name), self.assertRaisesRegex(ProjectError, "reserved for generated"):
                self.load({"a": "import %s\n" % name, name: ""})

    def test_delayed_reference_resource_error_keeps_dependency_path(self):
        with patch("algo2lean.project._References.visit", side_effect=RecursionError):
            with self.assertRaisesRegex(ProjectError, "resource limit") as raised:
                self.load({"a": "import b\n", "b": ""})
        self.assertEqual(Path(raised.exception.file), self.root / "b.algo")


if __name__ == "__main__":
    unittest.main()
