"""Composite types retain class identity across compiler and import boundaries."""

import unittest

from algo2lean.emitter import object_type
from algo2lean import CompileError, compile_source
from algo2lean.frontend import ClassInfo
from algo2lean.interfaces import canonical_type, _replace_self
from algo2lean.objects import type_tag
from algo2lean.project import Symbol
from algo2lean.recursive_modules import _translate_type


class TypeTraversalTests(unittest.TestCase):
    def test_future_builtin_names_have_source_diagnostics(self):
        for name in ("Real", "Tuple", "Set", "Dict"):
            with self.subTest(name=name), self.assertRaisesRegex(CompileError, "reserved"):
                compile_source("class %s:\n    value: Int\n" % name)

    def test_import_aliases_traverse_all_type_arguments(self):
        typ = "Tuple[Seq[Node?], Dict[Tuple[Int, Node], Set[Node]]]"
        origins = {"Node": Symbol("graph", "Vertex", "class")}
        self.assertEqual(canonical_type(typ, origins),
                         "Tuple[Seq[graph.Vertex?], Dict[Tuple[Int, graph.Vertex], Set[graph.Vertex]]]")

    def test_interface_self_and_recursive_facades_share_traversal(self):
        typ = "Dict[Tuple[Int, Self?], Seq[Tuple[Bool, Self]]]"
        expected = "Dict[Tuple[Int, Node?], Seq[Tuple[Bool, Node]]]"
        self.assertEqual(_replace_self(typ, "Self", "Node"), expected)
        self.assertEqual(_translate_type(typ, {"Self": "Node"}), expected)

    def test_pure_values_do_not_acquire_heap_inputs(self):
        for typ in ("Int", "Bool", "None", "Real", "Tuple[()]",
                    "Tuple[Int, Tuple[Bool, Real]]", "Seq"):
            with self.subTest(typ=typ):
                self.assertFalse(object_type(typ))
        for typ in ("Node", "Node?", "Tuple[Seq, Int]", "Tuple[Node?]",
                    "Seq[Bool]", "Set[Int]", "Dict[Int, Real]"):
            with self.subTest(typ=typ):
                self.assertTrue(object_type(typ))

    def test_runtime_tags_use_canonical_class_identity(self):
        classes = {"Node": ClassInfo("Node", runtime_tag="graph.Vertex")}
        self.assertEqual(type_tag("Seq[Seq[Node?]]", classes),
                         "Seq[Seq[graph.Vertex?]]")
        self.assertEqual(type_tag("Seq", classes), "Seq[Int]")
        self.assertEqual(type_tag("Tuple[Dict[Int, Node], Set[Node?]]", classes),
                         "Tuple[Dict[Int, graph.Vertex], Set[graph.Vertex?]]")


if __name__ == "__main__":
    unittest.main()
