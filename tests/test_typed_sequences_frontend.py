"""Element typing and alias safety for typed mutable sequences."""

import ast
import textwrap
import unittest

from algo2lean.frontend import CompileError, parse_program
from algo2lean.source_types import (
    collection_element, is_collection, is_sequence, sequence_element, sequence_type,
)


def parse(source):
    return parse_program(ast.parse(textwrap.dedent(source)))


NODE = "class Node:\n    value: Int\n"


class TypedSequencesFrontendTests(unittest.TestCase):
    def reject(self, source, message):
        with self.assertRaisesRegex(CompileError, message):
            parse(source)

    def test_canonical_types_and_integer_compatibility(self):
        functions, _ = parse('''
            def f(a: Seq[Int], b: Seq) -> Seq[Int]:
                result: Seq[Int] = const(0)
                result[-1] = a[-2] + b[-3]
                return result
        ''')
        function = functions["f"]
        self.assertEqual(function.parameters, [("a", "Seq"), ("b", "Seq")])
        self.assertEqual(function.return_type, "Seq")
        self.assertEqual(function.variables["result"], "Seq")
        self.assertEqual(sequence_type("Int"), "Seq")
        self.assertEqual(sequence_element("Seq"), "Int")
        self.assertEqual(sequence_element("Seq[Seq[Node?]]"), "Seq[Node?]")
        self.assertTrue(is_sequence("Seq"))
        self.assertFalse(is_collection("Seq"))
        self.assertTrue(is_collection("Seq[Bool]"))
        self.assertEqual(collection_element("Seq[Node]"), "Node")
        self.assertIsNone(collection_element("Seq"))
        self.assertIsNone(sequence_element("Node"))

    def test_object_elements_support_fields_methods_and_assignment(self):
        functions, _ = parse('''
            class Node:
                value: Int
                def set(self, value: Int) -> None:
                    self.value = value
            def f(nodes: Seq[Node], node: Node) -> Node:
                nodes[-1] = node
                nodes[-1].set(4)
                nodes[-2].value = nodes[-1].value
                return nodes[-1]
        ''')
        function = functions["f"]
        self.assertEqual(function.parameters[0], ("nodes", "Seq[Node]"))
        assignment, call, field_assignment, returned = function.node.body
        self.assertEqual(function.expression_types[id(assignment.targets[0])], "Node")
        self.assertEqual(call.value.resolved_name, "Node_set")
        self.assertEqual(function.expression_types[id(call.value.receiver)], "Node")
        self.assertEqual(field_assignment.targets[0].class_name, "Node")
        self.assertEqual(function.expression_types[id(returned.value)], "Node")

    def test_forward_quoted_and_nested_field_annotations(self):
        functions, classes = parse('''
            class Graph:
                vertices: "Seq[Node]"
                edges: Seq[Seq[Node | None]]
                visited: Seq[Bool]
                weights: Seq[Seq[Int]]
                def __init__(self) -> None:
                    self.edges = const(const(None))
                    self.visited = const(False)
                    self.weights = const(const(0))
            class Node:
                graph: Graph
            def vertex(g: Graph, i: Int) -> Node:
                return g.vertices[i]
        ''')
        self.assertEqual(classes["Graph"].fields, {
            "vertices": "Seq[Node]", "edges": "Seq[Seq[Node?]]",
            "visited": "Seq[Bool]", "weights": "Seq[Seq]",
        })
        initializer = functions["Graph___init__"]
        outer = initializer.node.body[0].value
        self.assertEqual(initializer.expression_types[id(outer)], "Seq[Seq[Node?]]")
        self.assertEqual(initializer.expression_types[id(outer.args[0])], "Seq[Node?]")
        self.assertEqual(outer.args[0].args[0].expected_type, "Node?")

    def test_const_inference_copy_and_update_preserve_element_types(self):
        functions, _ = parse(NODE + '''
def f(node: Node, rows: Seq[Seq[Node]]) -> Seq[Node]:
    nodes = const(node)
    copied = copy(nodes)
    changed = update(copied, -10, node)
    flags = const(True)
    empty = const(None)
    rows[0] = nodes
    return changed
''')
        function = functions["f"]
        self.assertEqual(function.variables["nodes"], "Seq[Node]")
        self.assertEqual(function.variables["copied"], "Seq[Node]")
        self.assertEqual(function.variables["changed"], "Seq[Node]")
        self.assertEqual(function.variables["flags"], "Seq[Bool]")
        self.assertEqual(function.variables["empty"], "Seq[None]")

    def test_fresh_const_adapts_in_all_expected_contexts(self):
        functions, _ = parse(NODE + '''
class Holder:
    nodes: Seq[Node | None]
    def __init__(self, node: Node) -> None:
        self.nodes = const(node)
def accept(nodes: Seq[Node | None]) -> None:
    pass
def f(node: Node, rows: Seq[Seq[Node | None]]) -> Seq[Node | None]:
    nodes: Seq[Node | None] = const(None)
    nodes = const(node)
    accept(const(node))
    rows[0] = const(node)
    update(rows, 1, const(None))
    nodes[-1] = None
    nodes[2] = node
    return const(node)
''')
        function = functions["f"]
        calls = [function.node.body[0].value, function.node.body[1].value,
                 function.node.body[2].value.args[0], function.node.body[3].value,
                 function.node.body[4].value.args[2], function.node.body[-1].value]
        for call in calls:
            self.assertEqual(function.expression_types[id(call)], "Seq[Node?]")
            self.assertEqual(call.args[0].expected_type, "Node?")
        initializer = functions["Holder___init__"]
        self.assertEqual(initializer.node.body[0].value.args[0].expected_type, "Node?")

    def test_nested_element_access_and_boolean_values(self):
        functions, _ = parse('''
            def f(rows: Seq[Seq[Bool]], i: Int, j: Int) -> Bool:
                rows[i][j] = True
                copied = copy(rows[i])
                return copied[j] and rows[i][j]
        ''')
        function = functions["f"]
        target = function.node.body[0].targets[0]
        self.assertEqual(function.expression_types[id(target.value)], "Seq[Bool]")
        self.assertEqual(function.expression_types[id(target)], "Bool")
        self.assertEqual(function.variables["copied"], "Seq[Bool]")

    def test_mutable_sequence_aliases_cannot_widen(self):
        cases = [
            "def f(a: Seq[Node]) -> Seq[Node | None]:\n    return a\n",
            "def f(a: Seq[Node]) -> None:\n    b: Seq[Node | None] = a\n",
            "def f(a: Seq[Node], b: Seq[Node | None]) -> None:\n    b = a\n",
            "def f(a: Seq[Seq[Node]]) -> Seq[Seq[Node | None]]:\n    return a\n",
            "def f(a: Seq[Node]) -> Seq[Seq[Node | None]]:\n    return const(a)\n",
            "def f(a: Seq[Node]) -> Seq[Node | None]:\n    return copy(a)\n",
            "def accept(a: Seq[Node | None]) -> None:\n    pass\ndef f(a: Seq[Node]) -> None:\n    accept(a)\n",
        ]
        for source in cases:
            with self.subTest(source=source):
                self.reject(NODE + source, "Expected Seq")

    def test_rejects_mismatched_elements_indices_and_non_sequences(self):
        cases = [
            ("def f(a: Seq[Node]) -> None:\n    a[0] = None\n", "Expected Node"),
            ("def f(a: Seq[Node]) -> None:\n    update(a, 0, 1)\n", "Expected Node"),
            ("def f(a: Seq[Bool]) -> None:\n    a[0] = 1\n", "Expected Bool"),
            ("def f(a: Seq[Node]) -> Node:\n    return a[True]\n", "Expected Int"),
            ("def f(a: Node) -> Int:\n    return a[0]\n", "Expected a sequence"),
            ("def f(a: Node) -> Node:\n    return copy(a)\n", "Expected a sequence"),
            ("def f(a: Seq[Node]) -> Seq[Node]:\n    return const(None)\n", "Expected Node"),
        ]
        for source, message in cases:
            with self.subTest(source=source):
                self.reject(NODE + source, message)

    def test_all_sequence_comparisons_are_rejected(self):
        for typ in ("Seq", "Seq[Node]", "Seq[Bool]", "Seq[Seq[Node | None]]"):
            for op in ("==", "!=", "is", "is not"):
                with self.subTest(typ=typ, op=op):
                    self.reject(NODE + "def f(a: %s, b: %s) -> Bool:\n    return a %s b\n" %
                                (typ, typ, op), "Sequence equality")

    def test_collection_annotations_do_not_enable_other_generics(self):
        for typ in ("Set[Node]", "Dict[Int, Node]", "Seq[Missing]", "Seq[Node, Int]", "Seq[Int | None]"):
            with self.subTest(typ=typ):
                self.reject(NODE + "def f(a: %s) -> None:\n    pass\n" % typ,
                            "type annotation|nullable class")


if __name__ == "__main__":
    unittest.main()
