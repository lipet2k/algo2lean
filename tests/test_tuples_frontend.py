"""Tuple typing preserves arity, reference aliasing, and evaluation boundaries."""

import ast
import tempfile
import textwrap
import unittest

from algo2lean.frontend import CompileError, parse_program
from algo2lean.interfaces import _lean_type, collect_interfaces
from algo2lean.project import ProjectError, Symbol, load_project


def parse(source):
    return parse_program(ast.parse(textwrap.dedent(source)))


NODE = "class Node:\n    value: Int\n"


class TuplesFrontendTests(unittest.TestCase):
    def reject(self, source, message):
        with self.assertRaisesRegex(CompileError, message):
            parse(source)

    def test_mixed_return_and_parameter_arities(self):
        functions, _ = parse('''
            def pair(value: Int, flag: Bool) -> Tuple[Int, Bool]:
                return value, flag
            def first(values: Tuple[Int, Bool]) -> Int:
                return values[0]
            def example() -> Int:
                return first(pair(3, True))
        ''')
        self.assertEqual(functions["pair"].return_type, "Tuple[Int, Bool]")
        self.assertEqual(functions["first"].parameters, [("values", "Tuple[Int, Bool]")])
        result = functions["pair"].node.body[0].value
        self.assertIsInstance(result, ast.Tuple)
        self.assertEqual(functions["pair"].expression_types[id(result)], "Tuple[Int, Bool]")
        self.reject('''
            def first(pair: Tuple[Int, Bool]) -> Int:
                return pair[0]
            def example() -> Int:
                return first(3, True)
        ''', "expects 1 argument")

    def test_empty_singleton_nested_and_grouping(self):
        functions, _ = parse('''
            def empty() -> Tuple[()]:
                return ()
            def singleton() -> Tuple[Int]:
                return (4,)
            def nested() -> Tuple[Tuple[Int], Tuple[()]]:
                return (4,), ()
            def grouped() -> Int:
                return (4)
        ''')
        self.assertEqual(functions["empty"].return_type, "Tuple[()]")
        self.assertEqual(functions["singleton"].return_type, "Tuple[Int]")
        self.assertEqual(functions["nested"].return_type, "Tuple[Tuple[Int], Tuple[()]]")
        self.assertIsInstance(functions["grouped"].node.body[0].value, ast.Constant)
        self.reject("def f() -> Tuple[Int]:\n    return (4)\n", "Expected Tuple")
        self.reject("def f() -> Tuple[()]:\n    return None\n", "Expected Tuple")

    def test_quoted_class_fields_and_sequence_elements(self):
        functions, classes = parse('''
            class Item:
                data: "Tuple[Int, Node | None]"
            class Node:
                value: Int
            def f(item: Item, nodes: Seq[Tuple[Int, Node]]) -> Tuple[Int, Node | None]:
                item.data = nodes[0]
                return item.data
        ''')
        self.assertEqual(classes["Item"].fields["data"], "Tuple[Int, Node?]")
        self.assertEqual(functions["f"].parameters[1][1], "Seq[Tuple[Int, Node]]")
        assignment = functions["f"].node.body[0]
        self.assertEqual(assignment.value.expected_type, "Tuple[Int, Node?]")

    def test_tuple_indices_are_normalized_and_sequences_remain_unbounded(self):
        functions, _ = parse('''
            def f(pair: Tuple[Int, Bool], values: Seq) -> Bool:
                first = pair[-2]
                last = pair[-1]
                again = pair[+0]
                negative = values[-1000]
                return pair[1]
        ''')
        function = functions["f"]
        self.assertEqual([statement.value.tuple_index for statement in function.node.body[:3]], [0, 1, 0])
        self.assertEqual(function.variables["first"], "Int")
        self.assertEqual(function.variables["last"], "Bool")
        self.assertFalse(hasattr(function.node.body[3].value, "tuple_index"))
        for index in ["2", "-3", "1000"]:
            self.reject("def f(p: Tuple[Int, Bool]) -> Int:\n    return p[%s]\n" % index,
                        "out of range")
        for index in ["i", "0 + 0", "True", "0:1"]:
            self.reject("def f(p: Tuple[Int, Bool], i: Int) -> Int:\n    return p[%s]\n" % index,
                        "integer literal")
        self.reject("def f(p: Tuple[()]) -> Int:\n    return p[0]\n", "out of range")

    def test_nested_unpacking_records_destinations_and_keeps_one_rhs(self):
        functions, _ = parse(NODE + '''
def draw(n: Node) -> Tuple[Int, Tuple[Node, Bool]]:
    return randint(0, 10), (n, True)
def use(n: Node) -> Int:
    result: Node | None = None
    value, (result, flag) = draw(n)
    value, other = value + 1, value
    () = ()
    return other
''')
        function = functions["use"]
        assignment = function.node.body[1]
        self.assertIsInstance(assignment.value, ast.Call)
        self.assertEqual(assignment.value.resolved_name, "draw")
        target = assignment.targets[0]
        self.assertEqual(function.expression_types[id(target)], "Tuple[Int, Tuple[Node?, Bool]]")
        self.assertEqual(function.expression_types[id(target.elts[1].elts[0])], "Node?")
        self.assertEqual(function.expression_types[id(assignment.value)], "Tuple[Int, Tuple[Node, Bool]]")
        self.assertFalse(hasattr(assignment.value, "expected_type"))
        self.assertEqual(function.variables["other"], "Int")

    def test_unpacking_errors_are_static_and_specific(self):
        self.reject("def f() -> Int:\n    a, b = (1,)\n    return a\n", "2 target.*1 component")
        self.reject("def f() -> Int:\n    a, b = 1\n    return a\n", "requires a tuple")
        self.reject("def f() -> Int:\n    a, *b = (1, 2, 3)\n    return a\n", "Starred tuple unpacking")
        self.reject("def f(a: Seq) -> Int:\n    a[0], b = (1, 2)\n    return b\n", "targets must be variables")
        self.reject(NODE + "def f(n: Node) -> Int:\n    n.value, b = (1, 2)\n    return b\n", "targets must be variables")
        self.reject("def f() -> Int:\n    a = 1\n    a, b = (True, 2)\n    return b\n", "Expected Int, got Bool")

    def test_literals_apply_nullable_coercions_without_changing_aliases(self):
        functions, _ = parse(NODE + '''
def f(n: Node) -> Tuple[Node | None, Tuple[Node | None]]:
    result: Tuple[Node | None, Tuple[Node | None]] = n, (None,)
    return result
''')
        function = functions["f"]
        value = function.node.body[0].value
        self.assertEqual(function.expression_types[id(value)], "Tuple[Node?, Tuple[Node?]]")
        self.assertEqual(value.elts[0].expected_type, "Node?")
        self.assertEqual(value.elts[1].elts[0].expected_type, "Node?")
        self.assertEqual(function.expression_types[id(value.elts[0])], "Node")

    def test_nonliteral_tuples_preserve_source_type_for_projection_coercion(self):
        functions, _ = parse(NODE + '''
def f(pair: Tuple[Node, Int]) -> Tuple[Node | None, Int]:
    return pair
''')
        function = functions["f"]
        value = function.node.body[0].value
        self.assertEqual(function.expression_types[id(value)], "Tuple[Node, Int]")
        self.assertEqual(value.expected_type, "Tuple[Node?, Int]")

    def test_fresh_sequences_inherit_nullable_tuple_element_context(self):
        functions, _ = parse(NODE + '''
def f(n: Node) -> Seq[Tuple[Node | None, Int]]:
    values: Seq[Tuple[Node | None, Int]] = const((n, 1))
    holder: Tuple[Seq[Node | None], Int] = const(None), 2
    return values
''')
        function = functions["f"]
        allocation = function.node.body[0].value
        self.assertEqual(function.expression_types[id(allocation)], "Seq[Tuple[Node?, Int]]")
        self.assertEqual(function.expression_types[id(allocation.args[0])], "Tuple[Node?, Int]")
        self.assertEqual(allocation.args[0].elts[0].expected_type, "Node?")
        self.assertEqual(function.expression_types[id(function.node.body[1].value.elts[0])], "Seq[Node?]")
        self.reject(NODE + '''
def f(values: Seq[Tuple[Node, Int]]) -> Seq[Tuple[Node | None, Int]]:
    return values
''', "Expected Seq")
        self.reject(NODE + '''
def f(values: Tuple[Seq[Node]]) -> Tuple[Seq[Node | None]]:
    return values
''', "Expected Seq")

    def test_tuple_conditional_joins_nullable_components(self):
        functions, _ = parse(NODE + '''
def f(flag: Bool, n: Node) -> Tuple[Int, Node | None]:
    return (1, n) if flag else (2, None)
''')
        function = functions["f"]
        value = function.node.body[0].value
        self.assertEqual(function.expression_types[id(value)], "Tuple[Int, Node?]")
        self.assertEqual(function.expression_types[id(value.body)], "Tuple[Int, Node?]")
        self.assertEqual(function.expression_types[id(value.orelse)], "Tuple[Int, Node?]")

    def test_comparison_chains_have_one_common_tuple_type(self):
        functions, _ = parse(NODE + '''
def f(a: Tuple[Node], b: Tuple[Node | None], n: Node) -> Bool:
    return a == (n,) != b == (None,)
''')
        function = functions["f"]
        comparison = function.node.body[0].value
        self.assertEqual(comparison.left.expected_type, "Tuple[Node?]")
        self.assertEqual(function.expression_types[id(comparison.comparators[0])], "Tuple[Node?]")
        self.assertEqual(function.expression_types[id(comparison.comparators[2])], "Tuple[Node?]")
        parse("def f() -> Bool:\n    return (1, True) == (2, False)\n")
        parse("def f() -> Bool:\n    return () == ()\n")

    def test_tuple_equality_restrictions_and_mutation_errors(self):
        for operator, message in [("is", "tuple identity"), ("<", "ordering"), (">=", "ordering")]:
            self.reject("def f() -> Bool:\n    return (1, True) %s (2, False)\n" % operator, message)
        self.reject("def f(a: Seq) -> Bool:\n    return (a, 1) == (a, 2)\n", "every component")
        self.reject("def f() -> Bool:\n    return (1,) == (True,)\n", "matching component")
        self.reject("def f() -> Bool:\n    return (1,) == 1\n", "matching component")
        for assignment in ["p[0] = 2", "p[0] += 2"]:
            self.reject("def f(p: Tuple[Int]) -> Int:\n    %s\n    return p[0]\n" % assignment,
                        "Tuple components cannot be assigned")
        self.reject("def f(p: Tuple[Int]) -> Tuple[Int]:\n    return (*p,)\n", "Starred tuple expansion")

    def test_nullable_tuple_annotation_is_rejected(self):
        self.reject("def f(p: Tuple[Int] | None) -> Int:\n    return 0\n", "Only nullable class references")
        self.reject("def f(p: Tuple) -> Int:\n    return 0\n", "type annotation")

    def test_interface_signatures_recurse_through_tuple_annotations(self):
        sources = {
            "nodes": NODE,
            "api": '''from algo2lean import Interface
from nodes import Node as Item
class Factory(Interface):
    def build(self, value: Tuple[Int, Item | None]) -> Tuple[Tuple[Int], Item]: ...
    def empty(self) -> Tuple[()]: ...
''',
        }
        with tempfile.TemporaryDirectory() as directory:
            project = load_project("api", root=directory, sources=sources)
            interface = collect_interfaces(project)[Symbol("api", "Factory", "interface")]
            self.assertEqual(interface.methods["build"].parameters,
                             (("value", "Tuple[Int, nodes.Node?]"),))
            self.assertEqual(interface.methods["build"].return_type,
                             "Tuple[Tuple[Int], nodes.Node]")
            self.assertEqual(interface.methods["empty"].return_type, "Tuple[()]")
            self.assertEqual(_lean_type("Tuple[()]"), "Unit")
            self.assertEqual(_lean_type("Tuple[Tuple[Int], nodes.Node?]"),
                             "((Tuple1 Int) × (Option ObjectRef))")
            sources["api"] = '''from algo2lean import Interface
class Factory(Interface):
    def invalid(self) -> Tuple[()] | None: ...
'''
            with self.assertRaisesRegex(ProjectError, "Only class or interface"):
                collect_interfaces(load_project("api", root=directory, sources=sources))


if __name__ == "__main__":
    unittest.main()
