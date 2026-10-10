"""Class schema, call resolution, and source diagnostics without Lean emission."""

import ast
import textwrap
import unittest

from algo2lean.frontend import CompileError, parse_program


def parse(source):
    return parse_program(ast.parse(textwrap.dedent(source)))


class ClassesFrontendTests(unittest.TestCase):
    def reject(self, source, message):
        with self.assertRaisesRegex(CompileError, message):
            parse(source)

    def test_linked_nodes_and_method_resolution(self):
        functions, classes = parse('''
            class Node:
                key: Int
                next: "Node | None"

                def __init__(self, key: Int, next: Node | None) -> None:
                    self.key = key
                    self.next = next

                def advance(self) -> Node | None:
                    return self.next

                def bump(self, amount: Int) -> None:
                    self.key += amount

            def head_value(n: Node | None) -> Int:
                if n is None:
                    return 0
                n.bump(1)
                return n.key

            def example() -> Node:
                n = Node(2, None)
                n.next = n
                n.next.bump(4)
                return n
        ''')
        self.assertEqual(classes["Node"].fields, {"key": "Int", "next": "Node?"})
        self.assertEqual(classes["Node"].methods["advance"], "Node_advance")
        constructor = functions["Node"]
        self.assertEqual(constructor.parameters, [("key", "Int"), ("next", "Node?")])
        self.assertEqual(constructor.return_type, "Node")
        self.assertEqual(constructor.constructor_for, "Node")
        self.assertFalse(constructor.assigned_at)
        allocation = constructor.node.body[0].value
        self.assertEqual(allocation.allocate_class, "Node")
        call = functions["example"].node.body[2].value
        self.assertEqual(call.resolved_name, "Node_bump")
        self.assertIs(call.receiver, call.func.value)
        self.assertEqual(functions["example"].expression_types[id(call.receiver)], "Node?")
        assigned = functions["example"].node.body[1]
        self.assertEqual(assigned.value.expected_type, "Node?")

    def test_mutually_recursive_classes_and_quoted_annotations(self):
        functions, classes = parse('''
            class Tree:
                owner: "Forest"
                left: None | Tree
            class Forest:
                root: "Tree | None"
            def root(f: "Forest") -> "Tree | None":
                return f.root
        ''')
        self.assertEqual(classes["Tree"].fields, {"owner": "Forest", "left": "Tree?"})
        self.assertEqual(functions["Forest"].parameters, [])
        self.assertEqual(len(functions["Forest"].node.body), 2)

    def test_fields_declared_inside_initializer_and_nested_sequence_targets(self):
        functions, classes = parse('''
            class Buffer:
                def __init__(self, n: Int) -> None:
                    self.values: Seq = const(n)
                    self.child: Buffer | None = None
                def set(self, i: Int, n: Int) -> None:
                    self.values[i] = n
                    self.child.values[i] = n + 1
                    self.child = self
        ''')
        self.assertEqual(classes["Buffer"].fields, {"values": "Seq", "child": "Buffer?"})
        setter = functions["Buffer_set"]
        target = setter.node.body[1].targets[0]
        self.assertEqual(setter.expression_types[id(target.value)], "Seq")
        self.assertEqual(setter.expression_types[id(target.value.value)], "Buffer?")

    def test_none_returns_and_fallthrough_are_normalized(self):
        functions, _ = parse('''
            def early(b: Bool) -> None:
                if b:
                    return
                pass
            def forever() -> None:
                while True:
                    pass
        ''')
        early = functions["early"]
        self.assertIsNone(early.node.body[0].body[0].value.value)
        self.assertIsNone(early.node.body[-1].value.value)
        self.assertNotIn(id(early.node.body[-1]), early.assigned_at)
        self.assertEqual(len(functions["forever"].node.body), 1)

    def test_nullable_assignments_preserve_declared_type(self):
        functions, _ = parse('''
            class Node:
                pass
            def f(n: Node, flag: Bool) -> Node | None:
                cursor: Node | None = None
                cursor = n
                cursor = None
                other = n if flag else None
                return other
        ''')
        function = functions["f"]
        self.assertEqual(function.variables["cursor"], "Node?")
        self.assertEqual(function.variables["other"], "Node?")
        choice = function.node.body[3].value
        self.assertEqual(choice.body.expected_type, "Node?")
        self.assertEqual(choice.orelse.expected_type, "Node?")

    def test_reference_equality_including_nullable_refs(self):
        functions, _ = parse('''
            class Node:
                pass
            def same(a: Node, b: Node | None) -> Bool:
                return (a == b) or (None is b) or (a is not None) or (b != None)
        ''')
        self.assertEqual(functions["same"].return_type, "Bool")

    def test_rejects_dynamic_features_and_invalid_schemas(self):
        cases = [
            ("class Node(object):\n    pass", "inheritance"),
            ("class Node:\n    key: Int = 1", "without values"),
            ("class Node:\n    key: Int\n    key: Bool", "conflicting field"),
            ("class Node:\n    def __init__(self) -> Int:\n        return 1", "must return None"),
            ("class Node:\n    def f(x: Int) -> Int:\n        return x", "first parameter"),
            ("class Node:\n    def f(self: Int) -> Int:\n        return 1", "self must have type"),
            ("class Node:\n    def f(self) -> Int:\n        return 1\n    f: Int", "conflicts with a method"),
            ("class Node:\n    def __eq__(self, x: Node) -> Bool:\n        return True", "special method"),
            ("class Node:\n    key: Int | None", "nullable class"),
            ("class Node:\n    key: Missing", "type annotation"),
            ("class Node:\n    def f(self) -> Int:\n        return self.unknown", "no declared field"),
            ("class Node:\n    def f(self) -> None:\n        self.unknown = 1", "no declared field"),
            ("class Node:\n    def f(self) -> None:\n        self.key: Int = 1", "self.field declaration"),
            ("class Node:\n    pass\ndef f(n: Node) -> None:\n    n.unknown()", "no method"),
            ("class Node:\n    def f(self) -> Int:\n        return 1\ndef Node_f() -> Int:\n    return 0", "conflicts with another"),
            ("class A:\n    pass\nclass B:\n    pass\ndef f(a: A, b: B) -> Bool:\n    return a == b", "different classes"),
            ("def f(a: Int) -> Bool:\n    return a is 1", "class references"),
            ("def f() -> Int:\n    return None", "Expected Int"),
        ]
        for source, message in cases:
            with self.subTest(source=source):
                self.reject(source, message)

    def test_unreachable_bodies_are_still_checked(self):
        self.reject('''
            def f() -> None:
                return
                import os
        ''', "Unsupported statement")

    def test_constructor_local_avoids_user_names(self):
        functions, _ = parse('''
            def _instance() -> Int:
                return 1
            class Box:
                value: Int
                def __init__(self, _instance_: Int) -> None:
                    self.value = _instance_
        ''')
        self.assertEqual(functions["Box"].node.body[0].targets[0].id, "_instance__")

    def test_matching_field_declarations_do_not_depend_on_member_order(self):
        _, classes = parse('''
            class Box:
                def __init__(self, n: Int) -> None:
                    self.value: Int = n
                value: Int
        ''')
        self.assertEqual(classes["Box"].fields, {"value": "Int"})


if __name__ == "__main__":
    unittest.main()
