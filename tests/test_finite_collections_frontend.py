"""Finite collection syntax, invariant types, and contextual empty literals."""

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


class FiniteCollectionsFrontendTests(unittest.TestCase):
    def reject(self, source, message):
        with self.assertRaisesRegex(CompileError, message):
            parse(source)

    def test_frequency_counter_uses_dictionary_operations(self):
        functions, _ = parse('''
            def count(values: Seq, n: Int) -> Dict[Int, Int]:
                counts: Dict[Int, Int] = {}
                for i in range(n):
                    value = values[i]
                    counts[value] = counts.get(value, 0) + 1
                return counts
        ''')
        function = functions["count"]
        self.assertEqual(function.return_type, "Dict[Int, Int]")
        empty = function.node.body[0].value
        self.assertEqual(function.expression_types[id(empty)], "Dict[Int, Int]")
        write = function.node.body[1].body[1]
        self.assertEqual(function.expression_types[id(write.targets[0])], "Int")
        self.assertEqual(write.value.left.collection_operation, "dict_get")
        self.assertIs(write.value.left.receiver, write.value.left.func.value)

    def test_visited_set_operations_and_result_types(self):
        functions, _ = parse('''
            def visit(v: Int) -> Tuple[Bool, Int]:
                seen: Set[Int] = set()
                added = seen.add(v)
                before = v in seen
                seen.discard(v)
                after = v not in seen
                return before and after, len(seen)
        ''')
        function = functions["visit"]
        self.assertEqual(function.variables["seen"], "Set[Int]")
        self.assertEqual(function.variables["added"], "None")
        self.assertEqual(function.node.body[1].value.collection_operation, "set_add")
        self.assertEqual(function.node.body[3].value.collection_operation, "set_discard")
        self.assertEqual(function.node.body[-1].value.elts[1].collection_operation, "length")

    def test_nonempty_literals_infer_types_and_keep_duplicates(self):
        functions, _ = parse('''
            def make() -> Tuple[Set[Int], Dict[Int, Bool]]:
                values = {1, 1, 2}
                flags = {1: True, 1: False, 2: True}
                return values, flags
        ''')
        function = functions["make"]
        self.assertEqual(function.variables["values"], "Set[Int]")
        self.assertEqual(function.variables["flags"], "Dict[Int, Bool]")
        self.assertEqual(len(function.node.body[0].value.elts), 3)
        self.assertEqual([key.value for key in function.node.body[1].value.keys], [1, 1, 2])
        self.assertEqual([value.value for value in function.node.body[1].value.values], [True, False, True])

    def test_dictionary_pairs_preserve_effectful_source_order(self):
        functions, _ = parse('''
            def sample() -> Dict[Int, Int]:
                return {randint(0, 10): randint(10, 20), randint(20, 30): randint(30, 40)}
        ''')
        value = functions["sample"].node.body[0].value
        self.assertEqual([(key.args[0].value, item.args[0].value)
                          for key, item in zip(value.keys, value.values)], [(0, 10), (20, 30)])
        self.assertTrue(all(isinstance(node, ast.Call) for node in [*value.keys, *value.values]))

    def test_typed_empties_in_returns_arguments_and_nested_literals(self):
        functions, _ = parse('''
            def accept(data: Dict[Int, Set[Int]]) -> Int:
                return len(data)
            def empty() -> Tuple[Set[Int], Dict[Int, Bool]]:
                return set(), {}
            def make() -> Int:
                nested: Dict[Int, Tuple[Dict[Int, Bool], Set[Int]]] = {0: ({}, set())}
                sequences: Seq[Dict[Int, Bool]] = const({})
                return accept({0: set()})
        ''')
        function = functions["empty"]
        value = function.node.body[0].value
        self.assertEqual(function.expression_types[id(value.elts[0])], "Set[Int]")
        self.assertEqual(function.expression_types[id(value.elts[1])], "Dict[Int, Bool]")
        make = functions["make"]
        self.assertEqual(make.variables["sequences"], "Seq[Dict[Int, Bool]]")
        argument = make.node.body[-1].value.args[0]
        self.assertEqual(make.expression_types[id(argument)], "Dict[Int, Set[Int]]")

    def test_existing_destinations_supply_context_for_empty_writes(self):
        functions, _ = parse('''
            class State:
                counts: Dict[Int, Int]
            def clear(state: State, nested: Dict[Int, Dict[Int, Int]]) -> Int:
                counts: Dict[Int, Int] = {0: 1}
                count = 1
                counts = {}
                state.counts = {}
                nested[0] = {}
                counts, count = ({}, 2)
                return count
        ''')
        function = functions["clear"]
        for statement in function.node.body[2:5]:
            self.assertEqual(function.expression_types[id(statement.value)], "Dict[Int, Int]")
        self.assertEqual(function.expression_types[id(function.node.body[5].value)],
                         "Tuple[Dict[Int, Int], Int]")

    def test_empty_conditional_branches_use_expected_type(self):
        functions, _ = parse('''
            def choose(flag: Bool) -> Dict[Int, Int]:
                return {} if flag else {1: 2}
        ''')
        function = functions["choose"]
        expression = function.node.body[0].value
        self.assertEqual(function.expression_types[id(expression.body)], "Dict[Int, Int]")
        self.assertEqual(function.expression_types[id(expression.orelse)], "Dict[Int, Int]")

    def test_untyped_empty_constructors_are_rejected(self):
        for expression, message in [("{}", "empty dictionary needs"), ("set()", "empty set needs")]:
            self.reject("def f() -> Int:\n    value = %s\n    return 0\n" % expression, message)
        self.reject("def f() -> Set[Int]:\n    return set(1)\n", "takes no arguments")
        self.reject("def f() -> Dict[Int, Int]:\n    return dict()\n", "Unknown function")

    def test_nullable_literal_keys_and_values_adopt_context(self):
        functions, _ = parse(NODE + '''
def make(n: Node) -> Dict[Node | None, Tuple[Node | None, Int]]:
    values: Set[Node | None] = {None, n}
    return {None: (n, 1), n: (None, 2)}
''')
        function = functions["make"]
        self.assertEqual(function.variables["values"], "Set[Node?]")
        returned = function.node.body[-1].value
        self.assertEqual(returned.keys[1].expected_type, "Node?")
        self.assertEqual(function.expression_types[id(returned.values[0])], "Tuple[Node?, Int]")
        self.assertEqual(returned.values[0].elts[0].expected_type, "Node?")

    def test_homogeneous_literals_join_nullable_references(self):
        functions, _ = parse(NODE + '''
def make(n: Node) -> Int:
    values = {n, None}
    mapping = {None: n, n: None}
    return len(values) + len(mapping)
''')
        self.assertEqual(functions["make"].variables["values"], "Set[Node?]")
        self.assertEqual(functions["make"].variables["mapping"], "Dict[Node?, Node?]")
        self.reject("def f() -> Int:\n    s = {True, 1}\n    return 0\n", "compatible types")
        self.reject("def f() -> Int:\n    d = {1: True, 2: 3}\n    return 0\n", "compatible types")

    def test_existing_mutable_aliases_cannot_be_widened(self):
        self.reject(NODE + '''
def invalid(values: Set[Node]) -> Set[Node | None]:
    return values
''', "Expected Set")
        self.reject(NODE + '''
def invalid(values: Dict[Int, Node]) -> Dict[Int, Node | None]:
    return values
''', "Expected Dict")
        self.reject(NODE + '''
def invalid(values: Dict[Int, Node]) -> Dict[Int, Node | None]:
    return copy(values)
''', "Expected Dict")

    def test_keys_include_nested_tuples_and_object_identities(self):
        functions, _ = parse(NODE + '''
def find(n: Node, data: Dict[Tuple[Int, Node], Seq]) -> Bool:
    keys: Set[Tuple[Int, Node | None]] = {(1, n), (2, None)}
    return (1, n) in keys and (1, n) in data
''')
        function = functions["find"]
        membership = function.node.body[-1].value.values[0]
        self.assertEqual(function.expression_types[id(membership.left)], "Tuple[Int, Node?]")
        parse("def f() -> Set[None]:\n    return {None}\n")
        parse("def f() -> Dict[Tuple[()], None]:\n    return {(): None}\n")

    def test_mutable_container_keys_are_rejected_even_when_nested(self):
        for typ in ["Seq", "Set[Int]", "Dict[Int, Bool]", "Tuple[Int, Seq]"]:
            self.reject("def f(s: Set[%s]) -> Int:\n    return 0\n" % typ,
                        "dictionary keys must")
            self.reject("def f(d: Dict[%s, Int]) -> Int:\n    return 0\n" % typ,
                        "dictionary keys must")
        self.reject("def f(a: Seq) -> Int:\n    s = {a}\n    return 0\n", "dictionary keys must")

    def test_get_requires_a_typed_explicit_default_and_keeps_its_expression(self):
        functions, _ = parse('''
            def fallback() -> Int:
                return randint(0, 10)
            def get(d: Dict[Int, Int]) -> Int:
                return d.get(1, fallback())
        ''')
        expression = functions["get"].node.body[0].value
        self.assertEqual(expression.collection_operation, "dict_get")
        self.assertIsInstance(expression.args[1], ast.Call)
        self.assertEqual(expression.args[1].resolved_name, "fallback")
        self.reject("def f(d: Dict[Int, Int]) -> Int:\n    return d.get(1)\n", "expects 2 argument")
        self.reject("def f(d: Dict[Int, Int]) -> Int:\n    return d.get(1, None)\n", "Expected Int")

    def test_lookup_none_values_and_delete_metadata(self):
        functions, _ = parse('''
            def clear(d: Dict[Int, None], k: Int) -> None:
                value = d[k]
                del d[k]
                return value
        ''')
        function = functions["clear"]
        self.assertEqual(function.variables["value"], "None")
        deletion = function.node.body[1]
        self.assertIsInstance(deletion, ast.Delete)
        self.assertEqual(function.expression_types[id(deletion.targets[0])], "None")
        self.reject("def f(s: Set[Int]) -> None:\n    del s[0]\n", "dictionary entries only")
        self.reject("def f(d: Dict[Int, Int]) -> None:\n    del d\n", "single dictionary entry")
        self.reject("def f(d: Dict[Int, Int]) -> None:\n    del d[0], d[1]\n", "single dictionary entry")

    def test_copy_preserves_exact_types_and_sequence_copy_path(self):
        functions, _ = parse('''
            def clone(a: Seq, s: Set[Int], d: Dict[Int, Seq]) -> Dict[Int, Seq]:
                sequence = copy(a)
                seen = copy(s)
                data = copy(d)
                return data
        ''')
        function = functions["clone"]
        self.assertFalse(hasattr(function.node.body[0].value, "collection_operation"))
        self.assertEqual(function.node.body[1].value.collection_operation, "copy")
        self.assertEqual(function.node.body[2].value.collection_operation, "copy")
        self.assertEqual(function.variables["data"], "Dict[Int, Seq]")

    def test_unsupported_equality_methods_and_membership_chains_are_clear(self):
        for operator in ["==", "!=", "is", "is not"]:
            self.reject("def f(s: Set[Int]) -> Bool:\n    return s %s s\n" % operator,
                        "equality and identity")
        self.reject("def f(s: Set[Int]) -> Bool:\n    return 1 in s == True\n", "Chained membership")
        self.reject("def f(a: Seq) -> Bool:\n    return 1 in a\n", "finite set or dictionary")
        self.reject("def f(s: Set[Int]) -> Int:\n    return s[0]\n", "Sets do not support indexing")
        self.reject("def f(s: Set[Int]) -> None:\n    s[0] = 1\n", "indexed assignment")
        self.reject("def f(s: Set[Int]) -> None:\n    s.remove(1)\n", "Unsupported Set method")
        self.reject("def f(a: Seq) -> Int:\n    return len(a)\n", "every integer index")

    def test_annotation_arity_expansion_and_comprehensions_are_rejected(self):
        self.reject("def f(s: Set[Int, Bool]) -> Int:\n    return 0\n", "expects 1 type argument")
        self.reject("def f(s: Dict[Int]) -> Int:\n    return 0\n", "expects 2 type argument")
        self.reject("def f(s: Set[Int]) -> Set[Int]:\n    return {*s}\n", "Starred set expansion")
        self.reject("def f(d: Dict[Int, Int]) -> Dict[Int, Int]:\n    return {**d}\n", "Expanded dictionary")
        self.reject("def f() -> Set[Int]:\n    return {x for x in range(3)}\n", "Unsupported expression")

    def test_abstract_signatures_use_collection_refs_and_reject_abstract_keys(self):
        sources = {"api": '''from algo2lean import Interface
class Table(Interface):
    def keys(self) -> Set[Tuple[Int, Bool]]: ...
    def counts(self, d: Dict[Int, Int]) -> Dict[Int, Int]: ...
'''}
        with tempfile.TemporaryDirectory() as directory:
            project = load_project("api", root=directory, sources=sources)
            interface = collect_interfaces(project)[Symbol("api", "Table", "interface")]
            self.assertEqual(interface.methods["keys"].return_type, "Set[Tuple[Int, Bool]]")
            self.assertEqual(_lean_type(interface.methods["keys"].return_type), "CollectionRef")
            self.assertEqual(_lean_type("Dict[Int, Int]"), "CollectionRef")
            sources["api"] = '''from algo2lean import Interface
class Key(Interface):
    def read(self) -> Int: ...
class Table(Interface):
    def counts(self) -> Dict[Tuple[Key], Int]: ...
'''
            with self.assertRaisesRegex(ProjectError, "Abstract interface references"):
                collect_interfaces(load_project("api", root=directory, sources=sources))

    def test_collection_iteration_records_snapshot_source_and_key_type(self):
        functions, _ = parse('''
            def total(values: Set[Int], data: Dict[Tuple[Int, Bool], Int]) -> Int:
                count = 0
                for value in values:
                    values.discard(value)
                    count += value
                for key in data:
                    count += key[0]
                    data[key] = count
                return count
        ''')
        function = functions["total"]
        first, second = function.node.body[1:3]
        self.assertEqual(first.collection_iteration, "Set[Int]")
        self.assertEqual(second.collection_iteration, "Dict[Tuple[Int, Bool], Int]")
        self.assertEqual(function.expression_types[id(first.target)], "Int")
        self.assertEqual(function.expression_types[id(second.target)], "Tuple[Int, Bool]")

    def test_collection_iteration_keeps_effectful_iterable_once(self):
        functions, _ = parse('''
            def make() -> Set[Int]:
                return {randint(0, 10)}
            def count() -> Int:
                result = 0
                for value in make():
                    result += 1
                return result
        ''')
        loop = functions["count"].node.body[1]
        self.assertIsInstance(loop.iter, ast.Call)
        self.assertEqual(loop.iter.resolved_name, "make")
        self.assertEqual(loop.collection_iteration, "Set[Int]")

    def test_collection_loop_target_coercion_and_zero_iteration_assignment(self):
        functions, _ = parse(NODE + '''
def last(values: Set[Node]) -> Node | None:
    value: Node | None = None
    for value in values:
        pass
    return value
''')
        function = functions["last"]
        loop = function.node.body[1]
        self.assertEqual(loop.collection_iteration, "Set[Node]")
        self.assertEqual(function.expression_types[id(loop.target)], "Node?")
        self.assertEqual(loop.target.expected_type, "Node?")
        self.reject("def f(s: Set[Int]) -> Int:\n    for x in s:\n        pass\n    return x\n", "may be unassigned")
        self.reject("def f(d: Dict[Int, Bool]) -> Int:\n    for key in d:\n        value = 1\n    return value\n", "may be unassigned")

    def test_collection_iteration_rejects_unpacking_else_and_nonfinite_sources(self):
        self.reject("def f(s: Set[Tuple[Int, Bool]]) -> None:\n    for x, flag in s:\n        pass\n", "unpacking loop targets")
        self.reject("def f(s: Set[Int]) -> None:\n    for x in s:\n        pass\n    else:\n        pass\n", "for ... else")
        self.reject("def f(s: Seq) -> None:\n    for x in s:\n        pass\n", "finite set")
        functions, _ = parse("def f(n: Int) -> None:\n    for x in range(n):\n        pass\n")
        self.assertFalse(hasattr(functions["f"].node.body[0], "collection_iteration"))


if __name__ == "__main__":
    unittest.main()
