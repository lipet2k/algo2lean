"""Exact reals use explicit scalar coercions and preserve mutable alias types."""

import ast
import tempfile
import textwrap
import unittest

from algo2lean.frontend import CompileError, parse_program
from algo2lean.interfaces import _lean_type, collect_interfaces
from algo2lean.project import ProjectError, Symbol, load_project
from algo2lean.source_validation import parse_source


def parse(source):
    return parse_program(parse_source(textwrap.dedent(source)))


def effective_type(function, node):
    return getattr(node, "expected_type", function.expression_types[id(node)])


class RealsFrontendTests(unittest.TestCase):
    def reject(self, source, message):
        with self.assertRaisesRegex(CompileError, message):
            parse(source)

    def test_annotations_fields_parameters_and_exact_literals(self):
        functions, classes = parse('''
            class Point:
                x: Real
                coordinates: "Tuple[Real, Real]"
            def value(p: Point, x: Real) -> Real:
                p.x = 0.1
                answer: Real = 7
                return answer + x
        ''')
        function = functions["value"]
        self.assertEqual(classes["Point"].fields, {"x": "Real", "coordinates": "Tuple[Real, Real]"})
        self.assertEqual(function.parameters, [("p", "Point"), ("x", "Real")])
        self.assertEqual(function.return_type, "Real")
        self.assertEqual(function.node.body[0].value.exact_ratio, (1, 10))
        integer = function.node.body[1].value
        self.assertEqual(function.expression_types[id(integer)], "Int")
        self.assertEqual(integer.expected_type, "Real")

    def test_int_arithmetic_stays_int_and_mixed_arithmetic_promotes_operands(self):
        functions, _ = parse('''
            def compute(n: Int, x: Real) -> Real:
                integer = (n + 2) * (n - 1)
                mixed = n + x
                negative = -x
                positive = +x
                return mixed * negative - positive
        ''')
        function = functions["compute"]
        self.assertEqual(function.variables["integer"], "Int")
        self.assertEqual(function.variables["mixed"], "Real")
        mixed = function.node.body[1].value
        self.assertEqual(mixed.left.expected_type, "Real")
        self.assertEqual(function.expression_types[id(mixed.left)], "Int")
        self.assertEqual(function.variables["negative"], "Real")
        self.assertEqual(function.variables["positive"], "Real")
        self.assertFalse(hasattr(function.node.body[0].value, "expected_type"))

    def test_division_always_returns_real_and_leaves_zero_check_to_execution(self):
        functions, _ = parse('''
            def fraction(n: Int, d: Int) -> Real:
                half = 1 / 2
                undefined = n / 0
                return half + n / d
        ''')
        function = functions["fraction"]
        half = function.node.body[0].value
        self.assertEqual(function.expression_types[id(half)], "Real")
        self.assertEqual(half.left.expected_type, "Real")
        self.assertEqual(half.right.expected_type, "Real")
        self.assertEqual(function.variables["undefined"], "Real")
        self.reject("def f() -> Int:\n    return 1 / 2\n", "Expected Int, got Real")

    def test_real_conversion_marks_one_existing_argument(self):
        functions, _ = parse('''
            def sample() -> Real:
                value = Real(randint(0, 2))
                return Real(value)
        ''')
        function = functions["sample"]
        conversion = function.node.body[0].value
        self.assertTrue(conversion.real_conversion)
        self.assertEqual(conversion.args[0].func.id, "randint")
        self.assertEqual(conversion.args[0].expected_type, "Real")
        self.assertEqual(function.expression_types[id(conversion.args[0])], "Int")
        self.assertEqual(sum(isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "randint"
                             for node in ast.walk(function.node)), 1)
        for expression in ("Real()", "Real(1, 2)"):
            self.reject("def f() -> Real:\n    return %s\n" % expression, "one Int or Real argument")
        self.reject("def f() -> Real:\n    return Real(True)\n", "Expected Real, got Bool")
        self.reject("def f() -> Real:\n    return Real(None)\n", "Expected Real, got None")

    def test_numeric_chains_coerce_all_operands_and_preserve_middle_call(self):
        functions, _ = parse('''
            def probe(n: Int) -> Int:
                return n
            def within(n: Int) -> Bool:
                return 0 < probe(n) <= 1.5 != 3
        ''')
        function = functions["within"]
        comparison = function.node.body[0].value
        operands = [comparison.left, *comparison.comparators]
        self.assertEqual([effective_type(function, operand) for operand in operands], ["Real"] * 4)
        self.assertEqual(function.expression_types[id(operands[1])], "Int")
        self.assertEqual(operands[1].resolved_name, "probe")
        self.assertEqual(sum(isinstance(node, ast.Call) for node in ast.walk(comparison)), 1)
        self.reject("def f(x: Real) -> Bool:\n    return x is 1\n", "class references and None")

    def test_tuple_equality_promotes_components_with_one_common_chain_type(self):
        functions, _ = parse('''
            def equal(a: Tuple[Int], b: Tuple[Real]) -> Bool:
                return a == (1,) != b == (0.5,)
        ''')
        function = functions["equal"]
        comparison = function.node.body[0].value
        operands = [comparison.left, *comparison.comparators]
        self.assertEqual([effective_type(function, operand) for operand in operands], ["Tuple[Real]"] * 4)
        self.assertEqual(function.expression_types[id(operands[0])], "Tuple[Int]")
        self.assertEqual(operands[1].elts[0].expected_type, "Real")
        self.reject("def f() -> Bool:\n    return (1.0,) < (2.0,)\n", "tuple ordering")

    def test_conditional_expressions_join_numeric_and_nested_tuple_types(self):
        functions, _ = parse('''
            def choose(flag: Bool) -> Tuple[Real, Tuple[Real, Bool]]:
                scalar = 1 if flag else 0.5
                pair = (1, True) if flag else (0.5, False)
                return scalar, pair
        ''')
        function = functions["choose"]
        self.assertEqual(function.variables["scalar"], "Real")
        self.assertEqual(function.variables["pair"], "Tuple[Real, Bool]")
        self.assertEqual(function.node.body[0].value.body.expected_type, "Real")
        self.assertEqual(function.node.body[1].value.body.elts[0].expected_type, "Real")

    def test_fresh_sequence_tuple_and_finite_literals_use_expected_types(self):
        functions, _ = parse('''
            def create() -> Tuple[Seq[Tuple[Real, Real]], Set[Real], Dict[Real, Tuple[Real, Real]]]:
                values: Seq[Tuple[Real, Real]] = const((1, 2))
                selected: Set[Real] = {1, 2}
                pairs: Dict[Real, Tuple[Real, Real]] = {1: (2, 3)}
                return values, selected, pairs
        ''')
        function = functions["create"]
        sequence, selected, pairs = [statement.value for statement in function.node.body[:3]]
        self.assertEqual(function.expression_types[id(sequence)], "Seq[Tuple[Real, Real]]")
        self.assertTrue(all(element.expected_type == "Real" for element in sequence.args[0].elts))
        self.assertEqual(function.expression_types[id(selected)], "Set[Real]")
        self.assertTrue(all(element.expected_type == "Real" for element in selected.elts))
        self.assertEqual(pairs.keys[0].expected_type, "Real")
        self.assertTrue(all(element.expected_type == "Real" for element in pairs.values[0].elts))
        parse("def empty() -> Tuple[Set[Real], Dict[Real, Real]]:\n    return set(), {}\n")

    def test_noncontextual_collection_literals_join_numeric_values(self):
        functions, _ = parse('''
            def create() -> Tuple[Set[Real], Dict[Real, Real]]:
                values = {1, 0.5}
                pairs = {1: 2.5, 0.5: 3}
                return values, pairs
        ''')
        function = functions["create"]
        self.assertEqual(function.variables["values"], "Set[Real]")
        self.assertEqual(function.variables["pairs"], "Dict[Real, Real]")
        self.assertEqual(function.node.body[0].value.elts[0].expected_type, "Real")
        self.assertEqual(function.node.body[1].value.keys[0].expected_type, "Real")
        self.assertEqual(function.node.body[1].value.values[1].expected_type, "Real")

    def test_existing_mutable_aliases_remain_invariant(self):
        pairs = [("Seq", "Seq[Real]"), ("Set[Int]", "Set[Real]"),
                 ("Dict[Int, Int]", "Dict[Int, Real]"), ("Dict[Int, Real]", "Dict[Real, Real]"),
                 ("Tuple[Seq]", "Tuple[Seq[Real]]")]
        for actual, expected in pairs:
            with self.subTest(actual=actual, expected=expected):
                self.reject("def widen(value: %s) -> %s:\n    return value\n" % (actual, expected), "Expected")
        self.reject("def widen(value: Dict[Int, Int]) -> Dict[Int, Real]:\n    return copy(value)\n", "Expected Dict")

    def test_scalar_writes_and_container_operations_promote_expected_values(self):
        functions, _ = parse('''
            class Box:
                value: Real
            def update_values(box: Box, values: Seq[Real], pairs: Dict[Real, Real], selected: Set[Real]) -> Real:
                box.value = 1
                values[0] = 2
                pairs[3] = 4
                selected.add(5)
                selected.discard(6)
                present = 7 in selected and 8 not in pairs
                fallback = pairs.get(9, 10)
                del pairs[11]
                return fallback
        ''')
        function = functions["update_values"]
        for statement in function.node.body[:3]:
            self.assertEqual(statement.value.expected_type, "Real")
        self.assertEqual(function.node.body[2].targets[0].slice.expected_type, "Real")
        self.assertEqual(function.node.body[3].value.args[0].expected_type, "Real")
        self.assertEqual(function.node.body[4].value.args[0].expected_type, "Real")
        self.assertEqual(function.node.body[6].value.args[0].expected_type, "Real")
        self.assertEqual(function.node.body[6].value.args[1].expected_type, "Real")
        self.assertEqual(function.node.body[7].targets[0].slice.expected_type, "Real")

    def test_immutable_tuple_values_and_unpacking_can_promote_components(self):
        functions, _ = parse('''
            def convert(pair: Tuple[Int, Tuple[Int]]) -> Tuple[Real, Tuple[Real]]:
                return pair
            def unpack(pair: Tuple[Int, Int]) -> Real:
                first: Real = 0
                first, second = pair
                return first + second
        ''')
        convert = functions["convert"]
        returned = convert.node.body[0].value
        self.assertEqual(convert.expression_types[id(returned)], "Tuple[Int, Tuple[Int]]")
        self.assertEqual(returned.expected_type, "Tuple[Real, Tuple[Real]]")
        unpack = functions["unpack"]
        target = unpack.node.body[1].targets[0]
        self.assertEqual(unpack.expression_types[id(target)], "Tuple[Real, Int]")
        self.assertEqual(unpack.node.body[1].value.id, "pair")

    def test_real_augmented_assignments_preserve_target_type(self):
        functions, _ = parse('''
            class Box:
                value: Real
            def advance(box: Box, value: Real, n: Int) -> Real:
                value += n
                value -= 1
                value *= 2
                value /= 3
                box.value += n
                box.value /= 2
                return value
        ''')
        function = functions["advance"]
        for statement in function.node.body[:-1]:
            self.assertEqual(function.expression_types[id(statement.target)], "Real")
            self.assertEqual(statement.value.expected_type, "Real")
        self.reject("def f(n: Int) -> Int:\n    n /= 2\n    return n\n", "requires a Real target")
        self.reject("def f(n: Int) -> Int:\n    n += 0.5\n    return n\n", "Expected Int, got Real")
        self.reject("def f(n: Real) -> Real:\n    n //= 2\n    return n\n", "Expected Int, got Real")
        self.reject("def f(n: Real) -> Real:\n    n %= 2\n    return n\n", "Expected Int, got Real")

    def test_integer_only_roles_reject_reals_without_implicit_rounding(self):
        cases = [
            "def f(a: Seq, x: Real) -> Int:\n    return a[x]\n",
            "def f(x: Real) -> Int:\n    return randint(0, x)\n",
            "def f(x: Real) -> Int:\n    for i in range(x):\n        pass\n    return 0\n",
            'def f(x: Real) -> Int:\n    tick("work", x)\n    return 0\n',
            "def f(x: Real) -> Real:\n    return x // 2\n",
            "def f(x: Real) -> Real:\n    return x % 2\n",
            "def f(x: Real) -> Int:\n    return x\n",
        ]
        for source in cases:
            with self.subTest(source=source):
                self.reject(source, "Expected Int, got Real")

    def test_range_and_collection_loop_targets_can_reuse_real_variables(self):
        functions, _ = parse('''
            def scan(x: Real, keys: Set[Int]) -> Real:
                for x in range(2):
                    pass
                for x in keys:
                    pass
                return x
        ''')
        function = functions["scan"]
        for statement in function.node.body[:2]:
            self.assertEqual(statement.target.expected_type, "Real")
            self.assertEqual(function.expression_types[id(statement.target)], "Real")
        self.assertEqual(function.node.body[1].collection_iteration, "Set[Int]")

    def test_booleans_are_not_numbers_and_real_is_not_a_reference(self):
        cases = [("True + 1.0", "Arithmetic requires"), ("-True", "require Int or Real"),
                 ("True", "Expected Real, got Bool"), ("None", "Expected Real, got None")]
        for expression, message in cases:
            self.reject("def f() -> Real:\n    return %s\n" % expression, message)
        self.reject("def f() -> Bool:\n    return True == 1.0\n", "Expected Bool, got Real")
        self.reject("def f(x: Real | None) -> Int:\n    return 0\n", "Only nullable class references")
        self.reject("def f(x: Real) -> Int:\n    if x:\n        return 1\n    return 0\n", "Expected Bool, got Real")

    def test_missing_exact_literal_metadata_fails_clearly(self):
        with self.assertRaisesRegex(CompileError, "original source text"):
            parse_program(ast.parse("def f() -> Real:\n    return 0.1\n"))

    def test_interface_signatures_and_real_keys_keep_source_types(self):
        source = '''from algo2lean import Interface
class Values(Interface):
    def lookup(self, value: Tuple[Real, Int], pairs: Dict[Real, Real]) -> Real: ...
    def all(self) -> Set[Tuple[Real, Bool]]: ...
'''
        with tempfile.TemporaryDirectory() as directory:
            project = load_project("api", root=directory, sources={"api": source})
            interface = collect_interfaces(project)[Symbol("api", "Values", "interface")]
            self.assertEqual(interface.methods["lookup"].parameters,
                             (("value", "Tuple[Real, Int]"), ("pairs", "Dict[Real, Real]")))
            self.assertEqual(interface.methods["lookup"].return_type, "Real")
            self.assertEqual(interface.methods["all"].return_type, "Set[Tuple[Real, Bool]]")
            self.assertEqual(_lean_type("Real"), "Real")
            self.assertEqual(_lean_type("Tuple[Real, Int]"), "(Real × Int)")
            self.assertEqual(_lean_type("Seq[Real]"), "CollectionRef")
            invalid = '''from algo2lean import Interface
class Values(Interface):
    def invalid(self) -> Set[Tuple[Real, Values]]: ...
'''
            with self.assertRaisesRegex(ProjectError, "Abstract interface references"):
                collect_interfaces(load_project("api", root=directory, sources={"api": invalid}))


if __name__ == "__main__":
    unittest.main()
