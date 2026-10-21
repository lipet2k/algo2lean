"""Front-end checks. Run with: python3 -m unittest discover -v."""

from pathlib import Path
import re
import unittest

from algo2lean.compiler import CompileError, compile_source
from algo2lean.modules import generated_module_name, validate_module_name


ROOT = Path(__file__).resolve().parents[1]


class CompilerTests(unittest.TestCase):
    def assert_compiles(self, source):
        result = compile_source(source, filename="test.algo")
        self.assertIsInstance(result.lean, str)
        self.assertTrue(result.lean.strip())
        self.assertNotIn("sorry", result.lean)
        self.assertNotIn("axiom ", result.lean)
        return result

    def assert_rejected(self, source):
        with self.assertRaises(CompileError) as caught:
            compile_source(source, filename="bad.algo")
        diagnostic = caught.exception.to_dict()
        self.assertIsInstance(diagnostic["message"], str)
        self.assertTrue(diagnostic["message"])
        self.assertIsInstance(diagnostic["line"], int)
        self.assertGreaterEqual(diagnostic["line"], 1)
        self.assertIsInstance(diagnostic["column"], int)
        self.assertGreaterEqual(diagnostic["column"], 1)
        return diagnostic

    def test_example_programs(self):
        examples = sorted((ROOT / "examples").glob("*.algo"))
        self.assertGreaterEqual(len(examples), 6)
        for path in examples:
            with self.subTest(path=path.name):
                self.assert_compiles(path.read_text(encoding="utf-8"))

    def test_function_metadata_and_input_arities(self):
        result = self.assert_compiles("""\
def zero() -> Int:
    return 0

def one(x: Int) -> Int:
    return x

def two(x: Int, values: Seq) -> Bool:
    return x == values[x]

def three(a: Int, b: Int, c: Int) -> Int:
    return a + b + c
""")
        self.assertTrue(all(function["points"] == [] for function in result.functions))
        self.assertEqual([{key: function[key] for key in ("name", "parameters", "return_type")}
                          for function in result.functions], [
            {"name": "zero", "parameters": [], "return_type": "Int"},
            {"name": "one", "parameters": [{"name": "x", "type": "Int"}], "return_type": "Int"},
            {"name": "two", "parameters": [{"name": "x", "type": "Int"}, {"name": "values", "type": "Seq"}], "return_type": "Bool"},
            {"name": "three", "parameters": [{"name": "a", "type": "Int"}, {"name": "b", "type": "Int"}, {"name": "c", "type": "Int"}], "return_type": "Int"},
        ])
        for name in ("zero", "one", "two", "three"):
            self.assertIn(name + ".Returns", result.lean)

    def test_repeatable_compilation(self):
        source = "def f(x: Int) -> Int:\n    return x + 1\n"
        first = self.assert_compiles(source)
        second = self.assert_compiles(source)
        self.assertEqual(first.lean, second.lean)
        self.assertEqual(first.functions, second.functions)

    def test_class_metadata_describes_public_heap_signatures(self):
        source = (ROOT / "examples" / "classes.algo").read_text()
        functions = {fn["name"]: fn for fn in self.assert_compiles(source).functions}
        expected = {
            "Counter_add": ("Counter.add", "Heap × (Ref_Counter × Int)", "Unit"),
            "Node_sum": ("Node.sum", "Heap × (Ref_Node)", "Int"),
            "make_node": ("make_node", "Int", "Heap × (Ref_Node)"),
            "counter_alias": ("counter_alias", "Int × Int", "Int"),
        }
        for name, signature in expected.items():
            with self.subTest(function=name):
                self.assertEqual(tuple(functions[name][key] for key in
                    ("display_name", "lean_input_type", "lean_output_type")), signature)

    def test_class_generated_helpers_cannot_collide(self):
        for source in (
            "class Box:\n    value: Int\n    value_set: Int\n",
            "class A:\n    b_c: Int\nclass A_b:\n    c: Int\n",
        ):
            with self.subTest(source=source):
                error = self.assert_rejected(source)
                self.assertIn("Generated Lean name", error["message"])

    def test_line_annotations_do_not_change_algorithm_definitions(self):
        source = """\
def modify(a: Seq, n: Int) -> Seq:
    b = copy(a)
    while n > 0:
        b[n] = a[n] + 1
        n -= 1
    return b
"""
        baseline = self.assert_compiles(source)
        variants = [
            source.replace("    b = copy(a)", "    # @start\n    b = copy(a)"),
            source.replace("    while n > 0:", "    # @loop\n    while n > 0:"),
            source.replace("        b[n] = a[n] + 1", "        # @write\n        b[n] = a[n] + 1"),
            source.replace("    return b", "    # @start\n    return b"),
            "# source commentary\n\n" + source.replace("    return b", "\n    # @finished\n    return b\n"),
        ]
        for variant in variants:
            with self.subTest(source=variant):
                result = self.assert_compiles(variant)
                self.assertEqual(result.lean, baseline.lean)
                self.assertEqual(result.program_lean, baseline.program_lean)
                self.assertEqual(result.shared_lean, baseline.shared_lean)
                self.assertNotEqual(result.points_lean, baseline.points_lean)

    def test_all_examples_core_survives_label_removal_and_line_shifts(self):
        for path in sorted((ROOT / "examples").glob("*.algo")):
            with self.subTest(path=path.name):
                source = path.read_text(encoding="utf-8")
                plain = re.sub(r"#[ \t]*@[A-Za-z_][A-Za-z_0-9]*[^\n]*", "", source)
                plain = "# shifted source\n\n" + plain
                labeled = compile_source(source, filename=path.name)
                unlabeled = compile_source(plain, filename=path.name)
                self.assertEqual(labeled.lean, unlabeled.lean)
                self.assertEqual(labeled.program_lean, unlabeled.program_lean)
                self.assertNotRegex(unlabeled.points_lean, r"(?m)^def \S+\.At\.")

    def test_separate_named_line_module_and_stable_summary_interface(self):
        source = "def f(a: Seq) -> Seq:\n    # @result\n    return a\n"
        result = compile_source(source, filename="sequence-copy.algo")
        self.assertEqual(result.module, "SequenceCopyGenerated")
        self.assertEqual(result.points_module, "SequenceCopyGeneratedPoints")
        self.assertTrue(result.points_lean.startswith("import «SequenceCopyGenerated»\n"))
        for prefix in ("f.At.result", "f.Local.a", "f.Element.a"):
            self.assertIn("def " + prefix, result.points_lean)
            self.assertNotIn("def " + prefix, result.lean)
        for name in ("f.Returns", "f.Call", "f.CallFrom"):
            self.assertIn("def " + name, result.lean)
            self.assertNotIn("def " + name, result.points_lean)
        self.assertEqual(result.lean, compile_source(source.replace("    # @result\n", "")).lean)
        self.assertEqual(result.stats, {
            "program_lines": len(result.program_lean.splitlines()),
            "shared_lines": len(result.shared_lean.splitlines()),
            "general_lines": len(result.lean.splitlines()),
            "points_lines": len(result.points_lean.splitlines()),
            "total_lines": len(result.lean.splitlines()) + len(result.points_lean.splitlines()),
        })

    def test_explicit_module_name_and_standalone_split(self):
        source = "def f(n: Int) -> Int:\n    # @result\n    return n\n"
        result = compile_source(source, module="custom_algorithm", standalone=True)
        self.assertEqual(result.module, "custom_algorithm")
        self.assertEqual(result.points_module, "custom_algorithmPoints")
        self.assertTrue(result.lean.startswith(result.shared_lean))
        self.assertTrue(result.points_lean.startswith("import «custom_algorithm»\n"))
        self.assertNotIn("namespace Algo2LeanCore", result.points_lean)
        self.assertNotRegex(result.lean, r"(?m)^def \S+\.At\.")

    def test_safe_module_identities(self):
        source = "def f() -> Int:\n    return 0\n"
        for invalid in ("", "1Example", "../Example", "A.B", "A\nimport Lean", "A/B",
                        "A\\B", "A-B", "«A»", "Algo2Lean", "Algo2LeanReal", "algo2leanprobability",
                        "Algo2LeanLib", "Algo2LeanExamples", "Mathlib", "Lean", "Std", "Init", "algo2lean", "STD", 1, True):
            with self.subTest(module=invalid):
                with self.assertRaises(CompileError):
                    compile_source(source, module=invalid)
                with self.assertRaises(ValueError):
                    validate_module_name(invalid)
        for filename in ("my_algorithm.algo", "/tmp/my algorithm.algo", "C:\\code\\my algorithm.algo"):
            self.assertEqual(generated_module_name(filename), "MyAlgorithmGenerated")
        for module in ("import", "def", "namespace", "Prop", "Type", "out"):
            with self.subTest(module=module):
                result = compile_source(source, module=module)
                self.assertEqual(result.points_lean.splitlines()[0], "import «%s»" % module)
        hostile = compile_source(source, filename="bad\nimport Lean.algo")
        self.assertEqual(hostile.module, "BadImportLeanGenerated")
        self.assertEqual(hostile.points_lean.splitlines()[0], "import «BadImportLeanGenerated»")

    def test_arbitrary_precision_literal(self):
        value = "9876543210" * 30
        result = self.assert_compiles("def large() -> Int:\n    return " + value + "\n")
        self.assertIn(value, result.lean)

    def test_forward_calls_and_mutual_recursion(self):
        self.assert_compiles("""\
def left(n: Int) -> Int:
    if n == 0:
        return 0
    return right(n - 1)

def right(n: Int) -> Int:
    if n == 0:
        return 1
    return left(n - 1)
""")

    def test_short_circuit_and_comparison_syntax(self):
        self.assert_compiles("""\
def diverge() -> Bool:
    return diverge()

def choose(x: Int) -> Bool:
    return (False and diverge()) or (not False and -10 <= x < 10)
""")

    def test_sequences_and_local_reassignment(self):
        self.assert_compiles("""\
def modify(a: Seq, n: Int) -> Seq:
    b: Seq = a
    b[-n] = 42
    b = update(b, n + 1, a[n])
    return b
""")

    def test_nested_control_flow(self):
        self.assert_compiles("""\
def nested(x: Int) -> Int:
    value: Int = 0
    while x > 0:
        if x > 3:
            value = value + x
        else:
            if x == 2:
                return value
            value = value - 1
        x = x - 1
    return value
""")

    def test_range_forms_and_existing_binding(self):
        self.assert_compiles("""\
def ranges(start: Int, stop: Int, step: Int) -> Int:
    answer = 0
    i = -1
    for i in range(stop):
        answer += i
    for i in range(start, stop):
        answer += i
    for i in range(start, stop, step):
        answer += i
    return answer + i
""")

    def test_copy_and_discarded_mutating_call(self):
        self.assert_compiles("""\
def write(a: Seq) -> Int:
    a[-1] = 19
    return 0

def caller(a: Seq) -> Seq:
    b = copy(a)
    write(b)
    update(b, 0, 7)
    return b
""")

    def test_branch_assignments(self):
        self.assert_compiles("""\
def branch(x: Int) -> Int:
    if x > 0:
        answer = 1
    else:
        answer = -1
    return answer
""")

    def test_divergence_without_unreachable_return(self):
        self.assert_compiles("def forever(x: Int) -> Int:\n    while True:\n        x = x + 1\n")

    def test_return_or_divergence(self):
        self.assert_compiles("""\
def maybe(x: Int) -> Int:
    if x > 0:
        return x
    else:
        while True:
            pass
""")

    def test_diagnostic_points_to_unknown_name(self):
        diagnostic = self.assert_rejected("def f(x: Int) -> Int:\n    value = 1\n    return unknown\n")
        self.assertEqual(diagnostic["line"], 3)

    def test_invalid_text_has_source_location(self):
        for character in ("\x00", "\ud800", "\udfff"):
            with self.subTest(character=repr(character)):
                diagnostic = self.assert_rejected(
                    "def f() -> Int:\n    return 1\n# " + character + "\n"
                )
                self.assertEqual(diagnostic["line"], 3)
                self.assertEqual(diagnostic["column"], 3)

    def test_invalid_syntax(self):
        cases = {
            "empty source": "",
            "parse error": "def f(x: Int) -> Int\n    return x\n",
            "indentation": "def f(x: Int) -> Int:\nreturn x\n",
            "import": "import os\n",
            "unreachable import": "def f() -> Int:\n    return 1\n    import os\n",
            "top level statement": "x = 10\n",
            "inheritance": "class X(Y):\n    pass\n",
            "lambda": "def f() -> Int:\n    return (lambda: 1)()\n",
            "attribute": "def f(x: Int) -> Int:\n    return x.real\n",
            "list": "def f() -> Seq:\n    return [1, 2]\n",
            "float": "def f() -> Int:\n    return 1.5\n",
            "string": "def f() -> Int:\n    return 'x'\n",
            "for loop": "def f(x: Int) -> Int:\n    for y in x:\n        pass\n    return x\n",
            "break": "def f() -> Int:\n    while True:\n        break\n    return 0\n",
            "keyword call": "def f(x: Int) -> Int:\n    return f(x=1)\n",
            "decorator": "@something\ndef f() -> Int:\n    return 0\n",
            "variadic args": "def f(*x: Int) -> Int:\n    return 0\n",
            "default args": "def f(x: Int = 1) -> Int:\n    return x\n",
            "type comment": "def f() -> Int:\n    x = 1 # type: Int\n    return x\n",
            "missing input type": "def f(x) -> Int:\n    return x\n",
            "missing output type": "def f(x: Int):\n    return x\n",
            "unknown type": "def f(x: Nat) -> Int:\n    return 0\n",
            "division": "def f(x: Int) -> Int:\n    return x / 2\n",
            "slice": "def f(x: Seq) -> Seq:\n    return x[1:3]\n",
            "duplicate function": "def f() -> Int:\n    return 0\ndef f() -> Int:\n    return 1\n",
            "duplicate parameter": "def f(x: Int, x: Int) -> Int:\n    return x\n",
            "reserved builtin function": "def const(x: Int) -> Int:\n    return x\n",
            "reserved builtin local": "def f() -> Int:\n    update = 0\n    return update\n",
            "reserved builtin parameter": "def f(const: Int) -> Int:\n    return const\n",
            "reserved copy function": "def copy(x: Int) -> Int:\n    return x\n",
            "reserved range local": "def f() -> Int:\n    range = 1\n    return range\n",
            "for else": "def f() -> Int:\n    for i in range(2):\n        pass\n    else:\n        pass\n    return 0\n",
            "for tuple target": "def f() -> Int:\n    for i, j in range(2):\n        pass\n    return 0\n",
            "continue": "def f() -> Int:\n    for i in range(2):\n        continue\n    return 0\n",
            "falling off function": "def f(x: Int) -> Int:\n    x = x + 1\n",
            "partial return": "def f(x: Int) -> Int:\n    if x > 0:\n        return x\n",
            "loop may terminate without return": "def f(x: Int) -> Int:\n    while x > 0:\n        x = x - 1\n",
        }
        for name, source in cases.items():
            with self.subTest(case=name):
                self.assert_rejected(source)

    def test_type_errors(self):
        cases = {
            "unknown variable": "def f() -> Int:\n    return missing\n",
            "unknown function": "def f() -> Int:\n    return missing()\n",
            "arity too few": "def f(x: Int) -> Int:\n    return f()\n",
            "arity too many": "def f(x: Int) -> Int:\n    return f(x, x)\n",
            "call argument type": "def f(x: Int) -> Int:\n    return f(True)\n",
            "return bool as int": "def f() -> Int:\n    return True\n",
            "return int as bool": "def f() -> Bool:\n    return 1\n",
            "return int as sequence": "def f() -> Seq:\n    return 0\n",
            "truthy integer condition": "def f(x: Int) -> Int:\n    if x:\n        return 0\n    return 1\n",
            "truthy loop condition": "def f(x: Int) -> Int:\n    while x:\n        x = x - 1\n    return x\n",
            "assignment type change": "def f() -> Int:\n    x = 0\n    x = True\n    return 0\n",
            "branch type conflict": "def f(x: Int) -> Int:\n    if x > 0:\n        y = 1\n    else:\n        y = True\n    return 0\n",
            "loop type conflict": "def f(x: Int) -> Int:\n    y = 1\n    while x > 0:\n        y = True\n        x = x - 1\n    return 0\n",
            "function shadowed by local": "def f() -> Int:\n    return 0\ndef g() -> Int:\n    f = 1\n    return f()\n",
            "annotation mismatch": "def f() -> Int:\n    x: Bool = 0\n    return 0\n",
            "branch possibly unbound": "def f(x: Int) -> Int:\n    if x > 0:\n        y = 1\n    return y\n",
            "loop possibly unbound": "def f(x: Int) -> Int:\n    while x > 0:\n        y = 1\n        x = x - 1\n    return y\n",
            "sequence index bool": "def f(x: Seq) -> Int:\n    return x[True]\n",
            "int not subscriptable": "def f(x: Int) -> Int:\n    return x[0]\n",
            "sequence arithmetic": "def f(x: Seq) -> Seq:\n    return x + x\n",
            "sequence ordering": "def f(x: Seq) -> Bool:\n    return x < x\n",
            "sequence equality": "def f(x: Seq) -> Bool:\n    return x == x\n",
            "sequence write bool": "def f(x: Seq) -> Seq:\n    x[0] = False\n    return x\n",
            "constant sequence arity": "def f() -> Seq:\n    return const()\n",
            "constant sequence bool": "def f() -> Seq:\n    return const(False)\n",
            "update nonsequence": "def f() -> Seq:\n    return update(0, 0, 0)\n",
            "update arity": "def f(x: Seq) -> Seq:\n    return update(x, 0)\n",
            "copy arity": "def f(x: Seq) -> Seq:\n    return copy(x, x)\n",
            "copy nonsequence": "def f() -> Seq:\n    return copy(0)\n",
            "range argument bool": "def f() -> Int:\n    for i in range(True):\n        pass\n    return 0\n",
            "range stop bool": "def f() -> Int:\n    for i in range(0, False):\n        pass\n    return 0\n",
            "range step bool": "def f() -> Int:\n    for i in range(0, 3, True):\n        pass\n    return 0\n",
            "range argument count": "def f() -> Int:\n    for i in range():\n        pass\n    return 0\n",
            "range too many args": "def f() -> Int:\n    for i in range(1, 2, 3, 4):\n        pass\n    return 0\n",
            "range keyword": "def f() -> Int:\n    for i in range(stop=3):\n        pass\n    return 0\n",
            "range variable possibly unbound": "def f() -> Int:\n    for i in range(3):\n        pass\n    return i\n",
            "range body variable possibly unbound": "def f() -> Int:\n    for i in range(3):\n        answer = i\n    return answer\n",
            "range bound uses new variable": "def f() -> Int:\n    for i in range(i):\n        pass\n    return 0\n",
            "range variable wrong type": "def f() -> Int:\n    i = False\n    for i in range(3):\n        pass\n    return 0\n",
            "range variable changes type": "def f() -> Int:\n    for i in range(3):\n        i = False\n    return 0\n",
            "range as value": "def f() -> Int:\n    return range(3)\n",
            "and integer": "def f(x: Int) -> Bool:\n    return x and True\n",
            "not integer": "def f(x: Int) -> Bool:\n    return not x\n",
            "bool arithmetic": "def f() -> Int:\n    return True + 1\n",
            "mixed equality": "def f() -> Bool:\n    return True == 1\n",
        }
        for name, source in cases.items():
            with self.subTest(case=name):
                self.assert_rejected(source)


if __name__ == "__main__":
    unittest.main()
