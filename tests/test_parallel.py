"""Fork-join generation, rejection boundaries, and portable Lean packages.

Execution/cost proof fixtures are checked from freshly generated definitions;
these tests never substitute a Python result for a Lean correctness theorem.
"""

import ast
import itertools
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from algo2lean import CompileError, compile_source
from algo2lean.analysis import check_analysis
from algo2lean.checker import check_lean
from algo2lean.browser import request as compiler_request
from algo2lean.modular import compile_project
from editor.analysis_export import request as analysis_request
from tests.test_analysis_export import unpack
from tests.test_interface_metadata import signature_checks
from scripts.check_parallel_examples import compose_analysis, export_payload, unexpected_axioms


ROOT = Path(__file__).resolve().parents[1]
PAIR_SOURCE = '''def increment(x: Int) -> Int:
    return x + 1

def positive(x: Int) -> Bool:
    return x > 0

def paired(x: Int) -> Tuple[Int, Bool]:
    # @fork
    result: Tuple[Int, Bool] = fork_join(increment(x), positive(x))
    return result
'''

READ_SOURCE = '''def read(a: Seq, index: Int) -> Int:
    return a[index]

def pair_read(a: Seq, i: Int, j: Int) -> Tuple[Int, Int]:
    return fork_join(read(a, i), read(a, j))
'''

WRITE_SOURCE = '''def write(a: Seq, i: Int, value: Int) -> Int:
    a[i] = value
    return value

def pair_write(a: Seq, i: Int, j: Int) -> Tuple[Int, Int]:
    return fork_join(write(a, i, 1), write(a, j, 2))
'''


CAPTURE_SOURCE = '''def captured_arguments(a: Seq) -> Tuple[Int, Int]:
    return fork_join(write(a, 0, 9), read(a, a[0]))
'''

ACCESS_SOURCE = """def nested(a: Seq, b: Seq, i: Int) -> Int:
    return a[b[i]]

def projected(value: Tuple[Seq, Int]) -> Int:
    return value[0][value[1]]

def literal(a: Seq, i: Int) -> Int:
    return (a, i)[0][(a, i)[1]]

def nested_tuple(value: Tuple[Int, Tuple[Seq, Int]]) -> Int:
    return value[1][0][value[1][1]]

def run(a: Seq, b: Seq, i: Int) -> Tuple[Int, Int]:
    return fork_join(nested(a, b, i), projected((a, i)))
"""


class ParallelCompilerTests(unittest.TestCase):
    def test_fork_result_has_both_source_types_and_public_contract(self):
        result = compile_source(PAIR_SOURCE, filename="paired.algo")
        function = next(item for item in result.functions if item["name"] == "paired")
        self.assertEqual(function["return_type"], "Tuple[Int, Bool]")
        self.assertEqual(function["lean_output_type"], "(Int × Bool)")
        self.assertIn("import Algo2LeanLib.Parallel", result.lean)
        self.assertIn("paired.ParallelCall", result.lean)
        self.assertNotIn("Mathlib", result.lean)
        self.assertFalse(result.randomized)
        names = {entry["name"] for entry in function["interface_entries"]}
        self.assertIn("paired.ParallelCall", names)

    def test_parallel_labels_do_not_change_general_definitions(self):
        first = compile_source(PAIR_SOURCE, filename="paired.algo")
        renamed = compile_source(PAIR_SOURCE.replace("@fork", "@children"), filename="paired.algo")
        unlabelled = compile_source(PAIR_SOURCE.replace("    # @fork\n", ""), filename="paired.algo")
        self.assertEqual(first.lean, renamed.lean)
        self.assertEqual(first.lean, unlabelled.lean)
        self.assertNotEqual(first.points_lean, renamed.points_lean)

    def test_plain_sequential_program_does_not_require_parallel_library(self):
        result = compile_source("def f(x: Int) -> Int:\n    return x + 1\n")
        self.assertNotIn("Algo2LeanLib.Parallel", result.lean)
        self.assertNotIn("ParallelCall", result.lean)

    def test_shared_read_and_disjoint_write_programs_compile(self):
        # Alias safety is a semantic obligation. The source accepts arbitrary
        # indices, while a valid parallel call must establish independence.
        for source in (READ_SOURCE, WRITE_SOURCE):
            with self.subTest(source=source):
                result = compile_source(source)
                self.assertIn("ParallelCall", result.lean)

    def test_recursive_parallel_calls_compile(self):
        source = '''def sum(a: Seq, lo: Int, n: Int) -> Int:
    if n <= 0:
        return 0
    if n == 1:
        return a[lo]
    half: Int = n // 2
    values: Tuple[Int, Int] = fork_join(sum(a, lo, half), sum(a, lo + half, n - half))
    return values[0] + values[1]
'''
        result = compile_source(source)
        self.assertIn("sum.ParallelCall", result.lean)

    def test_fork_requires_exactly_two_source_function_calls(self):
        helper = "def value(x: Int) -> Int:\n    return x\n"
        for expression in ("fork_join()", "fork_join(value(1))", "fork_join(value(1), value(2), value(3))",
                           "fork_join(1, value(2))", "fork_join(value(1), 2)",
                           "fork_join(value(1), other=value(2))", "fork_join(randint(0, 2), value(2))",
                           "fork_join(copy(a), value(2))"):
            with self.subTest(expression=expression):
                source = helper + "def run(a: Seq) -> Tuple[Int, Int]:\n    return " + expression + "\n"
                with self.assertRaises(CompileError):
                    compile_source(source)

    def test_randomness_reached_through_helper_is_rejected(self):
        source = '''def sample() -> Int:
    return randint(0, 2)

def wrapped() -> Int:
    return sample()

def run() -> Tuple[Int, Int]:
    return fork_join(wrapped(), wrapped())
'''
        with self.assertRaises(CompileError) as rejected:
            compile_source(source)
        self.assertRegex(str(rejected.exception).lower(), "parallel|fork|random")

    def test_project_mode_exposes_parallel_contract_companion(self):
        project = compile_project("paired", sources={"paired": PAIR_SOURCE})
        self.assertIn("paired.ParallelCall", project.entry.parallel_lean)
        self.assertNotIn("ParallelCall", project.entry.lean)

    def test_unsupported_intermediate_types_have_source_diagnostics(self):
        for expression in ("0.5 > 0.25", "const(True)[0]", "1 in {1, 2}"):
            source = ("def child() -> Bool:\n    return " + expression + "\n"
                      "def run() -> Tuple[Bool, Bool]:\n    return fork_join(child(), child())\n")
            with self.subTest(expression=expression), self.assertRaises(CompileError) as rejected:
                compile_source(source)
            self.assertRegex(str(rejected.exception), "fork_join.*supports")

    def test_parallel_runtime_namespace_is_reserved(self):
        for namespace in ("Algo2LeanParallel", "Algo2LeanParallel.User"):
            with self.subTest(namespace=namespace), self.assertRaises(CompileError):
                compile_source(PAIR_SOURCE, namespace=namespace)

    def test_nested_and_projected_reads_have_complete_access_records(self):
        generated = compile_source(ACCESS_SOURCE)
        for expected in (
            "Access.readSeq s.v0 (h.read s.v1 s.v2)",
            "Access.readSeq s.v1 s.v2",
            "Access.readSeq (s.v0).1 (s.v0).2",
            "Access.readSeq ((s.v0, s.v1)).1 ((s.v0, s.v1)).2",
            "Access.readSeq ((s.v0).2).1 ((s.v0).2).2",
        ):
            self.assertIn(expected, generated.lean)

    def test_cyclic_project_exposes_parallel_facades(self):
        sources = {
            "main": "from helper import leaf\ndef run(n: Int) -> Tuple[Int, Int]:\n"
                    "    return fork_join(leaf(n), leaf(n))\n",
            "helper": "from main import run\ndef leaf(n: Int) -> Int:\n"
                      "    if n <= 0:\n        return 0\n"
                      "    pair = run(n - 1)\n    return pair[0]\n",
        }
        project = compile_project("main", sources=sources)
        self.assertIn("run.ParallelCall", project.entry.parallel_lean)
        self.assertIn("leaf.ParallelCall", project.modules["helper"].parallel_lean)

    def test_fork_join_name_is_reserved(self):
        with self.assertRaises(CompileError):
            compile_source("def fork_join(x: Int) -> Int:\n    return x\n")


class MathematicalSequence:
    """A finite override map for an integer-indexed constant sequence."""
    def __init__(self, value=0):
        self.default = value
        self.cells = {}

    def __getitem__(self, index):
        return self.cells.get(index, self.default)

    def __setitem__(self, index, value):
        self.cells[index] = value


def example_execution_functions():
    """Execute only the checked repository fixture, preserving fork argument order.

    _defer captures the already evaluated arguments. The two child calls begin
    only after all parent-side argument expressions have been evaluated.
    Python executes their canonical serialization; the Lean proofs establish
    parallel safety and work/span, independently of this regression evaluator.
    """
    source = (ROOT / "examples/parallel/parallel.algo").read_text()
    compile_source(source, filename="parallel.algo")

    class DelayForkChildren(ast.NodeTransformer):
        def visit_Call(self, node):
            node = self.generic_visit(node)
            if isinstance(node.func, ast.Name) and node.func.id == "fork_join":
                node.args = [ast.copy_location(ast.Call(func=ast.Name(id="_defer", ctx=ast.Load()),
                    args=[child.func, *child.args], keywords=[]), child) for child in node.args]
            return node

    tree = ast.fix_missing_locations(DelayForkChildren().visit(ast.parse(source)))
    def defer(function, *arguments):
        return lambda: function(*arguments)
    namespace = {"Int": int, "Seq": MathematicalSequence, "const": MathematicalSequence,
                 "fork_join": lambda left, right: (left(), right()), "_defer": defer}
    exec(compile(tree, "parallel.algo", "exec"), namespace)
    return namespace


class ParallelExampleExecutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.functions = example_execution_functions()

    def check_values(self, values, lo, count=None):
        count = len(values) if count is None else count
        source = MathematicalSequence(-47)
        source[lo - 1], source[lo + len(values)] = 109, -113
        for index, value in enumerate(values):
            source[lo + index] = value
        before = dict(source.cells)
        total = self.functions["parallel_sum"](source, lo, count)
        output = self.functions["prefix_sum"](source, lo, count)
        used = values[:max(0, count)]
        self.assertEqual(total, sum(used))
        self.assertIsNot(output, source)
        self.assertEqual(source.cells, before)
        self.assertEqual(source.default, -47)
        self.assertEqual([output[lo + i] for i in range(max(0, count))],
                         [sum(used[:i]) for i in range(max(0, count))])
        for index in (lo - 3, lo - 1, lo + max(0, count), lo + max(0, count) + 3):
            self.assertEqual(output[index], 0)

    def test_all_small_signed_inputs_with_shifted_intervals(self):
        # Every ternary array through length six, including uneven recursive
        # splits, negative entries, equal values, and negative source indices.
        for size in range(7):
            for values in itertools.product((-2, 0, 3), repeat=size):
                for lo in (-5, 0, 7):
                    self.check_values(values, lo)

    def test_nonpositive_lengths_and_large_integer_values(self):
        for count in (-7, -1, 0):
            self.check_values([11, -13, 17], -4, count)
        values = [(-1 if i % 2 else 1) * (10 ** 70 + i) for i in range(129)]
        self.check_values(values, -23)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ParallelLeanTests(unittest.TestCase):
    def test_generated_finite_executions_cost_and_compatibility(self):
        generated = compile_source(PAIR_SOURCE + "\n" + READ_SOURCE + "\n" + WRITE_SOURCE + "\n" + CAPTURE_SOURCE,
                                   module="ParallelSemanticsGenerated")
        proof = (ROOT / "tests/proofs/parallel.lean").read_text()
        checked = check_analysis(generated.lean, proof, generated.module, timeout=120)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("sorryAx", checked.output)

    def test_interface_metadata_types_and_named_arguments_are_exact(self):
        source = PAIR_SOURCE + "\n" + READ_SOURCE + "\n" + WRITE_SOURCE
        for namespace in (None, "ParallelMetadata"):
            with self.subTest(namespace=namespace):
                generated = compile_source(source, filename="parallel_metadata.algo", namespace=namespace)
                proof = "\nopen Algo2LeanGenerated\n"
                if namespace:
                    proof += "open ParallelMetadata ParallelMetadata.Algo2LeanGenerated\n"
                proof += signature_checks(generated.functions)
                checked = check_lean(generated.lean, module=generated.module,
                                     points_lean=generated.points_lean + proof, timeout=120)
                self.assertTrue(checked.ok, checked.output)

    def test_nested_and_projected_access_terms_are_lean_typed(self):
        generated = compile_source(ACCESS_SOURCE)
        checked = check_lean(generated.lean, module=generated.module, timeout=120)
        self.assertTrue(checked.ok, checked.output)

    def test_example_correctness_and_runtime_contracts(self):
        analysis = compose_analysis()
        for path in (ROOT / "examples/parallel/analysis").glob("*.lean"):
            self.assertNotRegex(path.read_text(), r"\b(?:sorry|admit)\b", str(path))
        body = export_payload(analysis)
        generated = compile_source(body["source"], filename=body["filename"])
        checked = check_analysis(generated.lean, analysis, generated.module, timeout=180)
        self.assertTrue(checked.ok, checked.output)
        self.assertFalse(unexpected_axioms(checked.output), checked.output)

    def test_single_file_standalone_has_its_complete_runtime(self):
        generated = compile_source(PAIR_SOURCE, module="StandaloneParallel", standalone=True)
        self.assertNotIn("import Algo2Lean", generated.lean)
        self.assertIn("namespace Algo2LeanParallel", generated.lean)
        checked = check_lean(generated.lean, module=generated.module,
                             points_lean=generated.points_lean, timeout=120)
        self.assertTrue(checked.ok, checked.output)


class ParallelExportTests(unittest.TestCase):
    def test_generation_and_analysis_archives_include_parallel_core(self):
        proof = "import PairedGenerated\n#check paired.ParallelCall\n"
        body = {"source": PAIR_SOURCE, "filename": "paired.algo", "analysis": proof,
                "analysis_filename": "Proof.lean"}
        generated = compile_source(PAIR_SOURCE, filename="paired.algo")
        for response in (compiler_request("/api/generation", {**body, "archive": True}),
                         analysis_request("/api/analysis-export", body)):
            files = unpack(response)
            self.assertEqual(files["PairedGenerated.lean"], generated.lean.encode())
            self.assertEqual(files["Algo2LeanLib/Parallel.lean"],
                             (ROOT / "Algo2LeanLib/Parallel.lean").read_bytes())
            self.assertIn("Algo2Lean.lean", files)
            self.assertNotIn(b'name = "mathlib"', files["lakefile.toml"])
            self.assertFalse(any(".lake/" in name for name in files))

    @unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
    def test_complete_example_analysis_download_builds_in_isolation(self):
        files = unpack(analysis_request("/api/analysis-export", export_payload(compose_analysis())))
        for name in ("Algo2LeanLib/Parallel.lean", "Algo2LeanLib/ParallelBounds.lean",
                     "Algo2LeanLib/ParallelSeq.lean", "ParallelGenerated.lean"):
            self.assertIn(name, files)
        self.build_archive(files, "ParallelAnalysis")

    @unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
    def test_parallel_analysis_download_builds_in_isolation(self):
        body = {"source": PAIR_SOURCE, "filename": "paired.algo",
                "analysis": "import PairedGenerated\n#check paired.ParallelCall\n",
                "analysis_filename": "Proof.lean"}
        files = unpack(analysis_request("/api/analysis-export", body))
        self.build_archive(files, "Proof")

    def build_archive(self, files, module):
        with tempfile.TemporaryDirectory(prefix="algo2lean-parallel-export-") as directory:
            root = Path(directory)
            for name, contents in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(contents)
            environment = dict(os.environ)
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            completed = subprocess.run([shutil.which("lake"), "--no-cache", "build"], cwd=root,
                env=environment, capture_output=True, text=True, timeout=180)
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            self.assertNotIn("declaration uses `sorry`", completed.stdout + completed.stderr)
            self.assertTrue((root / ".lake/build/lib/lean" / (module + ".olean")).is_file())


if __name__ == "__main__":
    unittest.main()
