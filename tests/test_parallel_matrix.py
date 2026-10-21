"""Nested matrix executions and source-connected fork-join proof packages."""

import ast
import itertools
import os
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
import unittest

from algo2lean import compile_source
from algo2lean.analysis import check_analysis
from editor.analysis_export import request as analysis_request
from scripts.check_parallel_matrix_examples import compose_analysis, export_payload, unexpected_axioms
from tests.test_analysis_export import unpack
from tests.test_parallel import MathematicalSequence

ROOT = Path(__file__).resolve().parents[1]


class Sequence(MathematicalSequence):
    @classmethod
    def __class_getitem__(cls, item):
        return cls


def execution_functions():
    source = (ROOT/"examples/parallel_matrix/parallel_matrix.algo").read_text()
    compile_source(source, filename="parallel_matrix.algo")

    class DelayChildren(ast.NodeTransformer):
        def visit_Call(self, node):
            node = self.generic_visit(node)
            if isinstance(node.func, ast.Name) and node.func.id == "fork_join":
                node.args = [ast.copy_location(ast.Call(func=ast.Name(id="_defer", ctx=ast.Load()),
                    args=[child.func, *child.args], keywords=[]), child) for child in node.args]
            return node

    tree = ast.fix_missing_locations(DelayChildren().visit(ast.parse(source)))
    namespace = {"Int": int, "Seq": Sequence, "const": Sequence,
                 "_defer": lambda fn, *args: lambda: fn(*args),
                 "fork_join": lambda left, right: (left(), right())}
    exec(compile(tree, "parallel_matrix.algo", "exec"), namespace)
    return namespace


def matrix(values, default=-100003):
    result = Sequence(Sequence(default))
    for i, row in enumerate(values):
        result[i] = Sequence(default)
        for j, value in enumerate(row):
            result[i][j] = value
    return result


def row_objects(value):
    return {id(row): row for row in [value.default, *value.cells.values()]}


def snapshot(value):
    return (value.default, dict(value.cells),
            {key: (row.default, dict(row.cells)) for key, row in row_objects(value).items()})


def product(a, b, n):
    return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


class ParallelMatrixExecutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.functions = execution_functions()

    def check_product(self, a, b, n):
        expected = product(a, b, n)
        before_a, before_b = snapshot(a), snapshot(b)
        out = self.functions["parallel_matrix_multiply"](a, b, n)
        self.assertIsNot(out, a)
        self.assertIsNot(out, b)
        self.assertEqual([[out[i][j] for j in range(n)] for i in range(n)], expected)
        self.assertEqual(snapshot(a), before_a)
        self.assertEqual(snapshot(b), before_b)
        row_ids = {id(out[i]) for i in range(n)}
        self.assertEqual(len(row_ids), n)
        self.assertNotIn(id(out.default), row_ids)
        self.assertTrue(row_ids.isdisjoint(row_objects(a)))
        self.assertTrue(row_ids.isdisjoint(row_objects(b)))
        for i in (-3, -1, n, n+3):
            for j in (-2, 0, n, n+2):
                self.assertEqual(out[i][j], 0)
        for i in range(n):
            for j in (-3, -1, n, n+3):
                self.assertEqual(out[i][j], 0)
        return out

    def test_exhaustive_ternary_two_by_two_products(self):
        arrays = [matrix([list(values[:2]), list(values[2:])])
                  for values in itertools.product((-2, 0, 3), repeat=4)]
        for a in arrays:
            for b in arrays:
                self.check_product(a, b, 2)

    def test_seeded_sizes_zero_through_nine_and_large_integers(self):
        rng = random.Random(2602)
        for n in range(10):
            for _ in range(5):
                a = matrix([[rng.randrange(-7, 8) for _ in range(n)] for _ in range(n)])
                b = matrix([[rng.randrange(-7, 8) for _ in range(n)] for _ in range(n)])
                self.check_product(a, b, n)
        n = 5
        a = matrix([[(-1)**(i+j)*(10**80+i-j) for j in range(n)] for i in range(n)])
        b = matrix([[10**75+(i*j)%3 for j in range(n)] for i in range(n)])
        self.check_product(a, b, n)

    def test_readonly_inputs_may_share_outer_and_inner_storage(self):
        for n in range(10):
            a = matrix([[(i-j)%5-2 for j in range(n)] for i in range(n)])
            self.check_product(a, a, n)
            shared = Sequence(17)
            for j in range(n):
                shared[j] = j-3
            aliased = Sequence(shared)
            self.check_product(aliased, aliased, n)
            if n:
                a[0] = shared
            self.check_product(a, aliased, n)

    def test_preallocated_rows_preserve_all_exterior_storage(self):
        for n in range(10):
            a = matrix([[i-2*j for j in range(n)] for i in range(n)])
            b = matrix([[i+j-3 for j in range(n)] for i in range(n)])
            out = matrix([[919]*n for _ in range(n)], default=317)
            out[-1], out[n+1] = Sequence(701), Sequence(709)
            for i in range(n):
                out[i][-2], out[i][n+2] = 803, 809
            before_a, before_b, before_out = snapshot(a), snapshot(b), snapshot(out)
            returned = self.functions["parallel_matrix_multiply_into"](a, b, out, n)
            self.assertEqual(returned, 0)
            self.assertEqual([[out[i][j] for j in range(n)] for i in range(n)], product(a,b,n))
            self.assertEqual(snapshot(a), before_a)
            self.assertEqual(snapshot(b), before_b)
            self.assertIs(out.default, before_out[0])
            self.assertEqual(out.cells, before_out[1])
            for i in range(n):
                old = before_out[2][id(out[i])]
                self.assertEqual(out[i].default, old[0])
                self.assertEqual({j:v for j,v in out[i].cells.items() if not 0 <= j < n},
                                 {j:v for j,v in old[1].items() if not 0 <= j < n})
            for i in (-1,n+1):
                self.assertEqual((out[i].default,dict(out[i].cells)), before_out[2][id(out[i])])

    def test_exterior_alias_of_selected_output_row_observes_writes(self):
        a = matrix([[2, -3], [0, 1]])
        b = matrix([[4, 2], [-1, 7]])
        out = matrix([[919, 919], [919, 919]], default=317)
        out[-1] = out[0]
        outer_before = dict(out.cells)
        self.functions["parallel_matrix_multiply_into"](a,b,out,2)
        self.assertEqual(out.cells,outer_before)
        self.assertEqual([out[-1][j] for j in range(2)],product(a,b,2)[0])
        self.assertEqual(out[-1][-1],317)

    def test_shifted_dot_interval_and_disjoint_column_slice(self):
        row = Sequence(2)
        b = Sequence(Sequence(-3))
        for i in range(-8,9):
            row[i] = i*2-1
            b[i] = Sequence(i+4)
        for lo in (-7,0,3):
            for count in range(8):
                expected = sum(row[k]*b[k][-4] for k in range(lo,lo+count))
                self.assertEqual(self.functions["parallel_matrix_dot"](row,b,-4,lo,count), expected)
        out = Sequence(997)
        old = dict(out.cells)
        self.functions["parallel_matrix_columns"](row,b,out,7,-4,6)
        for j in range(-4,2):
            self.assertEqual(out[j], sum(row[k]*b[k][j] for k in range(7)))
        self.assertEqual({j:v for j,v in out.cells.items() if not -4 <= j < 2},old)
        self.assertEqual(out.default,997)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ParallelMatrixProofTests(unittest.TestCase):
    def test_complete_generated_source_contracts(self):
        analysis = compose_analysis()
        for path in (ROOT/"examples/parallel_matrix/analysis").glob("*.lean"):
            self.assertNotRegex(path.read_text(), r"\b(?:sorry|admit)\b", str(path))
        payload = export_payload(analysis)
        generated = compile_source(payload["source"],filename=payload["filename"])
        checked = check_analysis(generated.lean,analysis,generated.module,timeout=300)
        self.assertTrue(checked.ok,checked.output)
        self.assertFalse(unexpected_axioms(checked.output),checked.output)

    @unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
    def test_complete_analysis_download_builds_in_isolation(self):
        files=unpack(analysis_request("/api/analysis-export",export_payload(compose_analysis())))
        for name in ("ParallelMatrixGenerated.lean","Algo2LeanLib/Parallel.lean","Algo2LeanLib/ParallelMatrix.lean"):
            self.assertIn(name,files)
        self.assertNotIn(b'name = "mathlib"',files["lakefile.toml"])
        with tempfile.TemporaryDirectory(prefix="algo2lean-parallel-matrix-export-") as directory:
            root=Path(directory)
            for name,contents in files.items():
                path=root/name
                path.parent.mkdir(parents=True,exist_ok=True)
                path.write_bytes(contents)
            environment=dict(os.environ)
            environment.pop("LEAN_PATH",None)
            environment.pop("LEAN_SRC_PATH",None)
            built=subprocess.run([shutil.which("lake"),"--no-cache","build"],cwd=root,
                env=environment,capture_output=True,text=True,timeout=300)
            self.assertEqual(built.returncode,0,built.stdout+built.stderr)
            self.assertNotIn("declaration uses `sorry`",built.stdout+built.stderr)
            self.assertTrue((root/".lake/build/lib/lean/ParallelMatrixAnalysis.olean").is_file())


if __name__ == "__main__":
    unittest.main()
