"""CLRS parallel merge/sort execution, generated proofs, and portable packages.

Python regressions check concrete values and storage boundaries. General
correctness and work/span guarantees are checked separately by Lean against
freshly generated definitions of the same source.
"""

import ast
from bisect import bisect_left
import itertools
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from algo2lean import compile_source
from algo2lean.analysis import check_analysis
from editor.analysis_export import request as analysis_request
from scripts.check_parallel_merge_examples import compose_analysis, export_payload, unexpected_axioms
from tests.test_analysis_export import unpack
from tests.test_parallel import MathematicalSequence

ROOT = Path(__file__).resolve().parents[1]


def execution_functions():
    source = (ROOT / "examples/parallel_merge/parallel_merge.algo").read_text()
    compile_source(source, filename="parallel_merge.algo")

    class DelayChildren(ast.NodeTransformer):
        def visit_Call(self, node):
            node = self.generic_visit(node)
            if isinstance(node.func, ast.Name) and node.func.id == "fork_join":
                node.args = [ast.copy_location(ast.Call(func=ast.Name(id="_defer", ctx=ast.Load()),
                    args=[child.func, *child.args], keywords=[]), child) for child in node.args]
            return node

    tree = ast.fix_missing_locations(DelayChildren().visit(ast.parse(source)))
    namespace = {"Int": int, "Seq": MathematicalSequence, "const": MathematicalSequence,
                 "_defer": lambda fn, *args: lambda: fn(*args),
                 "fork_join": lambda left, right: (left(), right())}
    exec(compile(tree, "parallel_merge.algo", "exec"), namespace)
    return namespace


def sequence(values, lo=0, default=-100003):
    result = MathematicalSequence(default)
    for i, value in enumerate(values):
        result[lo+i] = value
    return result


class ParallelMergeExecutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.functions = execution_functions()

    def test_binary_search_lower_bound_with_duplicates(self):
        for n in range(8):
            for values in itertools.combinations_with_replacement((-2, 0, 3), n):
                for lo in (-11, 0, 13):
                    a = sequence(values, lo)
                    before = dict(a.cells)
                    for target in (-5, -2, -1, 0, 1, 3, 7):
                        self.assertEqual(self.functions["binary_search"](a, lo, n, target),
                                         bisect_left(values, target))
                    self.assertEqual(a.cells, before)

    def check_merge(self, left, right, lo1, lo2, dst):
        a = sequence(left, lo1)
        for i, value in enumerate(right):
            a[lo2+i] = value
        before = dict(a.cells)
        out = sequence([801, 802, 803], dst-3, default=947)
        out[dst+len(left)+len(right)] = 919
        out_before = dict(out.cells)
        returned = self.functions["p_merge"](a, lo1, len(left), lo2, len(right), out, dst)
        self.assertEqual(returned, 0)
        self.assertEqual([out[dst+i] for i in range(len(left)+len(right))], sorted(left+right))
        self.assertEqual(a.cells, before)
        self.assertEqual(out.default, 947)
        self.assertEqual({i:v for i,v in out.cells.items() if not dst <= i < dst+len(left)+len(right)},
                         {i:v for i,v in out_before.items() if not dst <= i < dst+len(left)+len(right)})
        result = self.functions["parallel_merge"](a, lo1, len(left), lo2, len(right))
        self.assertIsNot(result, a)
        self.assertEqual([result[i] for i in range(len(left)+len(right))], sorted(left+right))
        self.assertEqual(result[-1], 0)
        self.assertEqual(result[len(left)+len(right)], 0)
        self.assertEqual(a.cells, before)

    def test_exhaustive_sorted_merges_and_preallocated_output_frames(self):
        arrays = [list(xs) for n in range(6)
                  for xs in itertools.combinations_with_replacement((-2, 0, 3), n)]
        for left in arrays:
            for right in arrays:
                for lo1, lo2, dst in ((-19, 7, -4), (2, 29, 11), (23, -17, 0)):
                    self.check_merge(left, right, lo1, lo2, dst)

    def test_read_only_input_intervals_may_overlap(self):
        values = [-7, -3, -3, 0, 4, 8]
        a = sequence(values, -8)
        before = dict(a.cells)
        for lo1, n1, lo2, n2 in ((-8, 6, -8, 6), (-8, 4, -6, 4), (-6, 3, -8, 5)):
            out = self.functions["parallel_merge"](a, lo1, n1, lo2, n2)
            expected = sorted([a[lo1+i] for i in range(n1)]+[a[lo2+i] for i in range(n2)])
            self.assertEqual([out[i] for i in range(n1+n2)], expected)
            self.assertEqual(a.cells, before)

    def check_sort(self, values, lo):
        a = sequence(values, lo)
        a[lo-1], a[lo+len(values)] = 107, -109
        before = dict(a.cells)
        result = self.functions["parallel_merge_sort"](a, lo, len(values))
        self.assertIsNot(result, a)
        self.assertEqual([result[lo+i] for i in range(len(values))], sorted(values))
        self.assertEqual(a.cells, before)
        for i in (lo-5, lo-1, lo+len(values), lo+len(values)+5):
            self.assertEqual(result[i], 0)

    def test_exhaustive_sort_with_duplicates_and_shifted_intervals(self):
        for n in range(8):
            for values in itertools.product((-2, 0, 3), repeat=n):
                for lo in (-5, 0, 11):
                    self.check_sort(list(values), lo)

    def test_sort_preserves_prepopulated_buffer_exteriors(self):
        for n in range(15):
            lo = -9
            values = [(i*7)%5-2 for i in range(n)]
            a = sequence(values, lo)
            before = dict(a.cells)
            out = sequence(list(range(45)), lo-12, default=123)
            scratch = sequence(list(range(-45, 0)), lo-12, default=-321)
            old_out, old_scratch = dict(out.cells), dict(scratch.cells)
            self.assertEqual(self.functions["sort_into"](a, lo, n, out, scratch), 0)
            self.assertEqual([out[lo+i] for i in range(n)], sorted(values))
            self.assertEqual(a.cells, before)
            for buf, old in ((out,old_out),(scratch,old_scratch)):
                self.assertEqual({i:v for i,v in buf.cells.items() if not lo <= i < lo+n},
                                 {i:v for i,v in old.items() if not lo <= i < lo+n})

    def test_larger_uneven_inputs_and_mathematical_integer_values(self):
        for n in (31, 64, 65, 127):
            values = [(-1 if i%2 else 1)*(10**80+(i%13)) for i in range(n)]
            self.check_sort(values, -103)
            self.check_merge(sorted(values[:n//3]), sorted(values[n//3:]), -301, 83, -47)


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class ParallelMergeProofTests(unittest.TestCase):
    def test_complete_source_correctness_and_runtime_contracts(self):
        analysis = compose_analysis()
        for path in (ROOT / "examples/parallel_merge/analysis").glob("*.lean"):
            self.assertNotRegex(path.read_text(), r"\b(?:sorry|admit)\b", str(path))
        payload = export_payload(analysis)
        generated = compile_source(payload["source"], filename=payload["filename"])
        checked = check_analysis(generated.lean, analysis, generated.module, timeout=240)
        self.assertTrue(checked.ok, checked.output)
        self.assertFalse(unexpected_axioms(checked.output), checked.output)

    @unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
    def test_complete_analysis_download_builds_in_isolation(self):
        files = unpack(analysis_request("/api/analysis-export", export_payload(compose_analysis())))
        for name in ("ParallelMergeGenerated.lean", "Algo2LeanLib/Parallel.lean",
                     "Algo2LeanLib/ParallelMergeSpec.lean", "Algo2LeanLib/ParallelMergeCost.lean"):
            self.assertIn(name, files)
        self.assertNotIn(b'name = "mathlib"', files["lakefile.toml"])
        with tempfile.TemporaryDirectory(prefix="algo2lean-parallel-merge-export-") as directory:
            root = Path(directory)
            for name, contents in files.items():
                path = root/name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(contents)
            environment = dict(os.environ)
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            built = subprocess.run([shutil.which("lake"), "--no-cache", "build"], cwd=root,
                env=environment, capture_output=True, text=True, timeout=240)
            self.assertEqual(built.returncode, 0, built.stdout+built.stderr)
            self.assertNotIn("declaration uses `sorry`", built.stdout+built.stderr)
            self.assertTrue((root/".lake/build/lib/lean/ParallelMergeAnalysis.olean").is_file())


if __name__ == "__main__":
    unittest.main()
