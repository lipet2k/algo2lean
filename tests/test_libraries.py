"""Example proofs remain separate modules when reused by another program."""

from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from algo2lean.analysis import check_analysis, analysis_support_sources
from algo2lean.checker import LeanSetupError, shared_imports
from algo2lean.compiler import CompileError, compile_source
from algo2lean.libraries import example_library_source


ROOT = Path(__file__).resolve().parents[1]


class LibrarySourceTests(unittest.TestCase):
    def test_default_compile_is_unchanged_and_namespaced_points_are_separate(self):
        source = "def f(x: Int) -> Int:\n    # @value\n    return x\n"
        ordinary = compile_source(source, module="ExampleGenerated")
        library = compile_source(source, module="ExampleGenerated", namespace="ExampleLibrary")
        self.assertIsNone(ordinary.namespace)
        self.assertEqual(library.namespace, "ExampleLibrary")
        # Only the root-qualified public bridge references acquire the wrapper.
        self.assertIn(ordinary.program_lean,
                      library.program_lean.replace("_root_.«ExampleLibrary».", "_root_."))
        self.assertNotIn("f.At.value", library.program_lean)
        self.assertIn("namespace «ExampleLibrary»", library.points_lean)
        renamed = compile_source(source.replace("@value", "@renamed"),
                                 module="ExampleGenerated", namespace="ExampleLibrary")
        self.assertEqual(library.lean, renamed.lean)

    def test_namespace_rejects_source_syntax_and_runtime_collisions(self):
        for namespace in ("../bad", "Name\nend", "Algo2Lean", "Algo2LeanGenerated", "Algo2LeanCore", 4):
            with self.subTest(namespace=namespace), self.assertRaises(CompileError):
                compile_source("def f() -> Int:\n    return 0\n", namespace=namespace)

    def test_proof_library_redirects_imports_and_keeps_the_proof_body(self):
        path, text = example_library_source(ROOT, "Algo2LeanExamples.Factorial")
        proof = text.decode()
        self.assertEqual(path.as_posix(), "Algo2LeanExamples/Factorial.lean")
        self.assertIn("import Algo2LeanExamples.FactorialGenerated", proof)
        self.assertIn("open FactorialLibrary FactorialLibrary.Algo2LeanGenerated", proof)
        original = (ROOT / "examples/analysis/factorial.lean").read_text()
        self.assertIn(original[original.index("namespace FactorialAnalysis"):], proof)
        self.assertEqual(shared_imports("import «Algo2LeanExamples».«FactorialGenerated»\n"),
                         ("Algo2LeanExamples.FactorialGenerated",))

    def test_example_source_and_analysis_changes_change_library_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "examples/analysis").mkdir(parents=True)
            source = root / "examples/tiny.algo"
            proof = root / "examples/analysis/tiny.lean"
            source.write_text("def f() -> Int:\n    return 1\n")
            proof.write_text("import TinyGenerated\nexample : True := .intro\n")
            before = example_library_source(root, "Algo2LeanExamples.TinyGenerated")[1]
            source.write_text("def f() -> Int:\n    return 2\n")
            after = example_library_source(root, "Algo2LeanExamples.TinyGenerated")[1]
            self.assertNotEqual(before, after)
            before_proof = example_library_source(root, "Algo2LeanExamples.Tiny")[1]
            proof.write_text(proof.read_text() + "example : 1 = 1 := rfl\n")
            self.assertNotEqual(before_proof, example_library_source(root, "Algo2LeanExamples.Tiny")[1])

    def test_import_redirection_handles_quoted_multiline_and_commented_headers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "examples/analysis").mkdir(parents=True)
            (root / "examples/tiny.algo").write_text("def f() -> Int:\n    return 0\n")
            proof = root / "examples/analysis/tiny.lean"
            for header in ("import «TinyGenerated»", "import TinyGenerated -- comment",
                           "import Std\nimport\n TinyGenerated", "  import TinyGenerated",
                           "/- import Fake -/\nimport TinyGenerated",
                           "import TinyGenerated /- trailing\n/- nested -/ comment -/"):
                with self.subTest(header=header):
                    proof.write_text(header + "\nexample : True := .intro\n")
                    _, library = example_library_source(root, "Algo2LeanExamples.Tiny")
                    self.assertIn("Algo2LeanExamples.TinyGenerated", shared_imports(library.decode()))
            proof.write_text("import TinyGenerated\n/-!\nimport Fake\n-/\nexample : True := .intro\n")
            _, library = example_library_source(root, "Algo2LeanExamples.Tiny")
            self.assertLess(library.index(b"open TinyLibrary"), library.index(b"/-!"))
            proof.write_text("import Std\nexample : True := .intro\n")
            with self.assertRaisesRegex(ValueError, "must import its generated"):
                example_library_source(root, "Algo2LeanExamples.Tiny")
            (root / "examples/tiny.algo").write_text("def broken(")
            with self.assertRaisesRegex(ValueError, "tiny.algo:"):
                example_library_source(root, "Algo2LeanExamples.TinyGenerated")

    def test_unknown_or_ambiguous_examples_are_rejected(self):
        with self.assertRaises(ValueError):
            example_library_source(ROOT, "Algo2LeanExamples.Missing")
        with self.assertRaises(ValueError):
            example_library_source(ROOT, "Algo2LeanExamples.../private")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "examples").mkdir()
            for filename in ("tiny-test.algo", "tiny_test.algo"):
                (root / "examples" / filename).write_text("def f() -> Int:\n    return 0\n")
            with self.assertRaises(ValueError):
                example_library_source(root, "Algo2LeanExamples.TinyTest")

    def test_support_modules_load_only_requested_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            support = root / "examples/analysis/support"
            support.mkdir(parents=True)
            (support / "Adapter.lean").write_text("import Helper\nimport CurrentGenerated\n")
            (support / "Helper.lean").write_text("import Algo2LeanLib.Embedding\n")
            (support / "Unused.lean").write_text("import Missing\n")
            with patch("algo2lean.analysis.ROOT", root):
                sources = analysis_support_sources("import Adapter\n", "CurrentGenerated")
                self.assertEqual(list(sources), ["Helper", "Adapter"])
                (support / "Helper.lean").write_text("import Adapter\n")
                with self.assertRaisesRegex(LeanSetupError, "import cycle"):
                    analysis_support_sources("import Adapter\n", "CurrentGenerated")
                with self.assertRaisesRegex(LeanSetupError, "conflicts"):
                    analysis_support_sources("import Adapter\n", "Adapter")


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class CheckedLibraryTests(unittest.TestCase):
    def test_another_algorithm_imports_an_existing_checked_proof(self):
        generated = compile_source("def unrelated(x: Int) -> Int:\n    return x + 1\n",
                                   module="UnrelatedGenerated")
        analysis = """import UnrelatedGenerated
import Algo2LeanExamples.Factorial
example (n : Int) :
    FactorialLibrary.factorial.Returns n (FactorialAnalysis.factorialValue n.toNat) :=
      FactorialAnalysis.output n
"""
        result = check_analysis(generated.lean, analysis, generated.module)
        self.assertTrue(result.ok, result.output)

    def test_support_contract_is_rechecked_against_current_algorithm(self):
        source = "def identity(x: Int) -> Int:\n    return x\n"
        adapter = """import IdentityGenerated
open Algo2LeanCore Algo2LeanGenerated
theorem identity_contract (heap : Heap) (x : Int) :
    identity.Call heap x heap x := by
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.identity_pc2 _ _ _)
  exact Reaches.single (Step.identity_pc1 _ _ _)
"""
        analysis = """import IdentityGenerated
import IdentityContract
example (heap : Algo2LeanGenerated.Heap) (x : Int) :
    identity.Call heap x heap x := identity_contract heap x
"""
        with patch("algo2lean.analysis.analysis_support_sources", return_value={"IdentityContract": adapter}):
            compiled = compile_source(source, module="IdentityGenerated")
            checked = check_analysis(compiled.lean, analysis, compiled.module)
            self.assertTrue(checked.ok, checked.output)
            changed = compile_source(source.replace("return x", "return x + 1"), module="IdentityGenerated")
            rejected = check_analysis(changed.lean, analysis, changed.module)
            self.assertFalse(rejected.ok)
            self.assertIn("IdentityContract.lean:", rejected.output)


if __name__ == "__main__":
    unittest.main()
