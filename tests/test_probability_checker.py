"""Optional Mathlib checks are explicit, offline, and use current proof sources."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest
from unittest.mock import patch

from algo2lean.analysis import check_analysis
from algo2lean.checker import CheckResult
from algo2lean.compiler import compile_source
from algo2lean.modular import compile_project
from algo2lean import probability_checker as backend
from algo2lean.project_checker import check_project


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_READY = bool(shutil.which("lake") and
    (ROOT / "probability/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Distributions/Uniform.olean").is_file())


class ProbabilityCheckerTests(unittest.TestCase):
    def test_missing_dependencies_give_setup_instructions_without_starting_lake(self):
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(backend, "PROBABILITY_ROOT", Path(directory)), \
                patch.object(backend, "_run") as run:
            checked = backend.check_probability_sources({"Analysis": "import Algo2LeanProbability\n"})
        self.assertFalse(checked.ok)
        self.assertFalse(checked.available)
        self.assertIn("lake update", checked.output)
        self.assertIn("do not download", checked.output)
        run.assert_not_called()

    def test_invalid_names_missing_imports_and_cycles_fail_before_setup(self):
        cases = [
            ({"../Analysis": ""}, "Invalid Lean module"),
            ({"Mathlib.Fake": ""}, "conflicts with a Lean library"),
            ({"Algo.X": "", "algo.Y": ""}, "Case-colliding"),
            ({"Analysis": "import Missing\n"}, "No Lean source"),
            ({"A": "import B\n", "B": "import A\n"}, "import cycle"),
        ]
        with patch.object(backend, "_prepare") as prepare:
            for sources, expected in cases:
                with self.subTest(expected=expected):
                    checked = backend.check_probability_sources(sources)
                    self.assertFalse(checked.ok)
                    self.assertIn(expected, checked.output)
        prepare.assert_not_called()

    def test_import_order_and_fresh_user_proofs(self):
        compiled = []

        def run(command, environment, deadline, **kwargs):
            source = Path(command[-1])
            compiled.append(source.name)
            Path(command[command.index("-o") + 1]).write_bytes(b"checked object")
            self.assertTrue(environment["LEAN_PATH"].endswith(os.pathsep + "/prepared"))
            return subprocess.CompletedProcess(command, 0, "", "")

        sources = {"Analysis": "import Helper\nexample : Nat := answer\n",
                   "Helper": "import Algo2LeanProbability\ndef answer := 42\n"}
        with patch.object(backend, "_prepare", side_effect=lambda *_: ("/lean", {"LEAN_PATH": "/prepared"})), \
                patch.object(backend, "_run", side_effect=run):
            for module in ("Algo2LeanProbability", "Algo2LeanProbability.Call"):
                sources["Helper"] = "import " + module + "\ndef answer := 42\n"
                checked = backend.check_probability_sources(sources)
                self.assertTrue(checked.ok, checked.output)
                self.assertIn("probability modules and analysis", checked.output)
        self.assertEqual(compiled, ["Helper.lean", "Analysis.lean"] * 2)

    def test_unfinished_proof_is_rejected(self):
        def run(command, environment, deadline, **kwargs):
            return subprocess.CompletedProcess(command, 0,
                command[-1] + ":2:0: warning: declaration uses `sorry`\n", "")
        with patch.object(backend, "_prepare", return_value=("/lean", {"LEAN_PATH": "/prepared"})), \
                patch.object(backend, "_run", side_effect=run):
            checked = backend.check_probability_sources({"Analysis": "example : False := by sorry\n"})
        self.assertFalse(checked.ok)
        self.assertIn("incomplete", checked.output)
        self.assertIn("Analysis.lean:2:", checked.output)

    def test_lake_build_uses_existing_dependencies_and_prepends_current_runtime(self):
        calls = []

        def run(command, environment, deadline, **kwargs):
            calls.append((command, dict(environment)))
            if "env" in command:
                payload = {"lean": "/pinned/bin/lean", "environment": {
                    "LEAN_PATH": ".lake/build/lib/lean" + os.pathsep + ".lake/packages/mathlib/.lake/build/lib/lean"}}
                return subprocess.CompletedProcess(command, 0, json.dumps(payload), "")
            return subprocess.CompletedProcess(command, 0, "Build completed successfully.\n", "")

        with patch.object(backend, "_installed_dependencies", return_value={"Algo2LeanProbability.lean": "import Algo2LeanLib.Choice\n"}), \
                patch.object(backend.shutil, "which", side_effect=lambda name: "/lake" if name == "lake" else None), \
                patch.object(backend, "_run", side_effect=run), \
                patch.object(backend, "prepare_lean_environment", return_value={"LEAN_PATH": "/current/runtime"}) as prepare:
            executable, environment = backend._prepare({"Analysis": "import Algo2LeanProbability\n"}, time.monotonic() + 30)
        self.assertEqual(executable, "/pinned/bin/lean")
        self.assertEqual(calls[0][0][:4], ["/lake", "--no-cache", "build", "Algo2LeanProbability"])
        self.assertTrue(all("--no-cache" in command for command, _ in calls))
        self.assertFalse(any("update" in command for command, _ in calls))
        build_environment = calls[0][1]
        index = int(build_environment["GIT_CONFIG_COUNT"]) - 1
        self.assertEqual(build_environment["GIT_CONFIG_KEY_%d" % index], "protocol.allow")
        self.assertEqual(build_environment["GIT_CONFIG_VALUE_%d" % index], "never")
        self.assertTrue(environment["LEAN_PATH"].startswith("/current/runtime" + os.pathsep))
        self.assertIn("Algo2LeanLib.Choice", prepare.call_args.kwargs["modules"])

    def test_missing_pinned_toolchain_does_not_start_lake(self):
        with patch.object(backend, "_installed_dependencies", return_value={"Algo2LeanProbability.lean": "import Algo2LeanLib.Choice\n"}), \
                patch.object(backend.shutil, "which", side_effect=lambda name: "/elan/" + name), \
                patch.object(backend, "_run", return_value=subprocess.CompletedProcess([], 0, "leanprover/lean4:v4.0.0\n", "")) as run:
            checked = backend.check_probability_sources({"Analysis": "import Algo2LeanProbability\n"})
        self.assertFalse(checked.ok)
        self.assertFalse(checked.available)
        self.assertIn("do not download toolchains", checked.output)
        self.assertEqual(run.call_args.args[0], ["/elan/elan", "toolchain", "list"])

    def test_single_analysis_routes_only_explicit_probability_imports(self):
        accepted = CheckResult(True, True, "accepted optional analysis")
        with patch.object(backend, "check_mathlib_sources", return_value=accepted) as check:
            result = check_analysis("core", "import DiceProbability\n", "Dice", probability_lean="companion")
            self.assertEqual(result, accepted)
            self.assertEqual(check.call_args.args[0], {
                "Dice": "core", "DiceProbability": "companion", "Analysis": "import DiceProbability\n"})
            check.reset_mock()
            with patch("algo2lean.analysis.shutil.which", return_value=None):
                core = check_analysis("core", "import Dice\n", "Dice", probability_lean="companion")
            self.assertFalse(core.available)
            check.assert_not_called()
            missing = check_analysis("core", "import DiceProbability\n", "Dice")
            self.assertFalse(missing.ok)
            self.assertIn("No generated probability companion", missing.output)
            check.assert_not_called()

    def test_mathlib_import_routes_without_a_randomized_algorithm(self):
        with patch.object(backend, "check_mathlib_sources", return_value=CheckResult(True, True, "checked")) as check:
            result = check_analysis("core", "import Mathlib.Data.Nat.Basic\n", "Core")
        self.assertTrue(result.ok)
        self.assertNotIn("CoreProbability", check.call_args.args[0])

    def test_project_probability_and_mathlib_imports_select_optional_backend(self):
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project("main", root=directory, sources={
                "main": "def sample() -> Int:\n    return randint(0, 2)\n"})
            with patch.object(backend, "check_mathlib_sources", return_value=CheckResult(True, True, "checked")) as check, \
                    patch("algo2lean.project_checker.shutil.which", return_value="/lean"):
                result = check_project(compiled, analysis="import Algo.main.Probability\n")
                self.assertTrue(result.ok)
                self.assertIn("Algo.main.Probability", check.call_args.args[0])
                result = check_project(compiled, analysis="import Mathlib.Data.Nat.Basic\n")
                self.assertTrue(result.ok)
                self.assertNotIn("Algo.main.Probability", check.call_args.args[0])


@unittest.skipUnless(MATHLIB_READY, "The optional pinned Mathlib cache is not installed")
class ProbabilityLeanTests(unittest.TestCase):
    def test_generated_die_law_and_analysis_diagnostics(self):
        compiled = compile_source("def die() -> Int:\n    return randint(1, 7)\n", module="Die")
        proof = """import DieProbability
open Algo2LeanCore Algo2LeanGenerated
example : Configuration → Choice Configuration := nextChoice
example (before after : Configuration) :
    (nextChoice before).Allows after ↔ Step before after := choice_step
#check die.law
#check die.outputProbability
#check die.expectedCost
"""
        checked = check_analysis(compiled.lean, proof, compiled.module,
                                 probability_lean=compiled.probability_lean)
        self.assertTrue(checked.ok, checked.output)
        self.assertIn("probability modules and analysis", checked.output)
        rejected = check_analysis(compiled.lean, "import DieProbability\nexample : False := by decide\n",
                                  compiled.module, probability_lean=compiled.probability_lean)
        self.assertFalse(rejected.ok)
        self.assertIn("Analysis.lean:2:", rejected.output)
        unfinished = check_analysis(compiled.lean, "import DieProbability\nexample : False := by sorry\n",
                                    compiled.module, probability_lean=compiled.probability_lean)
        self.assertFalse(unfinished.ok)
        self.assertIn("incomplete", unfinished.output)

    def test_project_probability_laws_reuse_recursive_group_companions(self):
        with tempfile.TemporaryDirectory() as directory:
            compiled = compile_project("main", root=directory, sources={
                "base": "def sample() -> Int:\n    return randint(0, 2)\n",
                "left": "from right import recurse\nfrom base import sample\ndef run(n: Int) -> Int:\n    if n <= 0:\n        return sample()\n    return recurse(n - 1)\n",
                "right": "from left import run\ndef recurse(n: Int) -> Int:\n    return run(n)\n",
                "main": "from left import run\ndef sample() -> Int:\n    return run(2)\n",
            })
            checked = check_project(compiled, analysis="""import Algo.main.Probability
import Algo.left.Probability
import Algo.right.Probability
#check Algo.main.sample.law
#check Algo.left.run.outputProbability
#check Algo.right.recurse.expectedCost
""")
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
