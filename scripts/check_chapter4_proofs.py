"""Check reusable Chapter 4 modules against freshly generated program semantics."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from algo2lean.checker import CheckResult, prepare_lean_environment, has_sorry_warning
from algo2lean.compiler import compile_source
from scripts.build_chapter4_analysis import MODULES as MATRIX_MODULES

MODULES = ("Substitution", "RecursionTree", "SubstitutionExamples", *MATRIX_MODULES,
           "RecurrenceApplications")
AUDIT_THEOREMS = (
    "Chapter4Substitution.upper_comparison",
    "Chapter4Substitution.lower_comparison",
    "Chapter4Substitution.exact_unique",
    "Chapter4RecursionTree.consistent_exists",
    "Chapter4RecursionTree.recurrence_tree_accounting",
    "Chapter4RecursionTree.Tree.total_eq_levels",
    "Chapter4RecursionTree.balanced_unroll",
    "Chapter4SubstitutionExamples.balancedCost_bounds",
    "Chapter4SubstitutionExamples.balancedCost_isTheta_nlogn",
    "MatrixStrassenVerified.every_execution_fresh",
    "Chapter4RecurrenceApplications.strassen_theta",
    "Chapter4RecurrenceApplications.terminates_with_bounds",
    "Chapter4RecurrenceApplications.runtime_via_tree",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def check_proofs(timeout=120):
    executable = shutil.which("lean")
    if executable is None:
        return CheckResult(False, False, "Lean was not found.")
    environment = prepare_lean_environment(timeout=timeout, executable=executable)
    source = ROOT / "examples/matrix_strassen.algo"
    generated = compile_source(source.read_text(encoding="utf-8"), filename=source.name)
    with tempfile.TemporaryDirectory(prefix="algo2lean-chapter4-") as directory:
        temporary = Path(directory)
        environment["LEAN_PATH"] = directory + os.pathsep + environment["LEAN_PATH"]
        sources = [(generated.module, generated.lean),
                   (generated.points_module, generated.points_lean)]
        sources += [(name, (ROOT / "proofs/chapter4" / (name + ".lean")).read_text(encoding="utf-8"))
                    for name in MODULES]
        for name, content in sources:
            path = temporary / (name + ".lean")
            path.write_text(content, encoding="utf-8")
            checked = subprocess.run(
                [executable, "--root=" + directory, "-o", str(path.with_suffix(".olean")), str(path)],
                cwd=ROOT, env=environment, capture_output=True, text=True, encoding="utf-8",
                errors="replace", timeout=timeout,
            )
            output = checked.stdout + checked.stderr
            if checked.returncode or has_sorry_warning(output):
                return CheckResult(False, True, name + ":\n" + output)
        audit = temporary / "Audit.lean"
        audit.write_text("import RecurrenceApplications\nimport SubstitutionExamples\n" +
                         "\n".join("#print axioms " + name for name in AUDIT_THEOREMS) + "\n",
                         encoding="utf-8")
        checked = subprocess.run([executable, str(audit)], cwd=ROOT, env=environment,
                                 capture_output=True, text=True, encoding="utf-8",
                                 errors="replace", timeout=timeout)
        output = checked.stdout + checked.stderr
        if checked.returncode:
            return CheckResult(False, True, output)
        for line in output.splitlines():
            if "depends on axioms:" in line:
                axioms = line.split("depends on axioms:", 1)[1].strip().strip("[]")
                unexpected = set(filter(None, (item.strip() for item in axioms.split(",")))) - STANDARD_AXIOMS
                if unexpected:
                    return CheckResult(False, True, "Unexpected proof assumptions: " + repr(unexpected))
        return CheckResult(True, True,
                           f"Lean accepted {len(MODULES)} Chapter 4 modules against fresh generated source.\n" + output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=120, help="timeout in seconds per Lean module")
    args = parser.parse_args()
    result = check_proofs(args.timeout)
    print(result.output)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
