"""Check reusable Chapter 4 modules against freshly generated program semantics."""

import argparse
import os
from pathlib import Path
import re
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
    "MatrixStrassenVerified.call",
    "MatrixStrassenVerified.correctness_and_running_time",
    "MatrixStrassenVerified.every_execution_fresh",
    "MatrixStrassenVerified.every_execution_fresh_rows",
    "Chapter4RecurrenceApplications.strassen_theta",
    "Chapter4RecurrenceApplications.terminates_with_bounds",
    "Chapter4RecurrenceApplications.runtime_via_tree",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def audit_assumptions(output, theorems=AUDIT_THEOREMS):
    """Return a diagnostic unless every requested theorem has allowed axioms."""
    reports = dict(re.findall(
        r"^'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", output, re.MULTILINE,
    ))
    without_axioms = set(re.findall(
        r"^'([^'\n]+)' does not depend on any axioms\s*$", output, re.MULTILINE,
    ))
    for theorem in theorems:
        if theorem not in reports:
            if theorem in without_axioms:
                continue
            return "Missing axiom report for " + theorem + "\n" + output
        axioms = {item.strip() for item in reports[theorem].split(",") if item.strip()}
        unexpected = axioms - STANDARD_AXIOMS
        if unexpected:
            return "Unexpected proof assumptions for " + theorem + ": " + repr(sorted(unexpected))
    return None


def check_proofs(timeout=120):
    executable = shutil.which("lean")
    if executable is None:
        return CheckResult(False, False, "Lean was not found.")
    environment = prepare_lean_environment(timeout=timeout, executable=executable,
                                           modules=("Algo2LeanLib.MatrixHeap", "Algo2LeanLib.CallCost"))
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
        diagnostic = audit_assumptions(output)
        if diagnostic:
            return CheckResult(False, True, diagnostic)
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
