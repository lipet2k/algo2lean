#!/usr/bin/env python3
"""Check the source-connected parallel proofs and optionally export one analysis.

The committed proofs remain separate source files. Their composition uses the
same single-file editor API that users export; no generated proof copy is stored
in the repository.
"""

import argparse
import base64
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from algo2lean import compile_source
from algo2lean.analysis import check_analysis
from algo2lean.editor_examples import parallel_example_analysis
from editor.analysis_export import request

AUDIT_THEOREMS = (
    "ParallelMatrixDot.call_contract",
    "ParallelMatrixColumns.call_contract",
    "ParallelMatrixRows.call_contract",
    "ParallelMatrixAllocationAnalysis.call_contract",
    "ParallelMatrixIntoAnalysis.call_contract",
    "ParallelMatrixIntoAnalysis.inputs_preserved",
    "ParallelMatrixIntoAnalysis.correctness",
    "ParallelMatrixIntoAnalysis.correctness_of_parallel_call",
    "ParallelMatrixIntoAnalysis.running_time_explicit",
    "ParallelMatrixIntoAnalysis.running_time",
    "ParallelMatrixPublic.call_contract",
    "ParallelMatrixPublic.correctness",
    "ParallelMatrixPublic.correctness_of_parallel_call",
    "ParallelMatrixPublic.running_time_explicit",
    "ParallelMatrixPublic.running_time",
)

STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def compose_analysis():
    """Join the exact proof bodies, replacing local imports with those bodies."""
    analysis = parallel_example_analysis("parallel_matrix")
    audit = "\n".join("#print axioms " + name for name in AUDIT_THEOREMS)
    return analysis + "\n" + audit + "\n"


def unexpected_axioms(output):
    result = set()
    for group in re.findall(r"depends on axioms: \[([^\]]*)\]", output):
        result.update(name.strip() for name in group.split(",") if name.strip())
    return result - STANDARD_AXIOMS


def export_payload(analysis):
    return {"source": (ROOT / "examples/parallel_matrix/parallel_matrix.algo").read_text(encoding="utf-8"),
            "filename": "parallel_matrix.algo", "analysis": analysis,
            "analysis_filename": "ParallelMatrixAnalysis.lean"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-analysis", type=Path, help="write the checked combined Lean analysis")
    parser.add_argument("--export", type=Path, help="write a portable Lake project ZIP")
    args = parser.parse_args()
    analysis = compose_analysis()
    payload = export_payload(analysis)
    generated = compile_source(payload["source"], filename=payload["filename"])
    checked = check_analysis(generated.lean, analysis, generated.module, timeout=300)
    print(checked.output)
    axioms = unexpected_axioms(checked.output)
    if not checked.ok or axioms:
        if axioms:
            print("Unexpected proof axioms: " + ", ".join(sorted(axioms)), file=sys.stderr)
        return 1
    if args.write_analysis:
        args.write_analysis.write_text(analysis, encoding="utf-8")
        print("Wrote " + str(args.write_analysis))
    if args.export:
        response = request("/api/analysis-export", payload)
        if response["status"] != 200:
            print(response, file=sys.stderr)
            return 1
        args.export.write_bytes(base64.b64decode(response["body"], validate=True))
        print("Wrote " + str(args.export))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
