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
from editor.analysis_export import request

PROOF_MODULES = ("parallel_sum", "upsweep", "prefix_sum", "prefix_contract")
AUDIT_THEOREMS = (
    "ParallelSumAnalysis.call_contract_all",
    "ParallelSumAnalysis.correctness",
    "ParallelSumAnalysis.running_time_explicit",
    "ParallelSumAnalysis.running_time",
    "ParallelPrefix.upsweep_contract",
    "ParallelPrefix.downsweep_contract",
    "ParallelPrefix.call_contract",
    "ParallelPrefix.correctness",
    "ParallelPrefix.running_time_explicit",
    "ParallelPrefix.running_time",
    "ParallelPrefix.correctness_of_parallel_call",
    "ParallelPrefix.integer_call_contract",
)
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def compose_analysis():
    """Join the exact proof bodies, replacing local imports with those bodies."""
    imports, bodies = [], []
    for name in PROOF_MODULES:
        path = ROOT / "examples/parallel/analysis" / (name + ".lean")
        source = path.read_text(encoding="utf-8")
        body = []
        for line in source.splitlines():
            if line.startswith("import "):
                module = line.removeprefix("import ").strip()
                if module not in PROOF_MODULES and line not in imports:
                    imports.append(line)
            else:
                body.append(line)
        bodies.append("-- Source: examples/parallel/analysis/" + path.name + "\n" + "\n".join(body))
    audit = "\n".join("#print axioms " + name for name in AUDIT_THEOREMS)
    return "\n".join(imports) + "\n\n" + "\n\n".join(bodies) + "\n\n" + audit + "\n"


def unexpected_axioms(output):
    result = set()
    for group in re.findall(r"depends on axioms: \[([^\]]*)\]", output):
        result.update(name.strip() for name in group.split(",") if name.strip())
    return result - STANDARD_AXIOMS


def export_payload(analysis):
    return {"source": (ROOT / "examples/parallel/parallel.algo").read_text(encoding="utf-8"),
            "filename": "parallel.algo", "analysis": analysis,
            "analysis_filename": "ParallelAnalysis.lean"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-analysis", type=Path, help="write the checked combined Lean analysis")
    parser.add_argument("--export", type=Path, help="write a portable Lake project ZIP")
    args = parser.parse_args()
    analysis = compose_analysis()
    payload = export_payload(analysis)
    generated = compile_source(payload["source"], filename=payload["filename"])
    checked = check_analysis(generated.lean, analysis, generated.module, timeout=180)
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
