"""Check a separate analysis module importing the generated algorithm."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

from .checker import CheckResult, LeanSetupError, prepare_lean_environment, shared_imports, lean_imports, has_sorry_warning
from .modules import generated_module_name, validate_module_name


ROOT = Path(__file__).resolve().parent.parent


def analysis_support_sources(analysis: str, module: str) -> dict:
    """Load requested proof adapters from packaged sources, in dependency order.

    Adapters are checked against this request's generated module, never a
    previously compiled application. They can import cached component proofs.
    Only the fixed repository support directory is searched, not user paths.
    """
    sources, visiting = {}, set()
    reserved = {module.casefold(), (module + "Points").casefold(),
                (module + "Probability").casefold(), "analysis", "algorithmanalysis"}

    def visit(name):
        if "." in name or name in sources:
            return
        path = ROOT / "examples" / "analysis" / "support" / (name + ".lean")
        if not path.is_file():
            return
        if name.casefold() in reserved:
            raise LeanSetupError("Analysis support module '%s' conflicts with the current algorithm." % name)
        if name in visiting:
            raise LeanSetupError("Analysis support import cycle at %s." % name)
        visiting.add(name)
        source = path.read_text(encoding="utf-8")
        for dependency in lean_imports(source):
            visit(dependency)
        visiting.remove(name)
        sources[name] = source

    for dependency in lean_imports(analysis):
        visit(dependency)
    return sources


def check_analysis(generated: str, analysis: str, module: str, timeout: float = 120,
                   *, points_lean: str = None, probability_lean: str = None) -> CheckResult:
    """Build the algorithm and optional named points, then check an importing file.

    The files are never concatenated. Diagnostic line numbers refer to the
    analysis itself. Reject unfinished proofs when Lean reports a `sorry`
    warning. Success otherwise means acceptance under the analysis's own Lean
    options and assumptions, not an independent proof-completeness audit.
    In particular, `set_option warn.sorry false` suppresses that diagnostic.
    """
    validate_module_name(module)
    deadline = time.monotonic() + timeout
    try:
        support = analysis_support_sources(analysis, module)
        from .probability_checker import check_mathlib_sources, needs_mathlib
        probability_requested = module + "Probability" in lean_imports(analysis, *support.values())
        if probability_requested or needs_mathlib(generated, points_lean or "", analysis, *support.values()):
            if probability_requested and not probability_lean:
                return CheckResult(False, True, "No generated probability companion '%sProbability' was supplied." % module)
            sources = {module: generated}
            if points_lean is not None:
                sources[module + "Points"] = points_lean
            if probability_requested:
                sources[module + "Probability"] = probability_lean
            sources.update(support)
            proof_module = "AlgorithmAnalysis" if module.casefold() == "analysis" else "Analysis"
            sources[proof_module] = analysis
            checked = check_mathlib_sources(sources, timeout=max(0, deadline - time.monotonic()))
            if proof_module != "Analysis":
                checked = CheckResult(checked.ok, checked.available,
                                      checked.output.replace(proof_module + ".lean:", "Analysis.lean:"))
            return checked
        executable = shutil.which("lean")
        if executable is None:
            return CheckResult(False, False, "Lean was not found. Install Lean 4 and restart the editor.")
        environment = prepare_lean_environment(timeout=timeout, executable=executable,
            modules=shared_imports(generated, analysis, points_lean or "", *support.values()))
        with tempfile.TemporaryDirectory(prefix="algo2lean-analysis-") as directory:
            temporary = Path(directory)
            definition = temporary / (module + ".lean")
            proof = temporary / "Analysis.lean"
            # A user-selected core name must not overwrite the proof file.
            if module.casefold() == "analysis":
                proof = temporary / "AlgorithmAnalysis.lean"
            definition.write_text(generated, encoding="utf-8")
            proof.write_text(analysis, encoding="utf-8")
            environment["LEAN_PATH"] = directory + os.pathsep + environment["LEAN_PATH"]
            messages = []
            files = [(definition, ["-o", str(definition.with_suffix(".olean"))])]
            if points_lean is not None:
                points = temporary / (module + "Points.lean")
                points.write_text(points_lean, encoding="utf-8")
                files.append((points, ["-o", str(points.with_suffix(".olean"))]))
            for name, text in support.items():
                path = temporary / (name + ".lean")
                path.write_text(text, encoding="utf-8")
                files.append((path, ["-o", str(path.with_suffix(".olean"))]))
            files.append((proof, []))
            for path, options in files:
                completed = subprocess.run(
                    [executable, "--root=" + directory, *options, str(path)],
                    cwd=ROOT, env=environment, capture_output=True, text=True,
                    encoding="utf-8", errors="replace", timeout=max(0, deadline - time.monotonic()),
                )
                output = (completed.stdout + completed.stderr).replace(str(temporary) + os.sep, "")
                if path == proof and proof.name != "Analysis.lean":
                    output = output.replace(proof.name + ":", "Analysis.lean:")
                if output.strip():
                    messages.append(output.strip())
                if completed.returncode != 0:
                    return CheckResult(False, True, "\n".join(messages)[:20000])
                if has_sorry_warning(output):
                    return CheckResult(False, True, "Analysis is incomplete: replace every sorry with a proof.\n" + output[:19000])
            messages.append(
                "Lean accepted the analysis with its declared assumptions and options."
            )
            return CheckResult(True, True, "\n".join(messages))
    except LeanSetupError as error:
        return CheckResult(False, error.available, str(error))
    except subprocess.TimeoutExpired:
        return CheckResult(False, True, "Analysis checking timed out after %g seconds." % timeout)
    except (OSError, UnicodeError) as error:
        return CheckResult(False, True, "Could not check the analysis: %s" % error)
