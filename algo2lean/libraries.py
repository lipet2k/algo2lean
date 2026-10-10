"""Import separately checked repository example proofs without copying them.

Each example library has three distinct Lean modules: generated definitions,
named points, and handwritten analysis. Their contents are snapshots of the
versioned source and proof, and are included in the checker's cache key.
"""

from pathlib import Path
import re

from .compiler import CompileError, compile_source
from .modules import generated_module_name


def example_library_source(root: Path, module: str):
    """Resolve a safe Algo2LeanExamples import to its current generated text."""
    match = re.fullmatch(r"Algo2LeanExamples\.([A-Za-z][A-Za-z0-9_]*)", module)
    if match is None:
        raise ValueError("Invalid example library module: %s" % module)
    candidates = []
    for path in (root / "examples").glob("*.algo"):
        name = generated_module_name(path.name).removesuffix("Generated")
        for part in ("", "Generated", "Points"):
            if module == "Algo2LeanExamples." + name + part:
                candidates.append((path, name, part))
    if len(candidates) != 1:
        raise ValueError("Example library %s must identify exactly one repository example." % module)
    source, name, part = candidates[0]
    namespace = name + "Library"
    generated_module = "Algo2LeanExamples." + name + "Generated"
    points_module = "Algo2LeanExamples." + name + "Points"
    try:
        generated = compile_source(source.read_text(encoding="utf-8"), filename=source.name,
                                   namespace=namespace)
    except CompileError as error:
        raise ValueError("%s:%d:%d: %s" % (source.name, error.line, error.column, error.message)) from error
    if part == "Generated":
        text = generated.lean
    elif part == "Points":
        text = "import " + generated_module + "\n" + generated.points_lean.split("\n", 1)[1]
    else:
        proof = (root / "examples" / "analysis" / (source.stem + ".lean")).read_text(encoding="utf-8")
        # Companion analyses use standalone Generated and Points imports. Redirect
        # only those exact module names into the example library namespace.
        from .checker import after_import_header, redirect_imports
        proof, redirected = redirect_imports(proof, {generated.points_module: points_module,
                                                     generated.module: generated_module})
        if not redirected:
            raise ValueError("The example analysis must import its generated definitions.")
        position = after_import_header(proof)
        text = proof[:position] + "\nopen %s %s.Algo2LeanGenerated\n" % (namespace, namespace) + proof[position:]
    return Path(*module.split(".")).with_suffix(".lean"), text.encode("utf-8")
