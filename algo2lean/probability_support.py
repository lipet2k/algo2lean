"""Resolve optional Mathlib libraries without importing or installing Mathlib."""

from pathlib import Path
import re

from .checker import lean_imports

ROOT = Path(__file__).resolve().parent.parent
OPTIONAL_LIBRARIES = frozenset({"Algo2LeanReal", "Algo2LeanProbability"})


def is_optional_library(name):
    """Recognize a module in an optional library, including its submodules."""
    return name.split(".")[0] in OPTIONAL_LIBRARIES


def _source_path(name):
    return Path(*name.split(".")).with_suffix(".lean")


def needs_mathlib(sources):
    """Only an explicit optional-library or Mathlib import selects Mathlib."""
    return any(is_optional_library(name) or name.split(".")[0] == "Mathlib"
               for source in sources for name in lean_imports(source))


def required_libraries(sources):
    """Return optional library roots, including their optional dependencies."""
    pending = {name for source in sources for name in lean_imports(source)
               if is_optional_library(name)}
    selected = set()
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        selected.add(name)
        source = (ROOT / "probability" / _source_path(name)).read_text(encoding="utf-8")
        pending.update(dependency for dependency in lean_imports(source)
                       if is_optional_library(dependency) and dependency not in selected)
    return tuple(sorted(selected))


def optional_sources(sources):
    """Package only optional libraries actually imported by these sources."""
    return {_source_path(name).as_posix():
            (ROOT / "probability" / _source_path(name)).read_text(encoding="utf-8")
            for name in required_libraries(sources)}


def needs_probability(sources):
    """Compatibility name for selecting the optional Mathlib backend."""
    return needs_mathlib(sources)


def probability_sources():
    """Shared source, separate from generated code and the external dependency."""
    return {"Algo2LeanProbability.lean":
            (ROOT / "probability" / "Algo2LeanProbability.lean").read_text(encoding="utf-8")}


def mathlib_requirement():
    """Use the same immutable Mathlib revision as the development proof project."""
    config = (ROOT / "probability" / "lakefile.toml").read_text(encoding="utf-8")
    match = re.search(r'^rev = "([0-9a-f]{40})"$', config, re.MULTILINE)
    if match is None:
        raise ValueError("The optional library project must pin an exact Mathlib commit.")
    return ('\n[[require]]\nname = "mathlib"\n'
            'git = "https://github.com/leanprover-community/mathlib4.git"\n'
            'rev = "%s"\n' % match[1])


SETUP_INSTRUCTIONS = (
    "This package uses optional Mathlib support and a pinned Mathlib revision. "
    "Run `lake update` and `lake exe cache get` once to install the matching "
    "dependencies, then `lake build`. The download includes the Algo2Lean shared "
    "library sources and dependency configuration; Mathlib itself is fetched by Lake.\n"
)
