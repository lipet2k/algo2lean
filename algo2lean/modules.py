"""Validate generated Lean file identities and derive single-file module names."""

import re


def generated_module_name(filename: str) -> str:
    """A predictable Lean module name, also used for editor exports."""
    stem = filename.replace("\\", "/").rsplit("/", 1)[-1].rsplit(".", 1)[0]
    words = re.findall(r"[A-Za-z0-9]+", stem)
    name = "".join(word[0].upper() + word[1:] for word in words)
    if not name or name[0].isdigit():
        name = "Algorithm" + name
    return name + "Generated"


def validate_module_name(module: str) -> str:
    """Accept one importable file stem, without paths or Lean source syntax."""
    if not isinstance(module, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", module):
        raise ValueError("A Lean module name must start with an ASCII letter and contain only letters, digits, and underscores.")
    # Avoid shadowing these imports on case-insensitive filesystems as well.
    if module.lower() in {"algo2lean", "algo2leanlib", "algo2leanexamples",
                          "algo2leanreal", "algo2leanprobability", "std", "init", "lean", "mathlib"}:
        raise ValueError("'%s' is reserved for the shared Lean library or its dependencies." % module)
    return module
