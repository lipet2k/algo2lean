"""Regenerate source and compare a selected folder without running Lean."""

from pathlib import Path

from .browser import request


def verify_generated(source, directory, *, project_root=None, standalone=False):
    """Check exact paths and UTF-8 bytes, including any supplied shared libraries.

    All generated modules are required. Shared libraries are checked when
    present; unrelated Lean files are reported as extra. Non-Lean files such as
    the generation manifest are not trusted as evidence and are not compared.
    """
    source, directory = Path(source).resolve(), Path(directory).resolve()
    if not directory.is_dir():
        raise ValueError("Choose a folder containing the claimed generated Lean files.")
    payload = {"filename": source.name, "source": source.read_bytes().decode("utf-8"),
               "standalone": standalone}
    project = project_root is not None
    if project:
        from .project import load_project
        loaded = load_project(source, root=project_root)
        payload["filename"] = source.relative_to(loaded.root).as_posix()
        payload["project_sources"] = {module.path.relative_to(loaded.root).as_posix(): module.source
                                      for module in loaded.modules.values()}
    response = request("/api/generation", payload, project=project)
    if response["status"] != 200:
        result = response["body"]
        diagnostics = result.get("diagnostics", [])
        raise ValueError(result.get("message") or (diagnostics[0]["message"] if diagnostics else "Compilation failed."))
    data = response["body"]
    expected = {**data["libraries"], **data["files"]}
    matched, extra, different = set(), [], []
    for path in sorted(directory.rglob("*.lean")):
        relative = path.relative_to(directory)
        if any(part in {".lake", ".git"} for part in relative.parts):
            continue
        name = relative.as_posix()
        if path.is_symlink():
            raise ValueError("Choose ordinary generated files, not symbolic links: " + name)
        if not path.is_file():
            continue
        if name not in expected:
            extra.append(name)
            continue
        matched.add(name)
        if path.read_bytes() != expected[name].encode("utf-8"):
            different.append(name)
    missing = sorted(set(data["files"]) - matched)
    return {"exact": not (missing or extra or different), "compared": len(matched),
            "missing": missing, "extra": extra, "different": different}
