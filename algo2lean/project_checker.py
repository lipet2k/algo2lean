"""Check separately compiled projects and only their requested proof imports.

Each immutable module cache entry records its source, compiler identity, and
dependency identities. Editing a label or a proof does not rebuild independent
generated definitions; changing a dependency invalidates every affected caller.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import threading
import time

from . import checker
from .checker import CheckResult, LeanSetupError, lean_imports, shared_imports


_CACHE_LOCK = threading.Lock()
_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
_BUILTINS = {"Init", "Std", "Lean"}


def _module_path(name):
    return Path(*name.split(".")).with_suffix(".lean")


def _validate_name(name):
    if not isinstance(name, str) or not _MODULE.fullmatch(name):
        raise LeanSetupError("Invalid Lean project module name: %r." % (name,))
    if name.split(".")[0].casefold() in {"init", "std", "lean", "algo2lean", "algo2leanlib", "algo2leanexamples"}:
        raise LeanSetupError("Project module '%s' conflicts with a Lean library." % name)


def _sources(compilation, analysis, analysis_module, proof_sources, check_facts, analysis_modules=()):
    """Snapshot a root-confined source DAG, visiting only requested proofs."""
    project = compilation.project
    root = Path(project.root).expanduser().resolve()
    generated = dict(compilation.files)
    source_overlays = dict(getattr(project, "source_overlays", {}))
    # Imported proof-only algorithms must use the same original source snapshot
    # for every already-compiled dependency, even if disk files have changed.
    source_overlays.update({Path(*name.split(".")).with_suffix(".algo").as_posix(): module.source
                            for name, module in getattr(project, "modules", {}).items()})
    if not generated:
        raise LeanSetupError("The project has no generated Lean modules to check.")
    overlays = dict(proof_sources or {})
    if analysis is not None:
        analysis_module = analysis_module or "Algo." + project.entry + ".Analysis"
        if analysis_module in overlays:
            raise LeanSetupError("Analysis module '%s' was supplied twice." % analysis_module)
        overlays[analysis_module] = analysis
    spellings, paths = {}, {}

    def register(name, source):
        _validate_name(name)
        if not isinstance(source, str):
            raise LeanSetupError("Lean source for '%s' must be text." % name)
        parts = name.split(".")
        for end in range(1, len(parts) + 1):
            prefix = ".".join(parts[:end])
            old = spellings.get(prefix.casefold())
            if old is not None and old != prefix:
                raise LeanSetupError("Case-colliding Lean project modules '%s' and '%s'." % (old, prefix))
            spellings[prefix.casefold()] = prefix

    for name, source in generated.items():
        register(name, source)
    for name, source in overlays.items():
        if name in generated:
            raise LeanSetupError("Proof module '%s' would replace generated definitions." % name)
        register(name, source)

    def compile_dependency(name):
        from .frontend import CompileError
        from .modular import compile_project
        source_module = ".".join(name.split(".")[1:-1])
        try:
            entry_path = root.joinpath(*source_module.split(".")).with_suffix(".algo")
            imported = compile_project(entry_path, root=root, sources=source_overlays)
        except CompileError as error:
            raise LeanSetupError("No generated Lean module '%s' is available: %s" % (name, error)) from error
        for candidate, text in imported.files.items():
            if candidate in overlays:
                raise LeanSetupError("Proof module '%s' would replace generated definitions." % candidate)
            if candidate in generated and generated[candidate] != text:
                raise LeanSetupError("Imported algorithm '%s' conflicts with the compiled source snapshot." % candidate)
            register(candidate, text)
            generated[candidate] = text
        source_overlays.update({Path(*module.split(".")).with_suffix(".algo").as_posix(): snapshot.source
                                for module, snapshot in imported.project.modules.items()})
        return generated[name]

    def companion(name):
        if not name.startswith("Algo.") or not name.endswith(".Analysis") or len(name.split(".")) < 3:
            raise LeanSetupError("No generated Lean module '%s' exists in this project." % name)
        relative = Path(*name.split(".")[1:-1]).with_suffix(".lean")
        candidates = [root / "analysis" / relative, root / relative]
        found = []
        for candidate in candidates:
            real = candidate.resolve()
            if not real.is_relative_to(root):
                raise LeanSetupError("Proof module '%s' escapes the project root through a symbolic link." % name)
            if candidate.is_file():
                # Validate path spelling on both case-sensitive and insensitive
                # filesystems, without searching unrelated project directories.
                parent = root
                for segment in candidate.relative_to(root).parts:
                    matches = [item.name for item in parent.iterdir() if item.name.casefold() == segment.casefold()]
                    if matches != [segment]:
                        raise LeanSetupError("Proof module '%s' has an ambiguous or mismatched path case." % name)
                    parent /= segment
                found.append((candidate, real))
        if not found:
            raise LeanSetupError("Could not find proof module '%s'; expected %s or %s." %
                                 (name, candidates[0], candidates[1]))
        if len(found) != 1:
            raise LeanSetupError("Proof module '%s' is ambiguous: both %s and %s exist." %
                                 (name, candidates[0], candidates[1]))
        candidate, real = found[0]
        old = paths.get(real)
        if old is not None and old != name:
            raise LeanSetupError("Proof modules '%s' and '%s' refer to the same file." % (old, name))
        paths[real] = name
        source = candidate.read_text(encoding="utf-8")
        register(name, source)
        return source

    sources, dependencies, visiting = {}, {}, []

    def visit(name):
        if name in visiting:
            cycle = visiting[visiting.index(name):] + [name]
            raise LeanSetupError("Lean project import cycle: %s." % " -> ".join(cycle))
        if name in sources:
            return
        _validate_name(name)
        if name in generated:
            source = generated[name]
        elif name in overlays:
            source = overlays[name]
        elif (name.startswith("Algo.") and len(name.split(".")) >= 3 and
              name.rsplit(".", 1)[1] in {"Generated", "Points", "Facts"}):
            source = compile_dependency(name)
        else:
            source = companion(name)
        visiting.append(name)
        imports = lean_imports(source)
        for dependency in imports:
            if dependency in generated or dependency in overlays or dependency.startswith("Algo."):
                visit(dependency)
            elif dependency.split(".")[0] not in _BUILTINS and not shared_imports("import " + dependency):
                raise LeanSetupError("Unsupported Lean import '%s' in '%s'. Project checks support "
                                     "Std, Init, Lean, shared Algo2Lean libraries, and project modules." %
                                     (dependency, name))
        visiting.pop()
        sources[name] = source
        dependencies[name] = imports

    for name in list(generated):
        if check_facts or not name.endswith(".Facts"):
            visit(name)
    if analysis_module is not None:
        visit(analysis_module)
    for name in analysis_modules:
        visit(name)
    return sources, dependencies


def project_lean_sources(compilation, *, proof_sources=None, analysis_modules=(), check_facts=False):
    """Resolve exportable Lean sources without running Lean.

    Only the explicitly requested analysis roots and their imports are added
    to the compiled project. This shares the checker's root confinement, source
    snapshots, and on-demand algorithm compilation with project export.
    """
    return _sources(compilation, None, None, proof_sources, check_facts, analysis_modules)[0]


def _remaining(deadline):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise LeanSetupError("Lean project checking timed out.")
    return remaining


def _run(command, environment, deadline):
    try:
        return subprocess.run(command, cwd=checker.ROOT, env=environment, capture_output=True,
                              text=True, encoding="utf-8", errors="replace",
                              timeout=_remaining(deadline), check=False)
    except subprocess.TimeoutExpired as error:
        raise LeanSetupError("Lean project checking timed out.") from error
    except OSError as error:
        raise LeanSetupError("Could not start Lean: %s" % error, available=False) from error


def _digest(*parts):
    return hashlib.sha256(json.dumps(parts, ensure_ascii=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _shared_identities(environment, modules, compiler):
    """Hash the actual immutable sources used to build the prepared library.

    Reading this snapshot avoids a race with edits to the repository sources.
    Each identity uses its own dependency closure, so a newly imported proof
    library does not invalidate unrelated generated modules.
    """
    prepared = Path(environment["LEAN_PATH"].split(os.pathsep)[0])
    identities, visiting = {}, set()

    def visit(name):
        if name in identities:
            return identities[name]
        if name in visiting:
            raise LeanSetupError("Prepared shared-library import cycle at '%s'." % name)
        visiting.add(name)
        source = (prepared / _module_path(name)).read_text(encoding="utf-8")
        dependencies = [(dependency, visit(dependency)) for dependency in shared_imports(source)]
        visiting.remove(name)
        identities[name] = _digest("shared", compiler, name, source, dependencies)
        return identities[name]

    for name in modules:
        visit(name)
    return identities


def _cached(directory, name, identity):
    """Reuse a compiled Lean module only after its complete cache entry is published."""
    try:
        manifest = json.loads((directory / "complete.json").read_text(encoding="utf-8"))
        return (manifest["module"] == name and manifest["identity"] == identity and
                (directory / _module_path(name).with_suffix(".olean")).is_file() and
                bool(manifest["objects"]) and
                all((directory / part).is_file() for part in manifest["objects"]))
    except (OSError, ValueError, KeyError, TypeError):
        return False


def _build(name, source, identity, environment, executable, deadline):
    cache_root = Path(tempfile.gettempdir()) / "algo2lean-project-cache"
    cached = cache_root / identity
    if not _cached(cached, name, identity):
        if not _CACHE_LOCK.acquire(timeout=_remaining(deadline)):
            raise LeanSetupError("Waiting for a Lean project module build timed out.")
        try:
            if not _cached(cached, name, identity):
                cache_root.mkdir(mode=0o700, parents=True, exist_ok=True)
                # A deleted object or interrupted external cleanup must not
                # leave a permanently unusable entry at this content address.
                if cached.is_symlink():
                    cached.unlink()
                elif cached.exists():
                    shutil.rmtree(cached)
                with tempfile.TemporaryDirectory(prefix=".building-", dir=cache_root) as directory:
                    temporary = Path(directory).resolve()
                    path = temporary / _module_path(name)
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(source, encoding="utf-8")
                    compiled = path.with_suffix(".olean")
                    result = _run([executable, "--root=" + str(temporary), "-o", str(compiled), str(path)],
                                  environment, deadline)
                    output = (result.stdout + result.stderr).replace(str(temporary) + os.sep, "").strip()
                    if result.returncode != 0:
                        raise LeanSetupError("Lean rejected project module '%s'.\n%s" % (name, output[:19000]))
                    if "declaration uses 'sorry'" in output:
                        raise LeanSetupError("Analysis is incomplete: replace every sorry with a proof.\n" + output[:19000])
                    if not compiled.is_file():
                        raise LeanSetupError("Lean did not produce an object file for '%s'." % name)
                    (temporary / "complete.json").write_text(json.dumps({
                        "module": name, "identity": identity, "output": output,
                        "objects": [str(artifact.relative_to(temporary))
                                    for artifact in path.parent.glob(path.stem + ".olean*")],
                    }), encoding="utf-8")
                    try:
                        temporary.rename(cached)
                    except OSError:
                        # Independent processes may publish the same immutable
                        # node. No process may consume an unfinished one.
                        if not _cached(cached, name, identity):
                            raise LeanSetupError("Could not publish the Lean module cache for '%s'." % name)
        finally:
            _CACHE_LOCK.release()
    manifest = json.loads((cached / "complete.json").read_text(encoding="utf-8"))
    return cached, manifest.get("output", "")


def _stage(directory, workspace, name):
    """Stage compiled modules sharing a top-level namespace under one Lean import root."""
    relative = _module_path(name)
    source = directory / relative
    destination = workspace / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    # Lean object files may include public/private/server sidecars. Stage every
    # object part from the same completed cache entry.
    for artifact in source.parent.glob(source.stem + ".olean*"):
        target = destination.parent / artifact.name
        try:
            os.link(artifact, target)
        except OSError:
            shutil.copyfile(artifact, target)


def check_project(compilation, *, analysis=None, analysis_module=None, proof_sources=None,
                  check_facts=False, timeout=120) -> CheckResult:
    """Check generated modules and an optional importing analysis separately.

    ``compilation.files`` maps Lean module names to text. Companion imports such
    as ``Algo.pkg.sort.Analysis`` read only ``analysis/pkg/sort.lean`` or
    ``pkg/sort.lean`` beneath ``compilation.project.root``. ``proof_sources``
    supplies an optional in-memory overlay keyed by full Lean module name;
    unused proof modules are never checked. The active analysis defaults to
    ``Algo.<entry>.Analysis``. Supplying just ``analysis_module`` selects a disk
    companion. Generated ``.Facts`` modules are built only when imported, unless
    ``check_facts=True`` explicitly requests them all. Analyses may also import
    algorithms outside the source call graph; these are compiled on demand
    using the original source snapshots and editor overlays. Acceptance uses the
    analysis's declared assumptions and Lean options; it does not independently
    audit those assumptions or enforce proof completeness.
    """
    deadline = time.monotonic() + timeout
    executable = shutil.which("lean")
    if executable is None:
        return CheckResult(False, False, "Lean was not found. Install Lean 4 using elan, then restart the editor.")
    try:
        sources, dependencies = _sources(compilation, analysis, analysis_module, proof_sources, check_facts)
        environment = os.environ.copy()
        version = _run([executable, "--version"], environment, deadline)
        if version.returncode != 0:
            raise LeanSetupError("Could not determine the Lean version.\n" + (version.stdout + version.stderr).strip())
        compiler = (version.stdout, str(Path(executable).resolve()))
        libraries = shared_imports(*sources.values())
        shared = {}
        if libraries:
            environment = checker.prepare_lean_environment(timeout=_remaining(deadline), executable=executable,
                                                          modules=libraries)
            shared = _shared_identities(environment, libraries, compiler)
        identities, messages = {}, []
        with tempfile.TemporaryDirectory(prefix="algo2lean-project-imports-") as directory:
            workspace = Path(directory)
            previous = environment.get("LEAN_PATH", "")
            environment["LEAN_PATH"] = str(workspace) + (os.pathsep + previous if previous else "")
            for name, source in sources.items():
                _remaining(deadline)
                imported = [(dependency, identities.get(dependency, shared.get(dependency, "builtin")))
                            for dependency in dependencies[name]]
                identity = _digest("algo2lean-project-v1", compiler, name, source, imported)
                cached, output = _build(name, source, identity, environment, executable, deadline)
                _stage(cached, workspace, name)
                identities[name] = identity
                if output:
                    messages.append(output)
        messages.append("Lean accepted the project and analysis with their declared assumptions and options."
                        if analysis is not None or analysis_module is not None else
                        "Lean accepted the separately compiled project definitions and named points.")
        return CheckResult(True, True, "\n".join(messages)[:20000])
    except LeanSetupError as error:
        return CheckResult(False, error.available, str(error))
    except (OSError, UnicodeError, ValueError, TypeError) as error:
        return CheckResult(False, True, "Could not check the Lean project: %s" % error)
