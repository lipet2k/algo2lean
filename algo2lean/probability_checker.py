"""Explicit Mathlib checking with already installed, pinned dependencies.

The ordinary checker remains Std-only. This backend reuses Lake's incremental
build of the requested optional libraries and checks each requested application
or proof against its current source in a fresh temporary directory.
"""

from collections.abc import Mapping
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time

from .checker import (CheckResult, LeanSetupError, has_sorry_warning, lean_imports,
                      prepare_lean_environment, shared_imports)
from .probability_support import OPTIONAL_LIBRARIES, is_optional_library, optional_sources
from .probability_support import needs_mathlib as _needs_mathlib


ROOT = Path(__file__).resolve().parent.parent
PROBABILITY_ROOT = ROOT / "probability"
_BUILD_LOCK = threading.Lock()
_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
_RESERVED = {"init", "std", "lean", "mathlib", "algo2lean", "algo2leanlib",
             "algo2leanexamples", *(name.casefold() for name in OPTIONAL_LIBRARIES)}
_SETUP = (
    "Optional Mathlib dependencies are not prepared. In the repository's probability/ "
    "directory, explicitly run `lake update` and `lake exe cache get`, then retry. "
    "Mathlib checks do not download dependencies.")


def needs_mathlib(*sources):
    """An explicit library import selects the optional Mathlib backend."""
    return _needs_mathlib(sources)


def needs_probability(*sources):
    """Compatibility alias for callers selecting the optional Mathlib backend."""
    return needs_mathlib(*sources)


def _remaining(deadline):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise LeanSetupError("Mathlib checking timed out.")
    return remaining


def _run(command, environment, deadline, *, cwd=None):
    try:
        return subprocess.run(command, cwd=cwd or PROBABILITY_ROOT, env=environment,
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=_remaining(deadline), check=False)
    except subprocess.TimeoutExpired as error:
        raise LeanSetupError("Mathlib checking timed out.") from error
    except OSError as error:
        raise LeanSetupError("Could not start the Mathlib checker: %s" % error,
                             available=False) from error


def _ordered_sources(sources):
    if not isinstance(sources, Mapping) or not sources:
        raise LeanSetupError("Mathlib checking requires a nonempty mapping of Lean modules to source text.")
    spellings = {}
    for name, source in sources.items():
        if not isinstance(name, str) or not _MODULE.fullmatch(name):
            raise LeanSetupError("Invalid Lean module name: %r." % (name,))
        if name.split(".")[0].casefold() in _RESERVED:
            raise LeanSetupError("Lean module '%s' conflicts with a Lean library." % name)
        if not isinstance(source, str):
            raise LeanSetupError("Lean source for '%s' must be text." % name)
        parts = name.split(".")
        for end in range(1, len(parts) + 1):
            prefix = ".".join(parts[:end])
            previous = spellings.setdefault(prefix.casefold(), prefix)
            if previous != prefix:
                raise LeanSetupError("Case-colliding Lean modules '%s' and '%s'." % (previous, prefix))
    ordered, visiting = {}, []

    def visit(name):
        if name in ordered:
            return
        if name in visiting:
            raise LeanSetupError("Lean source import cycle: %s." %
                                 " -> ".join(visiting[visiting.index(name):] + [name]))
        visiting.append(name)
        for dependency in lean_imports(sources[name]):
            if dependency in sources:
                visit(dependency)
            elif (dependency.split(".")[0] not in {"Init", "Std", "Lean", "Mathlib"}
                  and not is_optional_library(dependency) and not shared_imports("import " + dependency)):
                raise LeanSetupError("No Lean source or supported library is available for '%s'." % dependency)
        visiting.pop()
        ordered[name] = sources[name]

    for name in sources:
        visit(name)
    return ordered


def _installed_dependencies(sources):
    """Check installed dependencies and only the requested Mathlib cache entries."""
    required = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
    if not all((PROBABILITY_ROOT / name).is_file() for name in required):
        raise LeanSetupError(_SETUP, available=False)
    try:
        manifest = json.loads((PROBABILITY_ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
        packages = manifest["packages"]
        packages_root = PROBABILITY_ROOT / manifest.get("packagesDir", ".lake/packages")
        mathlib = None
        for package in packages:
            if package["type"] == "path":
                directory = PROBABILITY_ROOT / package["dir"]
            elif package["type"] == "git":
                directory = packages_root / package["name"]
            else:
                raise ValueError("unsupported dependency type")
            if not (directory / package["configFile"]).is_file():
                raise LeanSetupError(_SETUP, available=False)
            if package["name"] == "mathlib":
                mathlib = directory
        if mathlib is None:
            raise LeanSetupError(_SETUP, available=False)
        libraries = optional_sources(sources.values())
        for dependency in lean_imports(*libraries.values(), *sources.values()):
            if dependency.split(".")[0] == "Mathlib":
                object_file = mathlib / ".lake/build/lib/lean" / Path(*dependency.split(".")).with_suffix(".olean")
                if not object_file.is_file():
                    raise LeanSetupError(_SETUP, available=False)
        return libraries
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as error:
        raise LeanSetupError(_SETUP + " Invalid or unreadable dependency setup: %s" % error,
                             available=False) from error


def _prepare(sources, deadline):
    libraries = _installed_dependencies(sources)
    lake = shutil.which("lake")
    if lake is None:
        raise LeanSetupError("Lake was not found. Install the pinned Lean toolchain and prepare probability/ dependencies.",
                             available=False)
    environment = os.environ.copy()
    toolchain = (PROBABILITY_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    environment["ELAN_TOOLCHAIN"] = toolchain
    elan = shutil.which("elan")
    if elan and Path(lake).parent == Path(elan).parent:
        installed = _run([elan, "toolchain", "list"], environment, deadline)
        if installed.returncode != 0 or toolchain not in {line.split()[0] for line in installed.stdout.splitlines() if line.strip()}:
            raise LeanSetupError("The pinned Lean toolchain '%s' is not installed. Install it explicitly before "
                                 "checking Mathlib modules; checks do not download toolchains." % toolchain,
                                 available=False)
    # Lake must use the installed sources and caches. Prevent automatic Git
    # network access if a dependency changes between the preflight and build.
    count = int(environment.get("GIT_CONFIG_COUNT", "0"))
    environment["GIT_CONFIG_COUNT"] = str(count + 1)
    environment["GIT_CONFIG_KEY_%d" % count] = "protocol.allow"
    environment["GIT_CONFIG_VALUE_%d" % count] = "never"
    environment["GIT_TERMINAL_PROMPT"] = "0"
    if not _BUILD_LOCK.acquire(timeout=_remaining(deadline)):
        raise LeanSetupError("Waiting for the optional library build timed out.")
    try:
        targets = sorted(path.removesuffix(".lean").replace("/", ".") for path in libraries) + sorted({
            name for name in lean_imports(*sources.values()) if name.split(".")[0] == "Mathlib"})
        if not targets:
            raise LeanSetupError("No optional Mathlib library was requested.")
        built = _run([lake, "--no-cache", "build", *targets], environment, deadline)
        output = built.stdout + built.stderr
        if built.returncode != 0 or has_sorry_warning(output):
            raise LeanSetupError("Lean rejected the requested Mathlib libraries.\n" + output[:19000].strip())
        probe = (
            "import json, os, shutil; "
            "print(json.dumps({'lean': shutil.which('lean'), 'environment': "
            "{key: os.environ[key] for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'PATH', "
            "'LD_LIBRARY_PATH', 'DYLD_LIBRARY_PATH') if key in os.environ}}))")
        selected = _run([lake, "--no-cache", "env", sys.executable, "-c", probe], environment, deadline)
        if selected.returncode != 0:
            raise LeanSetupError("Could not read the pinned Mathlib environment.\n" +
                                 (selected.stdout + selected.stderr)[:19000].strip())
        configuration = json.loads(selected.stdout)
        executable = configuration["lean"]
        if not executable:
            raise LeanSetupError("Lean is unavailable in the pinned Mathlib environment.", available=False)
        environment.update(configuration["environment"])
    finally:
        _BUILD_LOCK.release()
    shared = prepare_lean_environment(timeout=_remaining(deadline), executable=executable,
        modules=shared_imports(*libraries.values(), *sources.values()))
    lake_paths = [str((PROBABILITY_ROOT / item).resolve()) for item in environment.get("LEAN_PATH", "").split(os.pathsep) if item]
    shared_paths = shared["LEAN_PATH"].split(os.pathsep)
    environment["LEAN_PATH"] = os.pathsep.join(dict.fromkeys([shared_paths[0], *lake_paths, *shared_paths[1:]]))
    return executable, environment


def check_mathlib_sources(sources, timeout=120) -> CheckResult:
    """Check explicitly requested modules using an existing Mathlib setup.

    Modules are checked in import order, with no cached user proof objects and no
    implicit dependency downloads. Requested optional libraries use Lake's
    incremental cache. Success is scoped to the source's assumptions and Lean
    options, as with the standard checker.
    """
    deadline = time.monotonic() + timeout
    try:
        ordered = _ordered_sources(sources)
        executable, environment = _prepare(ordered, deadline)
        messages = []
        with tempfile.TemporaryDirectory(prefix="algo2lean-mathlib-check-") as directory:
            temporary = Path(directory)
            environment["LEAN_PATH"] = directory + os.pathsep + environment["LEAN_PATH"]
            for name, source in ordered.items():
                path = temporary.joinpath(*name.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding="utf-8")
                checked = _run([executable, "--root=" + directory, "-o", str(path.with_suffix(".olean")), str(path)],
                               environment, deadline)
                output = (checked.stdout + checked.stderr).replace(directory + os.sep, "")
                if output.strip():
                    messages.append(output.strip())
                if has_sorry_warning(output):
                    return CheckResult(False, True, "Analysis is incomplete: replace every sorry with a proof.\n" + output[:19000])
                if checked.returncode != 0:
                    return CheckResult(False, True, "\n".join(messages)[:20000])
                if not path.with_suffix(".olean").is_file():
                    raise LeanSetupError("Lean did not produce the checked module '%s'." % name)
        subject = "probability modules and analysis" if any(
            (name == "Algo2LeanProbability" or name.startswith("Algo2LeanProbability."))
            for source in sources.values() for name in lean_imports(source)) else "Mathlib modules and analysis"
        messages.append("Lean accepted the %s with their declared assumptions and options." % subject)
        return CheckResult(True, True, "\n".join(messages)[:20000])
    except LeanSetupError as error:
        return CheckResult(False, error.available, str(error))
    except (OSError, UnicodeError, ValueError, TypeError, KeyError) as error:
        return CheckResult(False, True, "Could not check Mathlib modules: %s" % error)


def check_probability_sources(sources, timeout=120) -> CheckResult:
    """Compatibility entry point for the optional Mathlib checker."""
    return check_mathlib_sources(sources, timeout=timeout)
