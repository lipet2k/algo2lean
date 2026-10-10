"""Check Lean with an automatically prepared, versioned shared-library cache."""

from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import threading
import time

from .modules import validate_module_name


ROOT = Path(__file__).resolve().parent.parent
_CACHE_LOCK = threading.Lock()
_SHARED_MODULE = r"(?:Algo2Lean|Algo2LeanLib(?:\.[A-Za-z_][A-Za-z0-9_]*)+|Algo2LeanExamples\.[A-Za-z][A-Za-z0-9_]*)"


class LeanSetupError(RuntimeError):
    """A missing Lean installation or a failed shared-library preparation."""

    def __init__(self, message: str, available: bool = True):
        super().__init__(message)
        self.available = available


@dataclass(frozen=True)
class CheckResult:
    ok: bool
    available: bool
    output: str


def _remaining(deadline: float) -> float:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise LeanSetupError("Preparing the shared Lean library timed out.")
    return remaining


def _run_setup(command, environment, deadline):
    try:
        return subprocess.run(
            command, cwd=str(ROOT), env=environment, capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            timeout=_remaining(deadline), check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise LeanSetupError("Preparing the shared Lean library timed out.") from error
    except OSError as error:
        raise LeanSetupError("Could not start Lean: %s" % error, available=False) from error


def _import_tokens(source: str):
    """Return header module tokens with offsets in the original source."""
    # Lean block comments nest. Keep character positions intact so redirection
    # can replace the module spelling without changing comments or proof text.
    clean, index, depth = [], 0, 0
    while index < len(source):
        pair = source[index:index + 2]
        if pair == "/-":
            depth += 1
            clean.append("  ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            clean.append("  ")
            index += 2
        elif not depth and pair == "--":
            end = source.find("\n", index)
            end = len(source) if end == -1 else end
            clean.append(" " * (end - index))
            index = end
        else:
            clean.append(source[index] if not depth or source[index] == "\n" else " ")
            index += 1
    cleaned = "".join(clean)
    whitespace = re.compile(r"\s*")
    index = whitespace.match(cleaned).end()
    # Lean's header grammar permits whitespace (including newlines) between
    # import tokens, and one module per import command. Stop at the first body
    # command so a string, quotation, or later invalid import is never scanned.
    for keyword in ("module", "prelude"):
        marker = re.compile(keyword + r"(?=\s|$)\s*").match(cleaned, index)
        if marker:
            index = marker.end()
    header = re.compile(r"(?:public\s+)?(?:meta\s+)?import(?=\s|«)\s*(?:all\s+)?")
    token = re.compile(r"(?:«[^»]*»|[^\s«»])+")
    while match := header.match(cleaned, index):
        name = token.match(cleaned, match.end())
        if name is None:
            break
        module = re.sub(r"«([A-Za-z_][A-Za-z0-9_]*)»", r"\1", name.group())
        yield module, name.start(), name.end()
        index = whitespace.match(cleaned, name.end()).end()


def lean_imports(*sources: str) -> tuple:
    """Read safe module identities from Lean's import header, ignoring comments."""
    modules = {module for source in sources for module, _, _ in _import_tokens(source)}
    return tuple(sorted(modules))


def redirect_imports(source: str, replacements: dict):
    """Redirect exact header module tokens, preserving comments and proof text."""
    changed = [(start, end, replacements[module]) for module, start, end in _import_tokens(source)
               if module in replacements]
    for start, end, replacement in reversed(changed):
        source = source[:start] + replacement + source[end:]
    return source, len(changed)


def after_import_header(source: str) -> int:
    """Return the insertion offset after the import header and its trailing comments."""
    tokens = list(_import_tokens(source))
    if not tokens:
        return 0
    index, depth = tokens[-1][2], 0
    while index < len(source):
        pair = source[index:index + 2]
        if not depth and pair == "--":
            end = source.find("\n", index)
            return len(source) if end == -1 else end + 1
        if pair == "/-":
            depth += 1
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            index += 2
        elif not depth and source[index] == "\n":
            return index + 1
        elif not depth and not source[index].isspace():
            return index  # A Lean command may follow an import on the same line.
        else:
            index += 1
    return len(source)


def shared_imports(*sources: str) -> tuple:
    """Select the repository-owned subset of a Lean file's import header."""
    return tuple(module for module in lean_imports(*sources) if re.fullmatch(_SHARED_MODULE, module))


def _library_sources(modules):
    """Read a dependency-ordered snapshot of the requested shared modules."""
    sources, visiting = {}, set()

    def visit(module):
        if not re.fullmatch(_SHARED_MODULE, module):
            raise LeanSetupError("Invalid shared Lean module: %s" % module)
        if module in visiting:
            raise LeanSetupError("Shared Lean library import cycle at %s." % module)
        if module in sources:
            return
        visiting.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        try:
            if module.startswith("Algo2LeanExamples."):
                from .libraries import example_library_source
                relative, source = example_library_source(ROOT, module)
            else:
                source = (ROOT / relative).read_bytes()
            dependencies = shared_imports(source.decode("utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            raise LeanSetupError("Could not read the shared Lean library %s: %s" % (module, error)) from error
        for dependency in dependencies:
            visit(dependency)
        visiting.remove(module)
        sources[module] = (relative, source)

    for module in ("Algo2Lean", *sorted(set(modules))):
        visit(module)
    return sources


def prepare_lean_environment(timeout: float = 30, executable: str = None,
                             *, modules: tuple = ()) -> dict:
    """Return a subprocess environment where ``import Algo2Lean`` works.

    The repository's pinned toolchain selects Lean when called from ROOT.
    Optional modules select reusable analysis libraries without adding them to
    ordinary algorithm checks. Dependencies are built first. A cache entry is
    keyed by all selected source files and the Lean version. Each
    build uses a private directory and publishes it atomically, so simultaneous
    processes cannot read a partial object file. A process-local lock avoids
    duplicate builds among concurrent editor requests. User LEAN_PATH entries
    are preserved after the compiled Algo2Lean library's directory.

    Callers running Lean directly can pass this result as ``subprocess.run``'s
    ``env`` argument. Failures raise LeanSetupError with a readable explanation.
    """
    executable = executable or shutil.which("lean")
    if executable is None:
        raise LeanSetupError(
            "Lean was not found. Install Lean 4 using elan, then restart the editor server.",
            available=False,
        )
    deadline = time.monotonic() + timeout
    environment = os.environ.copy()
    version = _run_setup([executable, "--version"], environment, deadline)
    if version.returncode != 0:
        details = (version.stdout + version.stderr).strip()
        raise LeanSetupError("Could not determine the Lean version.\n" + details)
    sources = _library_sources(modules)
    snapshot = b"\0".join(os.fsencode(str(path)) + b"\0" + source
                           for path, source in sources.values())
    key = hashlib.sha256(
        snapshot + b"\0" + version.stdout.encode("utf-8") + b"\0" +
        os.fsencode(str(Path(executable).resolve()))
    ).hexdigest()
    cache_root = Path(tempfile.gettempdir()) / "algo2lean-lean-cache"
    cached = cache_root / key
    object_file = cached / "Algo2Lean.olean"

    if not object_file.is_file():
        if not _CACHE_LOCK.acquire(timeout=_remaining(deadline)):
            raise LeanSetupError("Waiting for the shared Lean library build timed out.")
        try:
            if not object_file.is_file():
                cache_root.mkdir(mode=0o700, parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(prefix=".building-", dir=cache_root) as directory:
                    temporary = Path(directory).resolve()
                    build_environment = environment.copy()
                    previous = environment.get("LEAN_PATH", "")
                    build_environment["LEAN_PATH"] = str(temporary) + (os.pathsep + previous if previous else "")
                    for relative, source in sources.values():
                        library = temporary / relative
                        library.parent.mkdir(parents=True, exist_ok=True)
                        library.write_bytes(source)
                        compiled = library.with_suffix(".olean")
                        result = _run_setup(
                            [executable, "--root=" + str(temporary), "-o", str(compiled), str(library)],
                            build_environment, deadline,
                        )
                        output = (result.stdout + result.stderr).replace(str(temporary) + os.sep, "")
                        if result.returncode != 0 or "declaration uses 'sorry'" in output:
                            raise LeanSetupError("Lean rejected the shared library.\n" + output[:20000].strip())
                        if not compiled.is_file():
                            raise LeanSetupError("Lean did not produce the shared library object file for %s." % relative)
                    try:
                        temporary.rename(cached)
                    except OSError:
                        # Another process may have published the same complete
                        # source/version entry while this one was compiling.
                        if not object_file.is_file():
                            raise
        except OSError as error:
            raise LeanSetupError("Could not prepare the Lean library cache: %s" % error) from error
        finally:
            _CACHE_LOCK.release()

    previous = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(cached) + (os.pathsep + previous if previous else "")
    return environment


def check_lean(lean_source: str, timeout: float = 30, *, module: str = "Generated",
               points_lean: str = None) -> CheckResult:
    """Check algorithm definitions and their optional named-location module.

    Checking a Points module first builds the algorithm module's object file,
    then checks Points against that import. The generated sources are never
    concatenated. Omitting Points checks only the algorithm definitions.
    """
    validate_module_name(module)
    executable = shutil.which("lean")
    if executable is None:
        return CheckResult(False, False, "Lean was not found. Install Lean 4 using elan, then restart the editor server.")
    deadline = time.monotonic() + timeout
    environment = os.environ.copy()
    # The emitter uses single-line imports. Standalone exports import Std and
    # contain the runtime themselves, so they need no separate library build.
    imports = shared_imports(lean_source, points_lean or "")
    if imports:
        try:
            environment = prepare_lean_environment(timeout=timeout, executable=executable, modules=imports)
        except LeanSetupError as error:
            return CheckResult(False, error.available, str(error))
    with tempfile.TemporaryDirectory(prefix="algo2lean-") as directory:
        source = Path(directory) / (module + ".lean")
        source.write_text(lean_source, encoding="utf-8")
        files = [(source, [])]
        if points_lean is not None:
            points = Path(directory) / (module + "Points.lean")
            points.write_text(points_lean, encoding="utf-8")
            environment["LEAN_PATH"] = directory + (
                os.pathsep + environment["LEAN_PATH"] if environment.get("LEAN_PATH") else "")
            files = [(source, ["-o", str(source.with_suffix(".olean"))]), (points, [])]
        messages = []
        try:
            for path, options in files:
                result = subprocess.run(
                    [executable, "--root=" + directory, *options, str(path)],
                    cwd=str(ROOT), env=environment, capture_output=True,
                    text=True, encoding="utf-8", errors="replace", timeout=max(0, deadline - time.monotonic()),
                    check=False,
                )
                output = (result.stdout + result.stderr).replace(directory + os.sep, "")
                if output.strip():
                    messages.append(output.strip())
                if result.returncode != 0:
                    break
        except subprocess.TimeoutExpired:
            return CheckResult(False, True, "Lean checking timed out after %g seconds. The generated file can still be exported and checked locally." % timeout)
        except OSError as error:
            return CheckResult(False, False, "Could not start Lean: %s" % error)
        output = "\n".join(messages)
        if len(output) > 20000:
            output = output[:20000] + "\n[Further Lean output omitted.]"
        subject = "generated definitions and named points" if points_lean is not None else "generated definitions"
        message = ("Lean accepted the " if result.returncode == 0 else "Lean rejected the ") + subject + "."
        return CheckResult(result.returncode == 0, True, output.strip() or message)
