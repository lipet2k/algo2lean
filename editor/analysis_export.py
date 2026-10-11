"""Editor-only analysis bundles, layered over the unchanged compiler API.

This module also runs in the browser worker beside a frozen compiler release.
Exporting resolves imports and packages sources; it does not run Lean or prove
that a user's analysis is complete.
"""

import base64
import io
import json
from pathlib import PurePosixPath
import re
import zipfile

from algo2lean import browser
from algo2lean.analysis import analysis_support_sources
from algo2lean.checker import LeanSetupError, _library_sources, lean_imports, shared_imports
from algo2lean.server import MAX_ANALYSIS_BYTES, MAX_ANALYSIS_REQUEST_BYTES, MAX_SOURCE_BYTES


_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
_BUILTINS = {"Init", "Std", "Lean"}
_RESERVED = {"init", "std", "lean", "algo2lean", "algo2leanlib", "algo2leanexamples"}


def _error(message, status=400):
    return {"status": status, "content_type": "application/json; charset=utf-8",
            "body": {"ok": False, "message": message, "diagnostics": [{"message": message}]}}


def _text(value, label, limit, *, required=False):
    if not isinstance(value, str) or (required and not value.strip()):
        raise ValueError("%s must contain text." % label)
    if any(character == "\x00" or 0xD800 <= ord(character) <= 0xDFFF for character in value):
        raise ValueError("%s contains an invalid text character." % label)
    if len(value.encode("utf-8")) > limit:
        raise ValueError("%s exceeds the %s MiB text limit." % (label, limit / (1024 * 1024)))
    return value


def _module_path(name):
    if not isinstance(name, str) or not _MODULE.fullmatch(name):
        raise ValueError("Unsupported Lean module name '%s'." % name)
    return name.replace(".", "/") + ".lean"


def _add(files, name, contents):
    path = PurePosixPath(name)
    if (not name or path.is_absolute() or "\\" in name or "\x00" in name
            or any(part in {"", ".", ".."} for part in name.split("/"))):
        raise ValueError("Unsafe export path '%s'." % name)
    for previous in files:
        old_parts, parts = previous.split("/"), name.split("/")
        for old, new in zip(old_parts, parts):
            if old.casefold() != new.casefold():
                break
            if old != new:
                raise ValueError("Case-colliding export paths '%s' and '%s'." % (previous, name))
        if previous == name:
            raise ValueError("Export file '%s' would overwrite another source." % name)
        if previous.startswith(name + "/") or name.startswith(previous + "/"):
            raise ValueError("Conflicting export paths '%s' and '%s'." % (previous, name))
    files[name] = contents.encode("utf-8") if isinstance(contents, str) else contents


def _validate_imports(files):
    """Reject missing dependencies and cycles without inspecting proof bodies."""
    sources = {name[:-5].replace("/", "."): text.decode("utf-8")
               for name, text in files.items() if name.endswith(".lean") and not name.startswith("source/")}
    done, visiting = set(), []

    def visit(name):
        if name in visiting:
            raise ValueError("Lean import cycle: %s." % " → ".join(visiting + [name]))
        if name in done:
            return
        visiting.append(name)
        for dependency in lean_imports(sources[name]):
            if dependency in sources:
                visit(dependency)
            elif not _MODULE.fullmatch(dependency) or dependency.split(".")[0] not in _BUILTINS:
                raise ValueError("Cannot export '%s': unresolved or unsupported Lean import '%s'. "
                                 "Include the matching project analysis or use a packaged Algo2Lean library." % (name, dependency))
        visiting.pop()
        done.add(name)

    for name in sources:
        visit(name)


def _lakefile(files, selected):
    roots = sorted({name.split("/", 1)[0].removesuffix(".lean") for name in files
                    if name.endswith(".lean") and not name.startswith("source/")})
    # Shared example proofs occupy a distinct Lake library, even when a project
    # archive from the frozen compiler already includes their source files.
    return ('name = "algo2lean_analysis"\nversion = "0.1.0"\n'
            'defaultTargets = ' + json.dumps([selected]) + "\n" +
            "".join('\n[[lean_lib]]\nname = ' + json.dumps(name) + "\n" for name in roots))


def _archive(files, selected):
    _validate_imports(files)
    files["lakefile.toml"] = _lakefile(files, selected).encode("utf-8")
    files["README.md"] = (
        "# Algo2Lean analysis bundle\n\n"
        "Run `lake build` in this folder to check the selected analysis, `%s`, "
        "and its imports with the pinned Lean toolchain.\n\n"
        "The bundle preserves the analysis and algorithm source text and includes "
        "generated definitions, named-line interfaces, and required shared libraries. "
        "The `source` folder contains the algorithm inputs and, for projects, their proof drafts.\n\n"
        "Downloading resolves and packages imports; it does not check the proof. "
        "Lean may still report unfinished proofs or errors when you build.\n\n"
        "The included Algo2Lean shared libraries are covered by `LICENSE`. "
        "This notice does not assign a license to your algorithm or proof.\n" % selected
    ).encode("utf-8")
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, contents in sorted(files.items()):
            info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, contents)
    return {"status": 200, "content_type": "application/zip", "encoding": "base64",
            "body": base64.b64encode(output.getvalue()).decode("ascii")}


def _standalone(body):
    name = body.get("analysis_filename", "Analysis.lean")
    if (not isinstance(name, str) or len(name) > 255 or
            not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*\.lean", name)):
        raise ValueError("Choose an analysis filename with a Lean module name, such as Analysis.lean "
                         "(letters, digits, and underscores; no path or spaces).")
    selected = name[:-5]
    if selected.casefold() in _RESERVED:
        raise ValueError("Analysis filename '%s' conflicts with a Lean library." % name)
    payload = {key: body[key] for key in ("source", "filename", "standalone", "project_sources") if key in body}
    response = browser.request("/api/compile", payload)
    if response["status"] != 200:
        return response
    compiled = response["body"]
    files = {}
    _add(files, _module_path(compiled["module"]), compiled["lean"])
    _add(files, _module_path(compiled["points_module"]), compiled["points_lean"])
    _add(files, name, body["analysis"])
    support = analysis_support_sources(body["analysis"], compiled["module"])
    for module, text in support.items():
        _add(files, _module_path(module), text)
    libraries = _library_sources(shared_imports(*(text.decode("utf-8") for text in files.values())))
    for module, (_, text) in libraries.items():
        _add(files, _module_path(module), text)
    filename = body.get("filename", "untitled.algo").replace("\\", "/").rsplit("/", 1)[-1]
    if filename in {"", ".", ".."}:
        filename = "untitled.algo"
    _add(files, "source/" + filename, body["source"])
    _add(files, "LICENSE", (browser.ROOT / "LICENSE").read_bytes())
    _add(files, "lean-toolchain", (browser.ROOT / "lean-toolchain").read_bytes())
    return _archive(files, selected)


def _project(body):
    response = browser.request("/api/project-export", body, project=True)
    if response["status"] != 200:
        return response
    files = {}
    with zipfile.ZipFile(io.BytesIO(base64.b64decode(response["body"], validate=True))) as archive:
        for info in archive.infolist():
            _add(files, info.filename, archive.read(info))
    if "EXPORT_DIAGNOSTICS.txt" in files:
        raise ValueError("The analysis bundle could not resolve its source or proof imports: " +
                         files["EXPORT_DIAGNOSTICS.txt"].decode("utf-8").strip())
    selected = "Algo." + body.get("filename", "untitled.algo")[:-5].replace("/", ".") + ".Analysis"
    if _module_path(selected) not in files:
        raise ValueError("The selected analysis is missing from the project export.")
    return _archive(files, selected)


def request(path, body=None, project=False):
    """Mirror ``algo2lean.browser.request`` with an editor-only export endpoint."""
    if path == "/api/capabilities" and body is None:
        response = browser.request(path, body, project)
        if response["status"] == 200:
            response["body"]["analysis_export_protocol"] = 1
        return response
    if path != "/api/analysis-export":
        return browser.request(path, body, project)
    try:
        if type(project) is not bool or not isinstance(body, dict):
            raise ValueError("Send analysis export as a JSON object with a boolean project flag.")
        if len(json.dumps(body, ensure_ascii=True).encode("utf-8")) > MAX_ANALYSIS_REQUEST_BYTES:
            return _error("Analysis export requests must be at most 8 MiB.", 413)
        if body.get("standalone") is True:
            raise ValueError("Analysis bundles use separate generated modules and the shared library; "
                             "omit the standalone option.")
        _text(body.get("source"), "The algorithm source", MAX_SOURCE_BYTES)
        _text(body.get("analysis"), "The analysis", MAX_ANALYSIS_BYTES, required=True)
        return _project(body) if project else _standalone(body)
    except (ValueError, TypeError, UnicodeError, LeanSetupError) as error:
        return _error(str(error))
    except (OSError, zipfile.BadZipFile) as error:
        return _error("The analysis export resources could not be read: " + str(error), 503)
    except (RecursionError, MemoryError):
        return _error("The analysis or its imports are too large or deeply nested to export.")
