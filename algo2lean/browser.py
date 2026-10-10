"""Socket-free editor API for the hosted compiler and native reproduction.

The browser worker mounts the release resources beside this package. Requests
use the local editor's validation and compilation code; only transport and
availability of Lean checking differ. No source is executed as Python.
"""

import base64
from email.message import Message
import hashlib
import io
import json
from pathlib import Path
import platform
from urllib.parse import urlsplit
import zipfile

from .checker import CheckResult, LeanSetupError, _library_sources, shared_imports
from .publication import PublicationError, compiler_metadata
from .server import EditorHandler


ROOT = Path(__file__).resolve().parent.parent
LOCAL_CHECK_MESSAGE = (
    "Lean proof checking is not available in the browser. Download the generated "
    "files or project and check them locally with the pinned Lean toolchain. "
    "Generation matching does not check a Lean proof."
)
_GET_ROUTES = {"/api/examples", "/api/publication", "/api/capabilities", "/CITATION.cff"}
_POST_ROUTES = {"/api/compile", "/api/check", "/api/analyze", "/api/project-export", "/api/generation"}


class _MemoryHandler(EditorHandler):
    """Reuse HTTP handlers without creating a server, socket, or thread."""

    def __init__(self, path, body, project):
        self.path = path
        self.command = "GET" if body is None else "POST"
        self.headers = Message()
        self.response = None
        encoded = b"" if body is None else json.dumps(body, ensure_ascii=True).encode("utf-8")
        self.rfile = io.BytesIO(encoded)
        self.headers["Content-Type"] = "application/json"
        self.headers["Content-Length"] = str(len(encoded))
        if project:
            self.headers["X-Algo2Lean-Project"] = "1"

    def _local_request(self):
        return True

    def _send(self, status, data, content_type="application/json; charset=utf-8", *, attachment=None):
        response = {"status": status, "content_type": content_type, "body": data}
        if isinstance(data, bytes):
            if content_type == "application/zip":
                response.update(body=base64.b64encode(data).decode("ascii"), encoding="base64")
            else:
                response["body"] = data.decode("utf-8")
        self.response = response

    def _check_generated(self, *args, **kwargs):
        return CheckResult(False, False, LOCAL_CHECK_MESSAGE)

    def _check_analysis(self, *args, **kwargs):
        return CheckResult(False, False, LOCAL_CHECK_MESSAGE)

    def _check_project(self, *args, **kwargs):
        return CheckResult(False, False, LOCAL_CHECK_MESSAGE)


def _identity(contents):
    raw = contents.encode("utf-8") if isinstance(contents, str) else contents
    return {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}


def _identities(files):
    return {name: _identity(source) for name, source in sorted(files.items())}


def _source_files(body, compiled, project):
    if project:
        sources = dict(body["project_sources"])
        sources[body.get("filename", "untitled.algo")] = body["source"]
        return {module["filename"]: sources[module["filename"]]
                for module in compiled["project_modules"]}
    # Source names are logical identities, never a caller's absolute path.
    filename = body.get("filename", "untitled.algo").replace("\\", "/").rsplit("/", 1)[-1]
    return {filename if filename not in {"", ".", ".."} else "untitled.algo": body["source"]}


def generation(body, compiled, *, project=False):
    """Describe already-validated compilation with deterministic content hashes.

    The separate manifest records exact UTF-8 source text, without normalizing
    newlines. It does not add labels, hashes, or paths to the stable Lean core.
    Only transitive source dependencies belong to a project's generation.
    """
    if project:
        files = {module.replace(".", "/") + ".lean": source
                 for module, source in compiled["project_files"].items()}
    else:
        files = {compiled["module"] + ".lean": compiled["lean"],
                 compiled["points_module"] + ".lean": compiled["points_lean"]}
    libraries = {path.as_posix(): source.decode("utf-8") for path, source in
                 _library_sources(shared_imports(*files.values())).values()}
    sources = _source_files(body, compiled, project)
    metadata = compiler_metadata(ROOT)
    identity_path = ROOT / "release-manifest.json"
    release = json.loads(identity_path.read_text(encoding="utf-8")) if identity_path.is_file() else {}
    if not isinstance(release, dict):
        raise ValueError("The release manifest must be a JSON object.")
    compiler_files = {path.relative_to(ROOT).as_posix(): path.read_bytes()
                      for path in sorted((ROOT / "algo2lean").glob("*.py"))}
    compiler_files["publication.json"] = (ROOT / "publication.json").read_bytes()
    compiler_hashes = _identities(compiler_files)
    compiler_hash = hashlib.sha256(json.dumps(compiler_hashes, sort_keys=True,
                                             separators=(",", ":")).encode("utf-8")).hexdigest()
    manifest = {
        "schema_version": 1,
        "compiler": {"name": metadata["title"], "version": metadata["version"],
                     "commit": release.get("commit"), "bundle_sha256": release.get("bundle_sha256"),
                     "source_sha256": compiler_hash},
        "runtime": {"python": platform.python_version(), "pyodide": release.get("pyodide_version")},
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "source_encoding": "UTF-8; source text is hashed without newline normalization",
        "options": {"mode": "project" if project else "single", "entry": body.get("filename", "untitled.algo") if project else next(iter(sources)),
                    "module": compiled["module"], "namespace": compiled.get("namespace", ""),
                    "standalone": body.get("standalone", False)},
        "sources": _identities(sources), "outputs": _identities(files),
        "libraries": _identities(libraries),
    }
    return {"ok": True, "files": dict(sorted(files.items())),
            "libraries": dict(sorted(libraries.items())), "manifest": manifest}


def _generation_archive(data, body, compiled, project):
    files = {**data["libraries"], **data["files"]}
    files["LICENSE"] = (ROOT / "LICENSE").read_text(encoding="utf-8")
    files.update({"source/" + name: text for name, text in _source_files(body, compiled, project).items()})
    files["generation.json"] = json.dumps(data["manifest"], ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    files["lean-toolchain"] = data["manifest"]["lean_toolchain"] + "\n"
    if project:
        targets = sorted(compiled["project_files"])
        libraries = ["Algo"]
    else:
        targets = [compiled["module"], compiled["points_module"]]
        libraries = targets
    files["lakefile.toml"] = ('name = "algo2lean_generation"\nversion = "0.1.0"\n'
        'defaultTargets = ' + json.dumps(targets) + "\n" +
        "".join('\n[[lean_lib]]\nname = ' + json.dumps(name) + "\n"
                for name in ["Algo2Lean", "Algo2LeanLib", *libraries]))
    files["README.md"] = (
        "# Algo2Lean generated files\n\n"
        "Run `lake build` with the pinned Lean toolchain to check the generated definitions.\n"
        "`generation.json` identifies the compiler, source texts, outputs, and shared libraries.\n"
        "The `source` folder preserves the exact UTF-8 algorithm inputs.\n"
        "Generation matching does not check an analysis proof or prove the compiler correct.\n"
        "User-written analysis files are not part of this generated-code bundle.\n"
        "\nThe included Algo2Lean shared libraries are covered by `LICENSE`. "
        "This notice does not assign a license to your algorithm or proof.\n"
    )
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, contents in sorted(files.items()):
            info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, contents.encode("utf-8"))
    return output.getvalue()


def request(path, body=None, project=False):
    """Handle a worker request and return a JSON-compatible transport envelope.

    JSON responses have an object body. ZIP responses have a base64 body and
    ``encoding: "base64"``. ``/api/generation`` returns generated files, shared
    libraries and a separate manifest; ``archive: true`` downloads that bundle.
    Lean-check routes preserve validation but always return ``available: false``.
    """
    try:
        parsed = urlsplit(path) if isinstance(path, str) else None
        route = parsed.path if parsed else ""
        if not parsed or parsed.scheme or parsed.netloc or parsed.fragment or parsed.query or type(project) is not bool:
            raise ValueError("Use a relative API path and a boolean project flag.")
        handler = _MemoryHandler("/api/compile" if route == "/api/generation" else route, body, project)
    except (TypeError, ValueError, UnicodeError):
        return {"status": 400, "content_type": "application/json; charset=utf-8",
                "body": {"ok": False, "message": "The browser request is invalid.", "diagnostics": []}}
    if body is None:
        if route not in _GET_ROUTES and not route.startswith("/api/example-project/"):
            handler._error(404, "This browser compiler endpoint does not exist.")
        else:
            handler.do_GET()
            if route == "/api/capabilities" and handler.response["status"] == 200:
                handler.response["body"].update(browser_compiler=True, lean_check=False, generation_verifier=True)
    elif route not in _POST_ROUTES:
        handler._error(404, "This browser compiler endpoint does not exist.")
    else:
        handler.do_POST()
        if route == "/api/generation" and handler.response["status"] == 200:
            try:
                compiled = handler.response["body"]
                data = generation(body, compiled, project=project)
                if body.get("archive") is True:
                    handler._send(200, _generation_archive(data, body, compiled, project), "application/zip")
                else:
                    handler._send(200, data)
            except (OSError, UnicodeError, ValueError, LeanSetupError, PublicationError) as error:
                handler._error(503, "The release resources could not be read: " + str(error))
    return handler.response
