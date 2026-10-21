"""Local-only editor server. Algo2Lean source is parsed, never executed."""

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import ast
import io
import json
import keyword
from pathlib import Path
import re
import tempfile
from threading import BoundedSemaphore
from urllib.parse import urlsplit
import webbrowser
import zipfile

from .checker import LeanSetupError, check_lean
from .analysis import check_analysis
from .modules import generated_module_name
from .compiler import CompileError, compile_source
from .source_validation import parse_source
from .publication import PublicationError, citation_cff, metadata, publication_info


ROOT = Path(__file__).resolve().parent.parent
MAX_SOURCE_BYTES = 256 * 1024
# Analysis files can be much larger than their algorithm source. Match the
# editor's 1 MiB file limit and leave room for source text and JSON escaping.
MAX_ANALYSIS_BYTES = 1024 * 1024
MAX_ANALYSIS_REQUEST_BYTES = 8 * 1024 * 1024
LEAN_SLOTS = BoundedSemaphore(2)
ASSETS = {
    "/": ("index.html", "text/html; charset=utf-8"),
    "/index.html": ("index.html", "text/html; charset=utf-8"),
    "/styles.css": ("styles.css", "text/css; charset=utf-8"),
    "/app.js": ("app.js", "text/javascript; charset=utf-8"),
    "/drafts.js": ("drafts.js", "text/javascript; charset=utf-8"),
    "/interface.js": ("interface.js", "text/javascript; charset=utf-8"),
    "/proof-outline.js": ("proof-outline.js", "text/javascript; charset=utf-8"),
    "/code-search.js": ("code-search.js", "text/javascript; charset=utf-8"),
    "/code-search.css": ("code-search.css", "text/css; charset=utf-8"),
    "/publication.js": ("publication.js", "text/javascript; charset=utf-8"),
}


class EditorHandler(BaseHTTPRequestHandler):
    server_version = "Algo2Lean/0.1"

    def log_message(self, format, *args):
        # Do not log source or user-controlled request bodies.
        pass

    def _send(self, status, data, content_type="application/json; charset=utf-8", *, attachment=None):
        if not isinstance(data, bytes):
            data = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        if content_type == "application/zip":
            self.send_header("Content-Disposition", 'attachment; filename="Algo2Lean-project.zip"')
        elif attachment:
            self.send_header("Content-Disposition", 'attachment; filename="%s"' % attachment)
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; connect-src 'self'; base-uri 'none'; frame-ancestors 'none'; form-action 'none'")
        self.end_headers()
        try:
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _error(self, status, message, scope=None):
        field = "analysis_diagnostics" if scope == "analysis" else "diagnostics"
        self._send(status, {"ok": False, "message": message, "scope": scope,
                            field: [{"message": message, "line": 1, "column": 1}]})

    def _publication_error(self, error):
        self._send(503, {"ok": False, "scope": "setup", "message": "Compiler setup error: " + str(error),
                         "diagnostics": [], "analysis_diagnostics": []})

    def _local_request(self):
        port = self.server.server_port
        allowed = {"127.0.0.1:%d" % port, "localhost:%d" % port}
        if self.headers.get("Host", "") not in allowed:
            self._error(403, "Open this editor using its localhost address.")
            return False
        origin = self.headers.get("Origin")
        if origin and origin not in {"http://" + host for host in allowed}:
            self._error(403, "Requests must come from the local editor.")
            return False
        # Links from other sites may open the editor as a top-level document.
        # This exception does not permit embedded pages, assets, or API calls.
        editor_navigation = (
            self.command == "GET"
            and urlsplit(self.path).path in {"/", "/index.html"}
            and self.headers.get("Sec-Fetch-Mode") == "navigate"
            and self.headers.get("Sec-Fetch-Dest") == "document"
        )
        if self.headers.get("Sec-Fetch-Site") == "cross-site" and not editor_navigation:
            self._error(403, "Requests must come from the local editor.")
            return False
        return True

    def do_GET(self):
        if not self._local_request():
            return
        path = urlsplit(self.path).path
        if path in ASSETS:
            filename, content_type = ASSETS[path]
            try:
                self._send(200, (ROOT / "editor" / filename).read_bytes(), content_type)
            except OSError:
                self._error(404, "The editor asset was not found. Run the server from a complete checkout.")
        elif path == "/api/capabilities":
            # Assets are read from disk on each request, while Python modules
            # stay loaded. A fresh editor must detect an older running server.
            self._send(200, {"project_protocol": 1})
        elif path == "/api/publication":
            try:
                self._send(200, publication_info(ROOT))
            except (OSError, ValueError, KeyError, TypeError):
                self._error(500, "The project publication metadata could not be read.")
        elif path == "/CITATION.cff":
            try:
                citation = citation_cff(metadata(ROOT))
                if citation is None:
                    self._error(404, "The project authors have not configured a software citation yet.")
                else:
                    self._send(200, citation.encode("utf-8"), "application/yaml; charset=utf-8", attachment="CITATION.cff")
            except (OSError, ValueError, KeyError, TypeError):
                self._error(500, "The project citation could not be read.")
        elif path == "/api/examples":
            from .editor_examples import example_files, parallel_examples, project_examples
            examples = []
            for filename in example_files(ROOT / "examples"):
                source = filename.read_text(encoding="utf-8")
                first = source.splitlines()[0] if source else ""
                description = first.lstrip("# ") if first.startswith("#") else ""
                analysis_path = ROOT / "examples" / "analysis" / (filename.stem + ".lean")
                analysis = analysis_path.read_text(encoding="utf-8") if analysis_path.is_file() else None
                name = filename.stem.replace("_", " ").title()
                examples.append({"name": name, "filename": filename.name,
                                 "description": description, "source": source, "analysis": analysis,
                                 "module": generated_module_name(filename.name),
                                 "points_module": generated_module_name(filename.name) + "Points"})
            self._send(200, {"examples": examples + parallel_examples(ROOT / "examples") + project_examples()})
        elif path.startswith("/api/example-project/"):
            from .editor_examples import load_example_project
            try:
                self._send(200, load_example_project(path.removeprefix("/api/example-project/")))
            except KeyError:
                self._error(404, "This example project does not exist.")
            except PublicationError as error:
                self._publication_error(error)
            except (CompileError, LeanSetupError) as error:
                self._error(400, "The example project could not be prepared: " +
                            str(error).replace(str(ROOT) + "/", ""))
            except (OSError, UnicodeError):
                self._error(500, "The example project could not be read. Run the editor from a complete checkout.")
        else:
            self._error(404, "This page does not exist.")

    def do_POST(self):
        if not self._local_request():
            return
        path = urlsplit(self.path).path
        if path not in {"/api/compile", "/api/check", "/api/analyze", "/api/project-export"}:
            self._error(404, "This action does not exist.")
            return
        request_scope = "analysis" if path == "/api/analyze" else None
        if self.headers.get_content_type() != "application/json":
            self._error(415, "Send the request as JSON.", scope=request_scope)
            return
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self._error(400, "Invalid request length.", scope=request_scope)
            return
        project_request = self.headers.get("X-Algo2Lean-Project") == "1"
        request_limit = MAX_ANALYSIS_REQUEST_BYTES if request_scope or project_request else MAX_SOURCE_BYTES
        if not 0 < length <= request_limit:
            message = ("Project requests must be between 1 byte and 8 MiB." if project_request else
                       "Analysis requests must be between 1 byte and 8 MiB." if request_scope else
                       "Source requests must be between 1 byte and 256 KiB.")
            self._error(413, message, scope=request_scope)
            return
        try:
            body = json.loads(self.rfile.read(length).decode("utf-8"))
            if not isinstance(body, dict) or not isinstance(body.get("source"), str):
                self._error(400, "The source field must contain text.")
                return
            filename = body.get("filename", "untitled.algo")
            if not isinstance(filename, str) or len(filename) > 255:
                self._error(400, "The filename must be text of at most 255 characters.")
                return
            standalone = body.get("standalone", False)
            if not isinstance(standalone, bool):
                self._error(400, "The standalone field must be a boolean.")
                return
            if project_request:
                self._project_request(path, body, filename)
                return
            if "project_sources" in body or path == "/api/project-export":
                self._error(400, "Project requests must include X-Algo2Lean-Project: 1.")
                return
            if path == "/api/analyze":
                analysis = body.get("analysis")
                if not isinstance(analysis, str) or not analysis.strip():
                    self._error(400, "The analysis must contain Lean text.", scope="analysis")
                    return
                if any(character == "\x00" or 0xD800 <= ord(character) <= 0xDFFF for character in analysis):
                    self._error(400, "The analysis contains an invalid text character.", scope="analysis")
                    return
                if len(analysis.encode("utf-8")) > MAX_ANALYSIS_BYTES:
                    self._error(400, "The analysis must be at most 1 MiB of UTF-8 Lean text.", scope="analysis")
                    return
            result = compile_source(body["source"], filename=filename, standalone=standalone)
        except PublicationError as error:
            self._publication_error(error)
            return
        except (UnicodeError, json.JSONDecodeError):
            self._error(400, "The request must contain valid UTF-8 JSON.", scope=request_scope)
            return
        except CompileError as error:
            if not project_request:
                # Keep the compiler's precise syntax/type diagnostics. Only
                # replace an error at a top-level import with the editor action
                # needed to provide its dependencies.
                try:
                    imported = next((node for node in parse_source(body["source"], filename).body
                                     if isinstance(node, (ast.Import, ast.ImportFrom))
                                     and node.lineno == error.line), None)
                except CompileError:
                    imported = None
                if imported is not None:
                    error = CompileError(
                        "Imports are supported in projects. Use Open project and select the folder "
                        "containing this file and its imported .algo files.", error.line, error.column)
            self._send(400, {"ok": False, "diagnostics": [error.to_dict()]})
            return
        except (RecursionError, MemoryError):
            self._error(400, "This program is too large or deeply nested. Split it into smaller functions.")
            return
        response = {"ok": True, "lean": result.lean, "program_lean": result.program_lean,
                    "points_lean": result.points_lean, "points_module": result.points_module,
                    "randomized": getattr(result, "randomized", False),
                    "probability_lean": getattr(result, "probability_lean", ""),
                    "probability_module": getattr(result, "probability_module", ""),
                    "probability_diagnostic": getattr(result, "probability_diagnostic", ""),
                    "shared_lean": result.shared_lean, "stats": result.stats,
                    "functions": result.functions, "diagnostics": [], "module": result.module}
        if path in {"/api/check", "/api/analyze"}:
            if not LEAN_SLOTS.acquire(blocking=False):
                self._error(429, "Two Lean checks are already running. Try again shortly.",
                            scope="analysis" if path == "/api/analyze" else None)
                return
            try:
                if path == "/api/analyze":
                    analysis_options = {"points_lean": result.points_lean}
                    if response["randomized"] and response["probability_lean"]:
                        analysis_options["probability_lean"] = response["probability_lean"]
                    checked = self._check_analysis(result.lean, analysis, result.module, **analysis_options)
                    response.update(scope="analysis", analysis_diagnostics=analysis_diagnostics(checked.output))
                else:
                    checked = self._check_generated(result.lean, module=result.module, points_lean=result.points_lean)
                response.update(ok=checked.ok, available=checked.available, output=checked.output)
                if path == "/api/check" and response["randomized"]:
                    response.update(probability_checked=False)
                    response["output"] += "\nProbability companions require separate checking with the optional probability/ Mathlib project."
            finally:
                LEAN_SLOTS.release()
        self._send(200, response)

    def _check_generated(self, *args, **kwargs):
        return check_lean(*args, **kwargs)

    def _check_analysis(self, *args, **kwargs):
        return check_analysis(*args, **kwargs)

    def _check_project(self, *args, **kwargs):
        from .project_checker import check_project
        return check_project(*args, **kwargs)

    def _project_request(self, path, body, filename):
        """Projects contain only files explicitly selected in the browser."""
        from .modular import compile_project
        sources = body.get("project_sources")
        proofs = body.get("project_analyses", {})
        if not isinstance(sources, dict) or not sources or len(sources) > 256:
            self._error(400, "A project must contain between 1 and 256 .algo source files.")
            return
        if not isinstance(proofs, dict) or len(proofs) > 256:
            self._error(400, "Project analyses must be a mapping of at most 256 Lean modules to text.")
            return
        if body.get("standalone"):
            self._error(400, "Project modules share the runtime library; use Download project to export it.")
            return
        for name, source in sources.items():
            if (not isinstance(name, str) or not re.fullmatch(r"(?:[A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.algo", name)
                    or len(name) > 255 or any(keyword.iskeyword(part) for part in name[:-5].split("/"))
                    or not isinstance(source, str)):
                self._error(400, "Project sources must use relative .algo filenames with identifier path components.")
                return
            if len(source.encode("utf-8")) > MAX_SOURCE_BYTES:
                self._error(413, "Each algorithm source must be at most 256 KiB.")
                return
        for name, proof in proofs.items():
            if (not isinstance(name, str) or not re.fullmatch(r"Algo(?:\.[A-Za-z_][A-Za-z0-9_]*)+\.Analysis", name)
                    or not isinstance(proof, str)):
                self._error(400, "Analysis names must have the form Algo.module.Analysis.", scope="analysis")
                return
            if len(proof.encode("utf-8")) > MAX_ANALYSIS_BYTES:
                self._error(413, "Each analysis must be at most 1 MiB.", scope="analysis")
                return
            if any(character == "\x00" or 0xD800 <= ord(character) <= 0xDFFF for character in proof):
                self._error(400, "An analysis contains an invalid text character.", scope="analysis")
                return
        analysis = body.get("analysis")
        if path == "/api/analyze" and (not isinstance(analysis, str) or not analysis.strip()):
            self._error(400, "The analysis must contain Lean text.", scope="analysis")
            return
        if isinstance(analysis, str) and (len(analysis.encode("utf-8")) > MAX_ANALYSIS_BYTES or
                any(character == "\x00" or 0xD800 <= ord(character) <= 0xDFFF for character in analysis)):
            self._error(400, "The analysis must be valid text of at most 1 MiB.", scope="analysis")
            return
        sources = dict(sources)
        # The current editor text overrides its previously selected disk snapshot.
        if filename not in sources:
            self._error(400, "Select an algorithm file that belongs to the open project.")
            return
        if len(body["source"].encode("utf-8")) > MAX_SOURCE_BYTES:
            self._error(413, "Each algorithm source must be at most 256 KiB.")
            return
        sources[filename] = body["source"]
        selected_proof = "Algo." + filename[:-5].replace("/", ".") + ".Analysis"
        proofs = dict(proofs)
        if isinstance(analysis, str):
            proofs[selected_proof] = analysis
        if len(proofs) > 256:
            self._error(400, "A project can contain at most 256 analysis modules, including the active analysis.", scope="analysis")
            return
        # Check archive path identity before attempting compilation. Draft-only
        # exports must not bypass validation or overwrite a case-colliding file
        # when the archive is extracted on a case-insensitive filesystem.
        spellings = {}
        modules = [name[:-5].replace("/", ".") for name in sources]
        modules.extend(name[len("Algo."):-len(".Analysis")] for name in proofs)
        for module in modules:
            parts = module.split(".")
            for end in range(1, len(parts) + 1):
                prefix = ".".join(parts[:end])
                previous = spellings.get(prefix.casefold())
                if previous is not None and previous != prefix:
                    self._error(400, "Case-colliding project paths '%s' and '%s'." % (previous, prefix))
                    return
                spellings[prefix.casefold()] = prefix
        with tempfile.TemporaryDirectory(prefix="algo2lean-editor-project-") as directory:
            # macOS commonly exposes /var through a /private/var alias; match
            # the resolver's canonical paths before presenting diagnostics.
            directory = str(Path(directory).resolve())
            project, export_diagnostic = None, None
            try:
                project = compile_project(filename, root=directory, sources=sources)
            except CompileError as error:
                if path == "/api/project-export":
                    export_diagnostic = str(error).replace(directory + "/", "")
                else:
                    diagnostic = error.to_dict()
                    if "file" in diagnostic:
                        diagnostic["file"] = diagnostic["file"].removeprefix(directory + "/")
                    diagnostic["message"] = diagnostic["message"].replace(directory + "/", "")
                    if diagnostic["message"].startswith("Module '") and " was not found at " in diagnostic["message"]:
                        diagnostic["message"] += (
                            " Open the folder containing all imported modules as the project root.")
                    self._send(400, {"ok": False, "diagnostics": [diagnostic]})
                    return
            except (RecursionError, MemoryError):
                if path != "/api/project-export":
                    raise
                export_diagnostic = "This program is too large or deeply nested to compile. Split it into smaller functions."
            if path == "/api/project-export":
                archive = project_archive(project, proofs, sources, diagnostics=export_diagnostic)
                self._send(200, archive, "application/zip")
                return
            response = project_response(project)
            if path in {"/api/check", "/api/analyze"}:
                if not LEAN_SLOTS.acquire(blocking=False):
                    self._error(429, "Two Lean checks are already running. Try again shortly.",
                                scope="analysis" if path == "/api/analyze" else None)
                    return
                try:
                    checked = self._check_project(project, proof_sources=proofs,
                        analysis_module=selected_proof if path == "/api/analyze" else None)
                    output = checked.output.replace(directory + "/", "")
                    response.update(ok=checked.ok, available=checked.available, output=output)
                    if path == "/api/check" and response["randomized"]:
                        response.update(probability_checked=False)
                        response["output"] += "\nProbability companions require separate checking with the optional probability/ Mathlib project."
                    if path == "/api/analyze":
                        response.update(scope="analysis", analysis_diagnostics=project_analysis_diagnostics(output, project.project.entry))
                finally:
                    LEAN_SLOTS.release()
            self._send(200, response)


def project_response(compilation):
    """Build the selected module's generated-code, named-location, and interface response."""
    from .emitter import public_types
    from .public_names import interface_metadata
    entry = compilation.entry
    implementation = getattr(entry, "implementation", None)
    probability_module = getattr(entry, "probability_module", "") or entry.namespace + ".Probability"
    probability_lean = getattr(entry, "probability_lean", "") or compilation.files.get(probability_module, "")
    functions = []
    for function in entry.functions.values():
        if getattr(function.node, "parallel_adapter", False):
            continue
        inputs, output = public_types(function)
        functions.append({"name": function.name,
            "display_name": (function.class_name + "." + function.method_name) if function.class_name else function.name,
            "lean_input_type": inputs, "lean_output_type": output,
            "parameters": [{"name": name, "type": typ} for name, typ in function.parameters],
            "return_type": function.return_type, "clocks": list(entry.clocks),
            **interface_metadata(function, bool(entry.clocks) or bool(entry.dependencies),
                                 dependencies=bool(entry.dependencies), facts=function.name in entry.deterministic_functions,
                                 randomized=function.name not in entry.deterministic_functions, probability=bool(probability_lean),
                                 parallel=function.name in entry.parallel_functions),
            "points": list(function.points.values())})
        for declaration in functions[-1]["interface_entries"]:
            if ".ParallelCall" in declaration["name"]:
                declaration["file_kind"] = "parallel"
    return {"ok": True, "lean": entry.lean, "program_lean": entry.lean,
            "points_lean": entry.points_lean, "points_module": entry.points_module,
            "randomized": getattr(entry, "randomized", False),
            "probability_lean": probability_lean,
            "probability_module": probability_module if probability_lean else "",
            "probability_diagnostic": getattr(entry, "probability_diagnostic", ""),
            "parallel_module": entry.parallel_module, "parallel_lean": entry.parallel_lean,
            "shared_lean": "", "stats": entry.stats, "functions": functions,
            "diagnostics": [], "module": entry.lean_module, "namespace": entry.namespace,
            "implementation_module": implementation.lean_module if implementation else None,
            "implementation_points_module": implementation.points_module if implementation else None,
            "implementation_facts_module": implementation.facts_module if implementation else None,
            "project_files": compilation.files,
            "project_modules": [{"name": module.name,
                "filename": "/".join(module.name.split(".")) + ".algo",
                "module": module.lean_module, "points_module": module.points_module,
                "namespace": module.namespace} for module in compilation.modules.values()]}


def project_archive(compilation, proofs, source_files=None, *, diagnostics=None):
    """Always preserve validated drafts; add build files when imports resolve."""
    from .checker import LeanSetupError, _library_sources, shared_imports
    from .project_checker import project_lean_sources
    files = {}
    if compilation is not None:
        for name, module in compilation.project.modules.items():
            files["source/" + name.replace(".", "/") + ".algo"] = module.source
    for filename, source in (source_files or {}).items():
        files["source/" + filename] = source
    for name, source in proofs.items():
        files["source/analysis/" + name[len("Algo."):-len(".Analysis")].replace(".", "/") + ".lean"] = source
    if compilation is not None:
        try:
            generated = dict(compilation.files)
            generated.update(project_lean_sources(compilation, proof_sources=proofs, analysis_modules=tuple(proofs)))
            build = {name.replace(".", "/") + ".lean": source for name, source in generated.items()}
            from .probability_support import needs_mathlib, optional_sources, mathlib_requirement, SETUP_INSTRUCTIONS
            optional = optional_sources(build.values())
            mathlib = needs_mathlib(build.values())
            build.update(optional)
            shared = _library_sources(shared_imports(*build.values()))
            build.update({name.replace(".", "/") + ".lean": source for name, (_, source) in shared.items()})
            build["LICENSE"] = (ROOT / "LICENSE").read_text(encoding="utf-8")
            build["Algo.lean"] = "import " + compilation.entry.lean_module + "\n"
            build["lean-toolchain"] = (ROOT / "lean-toolchain").read_text(encoding="utf-8")
            build["lakefile.toml"] = ('name = "algo2lean_project"\nversion = "0.1.0"\n'
                'defaultTargets = ["Algo"]\n\n[[lean_lib]]\nname = "Algo"\n\n'
                '[[lean_lib]]\nname = "Algo2Lean"\n\n[[lean_lib]]\nname = "Algo2LeanLib"\n')
            if any(name.startswith("Algo2LeanExamples.") for name in shared):
                build["lakefile.toml"] += '\n[[lean_lib]]\nname = "Algo2LeanExamples"\n'
            if mathlib:
                build["lakefile.toml"] += "".join(
                    '\n[[lean_lib]]\nname = "%s"\n' % path.removesuffix(".lean") for path in optional)
                build["lakefile.toml"] += mathlib_requirement()
                setup_file = "PROBABILITY.md" if "Algo2LeanProbability.lean" in optional else "MATHLIB.md"
                build[setup_file] = SETUP_INSTRUCTIONS
            files.update(build)
        except (LeanSetupError, CompileError, OSError, UnicodeError) as error:
            diagnostics = str(error).replace(str(compilation.project.root) + "/", "")
        except (RecursionError, MemoryError):
            diagnostics = "The project or its proof imports are too large or deeply nested to generate build files."
    files["README.md"] = ("# Algo2Lean project\n\nOpen the `source` folder in the Algo2Lean editor to edit algorithms and analyses.\n"
        "All supplied source and analysis drafts are preserved there, including unsaved and unfinished edits.\n\n")
    if diagnostics or compilation is None:
        files["EXPORT_DIAGNOSTICS.txt"] = (diagnostics or "The project could not be compiled.") + "\n"
        files["README.md"] += ("This archive is a draft backup. Generated Lean build files are unavailable because a source or import could not be resolved.\n"
            "See `EXPORT_DIAGNOSTICS.txt`, fix the reported issue, and download the project again to include build files.\n")
    else:
        files["README.md"] += ("The `Algo` folder contains generated Lean definitions and analysis modules. Downloading does not check the proofs.\n"
            "Run `lake build` to check the selected algorithm definitions; build an `Algo.<module>.Analysis` target to check its proof.\n")
    if "LICENSE" in files:
        files["README.md"] += ("\nThe included Algo2Lean shared libraries are covered by `LICENSE`. "
            "This notice does not assign a license to your algorithm or proof.\n")
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, source in files.items():
            archive.writestr(name, source)
    return output.getvalue()


def project_analysis_diagnostics(output, entry):
    """Preserve which imported analysis produced a diagnostic."""
    pattern = r"^(Algo/(?:[A-Za-z_][A-Za-z0-9_]*/)+Analysis\.lean):(\d+):(\d+): (?:error|warning)(?:\([^\n)]*\))?:\s*"
    matches = list(re.finditer(pattern, output, re.MULTILINE))
    return [{"file": match[1], "module": match[1][5:-len('/Analysis.lean')].replace("/", "."),
             "line": int(match[2]), "column": int(match[3]) + 1,
             "message": output[match.end():matches[index + 1].start() if index + 1 < len(matches) else len(output)].strip()}
            for index, match in enumerate(matches)]


def analysis_diagnostics(output):
    """Locations refer to the independently checked analysis file."""
    matches = list(re.finditer(r"^Analysis\.lean:(\d+):(\d+): (?:error|warning)(?:\([^\n)]*\))?:\s*", output, re.MULTILINE))
    # Lean reports one-based lines and zero-based columns; the editor uses one-based positions.
    return [{"line": int(match[1]), "column": int(match[2]) + 1,
             "message": output[match.end():matches[index + 1].start() if index + 1 < len(matches) else len(output)].strip()}
            for index, match in enumerate(matches)]


def serve(port=8765, open_browser=False):
    if not 0 <= port <= 65535:
        raise ValueError("Port must be between 0 and 65535.")
    server = ThreadingHTTPServer(("127.0.0.1", port), EditorHandler)
    address = "http://127.0.0.1:%d" % server.server_port
    print("Algo2Lean editor: %s\nPress Ctrl+C to stop." % address, flush=True)
    if open_browser:
        webbrowser.open(address)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nEditor stopped.", flush=True)
    finally:
        server.server_close()
