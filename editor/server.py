"""Current local editor service without changing the frozen compiler package.

Run ``python -m editor.server --port 8765`` from the repository root.
"""

import argparse
import base64
import json
from pathlib import Path
from urllib.parse import urlsplit
import webbrowser

from algo2lean.server import EditorHandler as CompilerHandler, MAX_ANALYSIS_REQUEST_BYTES, ThreadingHTTPServer
from .analysis_export import request


ROOT = Path(__file__).resolve().parent


class EditorHandler(CompilerHandler):
    def do_GET(self):
        path = urlsplit(self.path).path
        if path not in {"/api/capabilities", "/analysis_export.py"}:
            return super().do_GET()
        if not self._local_request():
            return
        if path == "/api/capabilities":
            self._send(200, {"project_protocol": 1, "analysis_export_protocol": 1})
        else:
            try:
                self._send(200, (ROOT / "analysis_export.py").read_bytes(), "text/x-python; charset=utf-8")
            except OSError:
                self._error(404, "The analysis export adapter was not found.")

    def do_POST(self):
        if urlsplit(self.path).path != "/api/analysis-export":
            return super().do_POST()
        if not self._local_request():
            return
        if self.headers.get_content_type() != "application/json":
            self._error(415, "Send the request as JSON.")
            return
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self._error(400, "Invalid request length.")
            return
        if not 0 < length <= MAX_ANALYSIS_REQUEST_BYTES:
            self._error(413, "Analysis export requests must be between 1 byte and 8 MiB.")
            return
        try:
            body = json.loads(self.rfile.read(length).decode("utf-8"))
        except (UnicodeError, json.JSONDecodeError):
            self._error(400, "The request must contain valid UTF-8 JSON.")
            return
        response = request(urlsplit(self.path).path, body, project=self.headers.get("X-Algo2Lean-Project") == "1")
        contents = (base64.b64decode(response["body"]) if response.get("encoding") == "base64"
                    else response["body"])
        self._send(response["status"], contents, response["content_type"])


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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--open", action="store_true", dest="open_browser")
    arguments = parser.parse_args()
    serve(arguments.port, arguments.open_browser)
