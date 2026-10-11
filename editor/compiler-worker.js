"use strict";

const base = new URL(".", import.meta.url);
let runtime = null;
let requests = Promise.resolve();
let analysisExportReady = false;

function status(message) { postMessage({ type: "status", message }); }

async function initialize() {
  status("Loading the browser compiler. The first visit downloads its Python runtime…");
  const response = await fetch(new URL("release-config.json", base));
  if (!response.ok) throw new Error("This release is missing release-config.json. Reload the page or choose another release.");
  const config = await response.json();
  if (!/^[a-f0-9]{64}$/.test(config.compiler_archive_sha256 || "")) throw new Error("This release has invalid compiler metadata.");
  // The current editor can evolve independently of the archived compiler.
  // Only this exact, same-site version directory may supply a frozen runtime.
  const compilerBase = config.compiler_base ? new URL(config.compiler_base, base) : base;
  if (compilerBase.href !== base.href &&
      (!/^[A-Za-z0-9][A-Za-z0-9.+-]*$/.test(config.version || "") ||
       compilerBase.href !== new URL("../versions/v" + config.version + "/", base).href)) {
    throw new Error("The editor's compiler location is invalid.");
  }
  const archiveURL = new URL(config.compiler_archive || "compiler.zip", compilerBase);
  const runtimeURL = new URL(config.runtime_url || "runtime/", compilerBase);
  if (archiveURL.origin !== base.origin || runtimeURL.origin !== base.origin ||
      !archiveURL.href.startsWith(compilerBase.href) || !runtimeURL.href.startsWith(compilerBase.href)) {
    throw new Error("This release must serve its compiler and runtime from the same release directory.");
  }
  const archive = await fetch(archiveURL);
  if (!archive.ok) throw new Error("The compiler bundle could not be downloaded. Check your connection and reload this release.");
  const bytes = await archive.arrayBuffer();
  const digest = Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)),
    (byte) => byte.toString(16).padStart(2, "0")).join("");
  if (digest !== config.compiler_archive_sha256) throw new Error("The compiler bundle does not match this release's recorded hash. Reload the page; if the problem persists, choose another release.");
  const { loadPyodide } = await import(new URL("pyodide.mjs", runtimeURL).href);
  const python = await loadPyodide({ indexURL: runtimeURL.href });
  if (config.pyodide_version && python.version !== config.pyodide_version) throw new Error("The Python runtime does not match this release.");
  python.unpackArchive(bytes, "zip", { extractDir: "/release" });
  python.FS.writeFile("/release/release-config.json", JSON.stringify(config));
  await python.runPythonAsync("import sys, json\nsys.path.insert(0, '/release')\nfrom algo2lean.browser import request as _algo2lean_request");
  status("Browser compiler ready. Source stays on your device; Lean proof checking runs locally.");
  postMessage({ type: "ready" });
  return python;
}

async function prepareAnalysisExport(python) {
  if (analysisExportReady) return;
  const response = await fetch(new URL("analysis_export.py", base));
  if (!response.ok) throw new Error("Analysis packaging could not load. Reload the editor and try again.");
  python.FS.writeFile("/release/editor_analysis_export.py", await response.text());
  await python.runPythonAsync("from editor_analysis_export import request as _algo2lean_export_request");
  analysisExportReady = true;
}

self.onmessage = ({ data }) => {
  requests = requests.then(async () => {
    try {
      runtime = runtime || await initialize();
      const exporting = data.path === "/api/analysis-export";
      if (exporting) await prepareAnalysisExport(runtime);
      runtime.globals.set("_algo2lean_request_json", JSON.stringify({ path: data.path, body: data.body, project: data.project }));
      const handler = exporting ? "_algo2lean_export_request" : "_algo2lean_request";
      const result = await runtime.runPythonAsync("json.dumps(" + handler + "(**json.loads(_algo2lean_request_json)))");
      runtime.globals.delete("_algo2lean_request_json");
      postMessage({ id: data.id, result: JSON.parse(result) });
    } catch (error) {
      postMessage({ id: data.id, error: error.message || "The browser compiler failed. Reload this release and try again." });
    }
  });
};
