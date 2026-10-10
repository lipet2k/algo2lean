"use strict";

const base = new URL(".", import.meta.url);
let runtime = null;
let requests = Promise.resolve();

function status(message) { postMessage({ type: "status", message }); }

async function initialize() {
  status("Loading the browser compiler. The first visit downloads its Python runtime…");
  const response = await fetch(new URL("release-config.json", base));
  if (!response.ok) throw new Error("This release is missing release-config.json. Reload the page or choose another release.");
  const config = await response.json();
  if (!/^[a-f0-9]{64}$/.test(config.compiler_archive_sha256 || "")) throw new Error("This release has invalid compiler metadata.");
  const archiveURL = new URL(config.compiler_archive || "compiler.zip", base);
  const runtimeURL = new URL(config.runtime_url || "runtime/", base);
  if (archiveURL.origin !== base.origin || runtimeURL.origin !== base.origin ||
      !archiveURL.href.startsWith(base.href) || !runtimeURL.href.startsWith(base.href)) {
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

self.onmessage = ({ data }) => {
  requests = requests.then(async () => {
    try {
      runtime = runtime || await initialize();
      runtime.globals.set("_algo2lean_request_json", JSON.stringify({ path: data.path, body: data.body, project: data.project }));
      const result = await runtime.runPythonAsync("json.dumps(_algo2lean_request(**json.loads(_algo2lean_request_json)))");
      runtime.globals.delete("_algo2lean_request_json");
      postMessage({ id: data.id, result: JSON.parse(result) });
    } catch (error) {
      postMessage({ id: data.id, error: error.message || "The browser compiler failed. Reload this release and try again." });
    }
  });
};
