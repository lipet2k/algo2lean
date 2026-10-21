"use strict";

((root, factory) => {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else {
    root.Algo2LeanBrowserHost = api;
    root.Algo2LeanBackend = api.createBackend({
      workerURL: new URL("compiler-worker.js", document.currentScript.src),
      status(message) {
        const element = document.getElementById("browser-runtime-status");
        if (element) element.textContent = message;
      },
    });
  }
})(typeof globalThis === "object" ? globalThis : this, () => {
  function abortError() { return new DOMException("Compilation canceled.", "AbortError"); }

  function createBackend(options = {}) {
    const makeWorker = options.makeWorker || ((url) => new Worker(url, { type: "module" }));
    const responseClass = options.Response || Response;
    const schedule = options.setTimeout || setTimeout;
    const unschedule = options.clearTimeout || clearTimeout;
    let worker = null, active = null, ready = false, serial = 0;
    const queue = [];

    function reset() {
      if (worker) worker.terminate();
      worker = null;
      ready = false;
    }
    function finish(error, value) {
      const job = active;
      if (!job) return;
      active = null;
      unschedule(job.timer);
      job.signal?.removeEventListener("abort", job.cancel);
      if (error) job.reject(error); else job.resolve(value);
      pump();
    }
    function arm(milliseconds) {
      unschedule(active.timer);
      active.timer = schedule(() => {
        reset();
        finish(new Error("The browser compiler timed out and was restarted. Try again, or compile this project locally."));
      }, milliseconds);
    }
    function getWorker() {
      if (worker) return worker;
      const created = makeWorker(options.workerURL);
      worker = created;
      created.onmessage = ({ data }) => {
        if (created !== worker) return;
        if (data.type === "status") { options.status?.(data.message); return; }
        if (data.type === "ready") {
          ready = true;
          if (active) arm(options.requestTimeout || 90000);
          return;
        }
        if (!active || data.id !== active.id) return;
        if (data.error) {
          reset();
          finish(new Error(data.error));
          return;
        }
        try {
          const result = data.result;
          const content = result.encoding === "base64"
            ? Uint8Array.from(atob(result.body), (character) => character.charCodeAt(0))
            : typeof result.body === "string" ? result.body : JSON.stringify(result.body);
          finish(null, new responseClass(content, { status: result.status,
            headers: { "Content-Type": result.content_type || "application/json" } }));
        } catch (_) {
          reset();
          finish(new Error("The browser compiler returned an unreadable response. Reload this release and try again."));
        }
      };
      created.onerror = (event) => {
        if (created !== worker) return;
        event.preventDefault?.();
        reset();
        finish(new Error("The browser compiler could not load. Check your connection and reload this release. You can also use the local Python compiler."));
      };
      return created;
    }
    function pump() {
      if (active || !queue.length) return;
      active = queue.shift();
      if (active.signal?.aborted) { finish(abortError()); return; }
      try {
        const running = getWorker();
        arm(ready ? (options.requestTimeout || 90000) : (options.loadTimeout || 180000));
        running.postMessage({ id: active.id, path: active.path, body: active.body, project: active.project });
      } catch (error) { reset(); finish(error); }
    }
    function request(path, init = {}) {
      if (!/^\/api\/[a-z0-9_/-]+$/.test(path) && path !== "/CITATION.cff") {
        return Promise.reject(new Error("The browser backend only accepts compiler API requests."));
      }
      if (init.signal?.aborted) return Promise.reject(abortError());
      let body;
      try { body = init.body === undefined ? null : JSON.parse(init.body); }
      catch (_) { return Promise.reject(new Error("Compiler requests must contain JSON.")); }
      return new Promise((resolve, reject) => {
        const headers = new Headers(init.headers);
        const job = { id: ++serial, path, body, project: headers.get("X-Algo2Lean-Project") === "1",
          signal: init.signal, resolve, reject, timer: null };
        job.cancel = () => {
          if (active === job) { reset(); finish(abortError()); }
          else {
            const index = queue.indexOf(job);
            if (index >= 0) queue.splice(index, 1);
            job.signal?.removeEventListener("abort", job.cancel);
            reject(abortError());
          }
        };
        job.signal?.addEventListener("abort", job.cancel, { once: true });
        queue.push(job);
        pump();
      });
    }
    return { hosted: true, request };
  }

  async function compareFiles(expected, selected, libraries = {}, signal) {
    const encoder = new TextEncoder();
    const required = Object.keys(expected).sort();
    const contents = { ...libraries, ...expected };
    const names = Object.keys(contents).sort();
    const matched = new Set(), extra = [], different = [], duplicate = [];
    let bytes = 0;
    if (selected.length > 1024) throw new Error("Choose at most 1,024 generated Lean files.");
    for (const file of selected) {
      if (signal?.aborted) throw abortError();
      bytes += file.size;
      if (bytes > 128 * 1024 * 1024 || file.size > 32 * 1024 * 1024) {
        throw new Error("Choose generated files smaller than 32 MB each and 128 MB together.");
      }
      const relative = file.webkitRelativePath || file.name;
      // Folder selections carry module paths. Only the chosen root directory
      // may be stripped; a misplaced module must not match by filename alone.
      const candidates = file.webkitRelativePath
        ? [relative, relative.split("/").slice(1).join("/")]
        : [file.name, file.name.slice(0, -5).replace(/\./g, "/") + ".lean"];
      let name = candidates.find((candidate) => Object.hasOwn(contents, candidate));
      if (!name && !file.webkitRelativePath) {
        const suffixes = names.filter((candidate) => candidate.split("/").pop() === file.name);
        if (suffixes.length === 1) name = suffixes[0];
      }
      if (!name) { extra.push(relative); continue; }
      if (matched.has(name)) { duplicate.push(relative); continue; }
      matched.add(name);
      const actual = new Uint8Array(await file.arrayBuffer()), generated = encoder.encode(contents[name]);
      if (signal?.aborted) throw abortError();
      if (actual.length !== generated.length || actual.some((byte, index) => byte !== generated[index])) different.push(name);
    }
    const missing = required.filter((name) => !matched.has(name));
    return { exact: !missing.length && !extra.length && !different.length && !duplicate.length,
      compared: matched.size, missing, extra, different, duplicate };
  }
  return { createBackend, compareFiles };
});
