"use strict";

// The current catalog changes independently of the archived compiler. Only
// example reads use these static files; compilation stays in the release worker.
((root, factory) => {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.Algo2LeanBackend = api.withCurrentExamples(root.Algo2LeanBackend, {
    baseURL: new URL("examples/", document.currentScript.src),
  });
})(typeof globalThis === "object" ? globalThis : this, () => {
  function withCurrentExamples(backend, options = {}) {
    const fetchFile = options.fetch || fetch;
    return { ...backend, request(path, init = {}) {
      let file = null;
      if (path === "/api/examples") file = "catalog.json";
      const project = /^\/api\/example-project\/([A-Za-z0-9_-]+)$/.exec(path);
      if (project) file = "projects/" + project[1] + ".json";
      if (file !== null && init.body === undefined && (!init.method || init.method === "GET")) {
        return fetchFile(new URL(file, options.baseURL), { signal: init.signal, cache: "no-cache" });
      }
      return backend.request(path, init);
    } };
  }
  return { withCurrentExamples };
});
