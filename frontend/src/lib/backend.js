// The hosted site installs window.Algo2LeanBackend (browser-host.js) before the
// editor starts; the local Python server is reached with fetch otherwise.
export function getBackend() {
  return globalThis.Algo2LeanBackend || null;
}

export function isHosted() {
  return Boolean(getBackend()?.hosted);
}

export function request(path, options) {
  const backend = getBackend();
  return backend ? backend.request(path, options) : fetch(path, options);
}

export function compareFiles(...args) {
  const host = globalThis.Algo2LeanBrowserHost;
  if (!host || typeof host.compareFiles !== "function") throw new Error("Generation verification is only available in the hosted editor.");
  return host.compareFiles(...args);
}
