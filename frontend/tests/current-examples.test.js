import { test } from "vitest";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import path from "node:path";
import { ROOT } from "./support/paths.js";

const require = createRequire(path.join(ROOT, "frontend/tests/current-examples.test.js"));
const { withCurrentExamples } = require("../../editor/current-examples.js");

function harness() {
  const files = [], requests = [];
  const backend = withCurrentExamples({ hosted: true, request(...args) {
    requests.push(args);
    return Promise.resolve("compiler response");
  } }, { baseURL: "https://example.com/algo2lean/current/examples/", fetch(...args) {
    files.push(args);
    return Promise.resolve("catalog response");
  } });
  return { backend, files, requests };
}

test("current example reads use static files without starting or changing the compiler", async () => {
  const { backend, files, requests } = harness();
  assert.equal(backend.hosted, true);
  assert.equal(await backend.request("/api/examples"), "catalog response");
  assert.equal(await backend.request("/api/example-project/prim"), "catalog response");
  assert.deepEqual(files.map(([url]) => url.href), [
    "https://example.com/algo2lean/current/examples/catalog.json",
    "https://example.com/algo2lean/current/examples/projects/prim.json",
  ]);
  assert.equal(requests.length, 0);
});

test("compilation, proofs, generation, exports, and citations retain the archived backend", async () => {
  const { backend, files, requests } = harness();
  for (const path of ["/api/compile", "/api/analyze", "/api/generation", "/api/project-export", "/api/publication", "/CITATION.cff"]) {
    const init = { body: JSON.stringify({ source: "algorithm" }) };
    assert.equal(await backend.request(path, init), "compiler response");
    assert.deepEqual(requests.at(-1), [path, init]);
  }
  assert.equal(files.length, 0);
});

test("current example requests support cancellation and revalidate the changing catalog", async () => {
  const { backend, files } = harness();
  const controller = new AbortController();
  await backend.request("/api/example-project/mutual-recursion-imports", { signal: controller.signal });
  assert.equal(files[0][1].signal, controller.signal);
  assert.equal(files[0][1].cache, "no-cache");
});

test("catalog routing never turns path escapes or write requests into static fetches", async () => {
  const { backend, files, requests } = harness();
  for (const path of ["/api/example-project/../secret", "/api/example-project/%2e%2e", "/api/examples?extra=1"]) {
    await backend.request(path);
  }
  await backend.request("/api/examples", { method: "POST" });
  await backend.request("/api/examples", { body: "{}" });
  assert.equal(files.length, 0);
  assert.equal(requests.length, 5);
});
