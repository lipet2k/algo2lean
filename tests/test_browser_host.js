"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const { createBackend, compareFiles } = require("../editor/browser-host.js");

function harness(options = {}) {
  const workers = [];
  const backend = createBackend({ workerURL: "compiler-worker.js", ...options, makeWorker(url) {
    const worker = { url, sent: [], stopped: false,
      postMessage(message) { this.sent.push(message); },
      terminate() { this.stopped = true; },
      reply(result, id = this.sent.at(-1).id) { this.onmessage({ data: { id, result } }); },
      ready() { this.onmessage({ data: { type: "ready" } }); },
    };
    workers.push(worker);
    return worker;
  } });
  return { backend, workers };
}
const json = (body) => ({ status: 200, content_type: "application/json", body });
const file = (name, text, relative = "") => {
  const bytes = new TextEncoder().encode(text);
  return { name, size: bytes.length, webkitRelativePath: relative, async arrayBuffer() { return bytes.buffer; } };
};

test("browser API sends source to its worker and preserves project mode", async () => {
  const { backend, workers } = harness();
  const source = "def identity(x: Int) -> Int:\n    return x\n";
  const promise = backend.request("/api/compile", { method: "POST", headers: { "X-Algo2Lean-Project": "1" },
    body: JSON.stringify({ source }) });
  assert.equal(workers.length, 1);
  assert.deepEqual(workers[0].sent[0], { id: 1, path: "/api/compile", body: { source }, project: true });
  workers[0].ready();
  workers[0].reply(json({ ok: true, lean: "def test := 1" }));
  assert.deepEqual(await (await promise).json(), { ok: true, lean: "def test := 1" });
});

test("project examples with underscores and hyphens reach the browser compiler", async () => {
  for (const identifier of ["randomized_clrs", "additional_types", "mutual-recursion-imports"]) {
    const { backend, workers } = harness();
    const path = `/api/example-project/${encodeURIComponent(identifier)}`;
    const pending = backend.request(path);
    // Handle a rejected request before asserting that it reached the worker.
    const response = pending.then(value => value, error => error);
    assert.equal(workers.length, 1, identifier);
    assert.equal(workers[0].sent[0].path, path);
    workers[0].reply(json({ entry: "shuffle.algo", sources: {}, analyses: {} }));
    assert.equal((await (await response).json()).entry, "shuffle.algo");
  }
});

test("concurrent browser requests execute serially", async () => {
  const { backend, workers } = harness();
  const first = backend.request("/api/examples");
  const second = backend.request("/api/publication");
  assert.equal(workers[0].sent.length, 1);
  workers[0].reply(json([]));
  assert.equal(workers[0].sent.length, 2);
  workers[0].reply(json({ version: "0.1.0" }));
  await Promise.all([first, second]);
});

test("canceling active work restarts the worker and preserves queued requests", async () => {
  const { backend, workers } = harness();
  const controller = new AbortController();
  const first = backend.request("/api/compile", { signal: controller.signal });
  const aborted = assert.rejects(first, { name: "AbortError" });
  const second = backend.request("/api/examples");
  controller.abort();
  assert.equal(workers[0].stopped, true);
  assert.equal(workers.length, 2);
  workers[1].reply(json([]));
  await aborted;
  await second;
});

test("canceling queued work does not interrupt the active worker", async () => {
  const { backend, workers } = harness();
  const first = backend.request("/api/examples");
  const controller = new AbortController();
  const second = backend.request("/api/compile", { signal: controller.signal });
  const aborted = assert.rejects(second, { name: "AbortError" });
  controller.abort();
  assert.equal(workers[0].stopped, false);
  workers[0].reply(json([]));
  await first;
  await aborted;
  assert.equal(workers[0].sent.length, 1);
});

test("a timeout terminates work and reports a recovery action", async () => {
  const timers = [];
  const { backend, workers } = harness({ setTimeout(fn) { timers.push(fn); return timers.length; }, clearTimeout() {} });
  const pending = backend.request("/api/compile");
  const rejected = assert.rejects(pending, /timed out.*restarted/);
  timers[0]();
  assert.equal(workers[0].stopped, true);
  await rejected;
});

test("ZIP responses preserve every binary byte", async () => {
  const { backend, workers } = harness();
  const pending = backend.request("/api/generation", { body: JSON.stringify({ archive: true }) });
  workers[0].reply({ status: 200, content_type: "application/zip", encoding: "base64", body: "AP+AUEs=" });
  const response = await pending;
  assert.equal(response.headers.get("Content-Type"), "application/zip");
  assert.deepEqual([...new Uint8Array(await response.arrayBuffer())], [0, 255, 128, 80, 75]);
});

test("invalid paths and malformed JSON never create a worker", async () => {
  const { backend, workers } = harness();
  for (const path of ["https://example.com/api/compile", "/api/example-project/../private",
    "/api/example-project/%2e%2e", "/api/example-project/randomized_clrs?other=1",
    "/api/example-project/randomized_clrs#fragment", "/api/example-project/randomized clrs"]) {
    await assert.rejects(backend.request(path), /only accepts/);
  }
  await assert.rejects(backend.request("/api/compile", { body: "not JSON" }), /must contain JSON/);
  assert.equal(workers.length, 0);
});

test("comparison requires exact bytes, including Unicode and line endings", async () => {
  assert.equal((await compareFiles({ "Test.lean": "def α := 1\n" }, [file("Test.lean", "def α := 1\n")])).exact, true);
  const result = await compareFiles({ "Test.lean": "def α := 1\n" }, [file("Test.lean", "def α := 1\r\n")]);
  assert.deepEqual(result.different, ["Test.lean"]);
  assert.equal(result.exact, false);
});

test("comparison reports missing, extra, different, and duplicate files", async () => {
  const result = await compareFiles({ "A.lean": "a", "B.lean": "b" },
    [file("A.lean", "different"), file("Extra.lean", "extra"), file("A.lean", "a")]);
  assert.deepEqual(result.missing, ["B.lean"]);
  assert.deepEqual(result.extra, ["Extra.lean"]);
  assert.deepEqual(result.different, ["A.lean"]);
  assert.deepEqual(result.duplicate, ["A.lean"]);
});

test("project comparison maps folder paths and dotted exported module names", async () => {
  const expected = { "Algo/main/Generated.lean": "main", "Algo/library/Generated.lean": "lib" };
  const folder = await compareFiles(expected, [file("Generated.lean", "main", "output/Algo/main/Generated.lean"),
    file("Generated.lean", "lib", "output/Algo/library/Generated.lean")]);
  assert.equal(folder.exact, true);
  const dotted = await compareFiles(expected, [file("Algo.main.Generated.lean", "main"), file("Algo.library.Generated.lean", "lib")]);
  assert.equal(dotted.exact, true);
  const ambiguous = await compareFiles(expected, [file("Generated.lean", "main")]);
  assert.equal(ambiguous.exact, false);
  assert.deepEqual(ambiguous.extra, ["Generated.lean"]);
});


test("shared libraries are optional but must match when supplied", async () => {
  const expected = { "Generated.lean": "algorithm" }, libraries = { "Algo2Lean.lean": "library" };
  assert.equal((await compareFiles(expected, [file("Generated.lean", "algorithm")], libraries)).exact, true);
  assert.equal((await compareFiles(expected, [file("Generated.lean", "algorithm"), file("Algo2Lean.lean", "library")], libraries)).exact, true);
  const changed = await compareFiles(expected, [file("Generated.lean", "algorithm"), file("Algo2Lean.lean", "changed")], libraries);
  assert.deepEqual(changed.different, ["Algo2Lean.lean"]);
  assert.equal(changed.exact, false);
});

test("folder verification rejects misplaced modules even when a basename is unique", async () => {
  const expected = { "Algo/main/Generated.lean": "main" };
  const result = await compareFiles(expected, [file("Generated.lean", "main", "output/wrong/Generated.lean")]);
  assert.equal(result.exact, false);
  assert.deepEqual(result.missing, ["Algo/main/Generated.lean"]);
  assert.deepEqual(result.extra, ["output/wrong/Generated.lean"]);
  const dotted = await compareFiles(expected, [file("Algo.main.Generated.lean", "main", "output/wrong/Algo.main.Generated.lean")]);
  assert.equal(dotted.exact, false);
});

test("aborted comparison stops reading additional files", async () => {
  const controller = new AbortController();
  const first = file("A.lean", "a");
  first.arrayBuffer = async () => { controller.abort(); return new TextEncoder().encode("a").buffer; };
  const second = file("B.lean", "b");
  second.arrayBuffer = async () => { throw new Error("Canceled comparison read another file"); };
  await assert.rejects(compareFiles({ "A.lean": "a", "B.lean": "b" }, [first, second], {}, controller.signal), { name: "AbortError" });
});
