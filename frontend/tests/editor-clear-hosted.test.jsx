import { test } from "vitest";
import assert from "node:assert/strict";
import { editor, MemoryStorage, tick } from "./support/editor-harness.jsx";
import { LEGACY_KEY, PREFIX } from "../src/lib/drafts.js";

const PROJECT_PREFIX = "algo2lean.editor.project.v1.";
const PROJECT_SOURCE = "from library import increment\ndef run(x: Int) -> Int:\n    return increment(x)\n";
const PROJECT_LIBRARY = "def increment(x: Int) -> Int:\n    return x + 1\n";

function projectRecords(app) {
  return [...app.local.data].filter(([key]) => key.startsWith(PROJECT_PREFIX)).map(([, value]) => JSON.parse(value));
}

function snapshot(source = "original", filename = "example.algo") {
  return { source, filename, savedSource: "original", savedFilename: "example.algo" };
}

async function openProject(app, name = "sample", files = { "main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY }) {
  await app.click("open-project-button");
  await app.chooseFiles("project-picker", Object.entries(files).map(([filePath, text]) => ({
    name: filePath.split("/").pop(), webkitRelativePath: name + "/" + filePath, size: text.length, text: async () => text })));
  await app.ready();
}

test("Clear all drafts removes every recovery format without changing the open documents", async () => {
  const local = new MemoryStorage([["unrelated.preference", "keep me"]]);
  const app = editor(local);
  await app.ready();
  await app.edit("saved standalone source");
  await app.editAnalysis("-- saved standalone proof");
  await app.flush();

  const projectApp = editor(local);
  await projectApp.ready();
  await openProject(projectApp);
  await projectApp.edit("saved project source");
  await projectApp.flush();
  local.setItem(LEGACY_KEY, JSON.stringify({ version: 1, ...snapshot("legacy source"), updatedAt: 90 }));
  assert.ok([...local.data.keys()].some((key) => key.startsWith(PREFIX)));
  assert.ok([...local.data.keys()].some((key) => key.startsWith(PROJECT_PREFIX)));

  await app.edit("pending standalone source");
  await app.editAnalysis("-- pending standalone proof");
  const filename = app.byId("filename").value;
  const analysisFilename = app.byId("analysis-filename").value;
  app.confirm.answer = () => assert.fail("Clearing drafts must remain reversible without confirmation");
  await app.click("clear-drafts-button");
  assert.deepEqual([...local.data], [["unrelated.preference", "keep me"]]);
  assert.equal(app.byId("source").value, "pending standalone source");
  assert.equal(app.byId("analysis").value, "-- pending standalone proof");
  assert.equal(app.byId("filename").value, filename);
  assert.equal(app.byId("analysis-filename").value, analysisFilename);
  assert.equal(app.byId("undo-clear-drafts-button").hidden, false);

  await app.dispatchWindow("beforeunload");
  app.setVisibility("hidden");
  await app.dispatchDocument("visibilitychange");
  await app.flush();
  assert.deepEqual([...local.data], [["unrelated.preference", "keep me"]]);
  await app.edit("later standalone source");
  await app.flush();
  assert.equal(app.records().length, 1);
  assert.equal(app.records()[0].source, "later standalone source");
  assert.equal(app.records()[0].analysis, "-- pending standalone proof");
  assert.equal(projectRecords(app).length, 0);
  assert.equal(local.getItem(LEGACY_KEY), null);
});

test("Undo clear restores exact records and preserves drafts saved after clearing", async () => {
  const local = new MemoryStorage([["unrelated.preference", "keep me"]]);
  const app = editor(local);
  await app.ready();
  await app.edit("original draft source");
  await app.editAnalysis("-- original proof");
  await app.flush();
  const projectApp = editor(local);
  await projectApp.ready();
  await openProject(projectApp);
  await projectApp.edit("original project source");
  await projectApp.flush();
  local.setItem(LEGACY_KEY, JSON.stringify({ version: 1, ...snapshot("legacy source"), updatedAt: 90 }));
  const original = new Map(local.data);

  await app.click("clear-drafts-button");
  await app.editAnalysis("-- new proof after clearing");
  await app.flush();
  const newRecords = new Map([...local.data].filter(([key]) => key.startsWith(PREFIX)));
  assert.equal(newRecords.size, 1);
  assert.ok([...newRecords.keys()].every((key) => !original.has(key)));
  await app.click("undo-clear-drafts-button");
  for (const [key, value] of original) assert.equal(local.getItem(key), value, key);
  for (const [key, value] of newRecords) assert.equal(local.getItem(key), value, key);
  assert.equal(app.byId("source").value, "original draft source");
  assert.equal(app.byId("analysis").value, "-- new proof after clearing");
});

test("Undo clear never overwrites a newer value stored under an old draft key", async () => {
  const local = new MemoryStorage();
  const app = editor(local);
  await app.ready();
  await app.edit("original source");
  await app.flush();
  const old = app.records()[0];
  const key = PREFIX + old.id;
  const original = local.getItem(key);
  await app.click("clear-drafts-button");
  const replacement = JSON.stringify({ ...old, source: "newer work from another tab", updatedAt: old.updatedAt + 1 });
  local.setItem(key, replacement);
  await app.click("undo-clear-drafts-button");
  assert.notEqual(replacement, original);
  assert.equal(local.getItem(key), replacement);
  assert.equal(app.byId("source").value, "original source");
});

test("clearing an active project resets recovery without losing its open modules", async () => {
  const app = editor();
  await app.ready();
  await openProject(app);
  await app.edit("saved project source");
  await app.flush();
  const old = projectRecords(app)[0];
  const oldRaw = app.local.getItem(PROJECT_PREFIX + old.id);
  await app.edit("pending project source");
  await app.editAnalysis("-- pending project proof");
  await app.click("clear-drafts-button");
  assert.equal(app.byId("project-toolbar").hidden, false);
  assert.equal(app.byId("source").value, "pending project source");
  assert.equal(app.byId("analysis").value, "-- pending project proof");
  assert.equal(app.byId("filename").value, "main.algo");
  await app.dispatchWindow("beforeunload");
  await app.flush();
  assert.equal(projectRecords(app).length, 0);
  assert.equal(app.records().length, 0);

  await app.editAnalysis("-- later project proof");
  await app.flush();
  const fresh = projectRecords(app)[0];
  assert.notEqual(fresh.id, old.id);
  assert.equal(fresh.data.files["main.algo"].source, "pending project source");
  assert.equal(fresh.data.files["main.algo"].analysis, "-- later project proof");
  assert.equal(fresh.data.files["library.algo"].source, PROJECT_LIBRARY);
  const freshRaw = app.local.getItem(PROJECT_PREFIX + fresh.id);
  await app.click("undo-clear-drafts-button");
  assert.equal(app.local.getItem(PROJECT_PREFIX + old.id), oldRaw);
  assert.equal(app.local.getItem(PROJECT_PREFIX + fresh.id), freshRaw);
});

test("Undo clear is available only in the tab session that performed the clear", async () => {
  const app = editor();
  await app.ready();
  await app.edit("source to clear");
  await app.flush();
  await app.click("clear-drafts-button");
  assert.equal(app.byId("undo-clear-drafts-button").hidden, false);
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  assert.equal(reloaded.byId("undo-clear-drafts-button").hidden, true);
  await reloaded.click("undo-clear-drafts-button");
  assert.equal(reloaded.records().length, 0);
});

test("hosted editor routes compilation through its browser backend and describes local checking", async () => {
  const app = editor(undefined, undefined, { hosted: true });
  await app.ready();
  assert.ok(app.requests.some(({ url }) => url === "/api/compile"));
  assert.equal(app.byId("generation-tools").hidden, false);
  assert.match(app.text("compilation-description"), /stay on your device/);
  await app.click("check-button");
  await app.click("analyze-button");
  assert.equal(app.requests.some(({ url }) => url === "/api/check" || url === "/api/analyze"), false);
  assert.match(app.text("analysis-status"), /local Algo2Lean editor/);
});

test("hosted Save analysis requests the same archive endpoint through the browser backend", async () => {
  const app = editor(undefined, undefined, { hosted: true });
  await app.ready();
  await app.edit("def browser_work() -> Int:\n    return 3\n");
  await app.editAnalysis("-- browser proof");
  await app.rename("analysis-filename", "BrowserProof.lean");
  await app.click("analysis-save-button");
  const exported = app.requests.filter(({ url }) => url === "/api/analysis-export").at(-1);
  assert.equal(exported.body.source, app.byId("source").value);
  assert.equal(exported.body.analysis, "-- browser proof");
  assert.equal(exported.body.analysis_filename, "BrowserProof.lean");
  assert.equal(app.downloads.at(-1).name, "BrowserProof.zip");
  assert.equal(app.byId("analysis-filename").value, "BrowserProof.lean");
  assert.equal(app.text("analysis-save-state"), "Downloaded");
});

test("hosted editor downloads generation manifests through the worker backend", async () => {
  const app = editor(undefined, undefined, { hosted: true, fetch: async (url) => url === "/api/generation"
    ? { ok: true, json: async () => ({ manifest: { compiler: { version: "0.1.0" } } }) } : null });
  await app.ready();
  await app.click("generation-manifest-button");
  assert.ok(app.requests.some(({ url, body }) => url === "/api/generation" && body.filename === "merge_sort.algo"));
  assert.equal(app.downloads.at(-1).name, "generation.json");
});

test("source and filename edits invalidate an earlier exact generation match", async () => {
  const app = editor(undefined, undefined, { hosted: true, fetch: async (url) => url === "/api/generation"
    ? { ok: true, json: async () => ({ files: { "Generated.lean": "test" }, libraries: {} }) } : null });
  await app.ready();
  async function verify() {
    await app.chooseFiles("verify-files-picker", [{ name: "Generated.lean", size: 4, arrayBuffer: async () => new TextEncoder().encode("test").buffer }]);
    await app.ready();
    assert.match(app.text("generation-status"), /^Exact match/);
  }
  await verify();
  await app.edit("def changed() -> Int:\n    return 2\n");
  assert.match(app.text("generation-status"), /Workspace changed/);
  assert.equal(app.text("generation-details"), "");
  await verify();
  await app.rename("filename", "renamed.algo");
  assert.match(app.text("generation-status"), /Workspace changed/);
});

test("workspace changes cancel a pending generation request and suppress its late result", async () => {
  let complete, signal;
  const app = editor(undefined, undefined, { hosted: true, fetch: async (url, options) => {
    if (url !== "/api/generation") return null;
    signal = options.signal;
    return new Promise((resolve) => { complete = resolve; });
  } });
  await app.ready();
  await app.click("generation-manifest-button");
  assert.equal(signal.aborted, false);
  await app.edit("def changed() -> Int:\n    return 2\n");
  assert.equal(signal.aborted, true);
  const status = app.text("generation-status");
  complete({ ok: true, json: async () => ({ manifest: { stale: true } }) });
  await tick();
  assert.equal(app.text("generation-status"), status);
  assert.equal(app.downloads.length, 0);
});
