import { test } from "vitest";
import assert from "node:assert/strict";
import { draftAction, editor, MemoryStorage, tick } from "./support/editor-harness.jsx";
import { LEGACY_KEY } from "../src/lib/drafts.js";

function snapshot(source = "original", filename = "example.algo") {
  return { source, filename, savedSource: "original", savedFilename: "example.algo" };
}

function pairedSnapshot(source = "original", analysis = "-- saved proof", overrides = {}) {
  return { ...snapshot(source), analysis, analysisFilename: "Proof.lean",
    savedAnalysis: "-- saved proof", savedAnalysisFilename: "Proof.lean", ...overrides };
}

// Seed a draft record by running an editor against the shared storage.
async function seedPair(local, value = pairedSnapshot(), session = new MemoryStorage()) {
  const app = editor(local, session);
  await app.ready();
  app.store.draftStore.start(pairedSnapshot("", ""));
  app.store.draftStore.write(value);
  const record = app.store.draftStore.read(app.store.draftStore.activeId);
  app.unmount();
  return record;
}

async function seed(local, source = "recover me", session = new MemoryStorage()) {
  const app = editor(local, session);
  await app.ready();
  app.store.draftStore.start(snapshot());
  app.store.draftStore.write(snapshot(source));
  const record = app.store.draftStore.read(app.store.draftStore.activeId);
  app.unmount();
  return record;
}

test("editor retains a legacy draft for explicit recovery and leaves it unchanged on close", async () => {
  const legacy = { ...snapshot("legacy unsaved source", "legacy.algo"), updatedAt: 42 };
  const local = new MemoryStorage([[LEGACY_KEY, JSON.stringify(legacy)]]);
  const app = editor(local);
  await app.ready();
  assert.equal(app.byId("filename").value, "merge_sort.algo");
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.byId("source").value, legacy.source);
  assert.equal(app.byId("filename").value, legacy.filename);
  assert.equal(local.getItem(LEGACY_KEY), null);
  assert.equal(app.records()[0].updatedAt, 42);
  const before = [...local.data];
  await app.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("editor quota failure during legacy migration still exposes the original source", async () => {
  const legacy = { ...snapshot("legacy source to rescue", "legacy.algo"), updatedAt: 42 };
  const raw = JSON.stringify(legacy);
  const local = new MemoryStorage([[LEGACY_KEY, raw]]);
  local.fail.add("write");
  const app = editor(local);
  await app.ready();
  assert.equal(app.byId("filename").value, "merge_sort.algo");
  assert.match(app.text("draft-status"), /could not be migrated/i);
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.byId("source").value, legacy.source);
  assert.equal(app.byId("filename").value, legacy.filename);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  await app.edit("edited while quota exceeded");
  const close = await app.dispatchWindow("beforeunload");
  assert.equal(close.defaultPrevented, true);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  local.fail.clear();
  await app.dispatchWindow("beforeunload");
  assert.equal(app.records()[0].source, "edited while quota exceeded");
  assert.equal(local.getItem(LEGACY_KEY), raw);
});

test("an unchanged legacy fallback remains backed up after migration quota failure", async () => {
  const legacy = { ...snapshot("legacy source already backed up", "legacy.algo"), updatedAt: 42 };
  const raw = JSON.stringify(legacy);
  const local = new MemoryStorage([[LEGACY_KEY, raw]]);
  local.fail.add("write");
  const app = editor(local);
  await app.ready();
  await draftAction(app, legacy.source, "Recover").click();
  const close = await app.dispatchWindow("beforeunload");
  assert.notEqual(close.defaultPrevented, true);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  app.confirm.answer = () => assert.fail("The unchanged legacy backup should allow replacement without warning");
  await app.select("examples", "0");
  assert.equal(app.byId("filename").value, "other.algo");
  assert.equal(local.getItem(LEGACY_KEY), raw);
});

test("legacy quota fallback stays accessible even when the session prefers a newer draft", async () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const preferred = await seed(local, "preferred current source", session);
  const legacy = { ...snapshot("older legacy source", "legacy.algo"), updatedAt: 42 };
  const raw = JSON.stringify(legacy);
  local.setItem(LEGACY_KEY, raw);
  local.fail.add("write");
  const app = editor(local, session);
  await app.ready();
  assert.equal(app.byId("filename").value, "merge_sort.algo");
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.byId("source").value, legacy.source);
  assert.ok(draftAction(app, preferred.source, "Recover"));
  assert.equal(local.getItem(LEGACY_KEY), raw);
  assert.equal(app.records().find((record) => record.id === preferred.id).source, preferred.source);
});

test("analysis-only edits in concurrent tabs preserve each complete document pair", async () => {
  const local = new MemoryStorage();
  const original = await seedPair(local, pairedSnapshot("shared source", "-- shared proof"));
  const a = editor(local);
  const b = editor(local);
  await a.ready();
  await b.ready();
  for (const app of [a, b]) await draftAction(app, original.source, "Recover").click();
  assert.equal(a.byId("analysis").value, original.analysis);
  await a.editAnalysis("-- proof from A");
  await b.editAnalysis("-- proof from B");
  await a.flush();
  await b.flush();
  assert.deepEqual(a.records().map((record) => record.analysis).sort(),
    ["-- proof from A", "-- proof from B", "-- shared proof"]);
  assert.ok(a.records().every((record) => record.source === "shared source"));
  const before = [...local.data];
  await a.dispatchWindow("beforeunload");
  await b.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("stale editor hide and unload cannot overwrite another tab's analysis-only edit", async () => {
  const local = new MemoryStorage();
  const old = await seedPair(local, pairedSnapshot("same source", "-- old proof"));
  const stale = editor(local);
  const active = editor(local);
  await stale.ready();
  await active.ready();
  await active.editAnalysis("-- important new proof");
  active.setVisibility("hidden");
  await active.dispatchDocument("visibilitychange");
  const before = [...local.data];
  stale.setVisibility("hidden");
  await stale.dispatchDocument("visibilitychange");
  await stale.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
  assert.equal(active.records().find((record) => record.id === old.id).analysis, "-- old proof");
  assert.ok(active.records().some((record) => record.analysis === "-- important new proof"));
});

test("recovery restores paired filenames and saved baselines without making clean files dirty", async () => {
  const local = new MemoryStorage();
  const original = await seedPair(local, pairedSnapshot("clean source", "-- clean proof", {
    filename: "Clean.algo", savedSource: "clean source", savedFilename: "Clean.algo",
    analysisFilename: "CleanProof.lean", savedAnalysis: "-- clean proof", savedAnalysisFilename: "CleanProof.lean",
  }));
  await seedPair(local, pairedSnapshot("second source", "-- second proof"));
  const app = editor(local);
  await app.ready();
  await draftAction(app, original.source, "Recover").click();
  assert.equal(app.byId("source").value, original.source);
  assert.equal(app.byId("filename").value, original.filename);
  assert.equal(app.byId("analysis").value, original.analysis);
  assert.equal(app.byId("analysis-filename").value, original.analysisFilename);
  assert.doesNotMatch(app.text("save-state"), /Unsaved/);
  assert.doesNotMatch(app.text("analysis-save-state"), /Unsaved/);
  await app.editAnalysis("-- temporary edit");
  await app.editAnalysis(original.savedAnalysis);
  assert.doesNotMatch(app.text("analysis-save-state"), /Unsaved/);
  const before = [...local.data];
  await app.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("reload and duplicated tabs fork analysis edits while preserving the original pair", async () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const original = await seedPair(local, pairedSnapshot("reload source", "-- reload proof"), session);
  const reloaded = editor(local, session);
  const duplicate = editor(local, session.copy());
  await reloaded.ready();
  await duplicate.ready();
  for (const app of [reloaded, duplicate]) {
    assert.equal(app.byId("filename").value, "merge_sort.algo");
    await draftAction(app, original.source, "Recover").click();
    assert.equal(app.byId("source").value, original.source);
    assert.equal(app.byId("analysis").value, original.analysis);
  }
  await reloaded.editAnalysis("-- reloaded proof");
  await duplicate.editAnalysis("-- duplicate proof");
  await reloaded.flush();
  await duplicate.flush();
  assert.deepEqual(reloaded.records().map((record) => record.analysis).sort(),
    ["-- duplicate proof", "-- reload proof", "-- reloaded proof"]);
  assert.equal(reloaded.records().find((record) => record.id === original.id).analysis, original.analysis);
});

test("changing examples backs up pending analysis and loads the new matching proof", async () => {
  const app = editor();
  await app.ready();
  const priorSource = app.byId("source").value;
  await app.editAnalysis("-- pending proof of original source");
  await app.rename("analysis-filename", "OriginalProof.lean");
  app.confirm.answer = () => assert.fail("A successful backup should permit replacement");
  await app.select("examples", "0");
  const prior = app.records().find((record) => record.source === priorSource);
  assert.equal(prior.analysis, "-- pending proof of original source");
  assert.equal(prior.analysisFilename, "OriginalProof.lean");
  assert.equal(app.byId("filename").value, "other.algo");
  assert.match(app.byId("analysis").value, /import OtherGeneratedPoints/);
  assert.match(app.byId("analysis").value, /example proof/);
  await app.editAnalysis("-- edited other proof");
  await app.flush();
  assert.equal(app.records().find((record) => record.id === prior.id).analysis, prior.analysis);
  const newPair = app.records().find((record) => record.analysis === "-- edited other proof");
  assert.equal(newPair.filename, "other.algo");
  assert.notEqual(newPair.id, prior.id);
});

test("opening a source file preserves its previous paired analysis before loading a starter", async () => {
  const app = editor();
  await app.ready();
  await app.edit("previous source");
  await app.editAnalysis("-- previous proof");
  await app.openFile("file-picker", "New.algo", "def fresh() -> Int:\n    return 3\n");
  const previous = app.records().find((record) => record.source === "previous source");
  assert.equal(previous.analysis, "-- previous proof");
  assert.equal(app.byId("filename").value, "New.algo");
  assert.match(app.byId("analysis").value, /import NewGeneratedPoints/);
  assert.doesNotMatch(app.byId("analysis").value, /previous proof/);
});

test("opening a new analysis file forks the document pair and retains the prior analysis", async () => {
  const app = editor();
  await app.ready();
  await app.edit("algorithm kept across proofs");
  await app.editAnalysis("-- previous unsaved proof");
  await app.rename("analysis-filename", "Previous.lean");
  app.confirm.answer = () => assert.fail("A successful backup should permit replacing analysis");
  await app.openFile("analysis-file-picker", "NewProof.lean", "-- new proof\r\n");
  const previous = app.records().find((record) => record.analysis === "-- previous unsaved proof");
  assert.ok(previous);
  assert.equal(previous.analysisFilename, "Previous.lean");
  assert.equal(app.byId("source").value, previous.source);
  assert.equal(app.byId("analysis").value, "-- new proof\n");
  assert.equal(app.byId("analysis-filename").value, "NewProof.lean");
  await app.editAnalysis("-- new proof edited");
  await app.flush();
  const current = app.records().find((record) => record.analysis === "-- new proof edited");
  assert.notEqual(current.id, previous.id);
  assert.equal(current.savedAnalysis, "-- new proof\n");
  assert.equal(current.savedAnalysisFilename, "NewProof.lean");
  assert.equal(app.records().find((record) => record.id === previous.id).analysis, "-- previous unsaved proof");
});

test("canceling analysis replacement after quota failure retains text, names, and save baselines", async () => {
  const app = editor();
  await app.ready();
  const savedAnalysis = app.byId("analysis").value;
  await app.editAnalysis("-- irreplaceable unsaved proof");
  await app.rename("analysis-filename", "Keep.lean");
  app.local.fail.add("write");
  let asked = 0;
  app.confirm.answer = () => { asked += 1; return false; };
  await app.openFile("analysis-file-picker", "Replacement.lean", "-- replacement");
  assert.equal(asked, 1);
  assert.equal(app.byId("analysis").value, "-- irreplaceable unsaved proof");
  assert.equal(app.byId("analysis-filename").value, "Keep.lean");
  assert.match(app.text("analysis-save-state"), /Unsaved/);
  const close = await app.dispatchWindow("beforeunload");
  assert.equal(close.defaultPrevented, true);
  app.local.fail.clear();
  await app.dispatchWindow("beforeunload");
  const current = app.records().find((record) => record.analysis === "-- irreplaceable unsaved proof");
  assert.equal(current.savedAnalysis, savedAnalysis);
  assert.equal(current.savedAnalysisFilename, "Analysis.lean");
});

test("analysis-only quota failure warns before closing and retries the complete pair", async () => {
  const app = editor();
  await app.ready();
  const source = app.byId("source").value;
  app.local.fail.add("write");
  await app.editAnalysis("-- only analysis has unsaved changes");
  await app.flush();
  assert.match(app.text("draft-status"), /could not|cannot|unavailable/i);
  const close = await app.dispatchWindow("beforeunload");
  assert.equal(close.defaultPrevented, true);
  app.local.fail.clear();
  await app.dispatchWindow("beforeunload");
  assert.equal(app.records()[0].source, source);
  assert.equal(app.records()[0].analysis, "-- only analysis has unsaved changes");
});

test("paired legacy quota fallback restores proof filenames and protects later analysis edits", async () => {
  const legacy = { ...pairedSnapshot("legacy algorithm", "-- legacy proof", {
    analysisFilename: "Legacy.lean", savedAnalysis: "-- downloaded proof", savedAnalysisFilename: "Saved.lean",
  }), updatedAt: 42 };
  const raw = JSON.stringify(legacy);
  const local = new MemoryStorage([[LEGACY_KEY, raw]]);
  local.fail.add("write");
  const app = editor(local);
  await app.ready();
  assert.equal(app.byId("filename").value, "merge_sort.algo");
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.byId("source").value, legacy.source);
  assert.equal(app.byId("analysis").value, legacy.analysis);
  assert.equal(app.byId("analysis-filename").value, legacy.analysisFilename);
  assert.equal((await app.dispatchWindow("beforeunload")).defaultPrevented, false);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  await app.editAnalysis("-- updated legacy proof");
  assert.equal((await app.dispatchWindow("beforeunload")).defaultPrevented, true);
  local.fail.clear();
  await app.dispatchWindow("beforeunload");
  const saved = app.records()[0];
  assert.equal(saved.analysis, "-- updated legacy proof");
  assert.equal(saved.source, legacy.source);
  assert.equal(saved.savedAnalysis, legacy.savedAnalysis);
  assert.equal(saved.savedAnalysisFilename, legacy.savedAnalysisFilename);
  assert.equal(local.getItem(LEGACY_KEY), raw);
});

test("discarded analysis-only work is not resurrected by an unchanged tab close", async () => {
  const app = editor();
  await app.ready();
  const source = app.byId("source").value;
  await app.editAnalysis("-- deleted elsewhere");
  await app.flush();
  const saved = app.records()[0];
  app.store.draftStore.remove(saved.id);
  await app.dispatchWindow("storage", { key: "algo2lean.editor.draft.v2." + saved.id });
  assert.equal((await app.dispatchWindow("beforeunload")).defaultPrevented, true);
  assert.equal(app.records().length, 0);
  assert.equal(app.byId("source").value, source);
  assert.equal(app.byId("analysis").value, "-- deleted elsewhere");
});

test("compilation keeps algorithm and Points outputs separate and excludes generated text from drafts", async () => {
  const app = editor();
  await app.ready();
  assert.match(app.text("lean-code"), /test/);
  assert.match(app.text("points-code"), /named-line interface/);
  assert.equal(app.byId("points-output").hidden, false);
  await app.editAnalysis("-- user-owned proof");
  await app.flush();
  assert.equal(app.records()[0].analysis, "-- user-owned proof");
  const raw = JSON.parse(app.local.getItem("algo2lean.editor.draft.v2." + app.records()[0].id));
  assert.equal(Object.values(raw).some((value) => value === "-- named-line interface"), false);
  assert.equal(Object.values(raw).some((value) => value === "def test := 1"), false);
});

test("old source-only recovery reconstructs a starter without changing the saved draft", async () => {
  const local = new MemoryStorage();
  const original = await seed(local, "old source still recoverable");
  const before = [...local.data];
  const app = editor(local);
  await app.ready();
  await draftAction(app, original.source, "Recover").click();
  assert.equal(app.byId("source").value, original.source);
  assert.match(app.byId("analysis").value, /import ExampleGeneratedPoints/);
  assert.equal(app.byId("analysis-filename").value, "Analysis.lean");
  assert.doesNotMatch(app.text("analysis-save-state"), /Unsaved/);
  assert.notEqual((await app.dispatchWindow("beforeunload")).defaultPrevented, true);
  assert.deepEqual([...local.data], before);
});

test("an intentionally empty analysis is recovered as empty rather than replaced by a starter", async () => {
  const local = new MemoryStorage();
  const original = await seedPair(local, pairedSnapshot("source with empty proof", "", {
    savedAnalysis: "", analysisFilename: "Empty.lean", savedAnalysisFilename: "Empty.lean",
  }));
  const before = [...local.data];
  const app = editor(local);
  await app.ready();
  await draftAction(app, original.source, "Recover").click();
  assert.equal(app.byId("source").value, original.source);
  assert.equal(app.byId("analysis").value, "");
  assert.equal(app.byId("analysis-filename").value, "Empty.lean");
  assert.doesNotMatch(app.text("analysis-save-state"), /Unsaved/);
  await app.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("saving each file updates only its own baseline in the paired draft", async () => {
  const app = editor();
  await app.ready();
  const initialAnalysis = app.byId("analysis").value;
  await app.edit("unsaved algorithm");
  await app.editAnalysis("-- unsaved proof");
  await app.rename("analysis-filename", "MyProof.lean");
  await app.click("save-button");
  const sourceSaved = app.records()[0];
  assert.equal(sourceSaved.savedSource, "unsaved algorithm");
  assert.equal(sourceSaved.analysis, "-- unsaved proof");
  assert.equal(sourceSaved.savedAnalysis, initialAnalysis);
  assert.match(app.text("analysis-save-state"), /Unsaved/);
  await app.click("analysis-save-button");
  const bothSaved = app.records()[0];
  assert.equal(bothSaved.savedSource, "unsaved algorithm");
  assert.equal(bothSaved.savedAnalysis, "-- unsaved proof");
  assert.equal(bothSaved.savedAnalysisFilename, "MyProof.lean");
  assert.doesNotMatch(app.text("analysis-save-state"), /Unsaved/);
  assert.doesNotMatch(app.text("save-state"), /Unsaved/);
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  await draftAction(reloaded, "unsaved algorithm", "Recover").click();
  assert.equal(reloaded.byId("source").value, "unsaved algorithm");
  assert.equal(reloaded.byId("analysis").value, "-- unsaved proof");
  assert.equal(reloaded.byId("analysis-filename").value, "MyProof.lean");
  assert.doesNotMatch(reloaded.text("analysis-save-state"), /Unsaved/);
  assert.doesNotMatch(reloaded.text("save-state"), /Unsaved/);
  await app.flush();
});

test("Save analysis packages the latest standalone source and proof while preserving the Lean filename", async () => {
  const app = editor();
  await app.ready();
  const originalSource = app.byId("source").value;
  const latestSource = "def work() -> Int:\n    return 7\n";
  const latestProof = "import WorkGeneratedPoints\n-- latest handwritten proof\n";
  await app.rename("filename", "work.algo");
  await app.edit(latestSource);
  await app.rename("analysis-filename", "WorkProof.lean");
  await app.editAnalysis(latestProof);
  await app.click("analysis-save-button");
  const exported = app.requests.filter(({ url }) => url === "/api/analysis-export").at(-1);
  assert.equal(exported.request.method, "POST");
  assert.equal(exported.request.headers["Content-Type"], "application/json");
  assert.equal(exported.request.headers["X-Algo2Lean-Project"], undefined);
  assert.deepEqual(exported.body, { source: latestSource, filename: "work.algo", analysis: latestProof, analysis_filename: "WorkProof.lean" });
  assert.deepEqual(app.downloads.map(({ name }) => name), ["WorkProof.zip"]);
  assert.equal(app.downloads[0].content.type, "application/zip");
  assert.equal(app.byId("analysis-filename").value, "WorkProof.lean");
  assert.equal(app.text("analysis-save-state"), "Downloaded");
  assert.match(app.text("save-state"), /Unsaved/);
  assert.equal(app.records()[0].savedSource, originalSource);
  assert.equal(app.records()[0].savedAnalysis, latestProof);
  assert.equal(app.records()[0].savedAnalysisFilename, "WorkProof.lean");
  assert.match(app.text("analysis-file-message"), /shared Lean libraries and all resolved imports/);
  assert.match(app.text("analysis-file-message"), /Downloading does not check the proof/);
});

test("failed analysis packages leave the proof unsaved and restore the Save analysis button", async () => {
  const failures = [
    { response: { ok: false, status: 404 }, message: /Restart the local editor/ },
    { response: { ok: false, status: 422, json: async () => ({ analysis_diagnostics: [{ message: "Missing imported proof" }] }) }, message: /Missing imported proof/ },
    { error: new Error("Network unavailable"), message: /Network unavailable/ },
    { response: { ok: true, blob: async () => { throw new Error("Archive interrupted"); } }, message: /Archive interrupted/ },
  ];
  for (const failure of failures) {
    const app = editor(undefined, undefined, { fetch: async (url) => {
      if (url !== "/api/analysis-export") return null;
      if (failure.error) throw failure.error;
      return failure.response;
    } });
    await app.ready();
    const savedProof = app.byId("analysis").value;
    await app.editAnalysis("-- unsaved proof to keep");
    await app.rename("analysis-filename", "Pending.lean");
    await app.click("analysis-save-button");
    await app.flush();
    assert.equal(app.downloads.length, 0);
    assert.match(app.text("analysis-save-state"), /Unsaved/);
    assert.match(app.text("analysis-file-message"), failure.message);
    assert.equal(app.byId("analysis-save-button").disabled, false);
    assert.equal(app.text("analysis-save-button"), "Save analysis");
    assert.equal(app.byId("analysis-filename").value, "Pending.lean");
    assert.equal(app.records()[0].savedAnalysis, savedProof);
    assert.equal(app.records()[0].savedAnalysisFilename, "Analysis.lean");
    app.unmount();
  }
});

test("late analysis package responses cannot download or mark files saved after edits or renames", async () => {
  const changes = [
    ["source edit", (app) => app.edit("def latest() -> Int:\n    return 9\n")],
    ["proof edit", (app) => app.editAnalysis("-- newer unsaved proof")],
    ["source rename", (app) => app.rename("filename", "renamed.algo")],
    ["proof rename", (app) => app.rename("analysis-filename", "RenamedProof.lean")],
  ];
  for (const [description, change] of changes) {
    let finishArchive;
    const app = editor(undefined, undefined, { fetch: async (url) => url === "/api/analysis-export"
      ? { ok: true, blob: () => new Promise((resolve) => { finishArchive = resolve; }) } : null });
    await app.ready();
    const savedProof = app.byId("analysis").value;
    await app.editAnalysis("-- proof before pending download");
    await app.click("analysis-save-button");
    assert.equal(app.byId("analysis-save-button").disabled, true, description);
    await change(app);
    const currentSource = app.byId("source").value;
    const currentProof = app.byId("analysis").value;
    const currentName = app.byId("analysis-filename").value;
    finishArchive(new Blob(["old archive"], { type: "application/zip" }));
    await tick();
    await app.flush();
    assert.equal(app.downloads.length, 0, description);
    assert.equal(app.byId("source").value, currentSource, description);
    assert.equal(app.byId("analysis").value, currentProof, description);
    assert.equal(app.byId("analysis-filename").value, currentName, description);
    assert.match(app.text("analysis-save-state"), /Unsaved/, description);
    assert.match(app.text("analysis-file-message"), /workspace changed/i, description);
    assert.equal(app.byId("analysis-save-button").disabled, false, description);
    assert.equal(app.records()[0].savedAnalysis, savedProof, description);
    app.unmount();
  }
});

test("cross-tab notifications expose the paired recovery choice without replacing pending analysis", async () => {
  const app = editor();
  await app.ready();
  const source = app.byId("source").value;
  await app.editAnalysis("-- local pending proof");
  const foreign = await seedPair(app.local, pairedSnapshot("foreign algorithm", "-- foreign proof", { analysisFilename: "Foreign.lean" }));
  await app.dispatchWindow("storage", { key: "algo2lean.editor.draft.v2." + foreign.id });
  assert.equal(app.byId("source").value, source);
  assert.equal(app.byId("analysis").value, "-- local pending proof");
  const card = app.children("draft-list").find((candidate) => candidate.textContent.includes(foreign.source));
  assert.ok(card);
  assert.ok(card.textContent.includes(foreign.analysis));
  assert.match(card.textContent, /Foreign\.lean/);
  await draftAction(app, foreign.source, "Recover").click();
  assert.equal(app.byId("source").value, foreign.source);
  assert.equal(app.byId("analysis").value, foreign.analysis);
  assert.equal(app.byId("analysis-filename").value, "Foreign.lean");
  assert.ok(app.records().some((record) => record.source === source && record.analysis === "-- local pending proof"));
});

test("renaming the analysis while either file is being read cancels the stale replacement", async () => {
  for (const [pickerId, name, messageId] of [
    ["file-picker", "Replacement.algo", "file-message"],
    ["analysis-file-picker", "Replacement.lean", "analysis-file-message"],
  ]) {
    const app = editor();
    await app.ready();
    const source = app.byId("source").value;
    const analysis = app.byId("analysis").value;
    let finishRead;
    const fileRead = new Promise((resolve) => { finishRead = resolve; });
    await app.chooseFiles(pickerId, [{ name, size: 12, text: () => fileRead }]);
    await app.rename("analysis-filename", "KeepNewestName.lean");
    finishRead("replacement text");
    await tick();
    assert.equal(app.byId("source").value, source, pickerId);
    assert.equal(app.byId("analysis").value, analysis, pickerId);
    assert.equal(app.byId("analysis-filename").value, "KeepNewestName.lean", pickerId);
    assert.match(app.text(messageId), /workspace changed/i, pickerId);
    app.unmount();
  }
});
