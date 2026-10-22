import { test } from "vitest";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { descendants, draftAction, editor, fireEvent, MemoryStorage, tick } from "./support/editor-harness.jsx";
import { ROOT } from "./support/paths.js";

const EXAMPLE_SESSION_KEY = "algo2lean.editor.example.v1";
const PROJECT_SOURCE = "from library import increment\ndef run(x: Int) -> Int:\n    return increment(x)\n";
const PROJECT_LIBRARY = "def increment(x: Int) -> Int:\n    return x + 1\n";
const PROJECT_EXAMPLE = { name: "Dijkstra", project_id: "dijkstra", folder: "dijkstra", filename: "client/main.algo", source: PROJECT_SOURCE };
const PROJECT_BUNDLE = { name: "Dijkstra example", entry: "client/main.algo",
  sources: { "client/main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY },
  analyses: { "Algo.client.main.Analysis": "import Algo.library.Analysis\n-- final proof\n",
    "Algo.library.Analysis": "import Algo.library.Generated\n-- reusable proof\n" } };

function projectExampleResponse(url) {
  if (url === "/api/examples") return { ok: true, json: async () => ({ examples: [PROJECT_EXAMPLE] }) };
  if (url === "/api/example-project/dijkstra") return { ok: true, json: async () => PROJECT_BUNDLE };
  return undefined;
}

async function chooseProjectExample(app) {
  await app.select("examples", "0");
  await app.ready();
}

async function createFile(app, name) {
  await app.click("new-file-button");
  if (name !== undefined) await app.rename("new-file-name", name);
  fireEvent.submit(app.byId("new-file-form"));
  await tick();
}

async function openProject(app, name, files) {
  await app.click("open-project-button");
  await app.chooseFiles("project-picker", Object.entries(files).map(([filePath, text]) => ({
    name: filePath.split("/").pop(), webkitRelativePath: name + "/" + filePath, size: text.length, text: async () => text })));
  await app.ready();
}

function currentMergeSortExample() {
  return {
    name: "Merge Sort", filename: "merge_sort.algo", module: "MergeSortGenerated",
    source: fs.readFileSync(path.join(ROOT, "examples/merge_sort.algo"), "utf8"),
    analysis: fs.readFileSync(path.join(ROOT, "examples/analysis/merge_sort.lean"), "utf8"),
  };
}

function exampleCatalog(example) {
  return { fetch: (url) => url === "/api/examples" ? { ok: true, json: async () => ({ examples: [example] }) } : undefined };
}

function pairedSnapshot(source, analysis, overrides = {}) {
  return { source, filename: "example.algo", savedSource: "original", savedFilename: "example.algo",
    analysis, analysisFilename: "Proof.lean", savedAnalysis: "-- saved proof", savedAnalysisFilename: "Proof.lean", ...overrides };
}

function exampleDraft(example, overrides = {}) {
  return pairedSnapshot(example.source, example.analysis, {
    filename: example.filename, savedFilename: example.filename,
    savedSource: example.source, savedAnalysis: example.analysis, ...overrides,
  });
}

async function seedPair(local, value, session = new MemoryStorage()) {
  const app = editor(local, session);
  await app.ready();
  app.store.draftStore.start(pairedSnapshot("", ""));
  app.store.draftStore.write(value);
  const record = app.store.draftStore.read(app.store.draftStore.activeId);
  app.unmount();
  return record;
}

async function seed(local, source, session = new MemoryStorage()) {
  return seedPair(local, { source, filename: "example.algo", savedSource: "original", savedFilename: "example.algo" }, session);
}

function mainLabels(app) {
  return Array.from(app.container.querySelector(".proof-main-results").children).map((button) => button.textContent);
}

test("the example picker separates project folders from single files while retaining their catalog indices", async () => {
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/examples") return { ok: true, json: async () => ({ examples: [
      { name: "Merge sort", filename: "merge_sort.algo", source: "-- sort" },
      PROJECT_EXAMPLE,
      { name: "Reusable algorithms", project_id: "modules", folder: "modules", filename: "pipeline.algo", source: "-- pipeline" },
    ] }) };
    return projectExampleResponse(url);
  } });
  await app.ready();
  const groups = app.children("examples").filter((child) => child.tagName === "OPTGROUP");
  assert.deepEqual(groups.map((group) => group.label), ["Project folders", "Single files"]);
  assert.deepEqual(Array.from(groups[0].children).map((option) => [option.value, option.textContent]), [
    ["1", "Dijkstra · dijkstra/"], ["2", "Reusable algorithms · modules/"],
  ]);
  assert.equal(groups[1].children[0].value, "0");
  await app.select("examples", "1");
  assert.equal(app.text("project-name"), "Dijkstra example");
});

test("creating a file cancels replacement by a late project-example download", async () => {
  let finish;
  const pending = new Promise((resolve) => { finish = resolve; });
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/example-project/dijkstra") return pending;
    return projectExampleResponse(url);
  } });
  await app.ready();
  await chooseProjectExample(app);
  await createFile(app, "my_new_file.algo");
  finish({ ok: true, json: async () => PROJECT_BUNDLE });
  await tick();
  assert.equal(app.byId("filename").value, "my_new_file.algo");
  assert.equal(app.byId("project-toolbar").hidden, true);
  assert.equal(app.byId("source").value, "");
});

test("hosted projects can add files and send them to the browser compiler", async () => {
  const app = editor(undefined, undefined, { hosted: true, fetch: projectExampleResponse });
  await app.ready();
  await chooseProjectExample(app);
  await createFile(app, "client/extra.algo");
  await app.edit("def answer() -> Int:\n    return 42\n");
  await app.click("compile-button");
  const request = app.requests.filter(({ url }) => url === "/api/compile").at(-1);
  assert.equal(request.body.filename, "client/extra.algo");
  assert.equal(request.body.project_sources["client/extra.algo"], "def answer() -> Int:\n    return 42\n");
  assert.equal(request.body.project_sources["library.algo"], PROJECT_LIBRARY);
});

test("outdated project server is detected before compile, check, analysis, or export and retry recovers", async () => {
  let updated = false;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/capabilities") return { ok: updated, status: updated ? 200 : 404, json: async () => ({ project_protocol: 1 }) };
    return undefined;
  } });
  await app.ready();
  await openProject(app, "sample", { "main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY });
  assert.match(app.children("diagnostics")[0].textContent, /server is older.*Restart|server is older.*Stop/s);
  for (const button of ["compile-button", "check-button", "analyze-button", "project-export-button"]) {
    await app.click(button);
  }
  assert.equal(app.requests.filter(({ request }) => request?.headers?.["X-Algo2Lean-Project"]).length, 0);
  assert.equal(app.byId("source").value, PROJECT_SOURCE);
  const projectRecords = [...app.local.data].filter(([key]) => key.startsWith("algo2lean.editor.project.v1.")).map(([, value]) => JSON.parse(value));
  assert.equal(projectRecords.at(-1).data.files["library.algo"].source, PROJECT_LIBRARY);
  updated = true;
  await app.click("compile-button");
  assert.equal(app.requests.at(-1).url, "/api/compile");
  assert.equal(app.requests.at(-1).request.headers["X-Algo2Lean-Project"], "1");
  assert.ok(app.text("lean-code").includes("test"));
});

test("bundled import example opens its complete project and keeps the previous draft", async () => {
  const app = editor(undefined, undefined, { fetch: projectExampleResponse });
  await app.ready();
  await app.edit("my existing source");
  await app.editAnalysis("my existing proof");
  await chooseProjectExample(app);
  assert.equal(app.byId("filename").value, "client/main.algo");
  assert.equal(app.text("project-name"), "Dijkstra example");
  assert.equal(app.byId("analysis").value, PROJECT_BUNDLE.analyses["Algo.client.main.Analysis"]);
  const request = app.requests.filter(({ url }) => url === "/api/compile").at(-1);
  assert.equal(request.request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(request.body.project_sources["library.algo"], PROJECT_LIBRARY);
  assert.equal(request.body.project_analyses["Algo.library.Analysis"], PROJECT_BUNDLE.analyses["Algo.library.Analysis"]);
  await app.click("close-project-button");
  assert.equal(app.byId("source").value, "my existing source");
  assert.equal(app.byId("analysis").value, "my existing proof");
});

test("late example download cannot replace edits made while loading", async () => {
  let complete;
  const pending = new Promise((resolve) => { complete = resolve; });
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/example-project/dijkstra") return pending;
    return projectExampleResponse(url);
  } });
  await app.ready();
  await chooseProjectExample(app);
  await app.edit("keep newest source");
  complete({ ok: true, json: async () => PROJECT_BUNDLE });
  await tick();
  assert.equal(app.byId("source").value, "keep newest source");
  assert.equal(app.byId("project-toolbar").hidden, true);
  assert.match(app.text("file-message"), /workspace changed/);
});

test("incomplete example download leaves the current source and proof intact", async () => {
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/example-project/dijkstra") return { ok: true, json: async () => ({ ...PROJECT_BUNDLE, entry: "missing.algo" }) };
    return projectExampleResponse(url);
  } });
  await app.ready();
  await app.edit("keep source");
  await app.editAnalysis("keep proof");
  await chooseProjectExample(app);
  assert.equal(app.byId("source").value, "keep source");
  assert.equal(app.byId("analysis").value, "keep proof");
  assert.match(app.text("file-message"), /entry module is missing/);
});

test("an invalid bundled example shows the server diagnostic without replacing drafts", async () => {
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/example-project/dijkstra") return { ok: false, json: async () => ({ diagnostics: [{ message: "Module 'graph' was not found." }] }) };
    return projectExampleResponse(url);
  } });
  await app.ready();
  await app.edit("keep source");
  await app.editAnalysis("keep proof");
  await chooseProjectExample(app);
  assert.equal(app.byId("source").value, "keep source");
  assert.equal(app.byId("analysis").value, "keep proof");
  assert.match(app.text("file-message"), /Module 'graph' was not found/);
});

test("compiler setup failures preserve drafts and are not attributed to source or proofs", async () => {
  let failed = false;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (failed && ["/api/compile", "/api/check", "/api/analyze"].includes(url)) {
      return { ok: false, status: 503, json: async () => ({ scope: "setup",
        message: "Compiler setup error: publication.json is missing.", diagnostics: [], analysis_diagnostics: [] }) };
    }
    return undefined;
  } });
  await app.ready();
  await app.editAnalysis("-- keep this proof");
  const source = app.byId("source").value;
  assert.equal(app.byId("export-button").disabled, false);
  failed = true;
  for (const button of ["compile-button", "check-button", "analyze-button"]) {
    await app.click(button);
    assert.equal(app.text("compile-status"), "Compiler setup needs attention");
    assert.equal(app.text("lean-state"), "Compilation unavailable");
    assert.equal(app.byId("export-button").disabled, true);
    assert.equal(app.byId("source").value, source);
    assert.equal(app.byId("analysis").value, "-- keep this proof");
  }
  assert.equal(app.text("analysis-state"), "Not checked");
  assert.match(app.text("analysis-status"), /Compiler setup needs attention/);
});

test("merge sort main results preview and jump to the current proof without changing either document", async () => {
  const example = currentMergeSortExample();
  const app = editor(undefined, undefined, exampleCatalog(example));
  await app.ready();
  assert.equal(app.byId("source").value, example.source);
  const analysis = app.byId("analysis");
  const loaded = analysis.value;
  assert.ok(loaded.includes("theorem every_output_correct"));
  const nodes = () => descendants(app.byId("analysis-outline"));
  const result = nodes().find((node) => node.tagName === "BUTTON" && node.title === "every_output_correct");
  assert.ok(result);
  assert.equal(result.textContent, "Correctness");
  const before = analysis.selectionStart;
  fireEvent.click(result);
  const expectedStatement = loaded.slice(loaded.indexOf("theorem every_output_correct"),
    loaded.indexOf(" := by", loaded.indexOf("theorem every_output_correct")));
  assert.equal(nodes().find((node) => node.tagName === "PRE").textContent, expectedStatement);
  assert.equal(analysis.value, loaded);
  assert.equal(analysis.selectionStart, before);
  fireEvent.click(nodes().find((node) => node.textContent.startsWith("Go to proof")));
  await tick(2);
  assert.equal(analysis.selectionStart, loaded.indexOf("theorem every_output_correct"));
  assert.equal(document.activeElement, analysis);
  assert.ok(app.byId("analysis-editor").scrollTop > 0);
  const edited = "-- Additional explanation.\n" + loaded;
  await app.editAnalysis(edited);
  fireEvent.click(nodes().find((node) => node.textContent.startsWith("Go to proof")));
  await tick(2);
  assert.equal(analysis.selectionStart, edited.indexOf("theorem every_output_correct"));
  assert.equal(analysis.value, edited);
  assert.equal(app.byId("source").value, example.source);
});

for (const historical of [false, true]) test(`a recovered ${historical ? "pre-runtime" : "pre-marker"} merge-sort proof gains main-result navigation without rewriting drafts`, async () => {
  const example = currentMergeSortExample();
  const canonical = example.analysis;
  const statementStart = canonical.indexOf("theorem every_output_correct");
  const statement = canonical.slice(statementStart, canonical.indexOf(" := by", statementStart));
  // Older drafts use the compatibility name, have different proof bodies and
  // helpers, and contain no runtime theorem. Only their correctness is listed.
  const recovered = historical
    ? "import MergeSortGeneratedPoints\nnamespace MergeSortAnalysis\n" +
      statement.replace("merge_sort.Returns", "is_Output_merge_sort") +
      " := by\n  exact earlier_correctness_proof\n\n" +
      "theorem saved_helper : True := by trivial\nend MergeSortAnalysis\n"
    : "-- Saved before main-result navigation was added.\n" +
      canonical.replace(/^-- Main result:.*\n/gm, "");
  const expectedLabels = historical ? ["Correctness"]
    : [...canonical.matchAll(/^-- Main result:\s*(.+)$/gm)].map((match) => match[1]);
  assert.ok(expectedLabels.length > 0);
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const saved = await seedPair(local, pairedSnapshot(example.source, recovered, {
    filename: "my_merge_sort.algo", savedSource: example.source, savedFilename: "my_merge_sort.algo",
    analysisFilename: "MergeSortProof.lean", savedAnalysis: recovered, savedAnalysisFilename: "MergeSortProof.lean",
  }), session);
  const before = [...local.data];
  let deliverExamples;
  const pendingExamples = new Promise((resolve) => { deliverExamples = resolve; });
  const app = editor(local, session, { fetch: (url) => (url === "/api/examples" ? pendingExamples : undefined) });
  await app.ready();
  fireEvent.click(descendants(app.byId("draft-list")).find((node) => node.tagName === "BUTTON" && node.textContent === "Recover"));
  await tick();
  assert.equal(app.byId("analysis").value, recovered);
  assert.deepEqual(mainLabels(app), []);
  deliverExamples({ ok: true, json: async () => ({ examples: [example] }) });
  await app.ready();
  assert.deepEqual(mainLabels(app), expectedLabels);
  assert.equal(app.byId("source").value, example.source);
  assert.equal(app.byId("analysis").value, recovered);
  assert.equal(app.byId("analysis-filename").value, "MergeSortProof.lean");
  assert.doesNotMatch(app.text("save-state"), /Unsaved/);
  assert.doesNotMatch(app.text("analysis-save-state"), /Unsaved/);
  const nodes = () => descendants(app.byId("analysis-outline"));
  const result = nodes().find((node) => node.tagName === "BUTTON" && node.title === "every_output_correct");
  assert.equal(result.textContent, "Correctness");
  fireEvent.click(result);
  fireEvent.click(nodes().find((node) => node.textContent.startsWith("Go to proof")));
  await tick(2);
  assert.equal(app.byId("analysis").selectionStart, recovered.indexOf("theorem every_output_correct"));
  assert.equal(app.byId("analysis").value, recovered);
  await app.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
  assert.deepEqual(app.records().find((record) => record.id === saved.id), saved);
});

for (const changedPart of ["source", "analysis"]) test(`an older example ${changedPart} can be refreshed without losing its draft or returning after reload`, async () => {
  const example = currentMergeSortExample();
  const oldSource = changedPart === "source" ? example.source.replace(/^\s*tick\("merge_sort"\)\n/gm, "") : example.source;
  const oldProof = changedPart === "analysis"
    ? "import MergeSortGeneratedPoints\ntheorem old_output : is_Output_merge_sort input output := by\n  exact saved_proof\n"
    : example.analysis;
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const saved = await seedPair(local, exampleDraft(example, { source: oldSource, analysis: oldProof, savedSource: oldSource, savedAnalysis: oldProof }), session);
  const before = [...local.data];
  const options = exampleCatalog(example);
  const app = editor(local, session, options);
  await app.ready();
  assert.equal(app.byId("source").value, example.source);
  assert.equal(app.byId("analysis").value, example.analysis);
  assert.equal(app.byId("example-update").hidden, true);
  assert.deepEqual(app.records().find((record) => record.id === saved.id), saved);
  fireEvent.click(descendants(app.byId("draft-list")).find((node) => node.tagName === "BUTTON" && node.textContent === "Recover"));
  await tick();
  assert.equal(app.byId("example-update").hidden, false);
  assert.match(app.text("example-update-message"), /differ|older|current|updated/i);
  assert.equal(app.byId("source").value, oldSource);
  assert.equal(app.byId("analysis").value, oldProof);
  await app.click("load-current-example");
  assert.equal(app.byId("source").value, example.source);
  assert.equal(app.byId("analysis").value, example.analysis);
  assert.equal(app.byId("example-update").hidden, true);
  assert.equal(session.getItem(EXAMPLE_SESSION_KEY), example.filename);
  assert.deepEqual([...local.data], before);
  assert.deepEqual(app.records().find((record) => record.id === saved.id), saved);
  await app.dispatchWindow("beforeunload");
  const reloaded = editor(local, session, options);
  await reloaded.ready();
  assert.equal(reloaded.byId("source").value, example.source);
  assert.equal(reloaded.byId("analysis").value, example.analysis);
  assert.equal(reloaded.byId("example-update").hidden, true);
  assert.deepEqual(mainLabels(reloaded), ["Correctness", "Running time"]);
  await reloaded.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("example refresh notices follow source and proof changes and stay hidden for custom files and projects", async () => {
  const example = currentMergeSortExample();
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  await seedPair(local, exampleDraft(example), session);
  const app = editor(local, session, exampleCatalog(example));
  await app.ready();
  assert.equal(app.byId("example-update").hidden, true);
  await app.editAnalysis(example.analysis + "\n-- My additional analysis.\n");
  assert.equal(app.byId("example-update").hidden, false);
  await app.editAnalysis(example.analysis);
  assert.equal(app.byId("example-update").hidden, true);
  await app.edit(example.source + "\n# My variant.\n");
  assert.equal(app.byId("example-update").hidden, false);
  await app.rename("filename", "my_sort.algo");
  assert.equal(app.byId("example-update").hidden, true);
  await openProject(app, "custom-project", { "merge_sort.algo": example.source + "\n# Project version.\n" });
  assert.equal(app.byId("filename").value, "merge_sort.algo");
  assert.equal(app.byId("example-update").hidden, true);
});

test("refreshing an example backs up pending source and proof changes before replacing them", async () => {
  const example = currentMergeSortExample();
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const saved = await seedPair(local, exampleDraft(example), session);
  const app = editor(local, session, exampleCatalog(example));
  await app.ready();
  const source = example.source + "\n# Pending source change.\n";
  const proof = example.analysis + "\n-- Pending proof change.\n";
  await app.edit(source);
  await app.editAnalysis(proof);
  app.confirm.answer = () => assert.fail("A complete draft backup should permit replacement without confirmation");
  await app.click("load-current-example");
  assert.equal(app.byId("source").value, example.source);
  assert.equal(app.byId("analysis").value, example.analysis);
  assert.deepEqual(app.records().find((record) => record.id === saved.id), saved);
  const backup = app.records().find((record) => record.id !== saved.id);
  assert.equal(backup.source, source);
  assert.equal(backup.analysis, proof);
  assert.equal(app.records().length, 2);
});

test("declining example refresh after a failed backup preserves both pending documents", async () => {
  const example = currentMergeSortExample();
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const saved = await seedPair(local, exampleDraft(example), session);
  const app = editor(local, session, exampleCatalog(example));
  await app.ready();
  const source = example.source + "\n# Unsaved source.\n";
  const proof = example.analysis + "\n-- Unsaved proof.\n";
  await app.edit(source);
  await app.editAnalysis(proof);
  local.fail.add("write");
  let confirmations = 0;
  app.confirm.answer = () => { confirmations += 1; return false; };
  await app.click("load-current-example");
  assert.equal(confirmations, 1);
  assert.equal(app.byId("source").value, source);
  assert.equal(app.byId("analysis").value, proof);
  assert.equal(app.byId("example-update").hidden, false);
  assert.deepEqual(app.records().find((record) => record.id === saved.id), saved);
  assert.equal(app.records().length, 1);
  assert.equal(session.getItem(EXAMPLE_SESSION_KEY), example.filename);
});

test("every refresh starts the current merge-sort source and proof regardless of the prior example", async () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const original = await seed(local, "previous document", session);
  const example = currentMergeSortExample();
  const options = { fetch: (url) => url === "/api/examples" ? { ok: true, json: async () => ({ examples: [
    { name: "Other", source: "def other() -> Int:\n    return 5\n", filename: "other.algo", analysis: "-- other proof" },
    example,
  ] }) } : undefined };
  const app = editor(local, session, options);
  await app.ready();
  await app.select("examples", "0");
  assert.equal(session.getItem(EXAMPLE_SESSION_KEY), "other.algo");
  const before = [...local.data];
  for (let reload = 0; reload < 2; reload += 1) {
    const reopened = editor(local, session, options);
    await reopened.ready();
    assert.equal(reopened.byId("filename").value, example.filename);
    assert.equal(reopened.byId("source").value, example.source);
    assert.equal(reopened.byId("analysis").value, example.analysis);
    assert.equal(reopened.byId("draft-picker").open, false);
    await reopened.dispatchWindow("beforeunload");
    assert.deepEqual([...local.data], before);
    reopened.unmount();
  }
  assert.deepEqual(app.records().find((record) => record.id === original.id), original);
});

for (const changedPart of ["source", "analysis", "filename", "analysis-filename"]) test(`late startup examples preserve a user's ${changedPart} edit`, async () => {
  const example = currentMergeSortExample();
  let deliverExamples;
  const pending = new Promise((resolve) => { deliverExamples = resolve; });
  const app = editor(undefined, undefined, { fetch: (url) => (url === "/api/examples" ? pending : undefined) });
  await app.ready();
  if (changedPart === "source") await app.edit("def mine() -> Int:\n    return 7\n");
  else if (changedPart === "analysis") await app.editAnalysis("-- My analysis started before the catalog loaded.\n");
  else await app.rename(changedPart, changedPart === "filename" ? "Mine.algo" : "Mine.lean");
  const before = Object.fromEntries(["source", "analysis", "filename", "analysis-filename"].map((id) => [id, app.byId(id).value]));
  deliverExamples({ ok: true, json: async () => ({ examples: [example] }) });
  await app.ready();
  for (const [id, value] of Object.entries(before)) assert.equal(app.byId(id).value, value, id);
  await app.flush();
  assert.ok(app.records().some((record) => record.source === before.source && record.analysis === before.analysis));
});

test("example refresh starts merge sort and keeps edited copies available for explicit recovery", async () => {
  const app = editor();
  await app.ready();
  await app.select("examples", "0");
  await app.edit("def changed() -> Int:\n    return 8\n");
  await app.editAnalysis("-- My proof for the edited example.\n");
  await app.dispatchWindow("beforeunload");
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  assert.equal(reloaded.byId("filename").value, "merge_sort.algo");
  assert.match(reloaded.byId("source").value, /def merge_sort/);
  await draftAction(reloaded, "def changed() -> Int:\n    return 8\n", "Recover").click();
  assert.equal(reloaded.byId("source").value, "def changed() -> Int:\n    return 8\n");
  assert.equal(reloaded.byId("analysis").value, "-- My proof for the edited example.\n");
});
