import { test } from "vitest";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { descendants, editor, fireEvent, MemoryStorage, tick } from "./support/editor-harness.jsx";
import { ROOT } from "./support/paths.js";

const PROJECT_PREFIX = "algo2lean.editor.project.v1.";
const PROJECT_SESSION = "algo2lean.editor.active-project.v1";
const PROJECT_SOURCE = "from library import increment\ndef run(x: Int) -> Int:\n    return increment(x)\n";
const PROJECT_LIBRARY = "def increment(x: Int) -> Int:\n    return x + 1\n";

function projectRecords(app) {
  return [...app.local.data].filter(([key]) => key.startsWith(PROJECT_PREFIX)).map(([, value]) => JSON.parse(value));
}

export async function openProject(app, name = "sample", files = { "main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY }) {
  await app.click("open-project-button");
  await app.chooseFiles("project-picker", Object.entries(files).map(([filePath, text]) => ({
    name: filePath.split("/").pop(), webkitRelativePath: name + "/" + filePath, size: text.length, text: async () => text })));
  await app.ready();
}

async function selectModule(app, modulePath) {
  await app.select("project-module", modulePath);
  await app.ready();
}

async function createFile(app, name) {
  await app.click("new-file-button");
  if (name !== undefined) await app.rename("new-file-name", name);
  fireEvent.submit(app.byId("new-file-form"));
  await tick();
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

test("New file preserves the previous source and proof and creates an independent standalone draft", async () => {
  const app = editor();
  await app.ready();
  await app.edit("pending original algorithm");
  await app.editAnalysis("-- pending original proof");
  const compileRequests = app.requests.filter(({ url }) => url === "/api/compile").length;
  await createFile(app, "fresh");
  assert.equal(app.byId("filename").value, "fresh.algo");
  assert.equal(app.byId("source").value, "");
  assert.match(app.byId("analysis").value, /^import FreshGenerated\n/);
  assert.equal(app.byId("new-file-form").hidden, true);
  assert.equal(app.byId("new-file-button").getAttribute("aria-expanded"), "false");
  assert.equal(app.requests.filter(({ url }) => url === "/api/compile").length, compileRequests);
  const original = app.records().find((record) => record.source === "pending original algorithm");
  const fresh = app.records().find((record) => record.filename === "fresh.algo");
  assert.equal(original.analysis, "-- pending original proof");
  assert.equal(fresh.source, "");
  assert.notEqual(original.id, fresh.id);
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  assert.equal(reloaded.byId("filename").value, "merge_sort.algo");
  const card = reloaded.children("draft-list").find((candidate) => descendants(candidate).some((node) => node.tagName === "PRE" && node.textContent === "(Empty source)"));
  fireEvent.click(descendants(card).find((node) => node.tagName === "BUTTON" && node.textContent === "Recover"));
  await tick();
  assert.equal(reloaded.byId("filename").value, "fresh.algo");
  assert.equal(reloaded.byId("source").value, "");
});

test("New file defaults avoid existing drafts and Cancel or Escape leave the workspace unchanged", async () => {
  const app = editor();
  await app.ready();
  await createFile(app);
  assert.equal(app.byId("filename").value, "untitled.algo");
  const before = [...app.local.data];
  await app.click("new-file-button");
  assert.equal(app.byId("new-file-name").value, "untitled_2.algo");
  await app.click("cancel-new-file-button");
  assert.equal(app.byId("new-file-form").hidden, true);
  assert.deepEqual([...app.local.data], before);
  await app.click("new-file-button");
  fireEvent.keyDown(app.byId("new-file-form"), { key: "Escape" });
  await tick(2);
  assert.equal(app.byId("new-file-form").hidden, true);
  assert.equal(app.byId("filename").value, "untitled.algo");
  assert.deepEqual([...app.local.data], before);
});

test("New file refuses to replace an unbacked-up standalone source and proof", async () => {
  const app = editor();
  await app.ready();
  await app.edit("keep algorithm");
  await app.editAnalysis("keep proof");
  app.local.fail.add("write");
  app.confirm.answer = () => { throw new Error("New file should report the backup failure inline"); };
  await createFile(app, "fresh.algo");
  assert.equal(app.byId("source").value, "keep algorithm");
  assert.equal(app.byId("analysis").value, "keep proof");
  assert.equal(app.byId("new-file-form").hidden, false);
  assert.match(app.text("new-file-help"), /could not be backed up/);
});

test("New file adds a project source and companion without replacing any edited file or support proof", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", {
    "main.algo": PROJECT_SOURCE, "helpers/library.algo": PROJECT_LIBRARY,
    "analysis/support/facts.lean": "-- reusable support proof",
  });
  await app.edit("pending main");
  await app.editAnalysis("-- pending main proof");
  await selectModule(app, "helpers/library.algo");
  await app.edit("pending library");
  await app.editAnalysis("-- pending library proof");
  await app.click("new-file-button");
  assert.equal(app.byId("new-file-name").value, "helpers/untitled.algo");
  await app.rename("new-file-name", "helpers/search.algo");
  fireEvent.submit(app.byId("new-file-form"));
  await tick();
  assert.equal(app.byId("filename").value, "helpers/search.algo");
  assert.equal(app.byId("source").value, "");
  assert.equal(app.byId("analysis-filename").value, "analysis/helpers/search.lean");
  assert.match(app.byId("analysis").value, /^import Algo.helpers.search.Generated\n/);
  await app.edit("def search() -> Int:\n    return 1\n");
  await app.click("project-export-button");
  const payload = app.requests.filter(({ url }) => url === "/api/project-export").at(-1).body;
  assert.equal(payload.project_sources["helpers/search.algo"], "def search() -> Int:\n    return 1\n");
  assert.equal(payload.project_sources["main.algo"], "pending main");
  assert.equal(payload.project_sources["helpers/library.algo"], "pending library");
  assert.equal(payload.project_analyses["Algo.main.Analysis"], "-- pending main proof");
  assert.equal(payload.project_analyses["Algo.helpers.library.Analysis"], "-- pending library proof");
  assert.equal(payload.project_analyses["Algo.support.facts.Analysis"], "-- reusable support proof");
  await selectModule(app, "helpers/library.algo");
  assert.equal(app.byId("source").value, "pending library");
  assert.equal(app.byId("analysis").value, "-- pending library proof");
});

test("New project files reject invalid paths, duplicate sources, proof collisions, and inconsistent folder case", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", { "pkg/main.algo": PROJECT_LIBRARY, "analysis/support/facts.lean": "-- support proof" });
  const before = app.byId("source").value;
  for (const name of ["", "../new.algo", "/new.algo", "bad-name.algo", "pkg//new.algo", "pkg/main.algo",
    "Pkg/new.algo", "support/facts.algo", "Support/new.algo", "_a2l_groups/new.algo", "2wrong.algo"]) {
    await createFile(app, name);
    assert.equal(app.byId("new-file-form").hidden, false, name);
    assert.equal(app.byId("new-file-name").getAttribute("aria-invalid"), "true", name);
    assert.equal(app.byId("source").value, before, name);
    assert.equal(app.byId("filename").value, "pkg/main.algo", name);
  }
  await createFile(app, "new_folder/new.algo");
  assert.equal(app.byId("filename").value, "new_folder/new.algo");
  assert.equal(app.byId("new-file-form").hidden, true);
});

test("New standalone files reject folder paths and unsafe names without replacing the current file", async () => {
  const app = editor();
  await app.ready();
  for (const name of ["nested/new.algo", "../new.algo", "new file.algo", "", "_a2l_groups.algo"]) {
    await createFile(app, name);
    assert.equal(app.byId("filename").value, "merge_sort.algo");
    assert.equal(app.byId("new-file-form").hidden, false);
  }
});

test("New file respects the project source and proof limits", async () => {
  for (const proofsOnly of [false, true]) {
    const app = editor();
    await app.ready();
    const files = { "main.algo": PROJECT_LIBRARY };
    for (let index = 1; index < 256; index += 1) files[proofsOnly ? `analysis/support_${index}.lean` : `file_${index}.algo`] = proofsOnly ? "-- proof" : PROJECT_LIBRARY;
    await openProject(app, "full", files);
    await createFile(app, "extra.algo");
    assert.equal(app.byId("filename").value, "main.algo");
    assert.match(app.text("new-file-help"), /at most 256/);
    app.unmount();
  }
});

test("project file selection groups paths by folder and retains full path values", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", {
    "main.algo": PROJECT_LIBRARY, "sorting/main.algo": PROJECT_LIBRARY,
    "sorting/merge.algo": PROJECT_LIBRARY, "searching/main.algo": PROJECT_LIBRARY,
  });
  const groups = app.children("project-module");
  assert.deepEqual(groups.map((group) => group.label), ["Project root", "searching/", "sorting/"]);
  assert.ok(groups.every((group) => group.tagName === "OPTGROUP"));
  assert.deepEqual(Array.from(groups[2].children).map((option) => [option.textContent, option.value]), [
    ["main.algo", "sorting/main.algo"], ["merge.algo", "sorting/merge.algo"],
  ]);
  await selectModule(app, "sorting/main.algo");
  assert.equal(app.byId("filename").value, "sorting/main.algo");
});

test("project folder selection sends relative sources and canonical companion proof modules", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "sample", { "main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY,
    "analysis/library.lean": "import Algo.library.Generated\n-- saved library proof\n" });
  assert.equal(app.byId("project-toolbar").hidden, false);
  assert.equal(app.text("project-name"), "sample");
  assert.equal(app.byId("filename").value, "main.algo");
  assert.equal(app.byId("filename").readOnly, true);
  const request = app.requests.filter(({ url }) => url === "/api/compile").at(-1);
  assert.equal(request.request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(request.body.project_sources["library.algo"], PROJECT_LIBRARY);
  assert.equal(request.body.project_analyses["Algo.library.Analysis"], "import Algo.library.Generated\n-- saved library proof\n");
  assert.match(app.byId("analysis").value, /^import Algo.main.Generated\nimport Algo.main.Points\nimport Algo.main.Facts/);
  assert.match(app.byId("analysis").value, /open «Algo».«main» «Algo».«main».Algo2LeanGenerated/);
});

test("module switches retain each unsaved source and analysis and send all edited dependencies", async () => {
  const app = editor();
  await app.ready();
  await openProject(app);
  await app.edit("main edit");
  await app.editAnalysis("main proof edit");
  await selectModule(app, "library.algo");
  await app.edit("library edit");
  await app.editAnalysis("library proof edit");
  await selectModule(app, "main.algo");
  assert.equal(app.byId("source").value, "main edit");
  assert.equal(app.byId("analysis").value, "main proof edit");
  await app.click("analyze-button");
  const request = app.requests.filter(({ url }) => url === "/api/analyze").at(-1);
  assert.equal(request.body.project_sources["library.algo"], "library edit");
  assert.equal(request.body.project_analyses["Algo.library.Analysis"], "library proof edit");
  assert.equal(request.body.analysis, "main proof edit");
  assert.equal(request.request.headers["X-Algo2Lean-Project"], "1");
  await app.flush();
  assert.equal(projectRecords(app).at(-1).data.files["library.algo"].source, "library edit");
});

test("opening and closing a project preserves the existing standalone draft pair", async () => {
  const app = editor();
  await app.ready();
  await app.edit("unsaved standalone");
  await app.editAnalysis("unsaved standalone proof");
  await openProject(app);
  assert.ok(app.records().some((record) => record.source === "unsaved standalone" && record.analysis === "unsaved standalone proof"));
  await app.edit("project edit");
  await app.click("close-project-button");
  assert.equal(app.byId("project-toolbar").hidden, true);
  assert.equal(app.byId("source").value, "unsaved standalone");
  assert.equal(app.byId("analysis").value, "unsaved standalone proof");
  assert.ok(projectRecords(app).some((record) => record.data.files["main.algo"].source === "project edit"));
});

test("same-named project folders have separate recovery identities", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "same", { "main.algo": "first folder" });
  await app.edit("first edited");
  await openProject(app, "same", { "main.algo": "second folder" });
  await app.edit("second edited");
  await app.flush();
  const records = projectRecords(app);
  assert.equal(records.length, 2);
  assert.notEqual(records[0].id, records[1].id);
  assert.deepEqual(records.map((record) => record.data.files["main.algo"].source).sort(), ["first edited", "second edited"]);
});

test("project reload starts merge sort and explicit project recovery forks later edits", async () => {
  const local = new MemoryStorage(), session = new MemoryStorage();
  const original = editor(local, session);
  await original.ready();
  await openProject(original);
  await original.edit("saved project source");
  await original.editAnalysis("saved project proof");
  await original.flush();
  const saved = projectRecords(original)[0];
  assert.equal(session.getItem(PROJECT_SESSION), saved.id);
  original.unmount();
  const example = currentMergeSortExample();
  const options = exampleCatalog(example);
  const a = editor(local, session, options), b = editor(local, session.copy(), options);
  await a.ready();
  await b.ready();
  for (const app of [a, b]) {
    assert.equal(app.byId("filename").value, "merge_sort.algo");
    assert.equal(app.byId("source").value, example.source);
    assert.equal(app.byId("analysis").value, example.analysis);
    assert.equal(app.byId("project-toolbar").hidden, true);
    assert.equal(app.byId("draft-picker").open, false);
    fireEvent.click(descendants(app.byId("draft-list")).find((node) => node.tagName === "BUTTON" && node.textContent === "Recover project"));
    await tick();
  }
  assert.equal(a.byId("source").value, "saved project source");
  assert.equal(b.byId("analysis").value, "saved project proof");
  const before = [...local.data];
  await a.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
  await a.edit("tab A project");
  await b.editAnalysis("tab B proof");
  await a.flush();
  await b.flush();
  const records = projectRecords(a);
  assert.equal(records.length, 3);
  assert.equal(records.find((record) => record.id === saved.id).data.files["main.algo"].source, "saved project source");
  await a.click("close-project-button");
  assert.equal(a.byId("filename").value, "merge_sort.algo");
  assert.match(a.byId("source").value, /def merge_sort\(a: Seq, lo: Int, hi: Int\)/);
  assert.equal(a.store.state.generatedModule, "MergeSortGenerated");
});

test("a dirty inactive project module is protected when browser storage fails", async () => {
  const app = editor();
  await app.ready();
  await openProject(app);
  app.local.fail.add("write");
  await app.edit("unsaved main module");
  await selectModule(app, "library.algo");
  const closing = await app.dispatchWindow("beforeunload");
  assert.equal(closing.defaultPrevented, true);
  app.confirm.answer = () => false;
  await app.click("close-project-button");
  assert.equal(app.byId("project-toolbar").hidden, false);
  await selectModule(app, "main.algo");
  assert.equal(app.byId("source").value, "unsaved main module");
});

test("project source and analysis package downloads keep their module paths intact", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", { "pkg/item.algo": PROJECT_LIBRARY, "analysis/pkg/item.lean": "-- proof" });
  await app.click("save-button");
  await app.click("analysis-save-button");
  assert.equal(app.byId("filename").value, "pkg/item.algo");
  assert.equal(app.byId("analysis-filename").value, "analysis/pkg/item.lean");
  assert.deepEqual(app.downloads.map(({ name }) => name), ["item.algo", "item.zip"]);
  await app.click("compile-button");
  assert.equal(app.requests.at(-1).body.filename, "pkg/item.algo");
});

test("Save analysis packages pending project sources, companion proofs, and support imports", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", { "main.algo": PROJECT_SOURCE, "pkg/item.algo": PROJECT_LIBRARY,
    "analysis/main.lean": "-- saved main proof", "analysis/pkg/item.lean": "-- saved item proof",
    "analysis/support/facts.lean": "-- imported support proof" });
  await app.edit("latest main source");
  await app.editAnalysis("-- latest main proof");
  await selectModule(app, "pkg/item.algo");
  await app.edit("latest item source");
  await app.editAnalysis("import Algo.support.facts.Analysis\n-- latest item proof");
  await app.click("analysis-save-button");
  const exported = app.requests.filter(({ url }) => url === "/api/analysis-export").at(-1);
  assert.equal(exported.request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(exported.body.filename, "pkg/item.algo");
  assert.equal(exported.body.analysis_filename, "item.lean");
  assert.equal(exported.body.source, "latest item source");
  assert.equal(exported.body.analysis, "import Algo.support.facts.Analysis\n-- latest item proof");
  assert.deepEqual(exported.body.project_sources, { "main.algo": "latest main source", "pkg/item.algo": "latest item source" });
  assert.deepEqual(exported.body.project_analyses, {
    "Algo.main.Analysis": "-- latest main proof",
    "Algo.pkg.item.Analysis": "import Algo.support.facts.Analysis\n-- latest item proof",
    "Algo.support.facts.Analysis": "-- imported support proof",
  });
  assert.equal(app.downloads.at(-1).name, "item.zip");
  assert.equal(app.byId("analysis-filename").value, "analysis/pkg/item.lean");
  assert.equal(app.text("analysis-pane-filename"), "analysis/pkg/item.lean");
  const files = projectRecords(app)[0].data.files;
  assert.equal(files["pkg/item.algo"].savedAnalysis, exported.body.analysis);
  assert.equal(files["pkg/item.algo"].savedAnalysisFilename, "analysis/pkg/item.lean");
  assert.equal(files["pkg/item.algo"].savedSource, PROJECT_LIBRARY);
  assert.equal(files["main.algo"].savedAnalysis, "-- saved main proof");
});

test("late analysis packages do not download or mark another project module saved", async () => {
  let finishResponse;
  const app = editor(undefined, undefined, { fetch: async (url) => url === "/api/analysis-export"
    ? new Promise((resolve) => { finishResponse = resolve; }) : null });
  await app.ready();
  await openProject(app, "sample", { "main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY,
    "analysis/main.lean": "-- saved main proof", "analysis/library.lean": "-- saved library proof" });
  await app.editAnalysis("-- pending main proof");
  await app.click("analysis-save-button");
  await selectModule(app, "library.algo");
  await app.editAnalysis("-- pending library proof");
  finishResponse({ ok: true, blob: async () => new Blob(["old main archive"], { type: "application/zip" }) });
  await tick();
  await app.flush();
  assert.equal(app.downloads.length, 0);
  assert.equal(app.byId("filename").value, "library.algo");
  assert.equal(app.byId("analysis").value, "-- pending library proof");
  assert.match(app.text("analysis-save-state"), /Unsaved/);
  const files = projectRecords(app)[0].data.files;
  assert.equal(files["main.algo"].savedAnalysis, "-- saved main proof");
  assert.equal(files["library.algo"].savedAnalysis, "-- saved library proof");
});

test("late analysis packages cannot replace save state after switching to a different project", async () => {
  let finishArchive;
  const app = editor(undefined, undefined, { fetch: async (url) => url === "/api/analysis-export"
    ? { ok: true, blob: () => new Promise((resolve) => { finishArchive = resolve; }) } : null });
  await app.ready();
  await openProject(app, "first", { "main.algo": PROJECT_SOURCE, "analysis/main.lean": "-- first saved proof" });
  await app.editAnalysis("-- pending first proof");
  await app.click("analysis-save-button");
  await openProject(app, "second", { "main.algo": PROJECT_LIBRARY, "analysis/main.lean": "-- second saved proof" });
  await app.editAnalysis("-- pending second proof");
  const currentMessage = app.text("analysis-file-message");
  finishArchive(new Blob(["first archive"], { type: "application/zip" }));
  await tick();
  await app.flush();
  assert.equal(app.downloads.length, 0);
  assert.equal(app.text("project-name"), "second");
  assert.equal(app.byId("analysis").value, "-- pending second proof");
  assert.equal(app.text("analysis-file-message"), currentMessage);
  assert.match(app.text("analysis-save-state"), /Unsaved/);
  assert.equal(app.byId("analysis-save-button").disabled, false);
  for (const record of projectRecords(app)) {
    assert.equal(record.data.files["main.algo"].savedAnalysis, `-- ${record.data.name} saved proof`);
  }
});

test("pane filenames retain nested paths when switching project modules and returning to a standalone file", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", {
    "main.algo": PROJECT_SOURCE, "pkg/item.algo": PROJECT_LIBRARY,
    "analysis/main.lean": "-- main proof", "analysis/pkg/item.lean": "-- item proof",
  });
  const filenames = () => ["source", "lean", "points", "analysis"].map((pane) => app.text(pane + "-pane-filename"));
  assert.deepEqual(filenames(), ["main.algo", "Algo/main/Generated.lean", "Algo/main/Points.lean", "analysis/main.lean"]);
  await selectModule(app, "pkg/item.algo");
  assert.deepEqual(filenames(), ["pkg/item.algo", "Algo/pkg/item/Generated.lean", "Algo/pkg/item/Points.lean", "analysis/pkg/item.lean"]);
  await selectModule(app, "main.algo");
  assert.deepEqual(filenames(), ["main.algo", "Algo/main/Generated.lean", "Algo/main/Points.lean", "analysis/main.lean"]);
  await app.click("close-project-button");
  assert.deepEqual(filenames(), ["merge_sort.algo", "MergeSortGenerated.lean", "MergeSortGeneratedPoints.lean", "Analysis.lean"]);
});

test("project archive downloads include pending source and proof edits", async () => {
  const app = editor();
  await app.ready();
  await openProject(app);
  await app.edit("latest source");
  await app.editAnalysis("latest proof");
  await app.click("project-export-button");
  const request = app.requests.filter(({ url }) => url === "/api/project-export").at(-1);
  assert.equal(request.request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(request.body.project_sources["main.algo"], "latest source");
  assert.equal(request.body.project_analyses["Algo.main.Analysis"], "latest proof");
  assert.equal(app.downloads.at(-1).name, "Algo2Lean-project.zip");
});

test("folder read races leave newer standalone edits untouched", async () => {
  const app = editor();
  await app.ready();
  await app.click("open-project-button");
  let finish;
  await app.chooseFiles("project-picker", [{ name: "main.algo", webkitRelativePath: "sample/main.algo", size: 3,
    text: () => new Promise((resolve) => { finish = resolve; }) }]);
  await app.edit("newer source");
  finish("old source");
  await tick();
  assert.equal(app.byId("source").value, "newer source");
  assert.equal(app.byId("project-toolbar").hidden, true);
  assert.match(app.text("file-message"), /workspace changed/);
});

test("ambiguous companions, case collisions, and oversized projects leave the editor unchanged", async () => {
  const app = editor();
  await app.ready();
  const original = app.byId("source").value;
  for (const files of [
    { "main.algo": PROJECT_SOURCE, "main.lean": "one proof", "analysis/main.lean": "another proof" },
    { "pkg/a.algo": PROJECT_LIBRARY, "Pkg/b.algo": PROJECT_LIBRARY },
    { "main.algo": "x".repeat(256 * 1024 + 1) },
    { ["long".repeat(63) + ".algo"]: PROJECT_LIBRARY },
    { "main.algo": PROJECT_LIBRARY, ...Object.fromEntries(Array.from({ length: 256 }, (_, index) => [`analysis/proof_${index}.lean`, "-- companion"])) },
  ]) {
    await openProject(app, "bad", files);
    assert.equal(app.byId("source").value, original);
    assert.equal(app.byId("project-toolbar").hidden, true);
    assert.match(app.text("file-message"), /Could not open the project/);
  }
});

test("native directory picker cancellation preserves the workspace without an error", async () => {
  const app = editor();
  await app.ready();
  const before = app.byId("source").value;
  app.store.options.showDirectoryPicker = async () => { const error = new Error("canceled"); error.name = "AbortError"; throw error; };
  await app.click("open-project-button");
  assert.equal(app.byId("source").value, before);
  assert.equal(app.byId("open-project-button").disabled, false);
  assert.doesNotMatch(app.text("file-message"), /Could not open/);
});

test("native folder picker reads only files below the explicitly selected directory", async () => {
  const app = editor();
  await app.ready();
  let options;
  app.store.options.showDirectoryPicker = async (value) => {
    options = value;
    return { name: "native", async *values() {
      yield { kind: "file", name: "main.algo", getFile: async () => ({ size: 10, text: async () => PROJECT_LIBRARY }) };
      yield { kind: "directory", name: ".git", values: () => { throw new Error("Hidden folder read"); } };
    } };
  };
  await app.click("open-project-button");
  await app.ready();
  assert.equal(options.mode, "read");
  assert.equal(app.text("project-name"), "native");
  assert.equal(app.byId("source").value, PROJECT_LIBRARY);
});
