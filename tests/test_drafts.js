"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const { Store } = require("../editor/drafts.js");

const PREFIX = "algo2lean.editor.draft.v2.";
const LEGACY_KEY = "algo2lean.editor.draft.v1";
const SESSION_KEY = "algo2lean.editor.active.v2";
const EXAMPLE_SESSION_KEY = "algo2lean.editor.example.v1";

class MemoryStorage {
  constructor(entries = []) {
    this.data = new Map(entries);
    this.writes = [];
    this.fail = new Set();
  }

  check(operation) {
    if (this.fail.has(operation)) throw new Error(`Storage ${operation} unavailable`);
  }

  get length() { this.check("read"); return this.data.size; }
  key(index) { this.check("read"); return [...this.data.keys()][index] ?? null; }
  getItem(key) { this.check("read"); return this.data.get(key) ?? null; }
  setItem(key, value) {
    this.check("write");
    this.writes.push([key, String(value)]);
    this.data.set(key, String(value));
  }
  removeItem(key) { this.check("remove"); this.data.delete(key); }
  copy() { return new MemoryStorage(this.data); }
}

let serial = 0;
function store(local = new MemoryStorage(), session = new MemoryStorage()) {
  let time = 100;
  return new Store(local, session, {
    makeId: () => `draft-${++serial}`,
    now: () => ++time,
  });
}

function snapshot(source = "original", filename = "example.algo") {
  return { source, filename, savedSource: "original", savedFilename: "example.algo" };
}

function pairedSnapshot(source = "original", analysis = "-- saved proof", overrides = {}) {
  return {
    ...snapshot(source), analysis, analysisFilename: "Proof.lean",
    savedAnalysis: "-- saved proof", savedAnalysisFilename: "Proof.lean", ...overrides,
  };
}

function seedPair(local, value = pairedSnapshot(), session = new MemoryStorage()) {
  const writer = store(local, session);
  writer.start(pairedSnapshot("", ""));
  writer.write(value);
  return writer.read(writer.activeId);
}

function seed(local, source = "recover me", session = new MemoryStorage()) {
  const writer = store(local, session);
  writer.start(snapshot());
  writer.write(snapshot(source));
  return writer.read(writer.activeId);
}

test("an untouched tab cannot replace a newer browser draft when it closes", () => {
  const local = new MemoryStorage();
  const older = store(local);
  const newer = store(local);
  older.start(snapshot());
  newer.start(snapshot());
  newer.write(snapshot("new work"));
  const beforeClose = [...local.data];
  assert.equal(older.write(snapshot()), false);
  assert.deepEqual([...local.data], beforeClose);
  assert.equal(newer.list()[0].source, "new work");
});

test("two actively edited tabs keep independent records through alternating writes", () => {
  const local = new MemoryStorage();
  const a = store(local);
  const b = store(local);
  a.start(snapshot());
  b.start(snapshot());
  a.write(snapshot("A first"));
  b.write(snapshot("B first"));
  const aId = a.activeId;
  const bId = b.activeId;
  assert.notEqual(aId, bId);
  a.write(snapshot("A final"));
  b.write(snapshot("B final"));
  assert.equal(a.read(aId).source, "A final");
  assert.equal(b.read(bId).source, "B final");
  assert.equal(a.list().length, 2);
});

test("reloads and duplicated session pointers fork on edit without overwriting recovery", () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const original = seed(local, "before reload", session);
  const reloaded = store(local, session);
  const duplicate = store(local, session.copy());
  assert.equal(reloaded.preferredId(), original.id);
  assert.equal(duplicate.preferredId(), original.id);
  reloaded.start(original, original.id);
  duplicate.start(original, original.id);
  const unchanged = [...local.data];
  assert.equal(reloaded.write(original), false);
  assert.equal(duplicate.write(original), false);
  assert.deepEqual([...local.data], unchanged);
  reloaded.write({ ...original, source: "reload changes" });
  duplicate.write({ ...original, source: "duplicate changes" });
  assert.notEqual(reloaded.activeId, duplicate.activeId);
  assert.notEqual(reloaded.activeId, original.id);
  assert.notEqual(duplicate.activeId, original.id);
  assert.equal(reloaded.read(original.id).source, "before reload");
  assert.equal(reloaded.list().length, 3);
});

test("selecting recovery drafts does not change their content or timestamps", () => {
  const local = new MemoryStorage();
  const first = seed(local, "first document");
  const second = seed(local, "second document");
  const reader = store(local);
  const before = [...local.data];
  for (const saved of [first, second, first]) {
    reader.start(saved, saved.id);
    assert.equal(reader.hasChanges(saved), false);
    assert.equal(reader.write(saved), false);
  }
  assert.deepEqual([...local.data], before);
});

test("only content or file-save state changes update a draft timestamp", () => {
  const local = new MemoryStorage();
  const writer = store(local);
  writer.start(snapshot());
  assert.equal(writer.hasChanges(snapshot()), false);
  assert.equal(writer.write(snapshot("edit")), true);
  const first = writer.read(writer.activeId);
  const writes = local.writes.length;
  assert.equal(writer.write(snapshot("edit")), false);
  assert.equal(local.writes.length, writes);
  assert.equal(writer.read(writer.activeId).updatedAt, first.updatedAt);
  assert.equal(writer.write({ ...snapshot("edit"), savedSource: "edit" }), true);
  const saved = writer.read(writer.activeId);
  assert.equal(saved.savedSource, "edit");
  assert.ok(saved.updatedAt > first.updatedAt);
  assert.equal(writer.write({ ...snapshot("edit"), savedSource: "edit", filename: "renamed.algo" }), true);
  assert.equal(writer.read(writer.activeId).filename, "renamed.algo");
});

test("switching documents leaves the prior document recoverable", () => {
  const writer = store();
  writer.start(snapshot());
  writer.write(snapshot("first edited"));
  const firstId = writer.activeId;
  writer.start(snapshot("second original", "second.algo"));
  writer.write(snapshot("second edited", "second.algo"));
  assert.notEqual(writer.activeId, firstId);
  assert.equal(writer.read(firstId).source, "first edited");
  assert.equal(writer.list().length, 2);
});

test("explicitly discarded active drafts stay discarded until another edit", () => {
  const writer = store();
  writer.start(snapshot());
  writer.write(snapshot("edited"));
  const oldId = writer.activeId;
  writer.remove(oldId);
  assert.equal(writer.read(oldId), null);
  assert.equal(writer.write(snapshot("edited")), false);
  assert.equal(writer.list().length, 0);
  writer.write(snapshot("a later edit"));
  assert.notEqual(writer.activeId, oldId);
  assert.equal(writer.list().length, 1);
});

test("failed local writes preserve the recoverable copy and keep edits pending for retry", () => {
  const local = new MemoryStorage();
  const writer = store(local);
  writer.start(snapshot());
  writer.write(snapshot("last persisted"));
  const id = writer.activeId;
  local.fail.add("write");
  assert.throws(() => writer.write(snapshot("pending")), /unavailable/);
  assert.equal(writer.read(id).source, "last persisted");
  assert.equal(writer.hasChanges(snapshot("pending")), true);
  local.fail.clear();
  assert.equal(writer.write(snapshot("pending")), true);
  assert.equal(writer.read(writer.activeId).source, "pending");
});

test("disabled session storage still allows independent and recoverable drafts", () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  session.fail = new Set(["read", "write", "remove"]);
  const a = store(local, session);
  const b = store(local, session);
  a.start(snapshot());
  b.start(snapshot());
  assert.equal(a.write(snapshot("A")), true);
  assert.equal(b.write(snapshot("B")), true);
  assert.notEqual(a.activeId, b.activeId);
  assert.deepEqual(a.list().map((record) => record.source).sort(), ["A", "B"]);
  assert.doesNotThrow(() => a.preferredId());
});

test("local storage read and removal failures are visible to the caller", () => {
  const local = new MemoryStorage();
  const saved = seed(local);
  const reader = store(local);
  local.fail.add("read");
  assert.throws(() => reader.list(), /unavailable/);
  assert.throws(() => reader.read(saved.id), /unavailable/);
  local.fail.clear();
  local.fail.add("remove");
  assert.throws(() => reader.remove(saved.id), /unavailable/);
  assert.equal(reader.read(saved.id).source, saved.source);
});

test("a legacy draft is migrated once with file-save state intact", () => {
  const legacy = { ...snapshot("legacy edit"), updatedAt: 42 };
  const local = new MemoryStorage([[LEGACY_KEY, JSON.stringify(legacy)]]);
  const writer = store(local);
  const migrated = writer.migrateLegacy();
  assert.equal(migrated.source, legacy.source);
  assert.equal(migrated.savedSource, legacy.savedSource);
  assert.equal(migrated.updatedAt, 42);
  assert.equal(local.getItem(LEGACY_KEY), null);
  assert.equal(writer.list().length, 1);
  assert.equal(writer.migrateLegacy(), null);
  assert.equal(writer.list().length, 1);
});

test("legacy migration keeps the original when writing or verifying the copy fails", () => {
  for (const failure of ["write", "verify"]) {
    const raw = JSON.stringify({ ...snapshot("legacy work"), updatedAt: 42 });
    const local = new MemoryStorage([[LEGACY_KEY, raw]]);
    if (failure === "write") local.fail.add("write");
    else {
      const originalGet = local.getItem.bind(local);
      local.getItem = (key) => key.startsWith(PREFIX) ? null : originalGet(key);
    }
    assert.throws(() => store(local).migrateLegacy());
    assert.equal(local.getItem(LEGACY_KEY), raw);
  }
});

test("a failed legacy removal leaves both copies recoverable", () => {
  const raw = JSON.stringify({ ...snapshot("legacy work"), updatedAt: 42 });
  const local = new MemoryStorage([[LEGACY_KEY, raw]]);
  local.fail.add("remove");
  const writer = store(local);
  assert.throws(() => writer.migrateLegacy(), /unavailable/);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  assert.equal(writer.list()[0].source, "legacy work");
});

test("malformed legacy records remain untouched and do not become new drafts", () => {
  for (const raw of ["not JSON", "null", '{"source":2,"filename":"bad.algo"}']) {
    const local = new MemoryStorage([[LEGACY_KEY, raw]]);
    const writer = store(local);
    assert.equal(writer.migrateLegacy(), null);
    assert.equal(local.getItem(LEGACY_KEY), raw);
    assert.equal(writer.list().length, 0);
  }
});

test("one malformed or foreign record does not hide valid recovery records", () => {
  const local = new MemoryStorage();
  const valid = seed(local, "still recoverable");
  local.setItem(PREFIX + "broken", "not JSON");
  local.setItem(PREFIX + "wrong-type", JSON.stringify({ ...valid, id: "wrong-type", source: 7 }));
  local.setItem(PREFIX + "wrong-id", JSON.stringify(valid));
  local.setItem(PREFIX + "bad-time", JSON.stringify({ ...valid, id: "bad-time", updatedAt: -1 }));
  local.setItem("unrelated.setting", "true");
  const reader = store(local);
  assert.deepEqual(reader.list().map((record) => record.id), [valid.id]);
  assert.equal(reader.read("broken"), null);
  assert.equal(reader.read("wrong-id"), null);
  assert.equal(local.getItem("unrelated.setting"), "true");
});

// Run the real browser scripts with only the DOM, storage, and timers they use.
// This catches event-handler regressions without adding browser-test packages.
class Element {
  constructor(tagName = "div") {
    this.tagName = tagName.toUpperCase();
    this.value = "";
    this.textContent = "";
    this.innerHTML = "";
    this.children = [];
    this.listeners = new Map();
    this.attributes = new Map();
    this.style = {};
    this.dataset = {};
    this.hidden = false;
    this.open = false;
    this.selectionStart = 0;
    this.selectionEnd = 0;
    this.scrollTop = 0;
    this.scrollLeft = 0;
    this.classList = {
      toggle() {}, add() {}, remove() {}, contains: () => false,
    };
  }
  addEventListener(type, fn) {
    const listeners = this.listeners.get(type) || [];
    listeners.push(fn);
    this.listeners.set(type, listeners);
  }
  async dispatch(type, props = {}) {
    const event = { target: this, preventDefault() { this.defaultPrevented = true; }, ...props };
    for (const fn of this.listeners.get(type) || []) await fn(event);
    return event;
  }
  append(...children) { this.children.push(...children); }
  appendChild(child) { this.append(child); return child; }
  replaceChildren(...children) { this.children = children; }
  get firstChild() { return this.children[0] ?? null; }
  get childElementCount() { return this.children.length; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  getAttribute(name) { return this.attributes.get(name) ?? null; }
  removeAttribute(name) { this.attributes.delete(name); }
  querySelector(selector) {
    if (!this.selectors) this.selectors = new Map();
    if (!this.selectors.has(selector)) this.selectors.set(selector, new Element(selector));
    return this.selectors.get(selector);
  }
  focus() { this.focused = true; }
  blur() { this.focused = false; }
  scrollIntoView() { this.scrolledIntoView = true; }
  remove() {}
  click() { return this.dispatch("click"); }
  setSelectionRange(start, end) { this.selectionStart = start; this.selectionEnd = end; }
}

function archiveResponse(content = "zip bytes") {
  return { ok: true, blob: async () => new Blob([content], { type: "application/zip" }) };
}

function editor(local = new MemoryStorage(), session = new MemoryStorage(), options = {}) {
  const requests = [];
  const downloads = [];
  const html = fs.readFileSync(path.join(__dirname, "../editor/index.html"), "utf8");
  const elements = new Map([...html.matchAll(/\bid="([^"]+)"/g)].map((match) => [match[1], new Element()]));
  elements.get("filename").value = "merge_sort.algo";
  elements.get("analysis-filename").value = "Analysis.lean";
  elements.get("project-toolbar").hidden = true;
  elements.get("new-file-form").hidden = true;
  elements.get("undo-clear-drafts-button").hidden = true;
  elements.get("analyze-button").append({ textContent: "Check analysis " });
  elements.get("examples").options = [new Element("option")];
  const document = new Element("document");
  document.getElementById = (id) => {
    assert.ok(elements.has(id), `Unknown editor element #${id}`);
    return elements.get(id);
  };
  document.createElement = (tag) => {
    const element = new Element(tag);
    if (tag === "a") element.click = () => downloads.push({ name: element.download, href: element.href });
    return element;
  };
  document.createTextNode = (text) => ({ textContent: text });
  document.body = new Element("body");
  document.visibilityState = "visible";
  const window = new Element("window");
  window.confirm = () => true;
  const timers = new Map();
  let timerId = 0;
  const context = {
    document, window, navigator: { platform: "", clipboard: { writeText: async () => {} } },
    localStorage: local, sessionStorage: session,
    console, AbortController, Blob, URL, Date,
    crypto: { randomUUID: () => `browser-${++serial}` },
    setTimeout: (fn) => { timers.set(++timerId, fn); return timerId; },
    clearTimeout: (id) => timers.delete(id),
    fetch: async (url, request) => {
      requests.push({ url, request, body: request?.body ? JSON.parse(request.body) : null });
      if (options.fetch) {
        const custom = await options.fetch(url, request);
        if (custom) return custom;
      }
      if (url === "/api/analysis-export" || url === "/api/project-export") return archiveResponse();
      const body = request?.body ? JSON.parse(request.body) : {};
      const module = body.project_sources ? "Algo." + body.filename.replace(/\.algo$/, "").replace(/\//g, ".") : null;
      return { ok: true, blob: async () => new Blob(["zip bytes"], { type: "application/zip" }),
      json: async () => url === "/api/capabilities" ? { project_protocol: 1 } : url === "/api/examples"
        ? { examples: [{ name: "Other", source: "def other() -> Int:\n    return 5\n", filename: "other.algo",
          module: "OtherGenerated", analysis: "import OtherGenerated\nimport OtherGeneratedPoints\n-- example proof\n" }] }
        : { lean: "def test := 1", points_lean: "-- named-line interface", shared_lean: "-- shared library",
          program_lean: "def test := 1", diagnostics: [], functions: [], ok: true,
          ...(module ? { module: module + ".Generated", points_module: module + ".Points", namespace: module } : {}) },
      };
    },
  };
  if (options.hosted) {
    window.Algo2LeanBackend = { hosted: true, request: context.fetch };
    window.Algo2LeanBrowserHost = require("../editor/browser-host.js");
    context.fetch = async () => { throw new Error("Hosted source must use the browser worker backend"); };
  }
  if (options.blockStorageAccess) {
    Object.defineProperty(context, "localStorage", { get() { throw new Error("Storage disabled"); } });
    Object.defineProperty(context, "sessionStorage", { get() { throw new Error("Storage disabled"); } });
    Object.defineProperty(window, "localStorage", { get() { throw new Error("Storage disabled"); } });
    Object.defineProperty(window, "sessionStorage", { get() { throw new Error("Storage disabled"); } });
  } else {
    window.localStorage = local;
    window.sessionStorage = session;
  }
  vm.createContext(context);
  for (const filename of ["drafts.js", "interface.js", "proof-outline.js", "app.js"]) {
    vm.runInContext(fs.readFileSync(path.join(__dirname, "../editor", filename), "utf8"), context, { filename });
  }
  return {
    local, session, document, window, elements, requests, downloads,
    ready: async () => { for (let i = 0; i < 8; i++) await Promise.resolve(); },
    edit: async (text) => {
      elements.get("source").value = text;
      await elements.get("source").dispatch("input");
    },
    editAnalysis: async (text) => {
      elements.get("analysis").value = text;
      await elements.get("analysis").dispatch("input");
    },
    rename: async (id, name) => {
      elements.get(id).value = name;
      await elements.get(id).dispatch("input");
    },
    openFile: async (id, name, text) => {
      const picker = elements.get(id);
      picker.files = [{ name, size: text.length, text: async () => text }];
      await picker.dispatch("change");
    },
    flush: async () => {
      const pending = [...timers.values()];
      timers.clear();
      for (const fn of pending) await fn();
    },
    records: () => store(local).list(),
  };
}

function descendants(element) {
  return [element, ...(element.children || []).flatMap(descendants)];
}

function draftAction(app, sourceText, action) {
  const card = app.elements.get("draft-list").children.find((candidate) =>
    descendants(candidate).some((element) => element.tagName === "PRE" && element.textContent === sourceText));
  assert.ok(card, `Missing draft card for ${sourceText}`);
  const button = descendants(card).find((element) => element.tagName === "BUTTON" && element.textContent === action);
  assert.ok(button, `Missing ${action} button`);
  return button;
}

test("the editor shows scoped function, method, and point relations without rewriting a proof", async () => {
  const sourceText = "def work(n: Int) -> Int:\n    # @charge\n    tick(\"work\", n)\n    return n\n";
  const proof = "-- Keep my existing compatibility proof.\ntheorem old_proof : is_Output_work 0 0 := by\n  sorry\n";
  const functions = [
    { name: "work", lean_name: "work", output_relation: "work.Returns",
      transcript_relation: "work.ValidTranscript", cost_relation: "work.ReturnsWithCost",
      parameters: [{ type: "Int" }], return_type: "Int",
      points: [{ relation: "work.At.charge", line: 3, column: 5 }] },
    { name: "Counter_add", display_name: "Counter.add", lean_name: "Counter.add",
      output_relation: "Counter.add.Returns", transcript_relation: "Counter.add.ValidTranscript",
      lean_input_type: "ObjectRef × Int", lean_output_type: "Unit" },
    { name: "match", lean_name: "«match»", output_relation: "«match».Returns",
      transcript_relation: "«match».ValidTranscript", parameters: [], return_type: "Int" },
  ];
  const app = editor(new MemoryStorage(), new MemoryStorage(), { fetch: async (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      ok: true, lean: "-- compiled", points_lean: "-- points", functions,
    }) };
  } });
  await app.ready();
  await app.edit(sourceText);
  await app.editAnalysis(proof);
  await app.elements.get("compile-button").click();
  const text = descendants(app.elements.get("relations")).map((element) => element.textContent).join("\n");
  for (const expected of ["work.Returns", "work.ValidTranscript", "work.ReturnsWithCost", "work.At.charge",
    "Counter.add.Returns", "Counter.add.ValidTranscript", "«match».Returns"]) assert.ok(text.includes(expected), expected);
  assert.ok(!text.includes("is_Output_"));
  assert.ok(!text.includes("Counter_add"));
  const point = descendants(app.elements.get("relations")).find((element) => element.tagName === "BUTTON" && element.textContent === "work.At.charge");
  await point.click();
  assert.equal(point.getAttribute("aria-expanded"), "true");
  assert.equal(app.elements.get("source").selectionStart, 0);
  const jump = descendants(app.elements.get("relations")).find((element) => element.tagName === "BUTTON" && element.textContent.startsWith("Go to source"));
  await jump.click();
  assert.equal(app.elements.get("source").selectionStart, sourceText.indexOf('tick("work"'));
  assert.equal(app.elements.get("analysis").value, proof);
});

test("an older compiler requests an update without exposing removed interface names", async () => {
  const app = editor(new MemoryStorage(), new MemoryStorage(), { fetch: async (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      ok: true, lean: "-- compiled", functions: [
        { name: "plain", return_type: "Int" },
        { name: "Counter_add", display_name: "Counter.add", return_type: "Int" },
        { name: "Counter", display_name: "Counter.__init__", return_type: "Counter" },
      ],
    }) };
  } });
  await app.ready();
  const starter = app.elements.get("analysis").value;
  assert.ok(starter.includes("public relations shown by the compiler"));
  assert.ok(!starter.includes("f.Returns"));
  assert.ok(!starter.includes("f.Call"));
  await app.elements.get("compile-button").click();
  const text = descendants(app.elements.get("relations")).map((element) => element.textContent).join("\n");
  assert.match(text, /current compiler/);
  assert.doesNotMatch(text, /is_Output_|is_Transcript_/);
  assert.ok(!text.includes(".Returns"));
  assert.ok(!text.includes(".ValidTranscript"));
  assert.equal(app.elements.get("analysis").value, starter);
});

test("Escape leaves each code box without changing text or selection", async () => {
  const app = editor();
  await app.ready();
  await app.editAnalysis("theorem proof : True := by\n  trivial\n");
  for (const id of ["source", "analysis", "lean-selection", "points-selection", "shared-output", "check-output", "analysis-output"]) {
    const box = app.elements.get(id);
    const before = { value: box.value, text: box.textContent };
    box.setSelectionRange(2, 6);
    box.focus();
    assert.equal(box.focused, true);
    await box.dispatch("keydown", { key: "Escape" });
    assert.equal(box.focused, false, `${id} should release focus for page scrolling`);
    assert.deepEqual({ value: box.value, text: box.textContent }, before);
    assert.equal(box.selectionStart, 2);
    assert.equal(box.selectionEnd, 6);
  }
});

test("generated text controls contain the exact current Lean in both panes", async () => {
  let generation = 1;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      lean: `-- version ${generation}\nexample : 1 < 2 := by decide\n`,
      points_lean: `-- points ${generation}\ndef label := "<named>"\n`, functions: [],
    }) };
  } });
  await app.ready();
  for (generation of [1, 2]) {
    await app.elements.get("compile-button").click();
    const core = app.elements.get("lean-selection").value;
    const points = app.elements.get("points-selection").value;
    assert.equal(core, `-- version ${generation}\nexample : 1 < 2 := by decide\n`);
    assert.equal(points, `-- points ${generation}\ndef label := "<named>"\n`);
    // A measuring line after the real trailing newline keeps EOF selection in
    // the shared scroll surface instead of internally scrolling the textarea.
    assert.ok(app.elements.get("lean-code").innerHTML.endsWith("\n\n"));
    assert.ok(app.elements.get("points-code").innerHTML.endsWith("\n\n"));
    await app.elements.get("export-button").click();
    await app.elements.get("export-points-button").click();
    assert.equal(await (await fetch(app.downloads.at(-2).href)).text(), core);
    assert.equal(await (await fetch(app.downloads.at(-1).href)).text(), points);
  }
});

test("pane filenames follow standalone renames and example changes without relabeling stale output", async () => {
  const app = editor();
  await app.ready();
  const label = (id) => app.elements.get(id + "-pane-filename").textContent;
  await app.elements.get("compile-button").click();
  assert.equal(label("source"), "merge_sort.algo");
  assert.equal(label("lean"), "MergeSortGenerated.lean");
  assert.equal(label("points"), "MergeSortGeneratedPoints.lean");
  assert.equal(label("analysis"), "Analysis.lean");
  assert.match(app.elements.get("shared-summary").textContent, /Algo2Lean\.lean/);

  const previousOutput = app.elements.get("lean-selection").value;
  await app.rename("filename", "renamed_sort");
  await app.rename("analysis-filename", "SortProof");
  assert.equal(label("source"), "renamed_sort.algo");
  assert.equal(label("analysis"), "SortProof.lean");
  assert.equal(app.elements.get("lean-selection").value, previousOutput);
  assert.equal(label("lean"), "MergeSortGenerated.lean");
  assert.equal(label("points"), "MergeSortGeneratedPoints.lean");
  await app.elements.get("compile-button").click();
  assert.equal(label("lean"), "RenamedSortGenerated.lean");
  assert.equal(label("points"), "RenamedSortGeneratedPoints.lean");

  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  await app.ready();
  assert.equal(label("source"), "other.algo");
  assert.equal(label("lean"), "OtherGenerated.lean");
  assert.equal(label("points"), "OtherGeneratedPoints.lean");
  assert.equal(label("analysis"), "Analysis.lean");
});

test("shared execution browsing preserves public proof imports and exports the displayed files", async () => {
  const publicModule = "Algo.even.Generated";
  const publicPoints = "Algo.even.Points";
  const sharedModule = "Algo._a2l_groups.Gtest.Generated";
  const sharedPoints = "Algo._a2l_groups.Gtest.Points";
  const files = {
    [publicModule]: `import ${sharedModule}\n-- public even interface\n`,
    [publicPoints]: `import ${sharedPoints}\n-- public named points\n`,
    [sharedModule]: "-- shared transitions for even and odd\n",
    [sharedPoints]: "-- shared named points for even and odd\n",
  };
  let cyclic = true;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      ok: true, lean: files[publicModule], points_lean: files[publicPoints], functions: [],
      module: publicModule, points_module: publicPoints, project_files: files,
      implementation_module: cyclic ? sharedModule : null,
      implementation_points_module: cyclic ? sharedPoints : null,
    }) };
  } });
  await app.ready();
  await openProject(app, "mutual", {
    "even.algo": "from odd import odd\ndef even(n: Int) -> Int:\n    return odd(n)\n",
    "odd.algo": "from even import even\ndef odd(n: Int) -> Int:\n    return even(n)\n",
  });
  await app.elements.get("compile-button").click();
  const proof = app.elements.get("analysis").value;
  assert.equal(app.elements.get("generated-view-control").hidden, false);
  assert.equal(app.elements.get("lean-selection").value, files[publicModule]);
  assert.equal(app.elements.get("lean-pane-filename").textContent, "Algo/even/Generated.lean");
  assert.equal(app.elements.get("points-pane-filename").textContent, "Algo/even/Points.lean");
  app.elements.get("generated-view").value = "execution";
  await app.elements.get("generated-view").dispatch("change");
  assert.equal(app.elements.get("lean-selection").value, files[sharedModule]);
  assert.equal(app.elements.get("points-selection").value, files[sharedPoints]);
  assert.equal(app.elements.get("lean-pane-filename").textContent, "Algo/_a2l_groups/Gtest/Generated.lean");
  assert.equal(app.elements.get("points-pane-filename").textContent, "Algo/_a2l_groups/Gtest/Points.lean");
  assert.equal(app.elements.get("analysis-module").textContent, publicModule);
  assert.equal(app.elements.get("analysis-points-module").textContent, publicPoints);
  assert.equal(app.elements.get("analysis").value, proof);
  await app.elements.get("export-button").click();
  await app.elements.get("export-points-button").click();
  assert.equal(app.downloads.at(-2).name, sharedModule + ".lean");
  assert.equal(app.downloads.at(-1).name, sharedPoints + ".lean");
  assert.equal(await (await fetch(app.downloads.at(-2).href)).text(), files[sharedModule]);
  assert.equal(await (await fetch(app.downloads.at(-1).href)).text(), files[sharedPoints]);
  await app.elements.get("compile-button").click();
  assert.equal(app.elements.get("generated-view").value, "execution");
  assert.equal(app.elements.get("lean-selection").value, files[sharedModule]);
  await app.edit("-- edit source\n");
  assert.equal(app.elements.get("generated-view").disabled, true);
  cyclic = false;
  await app.elements.get("compile-button").click();
  assert.equal(app.elements.get("generated-view-control").hidden, true);
  assert.equal(app.elements.get("lean-selection").value, files[publicModule]);
  assert.equal(app.elements.get("lean-pane-filename").textContent, "Algo/even/Generated.lean");
  assert.equal(app.elements.get("points-pane-filename").textContent, "Algo/even/Points.lean");
});

test("probability browsing exports its companion and keeps ordinary checks distinct", async () => {
  const module = "DiceGenerated";
  const probabilityModule = module + "Probability";
  const probability = `import ${module}\nimport Algo2LeanProbability\n-- uniform draw law\n`;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (["/api/compile", "/api/check"].includes(url)) return { ok: true, json: async () => ({
      ok: true, available: true, lean: "-- possible executions\n", points_lean: "-- points\n",
      shared_lean: "-- shared library\n", program_lean: "-- possible executions\n", functions: [{
        name: "roll", interface_entries: [{ name: "roll.law", category: "probability", file_kind: "probability",
          signature: "roll.law (heap : Heap) (input : Unit) : MeasureTheory.Measure (Algo2LeanProbability.Run Configuration)",
          meaning: "Probability law of the whole execution.", arguments: [] }],
      }],
      module, points_module: module + "Points", randomized: true,
      probability_module: probabilityModule, probability_lean: probability, probability_checked: false,
    }) };
  } });
  await app.ready();
  await app.elements.get("compile-button").click();
  const proof = app.elements.get("analysis").value;
  assert.ok(app.elements.get("generated-view").children.some((option) => option.textContent === "Probability interface"));
  const probabilityPanel = descendants(app.elements.get("relations")).find((element) => element.className === "interface-spec");
  assert.ok(descendants(probabilityPanel).some((element) => element.textContent === probabilityModule + ".lean"));
  app.elements.get("generated-view").value = "probability";
  await app.elements.get("generated-view").dispatch("change");
  assert.equal(app.elements.get("lean-selection").value, probability);
  assert.equal(app.elements.get("lean-pane-filename").textContent, probabilityModule + ".lean");
  assert.equal(app.elements.get("points-output").hidden, true);
  assert.equal(app.elements.get("standalone-button").disabled, true);
  assert.equal(app.elements.get("analysis").value, proof);
  await app.elements.get("export-button").click();
  assert.equal(app.downloads.at(-1).name, probabilityModule + ".lean");
  assert.equal(await (await fetch(app.downloads.at(-1).href)).text(), probability);
  await app.elements.get("check-button").click();
  assert.equal(app.elements.get("generated-view").value, "probability");
  assert.equal(app.elements.get("lean-state").textContent, "Requires Mathlib check");
  app.elements.get("generated-view").value = "public";
  await app.elements.get("generated-view").dispatch("change");
  assert.equal(app.elements.get("lean-state").textContent, "Lean checked");
  assert.equal(app.elements.get("standalone-button").disabled, false);
});

test("randomized project starters omit unavailable Facts and show probability limitations", async () => {
  const module = "Algo.main.Generated";
  const diagnostic = "Probability semantics for abstract interface dependencies are not supported yet.";
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      ok: true, lean: "-- possible executions\n", points_lean: "-- points\n", functions: [],
      module, points_module: "Algo.main.Points", randomized: true,
      probability_lean: "", probability_diagnostic: diagnostic,
      project_files: { [module]: "-- possible executions\n", "Algo.main.Points": "-- points\n" },
    }) };
  } });
  await app.ready();
  await openProject(app, "random", { "main.algo": "def roll() -> Int:\n    return randint(1, 7)\n" });
  await app.elements.get("compile-button").click();
  assert.match(app.elements.get("analysis").value, /^import Algo.main.Generated\nimport Algo.main.Points/);
  assert.doesNotMatch(app.elements.get("analysis").value, /import Algo.main.Facts/);
  assert.ok(app.elements.get("diagnostics").children.some((entry) => entry.textContent === diagnostic));
  assert.equal(app.elements.get("generated-view-control").hidden, true);
  await app.editAnalysis("import Algo.main.Generated\n-- preserve my proof\n");
  await app.elements.get("compile-button").click();
  assert.equal(app.elements.get("analysis").value, "import Algo.main.Generated\n-- preserve my proof\n");
});

test("named-point navigation scrolls the shared source viewport only after the explicit source action", async () => {
  const sourceText = ["def work(n: Int) -> Int:", ...Array(12).fill("    n = n + 1"),
    "    if n > 0:", "        if n > 1:", "            if n > 2:", "                if n > 3:",
    "                    # @answer", "                    return n", "    return 0", ""].join("\n");
  const app = editor(new MemoryStorage(), new MemoryStorage(), { fetch: async (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      ok: true, lean: "-- compiled", functions: [{ name: "work",
        points: [{ relation: "work.At.answer", line: 19, column: 21 }] }],
    }) };
  } });
  await app.ready();
  await app.edit(sourceText);
  await app.elements.get("compile-button").click();
  const source = app.elements.get("source");
  const viewport = app.elements.get("source-editor");
  // Only the shared viewport owns scrolling; the textarea's offsets are unrelated.
  source.scrollTop = 73;
  source.scrollLeft = 29;
  viewport.scrollTop = 0;
  viewport.scrollLeft = 0;
  const buttons = descendants(app.elements.get("relations")).filter((element) => element.tagName === "BUTTON");
  await buttons.find((button) => button.textContent === "work.At.answer").click();
  assert.equal(viewport.scrollTop, 0);
  assert.equal(viewport.scrollLeft, 0);
  assert.equal(source.selectionStart, 0);
  await buttons.find((button) => button.textContent.startsWith("Go to source")).click();
  assert.equal(source.selectionStart, sourceText.indexOf("return n"));
  assert.equal(source.focused, true);
  assert.ok(viewport.scrollTop > 0);
  assert.ok(viewport.scrollLeft > 0);
  assert.equal(viewport.scrolledIntoView, true);
  assert.equal(source.scrollTop, 73);
  assert.equal(source.scrollLeft, 29);
});

test("analysis measurement follows edits, opened files, and empty proofs without stale content", async () => {
  const app = editor();
  await app.ready();
  const analysis = app.elements.get("analysis");
  const measure = app.elements.get("analysis-measure");
  const measuredText = () => measure.innerHTML.replace(/<[^>]*>/g, "")
    .replace(/&(?:amp|lt|gt|quot);/g, (entity) => ({ "&amp;": "&", "&lt;": "<", "&gt;": ">", "&quot;": '"' })[entity]);
  assert.equal(measuredText(), analysis.value + "\n");
  const longProof = "-- " + "wide proof ".repeat(50) + "\ntheorem test : True := by\n  trivial\n\n";
  await app.editAnalysis(longProof);
  assert.equal(measuredText(), longProof + "\n");
  assert.equal(app.elements.get("analysis-line-numbers").textContent, "1\n2\n3\n4\n5");
  await app.openFile("analysis-file-picker", "NewProof.lean", "-- new proof\r\nexample : True := by trivial\r\n");
  assert.equal(measuredText(), "-- new proof\nexample : True := by trivial\n\n");
  assert.equal(measuredText(), analysis.value + "\n");
  await app.editAnalysis("");
  assert.equal(measuredText(), "\n");
  assert.equal(app.elements.get("analysis-line-numbers").textContent, "1");
});

test("editor unchanged close cannot erase another tab's debounced edit", async () => {
  const local = new MemoryStorage();
  const stale = editor(local);
  const active = editor(local);
  await Promise.all([stale.ready(), active.ready()]);
  await active.edit("def important() -> Int:\n    return 42\n");
  await active.flush();
  const before = [...local.data];
  await stale.window.dispatch("beforeunload");
  stale.document.visibilityState = "hidden";
  await stale.document.dispatch("visibilitychange");
  assert.deepEqual([...local.data], before);
  assert.ok(active.records().some((record) => record.source.includes("important")));
});

test("editor flushes pending edits on hide and close without extra unchanged saves", async () => {
  const app = editor();
  await app.ready();
  await app.edit("pending when hidden");
  app.document.visibilityState = "hidden";
  await app.document.dispatch("visibilitychange");
  assert.ok(app.records().some((record) => record.source === "pending when hidden"));
  const writes = app.local.writes.length;
  await app.window.dispatch("beforeunload");
  await app.flush();
  assert.equal(app.local.writes.length, writes);
  await app.edit("pending when closed");
  await app.window.dispatch("beforeunload");
  assert.ok(app.records().some((record) => record.source === "pending when closed"));
});

test("two editor tabs save their own changes after their shared starting point", async () => {
  const local = new MemoryStorage();
  seed(local, "shared original");
  const a = editor(local);
  const b = editor(local);
  await Promise.all([a.ready(), b.ready()]);
  await a.edit("tab A changes");
  await b.edit("tab B changes");
  await Promise.all([a.flush(), b.flush()]);
  assert.deepEqual(a.records().map((record) => record.source).sort(), ["shared original", "tab A changes", "tab B changes"]);
});

test("multiple drafts remain folded by default and recover only when explicitly selected", async () => {
  const local = new MemoryStorage();
  const first = seed(local, "first preview");
  seed(local, "second preview");
  const app = editor(local);
  await app.ready();
  assert.equal(app.elements.get("draft-picker").open, false);
  assert.equal(app.elements.get("filename").value, "merge_sort.algo");
  assert.equal(app.elements.get("draft-count").textContent, "2");
  await app.elements.get("drafts-button").click();
  assert.equal(app.elements.get("draft-picker").open, true);
  const before = [...local.data];
  await draftAction(app, "first preview", "Recover").click();
  assert.equal(app.elements.get("source").value, first.source);
  assert.equal(app.elements.get("filename").value, first.filename);
  assert.equal(app.elements.get("draft-picker").open, false);
  await app.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
  await app.edit("changed recovery");
  await app.flush();
  assert.equal(store(local).read(first.id).source, first.source);
  assert.equal(app.records().length, 3);
});

test("recovering the current draft flushes pending edits before reading its latest source", async () => {
  const app = editor();
  await app.ready();
  await app.edit("last saved content");
  await app.flush();
  const draft = app.records()[0];
  await app.edit("pending newer content");
  await draftAction(app, "last saved content", "Recover").click();
  assert.equal(app.elements.get("source").value, "pending newer content");
  assert.equal(store(app.local).read(draft.id).source, "pending newer content");
  assert.equal(app.records().length, 1);
  await app.flush();
  assert.equal(app.elements.get("source").value, "pending newer content");
});

test("reload ignores the preferred draft until recovery and duplicated tabs keep independent edits", async () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const original = seed(local, "my current draft", session);
  seed(local, "another document");
  assert.equal(session.getItem(SESSION_KEY), original.id);
  const reloaded = editor(local, session);
  const duplicate = editor(local, session.copy());
  await Promise.all([reloaded.ready(), duplicate.ready()]);
  for (const app of [reloaded, duplicate]) {
    assert.equal(app.elements.get("filename").value, "merge_sort.algo");
    assert.notEqual(app.elements.get("source").value, original.source);
    await draftAction(app, original.source, "Recover").click();
    assert.equal(app.elements.get("source").value, original.source);
  }
  await reloaded.edit("reloaded edit");
  await duplicate.edit("duplicate edit");
  await reloaded.flush();
  await duplicate.flush();
  assert.deepEqual(reloaded.records().map((record) => record.source).sort(),
    ["another document", "duplicate edit", "my current draft", "reloaded edit"]);
});

test("editor Discard removes the chosen copy and pending unchanged close does not recreate it", async () => {
  const app = editor();
  await app.ready();
  await app.edit("saved before discard");
  await app.flush();
  await app.edit("pending at discard");
  await draftAction(app, "saved before discard", "Discard").click();
  assert.equal(app.records().length, 0);
  assert.equal(app.elements.get("source").value, "pending at discard");
  const close = await app.window.dispatch("beforeunload");
  assert.equal(close.defaultPrevented, true);
  await app.flush();
  assert.equal(app.records().length, 0);
  await app.edit("new edit after discard");
  await app.flush();
  assert.equal(app.records()[0].source, "new edit after discard");
});

test("loading an example saves the pending document before switching to a fresh one", async () => {
  const app = editor();
  await app.ready();
  await app.edit("pending previous document");
  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  assert.equal(app.elements.get("filename").value, "other.algo");
  assert.ok(app.records().some((record) => record.source === "pending previous document"));
  await app.edit("new example changes");
  await app.flush();
  assert.deepEqual(app.records().map((record) => record.source).sort(),
    ["new example changes", "pending previous document"]);
});

test("cross-tab storage notifications refresh recovery choices without replacing editor text", async () => {
  const local = new MemoryStorage();
  const app = editor(local);
  await app.ready();
  await app.edit("local pending edit");
  const foreign = seed(local, "foreign edit");
  await app.window.dispatch("storage", { key: PREFIX + foreign.id, storageArea: local });
  assert.equal(app.elements.get("source").value, "local pending edit");
  assert.equal(app.elements.get("draft-count").textContent, "1");
  assert.ok(draftAction(app, "foreign edit", "Recover"));
});

test("a draft discarded in another tab stays deleted and warns before losing its unsaved text", async () => {
  const app = editor();
  await app.ready();
  await app.edit("unsaved text removed elsewhere");
  await app.flush();
  const draft = app.records()[0];
  store(app.local).remove(draft.id);
  await app.window.dispatch("storage", { key: PREFIX + draft.id, storageArea: app.local });
  const close = await app.window.dispatch("beforeunload");
  assert.equal(close.defaultPrevented, true);
  assert.equal(app.records().length, 0);
  let asked = false;
  app.window.confirm = () => { asked = true; return false; };
  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  assert.equal(asked, true);
  assert.equal(app.elements.get("source").value, draft.source);
  assert.equal(app.records().length, 0);
});

test("editing then undoing before debounce leaves no draft and no saving status", async () => {
  const app = editor();
  await app.ready();
  const initial = app.elements.get("source").value;
  await app.edit("temporary edit");
  await app.edit(initial);
  await app.flush();
  assert.equal(app.records().length, 0);
  assert.doesNotMatch(app.elements.get("draft-status").textContent, /Saving browser draft/);
  const close = await app.window.dispatch("beforeunload");
  assert.notEqual(close.defaultPrevented, true);
});

test("editor retains a legacy draft for explicit recovery and leaves it unchanged on close", async () => {
  const legacy = { ...snapshot("legacy unsaved source", "legacy.algo"), updatedAt: 42 };
  const local = new MemoryStorage([[LEGACY_KEY, JSON.stringify(legacy)]]);
  const app = editor(local);
  await app.ready();
  assert.equal(app.elements.get("filename").value, "merge_sort.algo");
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.elements.get("source").value, legacy.source);
  assert.equal(app.elements.get("filename").value, legacy.filename);
  assert.equal(local.getItem(LEGACY_KEY), null);
  assert.equal(app.records()[0].updatedAt, 42);
  const before = [...local.data];
  await app.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("editor quota failure during legacy migration still exposes the original source", async () => {
  const legacy = { ...snapshot("legacy source to rescue", "legacy.algo"), updatedAt: 42 };
  const raw = JSON.stringify(legacy);
  const local = new MemoryStorage([[LEGACY_KEY, raw]]);
  local.fail.add("write");
  const app = editor(local);
  await app.ready();
  assert.equal(app.elements.get("filename").value, "merge_sort.algo");
  assert.match(app.elements.get("draft-status").textContent, /could not be migrated/i);
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.elements.get("source").value, legacy.source);
  assert.equal(app.elements.get("filename").value, legacy.filename);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  await app.edit("edited while quota exceeded");
  const close = await app.window.dispatch("beforeunload");
  assert.equal(close.defaultPrevented, true);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  local.fail.clear();
  await app.window.dispatch("beforeunload");
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
  const close = await app.window.dispatch("beforeunload");
  assert.notEqual(close.defaultPrevented, true);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  app.window.confirm = () => assert.fail("The unchanged legacy backup should allow replacement without warning");
  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  assert.equal(app.elements.get("filename").value, "other.algo");
  assert.equal(local.getItem(LEGACY_KEY), raw);
});

test("legacy quota fallback stays accessible even when the session prefers a newer draft", async () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const preferred = seed(local, "preferred current source", session);
  const legacy = { ...snapshot("older legacy source", "legacy.algo"), updatedAt: 42 };
  const raw = JSON.stringify(legacy);
  local.setItem(LEGACY_KEY, raw);
  local.fail.add("write");
  const app = editor(local, session);
  await app.ready();
  assert.equal(app.elements.get("filename").value, "merge_sort.algo");
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.elements.get("source").value, legacy.source);
  assert.ok(draftAction(app, preferred.source, "Recover"));
  assert.equal(local.getItem(LEGACY_KEY), raw);
  assert.equal(store(local).read(preferred.id).source, preferred.source);
});

test("canceling document replacement after a failed draft save preserves current source", async () => {
  const app = editor();
  await app.ready();
  await app.edit("unsaved source that must remain");
  app.local.fail.add("write");
  app.window.confirm = () => false;
  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  assert.equal(app.elements.get("source").value, "unsaved source that must remain");
  assert.equal(app.elements.get("filename").value, "merge_sort.algo");
});

test("editor handles blocked browser storage and warns before closing unsaved work", async () => {
  const app = editor(undefined, undefined, { blockStorageAccess: true });
  await app.ready();
  assert.match(app.elements.get("draft-status").textContent, /unavailable|could not|cannot/i);
  await app.edit("keep me despite blocked storage");
  await app.flush();
  const close = await app.window.dispatch("beforeunload");
  assert.equal(close.defaultPrevented, true);
  assert.equal(app.elements.get("source").value, "keep me despite blocked storage");
});

test("analysis content, names, and save baselines independently trigger a paired snapshot", () => {
  const writer = store();
  let current = pairedSnapshot();
  writer.start(current);
  for (const [field, value] of [
    ["analysis", "-- edited proof"], ["analysisFilename", "Renamed.lean"],
    ["savedAnalysis", "-- edited proof"], ["savedAnalysisFilename", "Renamed.lean"],
  ]) {
    current = { ...current, [field]: value };
    assert.equal(writer.hasChanges(current), true, field);
    assert.equal(writer.write(current), true, field);
    const saved = writer.read(writer.activeId);
    for (const [key, expected] of Object.entries(current)) assert.equal(saved[key], expected, key);
    assert.equal(writer.write(current), false);
  }
});

test("source-only v2 records remain recoverable without changing their on-disk content", () => {
  const legacyV2 = { id: "older-v2", ...snapshot("old source"), updatedAt: 42 };
  const raw = JSON.stringify(legacyV2);
  const local = new MemoryStorage([[PREFIX + legacyV2.id, raw]]);
  const reader = store(local);
  const recovered = reader.read(legacyV2.id);
  assert.equal(recovered.source, "old source");
  assert.equal(recovered.analysis, undefined);
  assert.equal(recovered.savedAnalysis, undefined);
  reader.start(recovered, recovered.id);
  assert.equal(reader.write(recovered), false);
  assert.equal(local.getItem(PREFIX + legacyV2.id), raw);
  reader.write({ ...recovered, analysis: "-- new proof", analysisFilename: "Proof.lean" });
  assert.notEqual(reader.activeId, legacyV2.id);
  assert.equal(reader.read(reader.activeId).analysis, "-- new proof");
  assert.equal(local.getItem(PREFIX + legacyV2.id), raw);
});

test("migrating a paired legacy record preserves all analysis save state", () => {
  const legacy = { ...pairedSnapshot("legacy source", "-- unsaved proof", {
    filename: "Legacy.algo", analysisFilename: "LegacyProof.lean", savedAnalysis: "-- downloaded proof",
    savedAnalysisFilename: "Downloaded.lean",
  }), updatedAt: 42 };
  const local = new MemoryStorage([[LEGACY_KEY, JSON.stringify(legacy)]]);
  const migrated = store(local).migrateLegacy();
  for (const [key, expected] of Object.entries(legacy)) assert.equal(migrated[key], expected, key);
  assert.equal(local.getItem(LEGACY_KEY), null);
});

test("a failed paired write retains the last complete source-and-analysis snapshot", () => {
  const local = new MemoryStorage();
  const writer = store(local);
  writer.start(pairedSnapshot());
  writer.write(pairedSnapshot("persisted source", "-- persisted analysis"));
  const id = writer.activeId;
  const pending = pairedSnapshot("pending source", "-- pending analysis");
  local.fail.add("write");
  assert.throws(() => writer.write(pending), /unavailable/);
  assert.equal(writer.read(id).source, "persisted source");
  assert.equal(writer.read(id).analysis, "-- persisted analysis");
  assert.equal(writer.hasChanges(pending), true);
  local.fail.clear();
  writer.write(pending);
  assert.equal(writer.read(id).source, "pending source");
  assert.equal(writer.read(id).analysis, "-- pending analysis");
});

test("analysis-only edits in concurrent tabs preserve each complete document pair", async () => {
  const local = new MemoryStorage();
  const original = seedPair(local, pairedSnapshot("shared source", "-- shared proof"));
  const a = editor(local);
  const b = editor(local);
  await Promise.all([a.ready(), b.ready()]);
  for (const app of [a, b]) await draftAction(app, original.source, "Recover").click();
  assert.equal(a.elements.get("analysis").value, original.analysis);
  await a.editAnalysis("-- proof from A");
  await b.editAnalysis("-- proof from B");
  await a.flush();
  await b.flush();
  assert.deepEqual(a.records().map((record) => record.analysis).sort(),
    ["-- proof from A", "-- proof from B", "-- shared proof"]);
  assert.ok(a.records().every((record) => record.source === "shared source"));
  const before = [...local.data];
  await a.window.dispatch("beforeunload");
  await b.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("stale editor hide and unload cannot overwrite another tab's analysis-only edit", async () => {
  const local = new MemoryStorage();
  const old = seedPair(local, pairedSnapshot("same source", "-- old proof"));
  const stale = editor(local);
  const active = editor(local);
  await Promise.all([stale.ready(), active.ready()]);
  await active.editAnalysis("-- important new proof");
  active.document.visibilityState = "hidden";
  await active.document.dispatch("visibilitychange");
  const before = [...local.data];
  stale.document.visibilityState = "hidden";
  await stale.document.dispatch("visibilitychange");
  await stale.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
  assert.equal(store(local).read(old.id).analysis, "-- old proof");
  assert.ok(active.records().some((record) => record.analysis === "-- important new proof"));
});

test("recovery restores paired filenames and saved baselines without making clean files dirty", async () => {
  const local = new MemoryStorage();
  const original = seedPair(local, pairedSnapshot("clean source", "-- clean proof", {
    filename: "Clean.algo", savedSource: "clean source", savedFilename: "Clean.algo",
    analysisFilename: "CleanProof.lean", savedAnalysis: "-- clean proof", savedAnalysisFilename: "CleanProof.lean",
  }));
  seedPair(local, pairedSnapshot("second source", "-- second proof"));
  const app = editor(local);
  await app.ready();
  await draftAction(app, original.source, "Recover").click();
  assert.equal(app.elements.get("source").value, original.source);
  assert.equal(app.elements.get("filename").value, original.filename);
  assert.equal(app.elements.get("analysis").value, original.analysis);
  assert.equal(app.elements.get("analysis-filename").value, original.analysisFilename);
  assert.doesNotMatch(app.elements.get("save-state").textContent, /Unsaved/);
  assert.doesNotMatch(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  await app.editAnalysis("-- temporary edit");
  await app.editAnalysis(original.savedAnalysis);
  assert.doesNotMatch(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  const before = [...local.data];
  await app.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("reload and duplicated tabs fork analysis edits while preserving the original pair", async () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const original = seedPair(local, pairedSnapshot("reload source", "-- reload proof"), session);
  const reloaded = editor(local, session);
  const duplicate = editor(local, session.copy());
  await Promise.all([reloaded.ready(), duplicate.ready()]);
  for (const app of [reloaded, duplicate]) {
    assert.equal(app.elements.get("filename").value, "merge_sort.algo");
    await draftAction(app, original.source, "Recover").click();
    assert.equal(app.elements.get("source").value, original.source);
    assert.equal(app.elements.get("analysis").value, original.analysis);
  }
  await reloaded.editAnalysis("-- reloaded proof");
  await duplicate.editAnalysis("-- duplicate proof");
  await reloaded.flush();
  await duplicate.flush();
  assert.deepEqual(reloaded.records().map((record) => record.analysis).sort(),
    ["-- duplicate proof", "-- reload proof", "-- reloaded proof"]);
  assert.equal(store(local).read(original.id).analysis, original.analysis);
});

test("changing examples backs up pending analysis and loads the new matching proof", async () => {
  const app = editor();
  await app.ready();
  const priorSource = app.elements.get("source").value;
  await app.editAnalysis("-- pending proof of original source");
  await app.rename("analysis-filename", "OriginalProof.lean");
  app.window.confirm = () => assert.fail("A successful backup should permit replacement");
  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  const prior = app.records().find((record) => record.source === priorSource);
  assert.equal(prior.analysis, "-- pending proof of original source");
  assert.equal(prior.analysisFilename, "OriginalProof.lean");
  assert.equal(app.elements.get("filename").value, "other.algo");
  assert.match(app.elements.get("analysis").value, /import OtherGeneratedPoints/);
  assert.match(app.elements.get("analysis").value, /example proof/);
  await app.editAnalysis("-- edited other proof");
  await app.flush();
  assert.equal(store(app.local).read(prior.id).analysis, prior.analysis);
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
  assert.equal(app.elements.get("filename").value, "New.algo");
  assert.match(app.elements.get("analysis").value, /import NewGeneratedPoints/);
  assert.doesNotMatch(app.elements.get("analysis").value, /previous proof/);
});

test("opening a new analysis file forks the document pair and retains the prior analysis", async () => {
  const app = editor();
  await app.ready();
  await app.edit("algorithm kept across proofs");
  await app.editAnalysis("-- previous unsaved proof");
  await app.rename("analysis-filename", "Previous.lean");
  app.window.confirm = () => assert.fail("A successful backup should permit replacing analysis");
  await app.openFile("analysis-file-picker", "NewProof.lean", "-- new proof\r\n");
  const previous = app.records().find((record) => record.analysis === "-- previous unsaved proof");
  assert.ok(previous);
  assert.equal(previous.analysisFilename, "Previous.lean");
  assert.equal(app.elements.get("source").value, previous.source);
  assert.equal(app.elements.get("analysis").value, "-- new proof\n");
  assert.equal(app.elements.get("analysis-filename").value, "NewProof.lean");
  await app.editAnalysis("-- new proof edited");
  await app.flush();
  const current = app.records().find((record) => record.analysis === "-- new proof edited");
  assert.notEqual(current.id, previous.id);
  assert.equal(current.savedAnalysis, "-- new proof\n");
  assert.equal(current.savedAnalysisFilename, "NewProof.lean");
  assert.equal(store(app.local).read(previous.id).analysis, "-- previous unsaved proof");
});

test("canceling analysis replacement after quota failure retains text, names, and save baselines", async () => {
  const app = editor();
  await app.ready();
  const savedAnalysis = app.elements.get("analysis").value;
  await app.editAnalysis("-- irreplaceable unsaved proof");
  await app.rename("analysis-filename", "Keep.lean");
  app.local.fail.add("write");
  let asked = 0;
  app.window.confirm = () => { asked += 1; return false; };
  await app.openFile("analysis-file-picker", "Replacement.lean", "-- replacement");
  assert.equal(asked, 1);
  assert.equal(app.elements.get("analysis").value, "-- irreplaceable unsaved proof");
  assert.equal(app.elements.get("analysis-filename").value, "Keep.lean");
  assert.match(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  const close = await app.window.dispatch("beforeunload");
  assert.equal(close.defaultPrevented, true);
  app.local.fail.clear();
  await app.window.dispatch("beforeunload");
  const current = app.records().find((record) => record.analysis === "-- irreplaceable unsaved proof");
  assert.equal(current.savedAnalysis, savedAnalysis);
  assert.equal(current.savedAnalysisFilename, "Analysis.lean");
});

test("analysis-only quota failure warns before closing and retries the complete pair", async () => {
  const app = editor();
  await app.ready();
  const source = app.elements.get("source").value;
  app.local.fail.add("write");
  await app.editAnalysis("-- only analysis has unsaved changes");
  await app.flush();
  assert.match(app.elements.get("draft-status").textContent, /could not|cannot|unavailable/i);
  const close = await app.window.dispatch("beforeunload");
  assert.equal(close.defaultPrevented, true);
  app.local.fail.clear();
  await app.window.dispatch("beforeunload");
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
  assert.equal(app.elements.get("filename").value, "merge_sort.algo");
  await draftAction(app, legacy.source, "Recover").click();
  assert.equal(app.elements.get("source").value, legacy.source);
  assert.equal(app.elements.get("analysis").value, legacy.analysis);
  assert.equal(app.elements.get("analysis-filename").value, legacy.analysisFilename);
  assert.equal((await app.window.dispatch("beforeunload")).defaultPrevented, undefined);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  await app.editAnalysis("-- updated legacy proof");
  assert.equal((await app.window.dispatch("beforeunload")).defaultPrevented, true);
  local.fail.clear();
  await app.window.dispatch("beforeunload");
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
  const source = app.elements.get("source").value;
  await app.editAnalysis("-- deleted elsewhere");
  await app.flush();
  const saved = app.records()[0];
  store(app.local).remove(saved.id);
  await app.window.dispatch("storage", { key: PREFIX + saved.id, storageArea: app.local });
  assert.equal((await app.window.dispatch("beforeunload")).defaultPrevented, true);
  assert.equal(app.records().length, 0);
  assert.equal(app.elements.get("source").value, source);
  assert.equal(app.elements.get("analysis").value, "-- deleted elsewhere");
});

test("compilation keeps algorithm and Points outputs separate and excludes generated text from drafts", async () => {
  const app = editor();
  await app.ready();
  assert.match(app.elements.get("lean-code").innerHTML, /test/);
  assert.match(app.elements.get("points-code").innerHTML, /named-line interface/);
  assert.equal(app.elements.get("points-output").hidden, false);
  await app.editAnalysis("-- user-owned proof");
  await app.flush();
  assert.equal(app.records()[0].analysis, "-- user-owned proof");
  const raw = JSON.parse(app.local.getItem(PREFIX + app.records()[0].id));
  assert.equal(Object.values(raw).some((value) => value === "-- named-line interface"), false);
  assert.equal(Object.values(raw).some((value) => value === "def test := 1"), false);
});

test("old source-only recovery reconstructs a starter without changing the saved draft", async () => {
  const local = new MemoryStorage();
  const original = seed(local, "old source still recoverable");
  const before = [...local.data];
  const app = editor(local);
  await app.ready();
  await draftAction(app, original.source, "Recover").click();
  assert.equal(app.elements.get("source").value, original.source);
  assert.match(app.elements.get("analysis").value, /import ExampleGeneratedPoints/);
  assert.equal(app.elements.get("analysis-filename").value, "Analysis.lean");
  assert.doesNotMatch(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  assert.notEqual((await app.window.dispatch("beforeunload")).defaultPrevented, true);
  assert.deepEqual([...local.data], before);
});

test("an intentionally empty analysis is recovered as empty rather than replaced by a starter", async () => {
  const local = new MemoryStorage();
  const original = seedPair(local, pairedSnapshot("source with empty proof", "", {
    savedAnalysis: "", analysisFilename: "Empty.lean", savedAnalysisFilename: "Empty.lean",
  }));
  const before = [...local.data];
  const app = editor(local);
  await app.ready();
  await draftAction(app, original.source, "Recover").click();
  assert.equal(app.elements.get("source").value, original.source);
  assert.equal(app.elements.get("analysis").value, "");
  assert.equal(app.elements.get("analysis-filename").value, "Empty.lean");
  assert.doesNotMatch(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  await app.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("saving each file updates only its own baseline in the paired draft", async () => {
  const app = editor();
  await app.ready();
  const initialAnalysis = app.elements.get("analysis").value;
  await app.edit("unsaved algorithm");
  await app.editAnalysis("-- unsaved proof");
  await app.rename("analysis-filename", "MyProof.lean");
  await app.elements.get("save-button").click();
  const sourceSaved = app.records()[0];
  assert.equal(sourceSaved.savedSource, "unsaved algorithm");
  assert.equal(sourceSaved.analysis, "-- unsaved proof");
  assert.equal(sourceSaved.savedAnalysis, initialAnalysis);
  assert.match(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  await app.elements.get("analysis-save-button").click();
  const bothSaved = app.records()[0];
  assert.equal(bothSaved.savedSource, "unsaved algorithm");
  assert.equal(bothSaved.savedAnalysis, "-- unsaved proof");
  assert.equal(bothSaved.savedAnalysisFilename, "MyProof.lean");
  assert.doesNotMatch(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  assert.doesNotMatch(app.elements.get("save-state").textContent, /Unsaved/);
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  await draftAction(reloaded, "unsaved algorithm", "Recover").click();
  assert.equal(reloaded.elements.get("source").value, "unsaved algorithm");
  assert.equal(reloaded.elements.get("analysis").value, "-- unsaved proof");
  assert.equal(reloaded.elements.get("analysis-filename").value, "MyProof.lean");
  assert.doesNotMatch(reloaded.elements.get("analysis-save-state").textContent, /Unsaved/);
  assert.doesNotMatch(reloaded.elements.get("save-state").textContent, /Unsaved/);
  await app.flush();
});

test("Save analysis packages the latest standalone source and proof while preserving the Lean filename", async () => {
  const app = editor();
  await app.ready();
  const originalSource = app.elements.get("source").value;
  const latestSource = "def work() -> Int:\n    return 7\n";
  const latestProof = "import WorkGeneratedPoints\n-- latest handwritten proof\n";
  await app.rename("filename", "work.algo");
  await app.edit(latestSource);
  await app.rename("analysis-filename", "WorkProof.lean");
  await app.editAnalysis(latestProof);
  await app.elements.get("analysis-save-button").click();
  const exported = app.requests.filter(({ url }) => url === "/api/analysis-export").at(-1);
  assert.equal(exported.request.method, "POST");
  assert.equal(exported.request.headers["Content-Type"], "application/json");
  assert.equal(exported.request.headers["X-Algo2Lean-Project"], undefined);
  assert.deepEqual(exported.body, { source: latestSource, filename: "work.algo",
    analysis: latestProof, analysis_filename: "WorkProof.lean" });
  assert.deepEqual(app.downloads.map(({ name }) => name), ["WorkProof.zip"]);
  assert.equal((await fetch(app.downloads[0].href)).headers.get("Content-Type"), "application/zip");
  assert.equal(app.elements.get("analysis-filename").value, "WorkProof.lean");
  assert.equal(app.elements.get("analysis-save-state").textContent, "Downloaded");
  assert.match(app.elements.get("save-state").textContent, /Unsaved/);
  assert.equal(app.records()[0].savedSource, originalSource);
  assert.equal(app.records()[0].savedAnalysis, latestProof);
  assert.equal(app.records()[0].savedAnalysisFilename, "WorkProof.lean");
  assert.match(app.elements.get("analysis-file-message").textContent, /shared Lean libraries and all resolved imports/);
  assert.match(app.elements.get("analysis-file-message").textContent, /Downloading does not check the proof/);
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
    const savedProof = app.elements.get("analysis").value;
    await app.editAnalysis("-- unsaved proof to keep");
    await app.rename("analysis-filename", "Pending.lean");
    await app.elements.get("analysis-save-button").click();
    await app.flush();
    assert.equal(app.downloads.length, 0);
    assert.match(app.elements.get("analysis-save-state").textContent, /Unsaved/);
    assert.match(app.elements.get("analysis-file-message").textContent, failure.message);
    assert.equal(app.elements.get("analysis-save-button").disabled, false);
    assert.equal(app.elements.get("analysis-save-button").textContent, "Save analysis");
    assert.equal(app.elements.get("analysis-filename").value, "Pending.lean");
    assert.equal(app.records()[0].savedAnalysis, savedProof);
    assert.equal(app.records()[0].savedAnalysisFilename, "Analysis.lean");
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
    const savedProof = app.elements.get("analysis").value;
    await app.editAnalysis("-- proof before pending download");
    const pending = app.elements.get("analysis-save-button").click();
    await app.ready();
    assert.equal(app.elements.get("analysis-save-button").disabled, true, description);
    await change(app);
    const currentSource = app.elements.get("source").value;
    const currentProof = app.elements.get("analysis").value;
    const currentName = app.elements.get("analysis-filename").value;
    finishArchive(new Blob(["old archive"], { type: "application/zip" }));
    await pending;
    await app.flush();
    assert.equal(app.downloads.length, 0, description);
    assert.equal(app.elements.get("source").value, currentSource, description);
    assert.equal(app.elements.get("analysis").value, currentProof, description);
    assert.equal(app.elements.get("analysis-filename").value, currentName, description);
    assert.match(app.elements.get("analysis-save-state").textContent, /Unsaved/, description);
    assert.match(app.elements.get("analysis-file-message").textContent, /workspace changed/i, description);
    assert.equal(app.elements.get("analysis-save-button").disabled, false, description);
    assert.equal(app.records()[0].savedAnalysis, savedProof, description);
  }
});

test("cross-tab notifications expose the paired recovery choice without replacing pending analysis", async () => {
  const app = editor();
  await app.ready();
  const source = app.elements.get("source").value;
  await app.editAnalysis("-- local pending proof");
  const foreign = seedPair(app.local, pairedSnapshot("foreign algorithm", "-- foreign proof", {
    analysisFilename: "Foreign.lean",
  }));
  await app.window.dispatch("storage", { key: PREFIX + foreign.id, storageArea: app.local });
  assert.equal(app.elements.get("source").value, source);
  assert.equal(app.elements.get("analysis").value, "-- local pending proof");
  const card = app.elements.get("draft-list").children.find((candidate) =>
    descendants(candidate).some((element) => element.tagName === "PRE" && element.textContent === foreign.source));
  assert.ok(card);
  assert.ok(descendants(card).some((element) => element.textContent === foreign.analysis));
  assert.ok(descendants(card).some((element) => /Foreign\.lean/.test(element.textContent)));
  await draftAction(app, foreign.source, "Recover").click();
  assert.equal(app.elements.get("source").value, foreign.source);
  assert.equal(app.elements.get("analysis").value, foreign.analysis);
  assert.equal(app.elements.get("analysis-filename").value, "Foreign.lean");
  assert.ok(app.records().some((record) => record.source === source && record.analysis === "-- local pending proof"));
});

test("renaming the analysis while either file is being read cancels the stale replacement", async () => {
  for (const [pickerId, name, messageId] of [
    ["file-picker", "Replacement.algo", "file-message"],
    ["analysis-file-picker", "Replacement.lean", "analysis-file-message"],
  ]) {
    const app = editor();
    await app.ready();
    const source = app.elements.get("source").value;
    const analysis = app.elements.get("analysis").value;
    let finishRead;
    const fileRead = new Promise((resolve) => { finishRead = resolve; });
    const picker = app.elements.get(pickerId);
    picker.files = [{ name, size: 12, text: () => fileRead }];
    const opening = picker.dispatch("change");
    await app.rename("analysis-filename", "KeepNewestName.lean");
    finishRead("replacement text");
    await opening;
    assert.equal(app.elements.get("source").value, source, pickerId);
    assert.equal(app.elements.get("analysis").value, analysis, pickerId);
    assert.equal(app.elements.get("analysis-filename").value, "KeepNewestName.lean", pickerId);
    assert.match(app.elements.get(messageId).textContent, /workspace changed/i, pickerId);
  }
});

const PROJECT_PREFIX = "algo2lean.editor.project.v1.";
const PROJECT_SESSION = "algo2lean.editor.active-project.v1";
const PROJECT_SOURCE = "from library import increment\ndef run(x: Int) -> Int:\n    return increment(x)\n";
const PROJECT_LIBRARY = "def increment(x: Int) -> Int:\n    return x + 1\n";

function projectRecords(app) {
  return [...app.local.data].filter(([key]) => key.startsWith(PROJECT_PREFIX)).map(([, value]) => JSON.parse(value));
}

async function openProject(app, name = "sample", files = { "main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY }) {
  await app.elements.get("open-project-button").click();
  const picker = app.elements.get("project-picker");
  picker.files = Object.entries(files).map(([path, text]) => ({ name: path.split("/").pop(), webkitRelativePath: name + "/" + path, size: text.length, text: async () => text }));
  await picker.dispatch("change");
  await app.ready();
}

async function selectModule(app, path) {
  app.elements.get("project-module").value = path;
  await app.elements.get("project-module").dispatch("change");
  await app.ready();
}

async function createFile(app, name) {
  await app.elements.get("new-file-button").click();
  if (name !== undefined) app.elements.get("new-file-name").value = name;
  await app.elements.get("new-file-form").dispatch("submit");
  await app.ready();
}

test("New file preserves the previous source and proof and creates an independent standalone draft", async () => {
  const app = editor();
  await app.ready();
  await app.edit("pending original algorithm");
  await app.editAnalysis("-- pending original proof");
  const compileRequests = app.requests.filter(({ url }) => url === "/api/compile").length;
  await createFile(app, "fresh");
  assert.equal(app.elements.get("filename").value, "fresh.algo");
  assert.equal(app.elements.get("source").value, "");
  assert.match(app.elements.get("analysis").value, /^import FreshGenerated\n/);
  assert.equal(app.elements.get("new-file-form").hidden, true);
  assert.equal(app.elements.get("new-file-button").getAttribute("aria-expanded"), "false");
  assert.equal(app.requests.filter(({ url }) => url === "/api/compile").length, compileRequests);
  const original = app.records().find((record) => record.source === "pending original algorithm");
  const fresh = app.records().find((record) => record.filename === "fresh.algo");
  assert.equal(original.analysis, "-- pending original proof");
  assert.equal(fresh.source, "");
  assert.notEqual(original.id, fresh.id);
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  assert.equal(reloaded.elements.get("filename").value, "merge_sort.algo");
  await draftAction(reloaded, "(Empty source)", "Recover").click();
  assert.equal(reloaded.elements.get("filename").value, "fresh.algo");
  assert.equal(reloaded.elements.get("source").value, "");
});

test("New file defaults avoid existing drafts and Cancel or Escape leave the workspace unchanged", async () => {
  const app = editor();
  await app.ready();
  await createFile(app);
  assert.equal(app.elements.get("filename").value, "untitled.algo");
  const before = [...app.local.data];
  await app.elements.get("new-file-button").click();
  assert.equal(app.elements.get("new-file-name").value, "untitled_2.algo");
  await app.elements.get("cancel-new-file-button").click();
  assert.equal(app.elements.get("new-file-form").hidden, true);
  assert.deepEqual([...app.local.data], before);
  await app.elements.get("new-file-button").click();
  await app.elements.get("new-file-form").dispatch("keydown", { key: "Escape" });
  assert.equal(app.elements.get("new-file-form").hidden, true);
  assert.equal(app.elements.get("filename").value, "untitled.algo");
  assert.deepEqual([...app.local.data], before);
});

test("New file refuses to replace an unbacked-up standalone source and proof", async () => {
  const app = editor();
  await app.ready();
  await app.edit("keep algorithm");
  await app.editAnalysis("keep proof");
  app.local.fail.add("write");
  app.window.confirm = () => { throw new Error("New file should report the backup failure inline"); };
  await createFile(app, "fresh.algo");
  assert.equal(app.elements.get("source").value, "keep algorithm");
  assert.equal(app.elements.get("analysis").value, "keep proof");
  assert.equal(app.elements.get("new-file-form").hidden, false);
  assert.match(app.elements.get("new-file-help").textContent, /could not be backed up/);
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
  await app.elements.get("new-file-button").click();
  assert.equal(app.elements.get("new-file-name").value, "helpers/untitled.algo");
  app.elements.get("new-file-name").value = "helpers/search.algo";
  await app.elements.get("new-file-form").dispatch("submit");
  assert.equal(app.elements.get("filename").value, "helpers/search.algo");
  assert.equal(app.elements.get("source").value, "");
  assert.equal(app.elements.get("analysis-filename").value, "analysis/helpers/search.lean");
  assert.match(app.elements.get("analysis").value, /^import Algo.helpers.search.Generated\n/);
  await app.edit("def search() -> Int:\n    return 1\n");
  await app.elements.get("project-export-button").click();
  const payload = app.requests.filter(({ url }) => url === "/api/project-export").at(-1).body;
  assert.equal(payload.project_sources["helpers/search.algo"], "def search() -> Int:\n    return 1\n");
  assert.equal(payload.project_sources["main.algo"], "pending main");
  assert.equal(payload.project_sources["helpers/library.algo"], "pending library");
  assert.equal(payload.project_analyses["Algo.main.Analysis"], "-- pending main proof");
  assert.equal(payload.project_analyses["Algo.helpers.library.Analysis"], "-- pending library proof");
  assert.equal(payload.project_analyses["Algo.support.facts.Analysis"], "-- reusable support proof");
  await selectModule(app, "helpers/library.algo");
  assert.equal(app.elements.get("source").value, "pending library");
  assert.equal(app.elements.get("analysis").value, "-- pending library proof");
});

test("New project files reject invalid paths, duplicate sources, proof collisions, and inconsistent folder case", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", {
    "pkg/main.algo": PROJECT_LIBRARY, "analysis/support/facts.lean": "-- support proof",
  });
  const before = app.elements.get("source").value;
  for (const name of ["", "../new.algo", "/new.algo", "bad-name.algo", "pkg//new.algo", "pkg/main.algo",
    "Pkg/new.algo", "support/facts.algo", "Support/new.algo", "_a2l_groups/new.algo", "2wrong.algo"]) {
    await createFile(app, name);
    assert.equal(app.elements.get("new-file-form").hidden, false, name);
    assert.equal(app.elements.get("new-file-name").getAttribute("aria-invalid"), "true", name);
    assert.equal(app.elements.get("source").value, before, name);
    assert.equal(app.elements.get("filename").value, "pkg/main.algo", name);
  }
  await createFile(app, "new_folder/new.algo");
  assert.equal(app.elements.get("filename").value, "new_folder/new.algo");
  assert.equal(app.elements.get("new-file-form").hidden, true);
});

test("New standalone files reject folder paths and unsafe names without replacing the current file", async () => {
  const app = editor();
  await app.ready();
  for (const name of ["nested/new.algo", "../new.algo", "new file.algo", "", "_a2l_groups.algo"]) {
    await createFile(app, name);
    assert.equal(app.elements.get("filename").value, "merge_sort.algo");
    assert.equal(app.elements.get("new-file-form").hidden, false);
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
    assert.equal(app.elements.get("filename").value, "main.algo");
    assert.match(app.elements.get("new-file-help").textContent, /at most 256/);
  }
});

test("project file selection groups paths by folder and retains full path values", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", {
    "main.algo": PROJECT_LIBRARY, "sorting/main.algo": PROJECT_LIBRARY,
    "sorting/merge.algo": PROJECT_LIBRARY, "searching/main.algo": PROJECT_LIBRARY,
  });
  const groups = app.elements.get("project-module").children;
  assert.deepEqual(groups.map((group) => group.label), ["Project root", "searching/", "sorting/"]);
  assert.ok(groups.every((group) => group.tagName === "OPTGROUP"));
  assert.deepEqual(groups[2].children.map((option) => [option.textContent, option.value]), [
    ["main.algo", "sorting/main.algo"], ["merge.algo", "sorting/merge.algo"],
  ]);
  await selectModule(app, "sorting/main.algo");
  assert.equal(app.elements.get("filename").value, "sorting/main.algo");
});

test("project folder selection sends relative sources and canonical companion proof modules", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "sample", { "main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY,
    "analysis/library.lean": "import Algo.library.Generated\n-- saved library proof\n" });
  assert.equal(app.elements.get("project-toolbar").hidden, false);
  assert.equal(app.elements.get("project-name").textContent, "sample");
  assert.equal(app.elements.get("filename").value, "main.algo");
  assert.equal(app.elements.get("filename").readOnly, true);
  const request = app.requests.filter(({ url }) => url === "/api/compile").at(-1);
  assert.equal(request.request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(request.body.project_sources["library.algo"], PROJECT_LIBRARY);
  assert.equal(request.body.project_analyses["Algo.library.Analysis"], "import Algo.library.Generated\n-- saved library proof\n");
  assert.match(app.elements.get("analysis").value, /^import Algo.main.Generated\nimport Algo.main.Points\nimport Algo.main.Facts/);
  assert.match(app.elements.get("analysis").value, /open «Algo».«main» «Algo».«main».Algo2LeanGenerated/);
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
  assert.equal(app.elements.get("source").value, "main edit");
  assert.equal(app.elements.get("analysis").value, "main proof edit");
  await app.elements.get("analyze-button").click();
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
  await app.elements.get("close-project-button").click();
  assert.equal(app.elements.get("project-toolbar").hidden, true);
  assert.equal(app.elements.get("source").value, "unsaved standalone");
  assert.equal(app.elements.get("analysis").value, "unsaved standalone proof");
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
  const example = currentMergeSortExample();
  const options = exampleCatalog(example);
  const a = editor(local, session, options), b = editor(local, session.copy(), options);
  await Promise.all([a.ready(), b.ready()]);
  for (const app of [a, b]) {
    assert.equal(app.elements.get("filename").value, "merge_sort.algo");
    assert.equal(app.elements.get("source").value, example.source);
    assert.equal(app.elements.get("analysis").value, example.analysis);
    assert.equal(app.elements.get("project-toolbar").hidden, true);
    assert.equal(app.elements.get("draft-picker").open, false);
    await descendants(app.elements.get("draft-list"))
      .find((node) => node.tagName === "BUTTON" && node.textContent === "Recover project").click();
  }
  assert.equal(a.elements.get("source").value, "saved project source");
  assert.equal(b.elements.get("analysis").value, "saved project proof");
  const before = [...local.data];
  await a.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
  await a.edit("tab A project");
  await b.editAnalysis("tab B proof");
  await a.flush();
  await b.flush();
  const records = projectRecords(a);
  assert.equal(records.length, 3);
  assert.equal(records.find((record) => record.id === saved.id).data.files["main.algo"].source, "saved project source");
  await a.elements.get("close-project-button").click();
  await a.ready();
  assert.equal(a.elements.get("filename").value, "merge_sort.algo");
  assert.match(a.elements.get("source").value, /def merge_sort\(a: Seq, lo: Int, hi: Int\)/);
  assert.equal(a.elements.get("analysis-module").textContent, "MergeSortGenerated");
});

test("a dirty inactive project module is protected when browser storage fails", async () => {
  const app = editor();
  await app.ready();
  await openProject(app);
  app.local.fail.add("write");
  await app.edit("unsaved main module");
  await selectModule(app, "library.algo");
  const closing = await app.window.dispatch("beforeunload");
  assert.equal(closing.defaultPrevented, true);
  app.window.confirm = () => false;
  await app.elements.get("close-project-button").click();
  assert.equal(app.elements.get("project-toolbar").hidden, false);
  await selectModule(app, "main.algo");
  assert.equal(app.elements.get("source").value, "unsaved main module");
});

test("project source and analysis package downloads keep their module paths intact", async () => {
  const app = editor();
  await app.ready();
  await openProject(app, "nested", { "pkg/item.algo": PROJECT_LIBRARY, "analysis/pkg/item.lean": "-- proof" });
  await app.elements.get("save-button").click();
  await app.elements.get("analysis-save-button").click();
  assert.equal(app.elements.get("filename").value, "pkg/item.algo");
  assert.equal(app.elements.get("analysis-filename").value, "analysis/pkg/item.lean");
  assert.deepEqual(app.downloads.map(({ name }) => name), ["item.algo", "item.zip"]);
  await app.elements.get("compile-button").click();
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
  await app.elements.get("analysis-save-button").click();
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
  assert.equal(app.elements.get("analysis-filename").value, "analysis/pkg/item.lean");
  assert.equal(app.elements.get("analysis-pane-filename").textContent, "analysis/pkg/item.lean");
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
  const pending = app.elements.get("analysis-save-button").click();
  await app.ready();
  await selectModule(app, "library.algo");
  await app.editAnalysis("-- pending library proof");
  finishResponse(archiveResponse("old main archive"));
  await pending;
  await app.flush();
  assert.equal(app.downloads.length, 0);
  assert.equal(app.elements.get("filename").value, "library.algo");
  assert.equal(app.elements.get("analysis").value, "-- pending library proof");
  assert.match(app.elements.get("analysis-save-state").textContent, /Unsaved/);
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
  const pending = app.elements.get("analysis-save-button").click();
  await app.ready();
  await openProject(app, "second", { "main.algo": PROJECT_LIBRARY, "analysis/main.lean": "-- second saved proof" });
  await app.editAnalysis("-- pending second proof");
  const currentMessage = app.elements.get("analysis-file-message").textContent;
  finishArchive(new Blob(["first archive"], { type: "application/zip" }));
  await pending;
  await app.flush();
  assert.equal(app.downloads.length, 0);
  assert.equal(app.elements.get("project-name").textContent, "second");
  assert.equal(app.elements.get("analysis").value, "-- pending second proof");
  assert.equal(app.elements.get("analysis-file-message").textContent, currentMessage);
  assert.match(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  assert.equal(app.elements.get("analysis-save-button").disabled, false);
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
  const filenames = () => ["source", "lean", "points", "analysis"]
    .map((pane) => app.elements.get(pane + "-pane-filename").textContent);
  assert.deepEqual(filenames(), ["main.algo", "Algo/main/Generated.lean", "Algo/main/Points.lean", "analysis/main.lean"]);
  await selectModule(app, "pkg/item.algo");
  assert.deepEqual(filenames(), ["pkg/item.algo", "Algo/pkg/item/Generated.lean", "Algo/pkg/item/Points.lean", "analysis/pkg/item.lean"]);
  await selectModule(app, "main.algo");
  assert.deepEqual(filenames(), ["main.algo", "Algo/main/Generated.lean", "Algo/main/Points.lean", "analysis/main.lean"]);
  await app.elements.get("close-project-button").click();
  await app.ready();
  assert.deepEqual(filenames(), ["merge_sort.algo", "MergeSortGenerated.lean", "MergeSortGeneratedPoints.lean", "Analysis.lean"]);
});

test("project archive downloads include pending source and proof edits", async () => {
  const app = editor();
  await app.ready();
  await openProject(app);
  await app.edit("latest source");
  await app.editAnalysis("latest proof");
  await app.elements.get("project-export-button").click();
  const request = app.requests.filter(({ url }) => url === "/api/project-export").at(-1);
  assert.equal(request.request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(request.body.project_sources["main.algo"], "latest source");
  assert.equal(request.body.project_analyses["Algo.main.Analysis"], "latest proof");
  assert.equal(app.downloads.at(-1).name, "Algo2Lean-project.zip");
});

test("folder read races leave newer standalone edits untouched", async () => {
  const app = editor();
  await app.ready();
  await app.elements.get("open-project-button").click();
  let finish;
  const picker = app.elements.get("project-picker");
  picker.files = [{ name: "main.algo", webkitRelativePath: "sample/main.algo", size: 3,
    text: () => new Promise((resolve) => { finish = resolve; }) }];
  const opening = picker.dispatch("change");
  await app.edit("newer source");
  finish("old source");
  await opening;
  assert.equal(app.elements.get("source").value, "newer source");
  assert.equal(app.elements.get("project-toolbar").hidden, true);
  assert.match(app.elements.get("file-message").textContent, /workspace changed/);
});

test("ambiguous companions, case collisions, and oversized projects leave the editor unchanged", async () => {
  const app = editor();
  await app.ready();
  const original = app.elements.get("source").value;
  for (const files of [
    { "main.algo": PROJECT_SOURCE, "main.lean": "one proof", "analysis/main.lean": "another proof" },
    { "pkg/a.algo": PROJECT_LIBRARY, "Pkg/b.algo": PROJECT_LIBRARY },
    { "main.algo": "x".repeat(256 * 1024 + 1) },
    { ["long".repeat(63) + ".algo"]: PROJECT_LIBRARY },
    { "main.algo": PROJECT_LIBRARY, ...Object.fromEntries(Array.from({ length: 256 }, (_, index) => [`analysis/proof_${index}.lean`, "-- companion"])) },
  ]) {
    await openProject(app, "bad", files);
    assert.equal(app.elements.get("source").value, original);
    assert.equal(app.elements.get("project-toolbar").hidden, true);
    assert.match(app.elements.get("file-message").textContent, /Could not open the project/);
  }
});

test("native directory picker cancellation preserves the workspace without an error", async () => {
  const app = editor();
  await app.ready();
  const before = app.elements.get("source").value;
  app.window.showDirectoryPicker = async () => { const error = new Error("canceled"); error.name = "AbortError"; throw error; };
  await app.elements.get("open-project-button").click();
  assert.equal(app.elements.get("source").value, before);
  assert.equal(app.elements.get("open-project-button").disabled, false);
  assert.doesNotMatch(app.elements.get("file-message").textContent, /Could not open/);
});

test("native folder picker reads only files below the explicitly selected directory", async () => {
  const app = editor();
  await app.ready();
  let options;
  app.window.showDirectoryPicker = async (value) => {
    options = value;
    return { name: "native", async *values() {
      yield { kind: "file", name: "main.algo", getFile: async () => ({ size: 10, text: async () => PROJECT_LIBRARY }) };
      yield { kind: "directory", name: ".git", values: () => { throw new Error("Hidden folder read"); } };
    } };
  };
  await app.elements.get("open-project-button").click();
  await app.ready();
  assert.equal(options.mode, "read");
  assert.equal(app.elements.get("project-name").textContent, "native");
  assert.equal(app.elements.get("source").value, PROJECT_LIBRARY);
});

const PROJECT_EXAMPLE = { name: "Dijkstra", project_id: "dijkstra", folder: "dijkstra",
  filename: "client/main.algo", source: PROJECT_SOURCE };
const PROJECT_BUNDLE = { name: "Dijkstra example", entry: "client/main.algo",
  sources: { "client/main.algo": PROJECT_SOURCE, "library.algo": PROJECT_LIBRARY },
  analyses: { "Algo.client.main.Analysis": "import Algo.library.Analysis\n-- final proof\n",
    "Algo.library.Analysis": "import Algo.library.Generated\n-- reusable proof\n" } };

function projectExampleResponse(url) {
  if (url === "/api/examples") return { ok: true, json: async () => ({ examples: [PROJECT_EXAMPLE] }) };
  if (url === "/api/example-project/dijkstra") return { ok: true, json: async () => PROJECT_BUNDLE };
}

async function chooseProjectExample(app) {
  const selector = app.elements.get("examples");
  selector.value = "0";
  await selector.dispatch("change");
  await app.ready();
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
  const groups = app.elements.get("examples").children;
  assert.deepEqual(groups.map((group) => group.label), ["Project folders", "Single files"]);
  assert.deepEqual(groups[0].children.map((option) => [option.value, option.textContent]), [
    ["1", "Dijkstra · dijkstra/"], ["2", "Reusable algorithms · modules/"],
  ]);
  assert.equal(groups[1].children[0].value, "0");
  app.elements.get("examples").value = "1";
  await app.elements.get("examples").dispatch("change");
  assert.equal(app.elements.get("project-name").textContent, "Dijkstra example");
});

test("creating a file cancels replacement by a late project-example download", async () => {
  let finish;
  const pending = new Promise((resolve) => { finish = resolve; });
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/example-project/dijkstra") return pending;
    return projectExampleResponse(url);
  } });
  await app.ready();
  const opening = chooseProjectExample(app);
  await app.ready();
  await createFile(app, "my_new_file.algo");
  finish({ ok: true, json: async () => PROJECT_BUNDLE });
  await opening;
  assert.equal(app.elements.get("filename").value, "my_new_file.algo");
  assert.equal(app.elements.get("project-toolbar").hidden, true);
  assert.equal(app.elements.get("source").value, "");
});

test("hosted projects can add files and send them to the browser compiler", async () => {
  const app = editor(undefined, undefined, { hosted: true, fetch: projectExampleResponse });
  await app.ready();
  await chooseProjectExample(app);
  await createFile(app, "client/extra.algo");
  await app.edit("def answer() -> Int:\n    return 42\n");
  await app.elements.get("compile-button").click();
  const request = app.requests.filter(({ url }) => url === "/api/compile").at(-1);
  assert.equal(request.body.filename, "client/extra.algo");
  assert.equal(request.body.project_sources["client/extra.algo"], "def answer() -> Int:\n    return 42\n");
  assert.equal(request.body.project_sources["library.algo"], PROJECT_LIBRARY);
});

test("outdated project server is detected before compile, check, analysis, or export and retry recovers", async () => {
  let updated = false;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/capabilities") return { ok: updated, status: updated ? 200 : 404,
      json: async () => ({ project_protocol: 1 }) };
  } });
  await app.ready();
  await openProject(app);
  assert.match(app.elements.get("diagnostics").children[0].children[0].textContent, /server is older.*Restart|server is older.*Stop/s);
  for (const button of ["compile-button", "check-button", "analyze-button", "project-export-button"]) {
    await app.elements.get(button).click();
  }
  assert.equal(app.requests.filter(({ request }) => request?.headers?.["X-Algo2Lean-Project"]).length, 0);
  assert.equal(app.elements.get("source").value, PROJECT_SOURCE);
  assert.equal(projectRecords(app).at(-1).data.files["library.algo"].source, PROJECT_LIBRARY);
  updated = true;
  await app.elements.get("compile-button").click();
  assert.equal(app.requests.at(-1).url, "/api/compile");
  assert.equal(app.requests.at(-1).request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(app.elements.get("lean-code").innerHTML.includes("test"), true);
});

test("bundled import example opens its complete project and keeps the previous draft", async () => {
  const app = editor(undefined, undefined, { fetch: projectExampleResponse });
  await app.ready();
  await app.edit("my existing source");
  await app.editAnalysis("my existing proof");
  await chooseProjectExample(app);
  assert.equal(app.elements.get("filename").value, "client/main.algo");
  assert.equal(app.elements.get("project-name").textContent, "Dijkstra example");
  assert.equal(app.elements.get("analysis").value, PROJECT_BUNDLE.analyses["Algo.client.main.Analysis"]);
  const request = app.requests.filter(({ url }) => url === "/api/compile").at(-1);
  assert.equal(request.request.headers["X-Algo2Lean-Project"], "1");
  assert.equal(request.body.project_sources["library.algo"], PROJECT_LIBRARY);
  assert.equal(request.body.project_analyses["Algo.library.Analysis"], PROJECT_BUNDLE.analyses["Algo.library.Analysis"]);
  await app.elements.get("close-project-button").click();
  assert.equal(app.elements.get("source").value, "my existing source");
  assert.equal(app.elements.get("analysis").value, "my existing proof");
});

test("late example download cannot replace edits made while loading", async () => {
  let complete;
  const pending = new Promise((resolve) => { complete = resolve; });
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/example-project/dijkstra") return pending;
    return projectExampleResponse(url);
  } });
  await app.ready();
  const opening = chooseProjectExample(app);
  await app.ready();
  await app.edit("keep newest source");
  complete({ ok: true, json: async () => PROJECT_BUNDLE });
  await opening;
  assert.equal(app.elements.get("source").value, "keep newest source");
  assert.equal(app.elements.get("project-toolbar").hidden, true);
  assert.match(app.elements.get("file-message").textContent, /workspace changed/);
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
  assert.equal(app.elements.get("source").value, "keep source");
  assert.equal(app.elements.get("analysis").value, "keep proof");
  assert.match(app.elements.get("file-message").textContent, /entry module is missing/);
});

test("an invalid bundled example shows the server diagnostic without replacing drafts", async () => {
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/example-project/dijkstra") return { ok: false,
      json: async () => ({ diagnostics: [{ message: "Module 'graph' was not found." }] }) };
    return projectExampleResponse(url);
  } });
  await app.ready();
  await app.edit("keep source");
  await app.editAnalysis("keep proof");
  await chooseProjectExample(app);
  assert.equal(app.elements.get("source").value, "keep source");
  assert.equal(app.elements.get("analysis").value, "keep proof");
  assert.match(app.elements.get("file-message").textContent, /Module 'graph' was not found/);
});

test("compiler setup failures preserve drafts and are not attributed to source or proofs", async () => {
  let failed = false;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (failed && ["/api/compile", "/api/check", "/api/analyze"].includes(url)) {
      return { ok: false, status: 503, json: async () => ({ scope: "setup",
        message: "Compiler setup error: publication.json is missing.", diagnostics: [], analysis_diagnostics: [] }) };
    }
  } });
  await app.ready();
  await app.editAnalysis("-- keep this proof");
  const source = app.elements.get("source").value;
  assert.equal(app.elements.get("export-button").disabled, false);
  failed = true;
  for (const button of ["compile-button", "check-button", "analyze-button"]) {
    await app.elements.get(button).click();
    await app.ready();
    assert.equal(app.elements.get("compile-status").textContent, "Compiler setup needs attention");
    assert.equal(app.elements.get("lean-state").textContent, "Compilation unavailable");
    assert.equal(app.elements.get("export-button").disabled, true);
    assert.equal(app.elements.get("source").value, source);
    assert.equal(app.elements.get("analysis").value, "-- keep this proof");
  }
  assert.equal(app.elements.get("analysis-state").textContent, "Not checked");
  assert.match(app.elements.get("analysis-status").textContent, /Compiler setup needs attention/);
});

test("merge sort main results preview and jump to the current proof without changing either document", async () => {
  const sourceText = fs.readFileSync(path.join(__dirname, "../examples/merge_sort.algo"), "utf8");
  const proof = fs.readFileSync(path.join(__dirname, "../examples/analysis/merge_sort.lean"), "utf8");
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/examples") return { ok: true, json: async () => ({ examples: [{
      name: "Merge Sort", filename: "merge_sort.algo", source: sourceText,
      module: "MergeSortGenerated", analysis: proof,
    }] }) };
  } });
  await app.ready();
  assert.equal(app.elements.get("source").value, sourceText);
  const analysis = app.elements.get("analysis");
  const loaded = analysis.value;
  assert.ok(loaded.includes("theorem every_output_correct"));
  const outline = app.elements.get("analysis-outline");
  const nodes = () => descendants(outline);
  const result = nodes().find((node) => node.tagName === "BUTTON" && node.title === "every_output_correct");
  assert.ok(result);
  assert.equal(result.textContent, "Correctness");
  await result.click();
  const expectedStatement = loaded.slice(loaded.indexOf("theorem every_output_correct"),
    loaded.indexOf(" := by", loaded.indexOf("theorem every_output_correct")));
  assert.equal(nodes().find((node) => node.tagName === "PRE").textContent, expectedStatement);
  assert.equal(analysis.value, loaded);
  assert.equal(analysis.selectionStart, 0);
  await nodes().find((node) => node.textContent.startsWith("Go to proof")).click();
  assert.equal(analysis.selectionStart, loaded.indexOf("theorem every_output_correct"));
  assert.equal(analysis.focused, true);
  assert.ok(app.elements.get("analysis-editor").scrollTop > 0);
  const edited = "-- Additional explanation.\n" + loaded;
  await app.editAnalysis(edited);
  await nodes().find((node) => node.textContent.startsWith("Go to proof")).click();
  assert.equal(analysis.selectionStart, edited.indexOf("theorem every_output_correct"));
  assert.equal(analysis.value, edited);
  assert.equal(app.elements.get("source").value, sourceText);
});

for (const historical of [false, true]) test(`a recovered ${historical ? "pre-runtime" : "pre-marker"} merge-sort proof gains main-result navigation without rewriting drafts`, async () => {
  const source = fs.readFileSync(path.join(__dirname, "../examples/merge_sort.algo"), "utf8");
  const canonical = fs.readFileSync(path.join(__dirname, "../examples/analysis/merge_sort.lean"), "utf8");
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
  const saved = seedPair(local, pairedSnapshot(source, recovered, {
    filename: "my_merge_sort.algo", savedSource: source, savedFilename: "my_merge_sort.algo",
    analysisFilename: "MergeSortProof.lean", savedAnalysis: recovered,
    savedAnalysisFilename: "MergeSortProof.lean",
  }), session);
  const before = [...local.data];
  let deliverExamples;
  const pendingExamples = new Promise((resolve) => { deliverExamples = resolve; });
  const app = editor(local, session, { fetch: (url) => {
    if (url === "/api/examples") return pendingExamples;
  } });
  await app.ready();
  await descendants(app.elements.get("draft-list"))
    .find((node) => node.tagName === "BUTTON" && node.textContent === "Recover").click();
  const outline = app.elements.get("analysis-outline");
  const nodes = () => descendants(outline);
  const mainLabels = () => nodes().find((node) => node.className === "proof-main-results")
    .children.map((button) => button.textContent);
  assert.equal(app.elements.get("analysis").value, recovered);
  assert.deepEqual(mainLabels(), []);
  deliverExamples({ ok: true, json: async () => ({ examples: [{
    name: "Merge Sort", filename: "merge_sort.algo", source,
    module: "MergeSortGenerated", analysis: canonical,
  }] }) });
  await app.ready();
  assert.deepEqual(mainLabels(), expectedLabels);
  assert.equal(app.elements.get("source").value, source);
  assert.equal(app.elements.get("analysis").value, recovered);
  assert.equal(app.elements.get("analysis-filename").value, "MergeSortProof.lean");
  assert.doesNotMatch(app.elements.get("save-state").textContent, /Unsaved/);
  assert.doesNotMatch(app.elements.get("analysis-save-state").textContent, /Unsaved/);
  const result = nodes().find((node) => node.tagName === "BUTTON" && node.title === "every_output_correct");
  assert.equal(result.textContent, "Correctness");
  await result.click();
  await nodes().find((node) => node.textContent.startsWith("Go to proof")).click();
  assert.equal(app.elements.get("analysis").selectionStart, recovered.indexOf("theorem every_output_correct"));
  assert.equal(app.elements.get("analysis").value, recovered);
  await app.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
  assert.deepEqual(store(local).read(saved.id), saved);
});

function currentMergeSortExample() {
  return {
    name: "Merge Sort", filename: "merge_sort.algo", module: "MergeSortGenerated",
    source: fs.readFileSync(path.join(__dirname, "../examples/merge_sort.algo"), "utf8"),
    analysis: fs.readFileSync(path.join(__dirname, "../examples/analysis/merge_sort.lean"), "utf8"),
  };
}

function exampleCatalog(example) {
  return { fetch: (url) => url === "/api/examples"
    ? { ok: true, json: async () => ({ examples: [example] }) } : undefined };
}

function exampleDraft(example, overrides = {}) {
  return pairedSnapshot(example.source, example.analysis, {
    filename: example.filename, savedFilename: example.filename,
    savedSource: example.source, savedAnalysis: example.analysis,
    ...overrides,
  });
}

for (const changedPart of ["source", "analysis"]) test(`an older example ${changedPart} can be refreshed without losing its draft or returning after reload`, async () => {
  const example = currentMergeSortExample();
  const oldSource = changedPart === "source" ? example.source.replace(/^\s*tick\("merge_sort"\)\n/gm, "") : example.source;
  const oldProof = changedPart === "analysis"
    ? "import MergeSortGeneratedPoints\ntheorem old_output : is_Output_merge_sort input output := by\n  exact saved_proof\n"
    : example.analysis;
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const saved = seedPair(local, exampleDraft(example, {
    source: oldSource, analysis: oldProof, savedSource: oldSource, savedAnalysis: oldProof,
  }), session);
  const before = [...local.data];
  const options = exampleCatalog(example);
  const app = editor(local, session, options);
  await app.ready();
  assert.equal(app.elements.get("source").value, example.source);
  assert.equal(app.elements.get("analysis").value, example.analysis);
  assert.equal(app.elements.get("example-update").hidden, true);
  assert.deepEqual(store(local).read(saved.id), saved);
  await descendants(app.elements.get("draft-list"))
    .find((node) => node.tagName === "BUTTON" && node.textContent === "Recover").click();
  assert.equal(app.elements.get("example-update").hidden, false);
  assert.match(app.elements.get("example-update-message").textContent, /differ|older|current|updated/i);
  assert.equal(app.elements.get("source").value, oldSource);
  assert.equal(app.elements.get("analysis").value, oldProof);
  await app.elements.get("load-current-example").click();
  await app.ready();
  assert.equal(app.elements.get("source").value, example.source);
  assert.equal(app.elements.get("analysis").value, example.analysis);
  assert.equal(app.elements.get("example-update").hidden, true);
  assert.equal(session.getItem(EXAMPLE_SESSION_KEY), example.filename);
  assert.deepEqual([...local.data], before);
  assert.deepEqual(store(local).read(saved.id), saved);
  await app.window.dispatch("beforeunload");
  const reloaded = editor(local, session, options);
  await reloaded.ready();
  assert.equal(reloaded.elements.get("source").value, example.source);
  assert.equal(reloaded.elements.get("analysis").value, example.analysis);
  assert.equal(reloaded.elements.get("example-update").hidden, true);
  const mainButtons = descendants(reloaded.elements.get("analysis-outline"))
    .find((node) => node.className === "proof-main-results").children;
  assert.deepEqual(mainButtons.map((button) => button.textContent), ["Correctness", "Running time"]);
  await reloaded.window.dispatch("beforeunload");
  assert.deepEqual([...local.data], before);
});

test("example refresh notices follow source and proof changes and stay hidden for custom files and projects", async () => {
  const example = currentMergeSortExample();
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  seedPair(local, exampleDraft(example), session);
  const app = editor(local, session, exampleCatalog(example));
  await app.ready();
  assert.equal(app.elements.get("example-update").hidden, true);
  await app.editAnalysis(example.analysis + "\n-- My additional analysis.\n");
  assert.equal(app.elements.get("example-update").hidden, false);
  await app.editAnalysis(example.analysis);
  assert.equal(app.elements.get("example-update").hidden, true);
  await app.edit(example.source + "\n# My variant.\n");
  assert.equal(app.elements.get("example-update").hidden, false);
  await app.rename("filename", "my_sort.algo");
  assert.equal(app.elements.get("example-update").hidden, true);
  await openProject(app, "custom-project", { "merge_sort.algo": example.source + "\n# Project version.\n" });
  assert.equal(app.elements.get("filename").value, "merge_sort.algo");
  assert.equal(app.elements.get("example-update").hidden, true);
});

test("refreshing an example backs up pending source and proof changes before replacing them", async () => {
  const example = currentMergeSortExample();
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const saved = seedPair(local, exampleDraft(example), session);
  const app = editor(local, session, exampleCatalog(example));
  await app.ready();
  const source = example.source + "\n# Pending source change.\n";
  const proof = example.analysis + "\n-- Pending proof change.\n";
  await app.edit(source);
  await app.editAnalysis(proof);
  app.window.confirm = () => assert.fail("A complete draft backup should permit replacement without confirmation");
  await app.elements.get("load-current-example").click();
  await app.ready();
  assert.equal(app.elements.get("source").value, example.source);
  assert.equal(app.elements.get("analysis").value, example.analysis);
  assert.deepEqual(store(local).read(saved.id), saved);
  const backup = app.records().find((record) => record.id !== saved.id);
  assert.equal(backup.source, source);
  assert.equal(backup.analysis, proof);
  assert.equal(app.records().length, 2);
});

test("declining example refresh after a failed backup preserves both pending documents", async () => {
  const example = currentMergeSortExample();
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const saved = seedPair(local, exampleDraft(example), session);
  const app = editor(local, session, exampleCatalog(example));
  await app.ready();
  const source = example.source + "\n# Unsaved source.\n";
  const proof = example.analysis + "\n-- Unsaved proof.\n";
  await app.edit(source);
  await app.editAnalysis(proof);
  local.fail.add("write");
  let confirmations = 0;
  app.window.confirm = () => { confirmations += 1; return false; };
  await app.elements.get("load-current-example").click();
  assert.equal(confirmations, 1);
  assert.equal(app.elements.get("source").value, source);
  assert.equal(app.elements.get("analysis").value, proof);
  assert.equal(app.elements.get("example-update").hidden, false);
  assert.deepEqual(store(local).read(saved.id), saved);
  assert.equal(app.records().length, 1);
  assert.equal(session.getItem(EXAMPLE_SESSION_KEY), example.filename);
});

test("every refresh starts the current merge-sort source and proof regardless of the prior example", async () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const original = seed(local, "previous document", session);
  const example = currentMergeSortExample();
  const options = { fetch: (url) => url === "/api/examples" ? { ok: true, json: async () => ({ examples: [
    { name: "Other", source: "def other() -> Int:\n    return 5\n", filename: "other.algo", analysis: "-- other proof" },
    example,
  ] }) } : undefined };
  const app = editor(local, session, options);
  await app.ready();
  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  await app.ready();
  assert.equal(session.getItem(EXAMPLE_SESSION_KEY), "other.algo");
  const before = [...local.data];
  for (let reload = 0; reload < 2; reload += 1) {
    const reopened = editor(local, session, options);
    await reopened.ready();
    assert.equal(reopened.elements.get("filename").value, example.filename);
    assert.equal(reopened.elements.get("source").value, example.source);
    assert.equal(reopened.elements.get("analysis").value, example.analysis);
    assert.equal(reopened.elements.get("draft-picker").open, false);
    await reopened.window.dispatch("beforeunload");
    assert.deepEqual([...local.data], before);
  }
  assert.deepEqual(store(local).read(original.id), original);
});

for (const changedPart of ["source", "analysis", "filename", "analysis-filename"]) test(`late startup examples preserve a user's ${changedPart} edit`, async () => {
  const example = currentMergeSortExample();
  let deliverExamples;
  const pending = new Promise((resolve) => { deliverExamples = resolve; });
  const app = editor(undefined, undefined, { fetch: (url) => url === "/api/examples" ? pending : undefined });
  await app.ready();
  if (changedPart === "source") await app.edit("def mine() -> Int:\n    return 7\n");
  else if (changedPart === "analysis") await app.editAnalysis("-- My analysis started before the catalog loaded.\n");
  else await app.rename(changedPart, changedPart === "filename" ? "Mine.algo" : "Mine.lean");
  const before = Object.fromEntries(["source", "analysis", "filename", "analysis-filename"]
    .map((id) => [id, app.elements.get(id).value]));
  deliverExamples({ ok: true, json: async () => ({ examples: [example] }) });
  await app.ready();
  for (const [id, value] of Object.entries(before)) assert.equal(app.elements.get(id).value, value, id);
  await app.flush();
  assert.ok(app.records().some((record) => record.source === before.source && record.analysis === before.analysis));
});

test("example refresh starts merge sort and keeps edited copies available for explicit recovery", async () => {
  const app = editor();
  await app.ready();
  app.elements.get("examples").value = "0";
  await app.elements.get("examples").dispatch("change");
  await app.edit("def changed() -> Int:\n    return 8\n");
  await app.editAnalysis("-- My proof for the edited example.\n");
  await app.window.dispatch("beforeunload");
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  assert.equal(reloaded.elements.get("filename").value, "merge_sort.algo");
  assert.match(reloaded.elements.get("source").value, /def merge_sort/);
  await draftAction(reloaded, "def changed() -> Int:\n    return 8\n", "Recover").click();
  assert.equal(reloaded.elements.get("source").value, "def changed() -> Int:\n    return 8\n");
  assert.equal(reloaded.elements.get("analysis").value, "-- My proof for the edited example.\n");
});

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
  const filename = app.elements.get("filename").value;
  const analysisFilename = app.elements.get("analysis-filename").value;
  app.window.confirm = () => assert.fail("Clearing drafts must remain reversible without confirmation");
  await app.elements.get("clear-drafts-button").click();
  assert.deepEqual([...local.data], [["unrelated.preference", "keep me"]]);
  assert.equal(app.elements.get("source").value, "pending standalone source");
  assert.equal(app.elements.get("analysis").value, "-- pending standalone proof");
  assert.equal(app.elements.get("filename").value, filename);
  assert.equal(app.elements.get("analysis-filename").value, analysisFilename);
  assert.equal(app.elements.get("undo-clear-drafts-button").hidden, false);

  await app.window.dispatch("beforeunload");
  app.document.visibilityState = "hidden";
  await app.document.dispatch("visibilitychange");
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

  await app.elements.get("clear-drafts-button").click();
  await app.editAnalysis("-- new proof after clearing");
  await app.flush();
  const newRecords = new Map([...local.data].filter(([key]) => key.startsWith(PREFIX)));
  assert.equal(newRecords.size, 1);
  assert.ok([...newRecords.keys()].every((key) => !original.has(key)));
  await app.elements.get("undo-clear-drafts-button").click();
  for (const [key, value] of original) assert.equal(local.getItem(key), value, key);
  for (const [key, value] of newRecords) assert.equal(local.getItem(key), value, key);
  assert.equal(app.elements.get("source").value, "original draft source");
  assert.equal(app.elements.get("analysis").value, "-- new proof after clearing");
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
  await app.elements.get("clear-drafts-button").click();
  const replacement = JSON.stringify({ ...old, source: "newer work from another tab", updatedAt: old.updatedAt + 1 });
  local.setItem(key, replacement);
  await app.elements.get("undo-clear-drafts-button").click();
  assert.notEqual(replacement, original);
  assert.equal(local.getItem(key), replacement);
  assert.equal(app.elements.get("source").value, "original source");
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
  await app.elements.get("clear-drafts-button").click();
  assert.equal(app.elements.get("project-toolbar").hidden, false);
  assert.equal(app.elements.get("source").value, "pending project source");
  assert.equal(app.elements.get("analysis").value, "-- pending project proof");
  assert.equal(app.elements.get("filename").value, "main.algo");
  await app.window.dispatch("beforeunload");
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
  await app.elements.get("undo-clear-drafts-button").click();
  assert.equal(app.local.getItem(PROJECT_PREFIX + old.id), oldRaw);
  assert.equal(app.local.getItem(PROJECT_PREFIX + fresh.id), freshRaw);
});

test("Undo clear is available only in the tab session that performed the clear", async () => {
  const app = editor();
  await app.ready();
  await app.edit("source to clear");
  await app.flush();
  await app.elements.get("clear-drafts-button").click();
  assert.equal(app.elements.get("undo-clear-drafts-button").hidden, false);
  const reloaded = editor(app.local, app.session);
  await reloaded.ready();
  assert.equal(reloaded.elements.get("undo-clear-drafts-button").hidden, true);
  await reloaded.elements.get("undo-clear-drafts-button").click();
  assert.equal(reloaded.records().length, 0);
});


test("hosted editor routes compilation through its browser backend and describes local checking", async () => {
  const app = editor(undefined, undefined, { hosted: true });
  await app.ready();
  assert.ok(app.requests.some(({ url }) => url === "/api/compile"));
  assert.equal(app.elements.get("generation-tools").hidden, false);
  assert.match(app.elements.get("compilation-description").textContent, /stay on your device/);
  await app.elements.get("check-button").click();
  await app.elements.get("analyze-button").click();
  assert.equal(app.requests.some(({ url }) => url === "/api/check" || url === "/api/analyze"), false);
  assert.match(app.elements.get("analysis-status").textContent, /local Algo2Lean editor/);
});

test("hosted Save analysis requests the same archive endpoint through the browser backend", async () => {
  const app = editor(undefined, undefined, { hosted: true });
  await app.ready();
  await app.edit("def browser_work() -> Int:\n    return 3\n");
  await app.editAnalysis("-- browser proof");
  await app.rename("analysis-filename", "BrowserProof.lean");
  await app.elements.get("analysis-save-button").click();
  const exported = app.requests.filter(({ url }) => url === "/api/analysis-export").at(-1);
  assert.equal(exported.body.source, app.elements.get("source").value);
  assert.equal(exported.body.analysis, "-- browser proof");
  assert.equal(exported.body.analysis_filename, "BrowserProof.lean");
  assert.equal(app.downloads.at(-1).name, "BrowserProof.zip");
  assert.equal(app.elements.get("analysis-filename").value, "BrowserProof.lean");
  assert.equal(app.elements.get("analysis-save-state").textContent, "Downloaded");
});

test("hosted editor downloads generation manifests through the worker backend", async () => {
  const app = editor(undefined, undefined, { hosted: true, fetch: async (url) => url === "/api/generation"
    ? { ok: true, json: async () => ({ manifest: { compiler: { version: "0.1.0" } } }) } : null });
  await app.ready();
  await app.elements.get("generation-manifest-button").click();
  await app.ready();
  assert.ok(app.requests.some(({ url, body }) => url === "/api/generation" && body.filename === "merge_sort.algo"));
  assert.equal(app.downloads.at(-1).name, "generation.json");
});

test("source and filename edits invalidate an earlier exact generation match", async () => {
  const app = editor(undefined, undefined, { hosted: true, fetch: async (url) => url === "/api/generation"
    ? { ok: true, json: async () => ({ files: { "Generated.lean": "test" }, libraries: {} }) } : null });
  await app.ready();
  const picker = app.elements.get("verify-files-picker");
  async function verify() {
    picker.files = [{ name: "Generated.lean", size: 4, arrayBuffer: async () => new TextEncoder().encode("test").buffer }];
    await picker.dispatch("change");
    await app.ready();
    assert.match(app.elements.get("generation-status").textContent, /^Exact match/);
  }
  await verify();
  await app.edit("def changed() -> Int:\n    return 2\n");
  assert.match(app.elements.get("generation-status").textContent, /Workspace changed/);
  assert.equal(app.elements.get("generation-details").textContent, "");
  await verify();
  await app.rename("filename", "renamed.algo");
  assert.match(app.elements.get("generation-status").textContent, /Workspace changed/);
});

test("workspace changes cancel a pending generation request and suppress its late result", async () => {
  let complete, signal;
  const app = editor(undefined, undefined, { hosted: true, fetch: async (url, options) => {
    if (url !== "/api/generation") return null;
    signal = options.signal;
    return new Promise((resolve) => { complete = resolve; });
  } });
  await app.ready();
  const pending = app.elements.get("generation-manifest-button").click();
  await app.ready();
  assert.equal(signal.aborted, false);
  await app.edit("def changed() -> Int:\n    return 2\n");
  assert.equal(signal.aborted, true);
  const status = app.elements.get("generation-status").textContent;
  complete({ ok: true, json: async () => ({ manifest: { stale: true } }) });
  await pending;
  await app.ready();
  assert.equal(app.elements.get("generation-status").textContent, status);
  assert.equal(app.downloads.length, 0);
});
