// Keyboard behaviour of the code editors and the document-level shortcuts.
import { test } from "vitest";
import assert from "node:assert/strict";
import { act, editor, fireEvent, tick } from "./support/editor-harness.jsx";

function caret(textarea, position) {
  textarea.focus();
  textarea.setSelectionRange(position, position);
}

async function press(textarea, key, init = {}) {
  fireEvent.keyDown(textarea, { key, ...init });
  await tick(4);
}

async function chord(app, key, init = {}) {
  const event = new KeyboardEvent("keydown", { key, cancelable: true, ...init });
  await act(async () => { app.documentEvents.dispatchEvent(event); await Promise.resolve(); });
  await tick(4);
  return event;
}

test("Tab fills to the next indent stop and shifts selected lines in both directions", async () => {
  const app = editor();
  await app.ready();
  const source = app.byId("source");
  await app.edit("def f(x):\nreturn x\n");
  caret(source, 10);
  await press(source, "Tab");
  assert.equal(app.store.state.source, "def f(x):\n    return x\n");
  assert.equal(source.selectionStart, 14);
  caret(source, 12);
  await press(source, "Tab");
  assert.equal(app.store.state.source, "def f(x):\n      return x\n");
  assert.equal(source.selectionStart, 14);

  await app.edit("a\nb\n");
  source.focus();
  source.setSelectionRange(0, 3);
  await press(source, "Tab");
  assert.equal(app.store.state.source, "    a\n    b\n");
  assert.deepEqual([source.selectionStart, source.selectionEnd], [0, 11]);
  await press(source, "Tab", { shiftKey: true });
  assert.equal(app.store.state.source, "a\nb\n");
  assert.deepEqual([source.selectionStart, source.selectionEnd], [0, 3]);
  await press(source, "Tab", { shiftKey: true });
  assert.equal(app.store.state.source, "a\nb\n", "lines without indentation are unchanged");
  app.unmount();
});

test("Enter keeps the indentation and opens a block after a colon or a Lean tactic keyword", async () => {
  const app = editor();
  await app.ready();
  const source = app.byId("source");
  await app.edit("if x:  # note");
  caret(source, source.value.length);
  await press(source, "Enter");
  assert.equal(app.store.state.source, "if x:  # note\n    ");
  await app.edit("    return x");
  caret(source, source.value.length);
  await press(source, "Enter");
  assert.equal(app.store.state.source, "    return x\n    ");

  const analysis = app.byId("analysis");
  await app.editAnalysis("theorem t : True := by");
  caret(analysis, analysis.value.length);
  await press(analysis, "Enter");
  assert.equal(app.store.state.analysis, "theorem t : True := by\n  ");
  assert.equal(document.activeElement, analysis);
  await press(analysis, "Escape");
  assert.notEqual(document.activeElement, analysis);
  app.unmount();
});

test("Ctrl/Cmd+Enter compiles or checks the focused document and Ctrl/Cmd+S saves it", async () => {
  const app = editor();
  await app.ready();
  const count = (url) => app.requests.filter((request) => request.url === url).length;
  const compiles = count("/api/compile");
  app.byId("source").focus();
  const compile = await chord(app, "Enter", { metaKey: true });
  assert.ok(compile.defaultPrevented);
  assert.equal(count("/api/compile"), compiles + 1);
  await chord(app, "s", { ctrlKey: true });
  assert.equal(app.downloads.at(-1).name, "merge_sort.algo");

  app.byId("analysis").focus();
  const analyses = count("/api/analyze");
  await chord(app, "Enter", { ctrlKey: true });
  assert.equal(count("/api/analyze"), analyses + 1);
  await chord(app, "S", { metaKey: true });
  assert.equal(app.downloads.at(-1).name, "Analysis.zip", "the analysis saves as a package with its dependencies");

  const downloads = app.downloads.length;
  const requests = app.requests.length;
  for (const init of [{ ctrlKey: true, altKey: true }, {}]) {
    const ignored = await chord(app, "Enter", init);
    assert.ok(!ignored.defaultPrevented);
    await chord(app, "s", init);
  }
  assert.equal(app.requests.length, requests);
  assert.equal(app.downloads.length, downloads);
  app.unmount();
});

test("opening a file focuses its editor with the caret at the start of the new text", async () => {
  const app = editor();
  await app.ready();
  const source = app.byId("source");
  caret(source, source.value.length);
  source.blur();
  await app.openFile("file-picker", "other.algo", "def g() -> Int:\n    return 2\n");
  assert.equal(source.value, "def g() -> Int:\n    return 2\n");
  assert.equal(document.activeElement, source);
  assert.deepEqual([source.selectionStart, source.selectionEnd], [0, 0]);

  const analysis = app.byId("analysis");
  caret(analysis, analysis.value.length);
  analysis.blur();
  await app.openFile("analysis-file-picker", "Proof.lean", "theorem t : True := trivial\n");
  assert.equal(analysis.value, "theorem t : True := trivial\n");
  assert.equal(document.activeElement, analysis);
  assert.deepEqual([analysis.selectionStart, analysis.selectionEnd], [0, 0]);
  app.unmount();
});

test("the Browser drafts button reveals the picker and moves focus to its summary", async () => {
  const app = editor();
  await app.ready();
  assert.ok(app.byId("draft-picker").hidden, "the picker starts hidden on a first visit");
  await app.click("drafts-button");
  const picker = app.byId("draft-picker");
  assert.ok(!picker.hidden);
  assert.ok(picker.open);
  assert.equal(document.activeElement, picker.querySelector("summary"));
  app.unmount();
});
