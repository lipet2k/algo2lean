"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const { matches, create } = require("../editor/code-search.js");

class Element {
  constructor(tag, document) {
    this.tagName = tag.toUpperCase();
    this.ownerDocument = document;
    this.children = [];
    this.parentElement = null;
    this.listeners = new Map();
    this.attributes = new Map();
    this.style = {};
    this.value = "";
    this.textContent = "";
    this.hidden = false;
    this.disabled = false;
    this.selectionStart = this.selectionEnd = 0;
    this.scrollTop = this.scrollLeft = 0;
    this.clientHeight = 100;
    this.clientWidth = 300;
  }
  append(...nodes) { nodes.forEach((node) => { node.parentElement = this; this.children.push(node); }); }
  insertBefore(node, other) { node.parentElement = this; this.children.splice(this.children.indexOf(other), 0, node); }
  remove() { this.parentElement.children.splice(this.parentElement.children.indexOf(this), 1); this.parentElement = null; }
  setAttribute(name, value) { this.attributes.set(name, value); }
  getAttribute(name) { return this.attributes.get(name); }
  addEventListener(name, handler) { if (!this.listeners.has(name)) this.listeners.set(name, new Set()); this.listeners.get(name).add(handler); }
  removeEventListener(name, handler) { this.listeners.get(name)?.delete(handler); }
  focus() { this.ownerDocument.activeElement = this; }
  select() { this.setSelectionRange(0, this.value.length); }
  setSelectionRange(start, end) { this.selectionStart = start; this.selectionEnd = end; }
  getBoundingClientRect() {
    return this.tagName === "TEXTAREA"
      ? { top: -this.viewport.scrollTop, left: 50 - this.viewport.scrollLeft }
      : { top: 0, left: 0 };
  }
  scrollIntoView() { this.revealed = true; }
  dispatch(type, fields = {}) {
    const event = { target: this, key: "", defaultPrevented: false, stopped: false,
      preventDefault() { this.defaultPrevented = true; }, stopPropagation() { this.stopped = true; }, ...fields };
    let node = this;
    while (node) {
      for (const handler of node.listeners.get(type) || []) handler(event);
      if (event.stopped) break;
      node = node.parentElement;
    }
    return event;
  }
}

function surface(text = "alpha beta alpha") {
  const document = { defaultView: { getComputedStyle: () => ({ fontSize: "14px", lineHeight: "24px", paddingTop: "22px", paddingLeft: "18px", tabSize: "2" }) },
    createElement: (tag) => new Element(tag, document) };
  const scope = document.createElement("section");
  const viewport = document.createElement("div");
  const canvas = document.createElement("div");
  const textarea = document.createElement("textarea");
  textarea.viewport = viewport;
  textarea.value = text;
  canvas.append(textarea);
  viewport.append(canvas);
  scope.append(viewport);
  const search = create({ textarea, viewport, scope, document, label: "analysis" });
  scope.insertBefore(search.element, viewport);
  const input = search.element.children[0].children[0];
  const count = search.element.children[1];
  const previous = search.element.children[2];
  const next = search.element.children[3];
  const close = search.element.children[4];
  const highlight = canvas.children[0];
  return { document, scope, viewport, textarea, search, input, count, previous, next, close, highlight };
}

test("literal case-insensitive matching preserves actual Unicode and punctuation offsets", () => {
  assert.deepEqual(matches("Call call CALL", "call"), [{ start: 0, end: 4 }, { start: 5, end: 9 }, { start: 10, end: 14 }]);
  assert.deepEqual(matches("a.b axb a.b", "a.b"), [{ start: 0, end: 3 }, { start: 8, end: 11 }]);
  assert.deepEqual(matches("[a] + [a]", "[a]"), [{ start: 0, end: 3 }, { start: 6, end: 9 }]);
  assert.deepEqual(matches("İ 𝒂 = 𝒂", "𝒂"), [{ start: 2, end: 4 }, { start: 7, end: 9 }]);
  assert.deepEqual(matches("anything", ""), []);
});

test("search selects from the caret, wraps in both directions, and keeps find-field focus", () => {
  const { search, textarea, input, next, previous, count, document } = surface();
  textarea.setSelectionRange(6, 6);
  search.open("alpha");
  assert.equal(count.textContent, "2 of 2");
  assert.deepEqual([textarea.selectionStart, textarea.selectionEnd], [11, 16]);
  assert.equal(document.activeElement, input);
  next.dispatch("click");
  assert.deepEqual([textarea.selectionStart, textarea.selectionEnd], [0, 5]);
  assert.equal(count.textContent, "1 of 2");
  previous.dispatch("click");
  assert.equal(textarea.selectionStart, 11);
  assert.equal(document.activeElement, input);
});

test("Ctrl/Cmd+F opens only the scoped editor, and Enter/Shift+Enter/Escape work", () => {
  const { search, textarea, input, document, close } = surface();
  textarea.setSelectionRange(0, 5);
  assert.equal(textarea.dispatch("keydown", { key: "f", metaKey: true }).defaultPrevented, true);
  assert.equal(input.value, "alpha");
  assert.equal(search.element.hidden, false);
  assert.equal(input.dispatch("keydown", { key: "Enter" }).defaultPrevented, true);
  assert.equal(textarea.selectionStart, 11);
  input.dispatch("keydown", { key: "Enter", shiftKey: true });
  assert.equal(textarea.selectionStart, 0);
  assert.equal(close.dispatch("keydown", { key: "Enter" }).defaultPrevented, false, "buttons retain their own Enter action");
  assert.equal(input.dispatch("keydown", { key: "Escape" }).defaultPrevented, true);
  assert.equal(search.element.hidden, true);
  assert.equal(document.activeElement, textarea);
  assert.equal(textarea.dispatch("keydown", { key: "f", ctrlKey: true }).defaultPrevented, true);
  search.close();
  assert.equal(textarea.dispatch("keydown", { key: "f", ctrlKey: true, shiftKey: true }).defaultPrevented, false);
  assert.equal(search.element.hidden, true);
  const outside = document.createElement("input");
  assert.equal(outside.dispatch("keydown", { key: "f", metaKey: true }).defaultPrevented, false);
});

test("typing updates counts without moving focus, and no matches disable navigation", () => {
  const { search, textarea, input, document, count, next, previous, highlight } = surface();
  search.open();
  assert.equal(count.textContent, "Type to find");
  input.value = "beta";
  input.dispatch("input");
  assert.equal(count.textContent, "1 of 1");
  assert.deepEqual([textarea.selectionStart, textarea.selectionEnd], [6, 10]);
  assert.equal(document.activeElement, input);
  assert.equal(highlight.hidden, false);
  assert.equal(highlight.children.at(-1).textContent, "beta");
  input.value = "missing";
  input.dispatch("input");
  assert.equal(count.textContent, "No matches");
  assert.equal(next.disabled, true);
  assert.equal(previous.disabled, true);
  assert.equal(highlight.hidden, true);
  input.value = "";
  input.dispatch("input");
  assert.equal(count.textContent, "Type to find");
});

test("editing and programmatic loads refresh matches without rewriting code or the editing caret", () => {
  const { search, textarea, count } = surface();
  search.open("alpha");
  textarea.value = "beta alpha";
  textarea.setSelectionRange(2, 2);
  textarea.dispatch("input");
  assert.equal(count.textContent, "1 of 1");
  assert.equal(textarea.selectionStart, 2);
  assert.equal(textarea.value, "beta alpha");
  textarea.value = "new document";
  search.refresh();
  assert.equal(count.textContent, "No matches");
  textarea.value = "alpha restored";
  search.refresh();
  assert.equal(count.textContent, "1 of 1");
  assert.equal(textarea.value, "alpha restored");
});

test("a distant match scrolls the shared viewport vertically and horizontally", () => {
  const { search, textarea, viewport } = surface("line\n".repeat(40) + "\t" + " ".repeat(100) + "needle");
  search.open("needle");
  assert.ok(viewport.scrollTop > 850);
  assert.ok(viewport.scrollLeft > 500);
  assert.equal(textarea.value.slice(textarea.selectionStart, textarea.selectionEnd), "needle");
  search.close();
});

test("closing and destruction release highlights and keyboard listeners", () => {
  const { search, textarea, close, highlight, document, scope } = surface();
  search.open("alpha");
  close.dispatch("click");
  assert.equal(highlight.hidden, true);
  assert.equal(document.activeElement, textarea);
  search.destroy();
  assert.equal(scope.children.length, 1);
  assert.equal(textarea.parentElement.children.length, 1);
  assert.equal(textarea.dispatch("keydown", { key: "f", ctrlKey: true }).defaultPrevented, false);
});

test("the browser script exposes search without a module loader", () => {
  const context = { window: {} };
  vm.runInNewContext(fs.readFileSync(path.join(__dirname, "../editor/code-search.js"), "utf8"), context);
  assert.equal(typeof context.window.Algo2LeanCodeSearch.create, "function");
});
