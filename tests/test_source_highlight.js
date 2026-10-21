"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");

// Exercise the editor's source renderer without opening a browser or starting
// its unrelated project, storage, and network handlers.
const app = fs.readFileSync(path.join(__dirname, "../editor/app.js"), "utf8");
const start = app.indexOf("  function escapeHtml(value) {");
const end = app.indexOf("  function renderSource() {", start);
assert.ok(start >= 0 && end > start, "Source highlighting functions are present");
const highlight = vm.runInNewContext(app.slice(start, end) + "\nhighlight;");

test("random draws use the same function color as other builtins", () => {
  const html = highlight("randint(-2, 2) + copy(values)[0]");
  assert.match(html, /<span class="token-function">randint<\/span>\(/);
  assert.match(html, /<span class="token-function">copy<\/span>\(/);
  assert.equal(highlight("randint"), '<span class="token-function">randint</span>');
});

test("random identifiers inside comments and strings keep their own syntax color", () => {
  const html = highlight('# randint(0, 1)\ntick("randint")\nrandint_count = 1');
  assert.match(html, /<span class="token-comment"># randint\(0, 1\)<\/span>/);
  assert.match(html, /<span class="token-string">&quot;randint&quot;<\/span>/);
  assert.match(html, /\nrandint_count = /);
  assert.doesNotMatch(html, /<span class="token-function">randint<\/span>/);
});

test("tuple, collection, and real source types use the integer type color", () => {
  const html = highlight("Tuple[Real, Dict[Int, Set[Bool]]] = Real(1)");
  for (const name of ["Tuple", "Real", "Dict", "Int", "Set", "Bool"]) {
    assert.match(html, new RegExp(`<span class="token-type">${name}</span>`));
  }
  assert.match(html, /<span class="token-type">Real<\/span>\(/);
  assert.equal(highlight("len set"), '<span class="token-function">len</span> <span class="token-function">set</span>');
  assert.match(highlight("del counts[1]"), /<span class="token-keyword">del<\/span>/);
});

test("exact decimal and scientific literals keep their entire numeric token", () => {
  for (const value of ["0.1", ".5", "1.", "1e309", "1e-1000", "12_3.4_5e+0_2"]) {
    assert.equal(highlight(value), `<span class="token-number">${value}</span>`);
  }
  assert.equal(highlight("-0.5"), '-<span class="token-number">0.5</span>');
  assert.equal(highlight("some_1e3"), "some_1e3");
  assert.equal(highlight('"1e309 Real Set"'), '<span class="token-string">&quot;1e309 Real Set&quot;</span>');
});


test("fork-join calls use builtin colors without coloring comments or larger names", () => {
  assert.equal(highlight("fork_join"), '<span class="token-function">fork_join</span>');
  assert.match(highlight("fork_join(left(n), right(n))"), /<span class="token-function">fork_join<\/span>\(/);
  assert.equal(highlight("fork_join_count"), "fork_join_count");
  assert.match(highlight("# fork_join(left(), right())"), /<span class="token-comment">/);
  assert.doesNotMatch(highlight("# fork_join(left(), right())"), /token-function/);
});
