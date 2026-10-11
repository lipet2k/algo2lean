"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const { declarations, create } = require("../editor/proof-outline.js");

class Element {
  constructor(tag, ownerDocument) {
    this.tagName = tag.toUpperCase();
    this.ownerDocument = ownerDocument;
    this.children = [];
    this.attributes = new Map();
    this.listeners = new Map();
    this.textContent = "";
    this.value = "";
    this.hidden = false;
  }
  set innerHTML(_) { throw new Error("Proof source must be rendered as text, not HTML"); }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = children; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  getAttribute(name) { return this.attributes.get(name); }
  addEventListener(name, callback) { this.listeners.set(name, callback); }
  click() { this.listeners.get("click")?.({ target: this }); }
  change(value) { this.value = value; this.listeners.get("change")?.({ target: this }); }
}

function surface() {
  const document = { createElement: (tag) => new Element(tag, document) };
  const container = document.createElement("div");
  const jumps = [];
  const outline = create(container, { document, onJump: (...position) => jumps.push(position) });
  return { container, outline, jumps };
}

function descendants(element) { return [element, ...element.children.flatMap(descendants)]; }
function text(element) { return descendants(element).map((node) => node.textContent).join("\n"); }
function tag(element, name) { return descendants(element).filter((node) => node.tagName === name); }
function preview(element) { return descendants(element).find((node) => node.className === "proof-statement"); }
function mainButtons(element) {
  return descendants(element).find((node) => node.className === "proof-main-results").children;
}

test("comments, strings, and multiline quoted identifiers cannot fabricate theorem links", () => {
  const source = String.raw`-- theorem hidden_line : True := by trivial
/- Outer comment
  /- theorem hidden_nested : True := by trivial -/
  -- Main result: Hidden
  theorem hidden_block : True := by trivial
-/
def text := "a quoted \" word
theorem hidden_string : True := by trivial"
def «multiline
theorem hidden_name : True := by trivial
» := 0
theorem actual : True := by trivial
`;
  const entries = declarations(source);
  assert.deepEqual(entries.map((entry) => entry.name), ["actual"]);
  assert.equal(entries[0].line, 12);
  assert.equal(entries[0].label, null);
  assert.equal(entries[0].statement, "theorem actual : True");
});

test("main-result labels pair with theorem documentation across comments and attributes", () => {
  const source = `-- Main result: Correct output
/-- Every accepted output meets the specification.
    Nested /- explanatory -/ text is part of the documentation. -/
@[simp]
private theorem correct (n : Nat) : n = n := by rfl

-- Main result: Reusable call
/- A regular comment does not replace the documentation. -/
/-- The caller may reuse the established contract. -/
@[simp] protected lemma reusable : True := by trivial
`;
  const entries = declarations(source);
  assert.deepEqual(entries.map((entry) => [entry.name, entry.label, entry.line]), [
    ["correct", "Correct output", 5], ["reusable", "Reusable call", 10],
  ]);
  assert.match(entries[0].description, /Every accepted output/);
  assert.match(entries[0].description, /Nested \/- explanatory -\/ text/);
  assert.equal(entries[1].description, "The caller may reuse the established contract.");
  assert.equal(entries[1].statement, "@[simp] protected lemma reusable : True");
});

test("labels and documentation do not leak past another declaration", () => {
  const source = `-- Main result: A definition is not a theorem
/-- Documentation for the definition. -/
def identity (n : Nat) := n
theorem first : True := by trivial
-- Main result: First label
-- Main result: Replacement label
/-- Documentation for the next theorem. -/
theorem second : True := by trivial
theorem third : True := by trivial
`;
  const entries = declarations(source);
  assert.deepEqual(entries.map((entry) => entry.label), [null, "Replacement label", null]);
  assert.equal(entries[0].description, "");
  assert.equal(entries[1].description, "Documentation for the next theorem.");
  assert.equal(entries[2].description, "");
});

test("statement extraction skips binder defaults, strings, and character delimiters", () => {
  const statements = [
    `theorem defaults (n : Nat := 2) (s : String := "(:=)") : n = n`,
    `theorem character : '(' = '('`,
    String.raw`theorem escaped : '\'' = '\''`,
    `theorem value' (n' : Nat := 1) : n' = n'`,
    `theorem quoted.«result:=name» : True`,
  ];
  for (const statement of statements) {
    assert.equal(declarations(statement + " := by rfl\n")[0].statement, statement, statement);
  }
});

test("local let, instance, and have bindings remain in the complete theorem statement", () => {
  const statements = [
    "theorem localLet : let n := 1; let m := n + 1; m = 2",
    "theorem localInstance : letI : Inhabited Nat := ⟨0⟩; True",
    "theorem localInstancePrime : letI' : Inhabited Nat := ⟨0⟩; True",
    "theorem localHave : have h : True := True.intro; True",
    "theorem nested : (let n := 1; n = 1) ∧ True",
  ];
  for (const statement of statements) {
    assert.equal(declarations(statement + " := by trivial\n")[0].statement, statement, statement);
  }
});

test("quoted names preserve their spelling and source offsets", () => {
  const source = "\r\n-- Main result: Quoted result\r\n" +
    "theorem «result -- /- := with spaces» : True := by trivial\r\n";
  const [entry] = declarations(source);
  assert.equal(entry.name, "«result -- /- := with spaces»");
  assert.equal(entry.label, "Quoted result");
  assert.equal(entry.line, 3);
  assert.equal(entry.statement, "theorem «result -- /- := with spaces» : True");
});

test("unfinished editing keeps safe navigation and never consumes the next declaration as a proof", () => {
  const entries = declarations("theorem unfinished (n : Nat) :\ntheorem complete : True := by trivial\n");
  assert.equal(entries[0].name, "unfinished");
  assert.equal(entries[0].statement, null);
  assert.equal(entries[1].statement, "theorem complete : True");
  assert.deepEqual(declarations('/- theorem hidden : True := by trivial'), []);
  assert.deepEqual(declarations('def text := "unterminated\ntheorem hidden : True := by trivial'), []);
  assert.deepEqual(declarations("theorem"), []);
});

test("all bundled main-result markers identify declarations with full statement previews", () => {
  function leanFiles(directory) {
    return fs.readdirSync(directory, { withFileTypes: true }).flatMap((entry) => {
      const file = path.join(directory, entry.name);
      return entry.isDirectory() ? leanFiles(file) : file.endsWith(".lean") ? [file] : [];
    });
  }
  const root = path.join(__dirname, "../examples");
  let markedFiles = 0;
  for (const file of leanFiles(root)) {
    const source = fs.readFileSync(file, "utf8");
    const entries = declarations(source);
    for (const entry of entries) {
      assert.doesNotMatch(entry.statement || "",
        /\bis_(?:OutputWithCost|Output|Execution|SummaryFrom|Summary|HeapTranscript|Transcript)_/,
        `${file}: ${entry.name} uses the public interface in its statement`);
    }
    const labels = [...source.matchAll(/^--\s*Main result:\s*(.+?)\s*$/gm)].map((match) => match[1]);
    if (!labels.length) continue;
    markedFiles++;
    const marked = entries.filter((entry) => entry.label);
    assert.deepEqual(marked.map((entry) => entry.label), labels, path.relative(root, file));
    for (const entry of marked) {
      assert.ok(entry.statement?.includes(entry.name), `${file}: ${entry.name} has a statement`);
      assert.ok(entry.line > 0, `${file}: ${entry.name} has a source line`);
    }
    const { container, outline } = surface();
    outline.setExamples([source]);
    outline.update(source);
    const buttons = mainButtons(container);
    assert.ok(buttons.length <= 3, `${file}: correctness and at most two runtime statements`);
    assert.ok(buttons.every((button) => ["Correctness", "Running time",
      "Running time (total)", "Running time (after sorting)"].includes(button.textContent)),
      `${file}: result buttons use short category names`);
  }
  assert.ok(markedFiles >= 30, "The public example collection exposes its main results");
});

test("main-result buttons preview exact statements and navigate only on request", () => {
  const { container, outline, jumps } = surface();
  outline.update("-- Main result: Exact result\n/-- Returns the supplied value. -/\ntheorem exact_value (n : Nat) : n = n := by rfl\n");
  assert.equal(container.hidden, false);
  assert.equal(tag(container, "H3")[0].textContent, "Main results");
  const button = mainButtons(container)[0];
  assert.equal(button.type, "button");
  assert.equal(button.getAttribute("aria-pressed"), "false");
  assert.equal(preview(container).hidden, true);
  button.click();
  assert.deepEqual(jumps, []);
  assert.equal(preview(container).hidden, false);
  assert.equal(button.getAttribute("aria-pressed"), "true");
  assert.equal(button.getAttribute("aria-controls"), preview(container).id);
  assert.ok(text(preview(container)).includes("Returns the supplied value."));
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem exact_value (n : Nat) : n = n");
  tag(preview(container), "BUTTON")[0].click();
  assert.deepEqual(jumps, [[3, 1]]);
});

test("a combined result has two short buttons sharing one exact statement", () => {
  const { container, outline, jumps } = surface();
  outline.update("-- Main result: Correctness and running time\n" +
    "theorem result (n : Nat) : n = n := by rfl\n");
  const buttons = mainButtons(container);
  assert.deepEqual(buttons.map((button) => button.textContent), ["Correctness", "Running time"]);
  for (const button of buttons) {
    button.click();
    assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem result (n : Nat) : n = n");
    assert.ok(buttons.every((item) => item.getAttribute("aria-pressed") === "true"));
    assert.equal(tag(container, "SELECT")[0].value, "0");
  }
  tag(preview(container), "BUTTON")[0].click();
  assert.deepEqual(jumps, [[2, 1]]);
  tag(container, "SELECT")[0].change("");
  assert.ok(buttons.every((button) => button.getAttribute("aria-pressed") === "false"));
});

test("each category appears once while alternate results remain in All theorems", () => {
  const { container, outline } = surface();
  outline.update("-- Main result: Correctness and running time\n" +
    "theorem first : True := by trivial\n" +
    "-- Main result: Correctness and running time\ntheorem second : True := by trivial\n");
  assert.deepEqual(mainButtons(container).map((button) => button.textContent), ["Correctness", "Running time"]);
  const select = tag(container, "SELECT")[0];
  assert.equal(tag(select, "OPTION").length, 3);
  select.change("1");
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem second : True");
  assert.ok(mainButtons(container).every((button) => button.getAttribute("aria-pressed") === "false"));
});

test("custom unmarked proofs remain navigable through the theorem chooser", () => {
  const { container, outline, jumps } = surface();
  outline.update("theorem helper : True := by trivial\nlemma unfinished :\n");
  assert.equal(tag(container, "H3")[0].textContent, "Main results");
  assert.match(text(container), /Main result:/);
  assert.equal(mainButtons(container).length, 0);
  const select = tag(container, "SELECT")[0];
  assert.equal(select.getAttribute("aria-label"), "Find a theorem");
  assert.equal(tag(select, "OPTION").length, 3);
  select.change("1");
  assert.match(text(preview(container)), /Open this declaration/);
  tag(preview(container), "BUTTON")[0].click();
  assert.deepEqual(jumps, [[2, 1]]);
  select.change("");
  assert.equal(preview(container).hidden, true);
});

test("source edits refresh statement text and navigation without switching duplicate theorem names", () => {
  const { container, outline, jumps } = surface();
  const source = "namespace A\ntheorem result : True := by trivial\nend A\n" +
    "namespace B\ntheorem result : 1 = 1 := rfl\nend B\n";
  outline.update(source);
  tag(container, "SELECT")[0].change("1");
  assert.match(text(preview(container)), /1 = 1/);
  outline.update("-- Added explanation\n" + source.replace("1 = 1", "2 = 2"));
  assert.match(text(preview(container)), /2 = 2/);
  assert.equal(tag(container, "SELECT")[0].value, "1");
  tag(preview(container), "BUTTON")[0].click();
  assert.deepEqual(jumps, [[6, 1]]);
  outline.update("theorem different : True := by trivial\n");
  assert.equal(preview(container).hidden, true);
  outline.update("def noTheorem := 1\n");
  assert.equal(container.hidden, false);
  assert.equal(tag(container, "H3")[0].textContent, "Main results");
  assert.match(text(container), /theorem/i);
});

test("the main-results panel remains visible and explains how to add results in an empty proof", () => {
  const { container, outline } = surface();
  outline.update("");
  assert.equal(container.hidden, false);
  assert.equal(tag(container, "H3")[0].textContent, "Main results");
  assert.match(text(container), /theorem/i);
  assert.match(text(container), /Load an example|write a theorem/);
});

test("bundled labels arrive after a recovered proof and ignore only comments and formatting", () => {
  const { container, outline, jumps } = surface();
  const canonical = "-- Main result: Exact result\n/-- Returns the supplied value. -/\n" +
    "theorem result (n : Nat) : n = n := by rfl\n";
  const recovered = "-- Saved personal explanation\ntheorem result (n : Nat) : n = n := by rfl\n";
  outline.update(recovered);
  assert.equal(mainButtons(container).length, 0);
  outline.setExamples([canonical]);
  assert.equal(mainButtons(container).length, 1);
  assert.equal(mainButtons(container)[0].textContent, "Exact result");
  mainButtons(container)[0].click();
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem result (n : Nat) : n = n");
  tag(preview(container), "BUTTON")[0].click();
  assert.deepEqual(jumps, [[2, 1]]);
  outline.update("/- Different /- nested -/ explanation. -/\n\n" +
    "theorem result\n    (n : Nat) : n = n := by\n  rfl\n");
  assert.equal(mainButtons(container).length, 1);
  assert.equal(mainButtons(container)[0].textContent, "Exact result");
  outline.update(recovered.replace("n = n", "n = 0"));
  assert.equal(mainButtons(container).length, 0);
});

test("known-example labels never match changed string, character, or quoted-name contents", () => {
  const cases = [
    ['theorem result : "a b" = "a b" := rfl\n', 'theorem result : "ab" = "ab" := rfl\n'],
    ["theorem result : '(' = '(' := rfl\n", "theorem result : ')' = ')' := rfl\n"],
    ["theorem «a b» : True := by trivial\n", "theorem «ab» : True := by trivial\n"],
    ['def value := "-- text"\ntheorem result : value = value := rfl\n',
      'def value := "-- other"\ntheorem result : value = value := rfl\n'],
  ];
  for (const [canonical, changed] of cases) {
    const { container, outline } = surface();
    const marker = "-- Main result: Exact result\n";
    const marked = canonical.replace("theorem ", marker + "theorem ");
    outline.setExamples([marked]);
    outline.update(canonical);
    assert.equal(mainButtons(container).length, 1, canonical);
    outline.update(changed);
    assert.equal(mainButtons(container).length, 0, changed);
  }
});

test("matching saved examples adopt current categories and remove obsolete helper highlights", () => {
  const { container, outline, jumps } = surface();
  const canonical = "theorem helper : True := by trivial\n" +
    "-- Main result: Correctness and running time\ntheorem result : True := by trivial\n";
  const saved = "-- Main result: Reusable call contract\ntheorem helper : True := by trivial\n" +
    "-- Main result: Output and exact costs\ntheorem result : True := by trivial\n";
  outline.update(saved);
  assert.equal(mainButtons(container).length, 2);
  outline.setExamples([canonical]);
  const buttons = mainButtons(container);
  assert.deepEqual(buttons.map((button) => button.textContent), ["Correctness", "Running time"]);
  buttons[1].click();
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem result : True");
  tag(preview(container), "BUTTON")[0].click();
  assert.deepEqual(jumps, [[4, 1]]);
  assert.equal(tag(tag(container, "SELECT")[0], "OPTION").length, 3);
  assert.equal(declarations(saved)[0].label, "Reusable call contract", "saved proof comments remain intact");
});

test("matching bundled analyses with no principal results clear obsolete highlights", () => {
  const { container, outline } = surface();
  const theorem = "theorem helper : True := by trivial\n";
  outline.setExamples([theorem]);
  outline.update("-- Main result: Reusable call contract\n" + theorem);
  assert.equal(mainButtons(container).length, 0);
  assert.equal(tag(tag(container, "SELECT")[0], "OPTION").length, 2);
});

test("matching bundled code uses curated labels even if its comments were customized", () => {
  const { container, outline } = surface();
  const theorem = "theorem result : True := by trivial\n";
  outline.setExamples(["-- Main result: Correctness\n" + theorem]);
  outline.update("-- Main result: My specification\n" + theorem);
  assert.equal(mainButtons(container)[0].textContent, "Correctness");
});

test("custom labels remain available when the proof does not match a bundled example", () => {
  const { container, outline } = surface();
  outline.setExamples(["-- Main result: Correctness\ntheorem result : True := by trivial\n"]);
  outline.update("-- Main result: My specification\ntheorem result : 1 = 1 := by rfl\n");
  assert.equal(mainButtons(container)[0].textContent, "My specification");
});

test("saved named results survive changed proof bodies and unrelated helper changes", () => {
  const { container, outline, jumps } = surface();
  const canonical = "namespace Sorting\nnamespace Merge\nsection Facts\n" +
    "theorem helper : True := by trivial\n" +
    "-- Main result: Correctness\ntheorem correct (n : Nat) : n = n := by rfl\n" +
    "-- Main result: Running time\ntheorem running_time : 1 ≤ 2 := by decide\n" +
    "end Facts\nend Merge\nend Sorting\n";
  const saved = "namespace Sorting\nnamespace Merge\nsection Facts\n" +
    "theorem correct (n : Nat) : n = n := by exact Eq.refl n\n" +
    "theorem additional_helper : True := by trivial\n" +
    "end Facts\nend Merge\nend Sorting\n";
  outline.update(saved);
  assert.equal(mainButtons(container).length, 0);
  outline.setExamples([canonical]);
  assert.deepEqual(mainButtons(container).map((button) => button.textContent), ["Correctness"]);
  mainButtons(container)[0].click();
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem correct (n : Nat) : n = n");
  tag(preview(container), "BUTTON")[0].click();
  assert.deepEqual(jumps, [[4, 1]]);
  assert.equal(declarations(saved)[0].label, null, "navigation leaves saved proof text unchanged");
});

test("named-result recovery recognizes legacy output aliases without replacing its preview", () => {
  const { container, outline } = surface();
  const canonical = "namespace MergeSortAnalysis\n-- Main result: Correctness\n" +
    "theorem correct (a result : Seq) (h : merge_sort.Returns (a, 0, 2) result) : result = result := by rfl\n" +
    "end MergeSortAnalysis\n";
  const saved = canonical.replace("-- Main result: Correctness\n", "")
    .replace("merge_sort.Returns", "is_Output_merge_sort").replace("by rfl", "by exact rfl");
  outline.setExamples([canonical]);
  outline.update(saved);
  assert.deepEqual(mainButtons(container).map((button) => button.textContent), ["Correctness"]);
  mainButtons(container)[0].click();
  assert.match(tag(preview(container), "PRE")[0].textContent, /is_Output_merge_sort/);
});

test("named-result recovery requires the same complete statement and namespace", () => {
  const { container, outline } = surface();
  outline.setExamples(["namespace Sorting\n-- Main result: Correctness\n" +
    "theorem correct (n : Nat) : n = n := by rfl\nend Sorting\n"]);
  const misses = [
    "namespace Other\ntheorem correct (n : Nat) : n = n := by exact rfl\nend Other\n",
    "namespace Sorting\ntheorem correct (n : Nat) : n = 0 := by omega\nend Sorting\n",
    "namespace Sorting\ntheorem correct (n : Nat) : n = n\nend Sorting\n",
    "namespace Sorting\nend Sorting\ntheorem correct (n : Nat) : n = n := by exact rfl\n",
  ];
  for (const source of misses) {
    outline.update(source);
    assert.equal(mainButtons(container).length, 0, source);
  }
});

test("named-result recovery preserves literal contents when normalizing legacy aliases", () => {
  const cases = [
    ['"is_Output_merge_sort"', '"merge_sort.Returns"'],
    ['"a b"', '"ab"'],
    ["'('", "')'"],
    ["«a b»", "«ab»"],
  ];
  for (const [before, after] of cases) {
    const { container, outline } = surface();
    const theorem = `theorem correct : ${before} = ${before} := by rfl\n`;
    outline.setExamples(["namespace Sorting\n-- Main result: Correctness\n" + theorem + "end Sorting\n"]);
    outline.update("namespace Sorting\n" + theorem.replaceAll(before, after) + "end Sorting\n");
    assert.equal(mainButtons(container).length, 0, `${before} → ${after}`);
  }
});

test("ambiguous named-result labels do not infer a category for an edited proof", () => {
  const { container, outline } = surface();
  const body = "theorem correct : True := by trivial\nend Sorting\n";
  outline.setExamples([
    "namespace Sorting\n-- Main result: Correctness\n" + body,
    "namespace Sorting\n-- Main result: Running time\n" + body,
  ]);
  outline.update("namespace Sorting\ntheorem correct : True := by exact True.intro\nend Sorting\n");
  assert.equal(mainButtons(container).length, 0);
});

test("global theorem recovery still requires a complete bundled-file match", () => {
  const { container, outline } = surface();
  outline.setExamples(["-- Main result: Correctness\ntheorem correct : True := by trivial\n"]);
  outline.update("theorem correct : True := by exact True.intro\n");
  assert.equal(mainButtons(container).length, 0);
});

test("untrusted theorem names, descriptions, and labels are displayed as text", () => {
  const { container, outline } = surface();
  outline.update("-- Main result: <img src=x onerror=run()>\n" +
    "/-- <script>run()</script> -/\ntheorem «<b>result</b>» : True := by trivial\n");
  mainButtons(container)[0].click();
  assert.ok(text(container).includes("<img src=x onerror=run()>"));
  assert.ok(text(container).includes("<script>run()</script>"));
  assert.ok(text(container).includes("«<b>result</b>»"));
  assert.ok(!descendants(container).some((node) => ["IMG", "SCRIPT", "B"].includes(node.tagName)));
});

test("the browser script exposes navigation without requiring a module loader", () => {
  const context = { window: {} };
  vm.runInNewContext(fs.readFileSync(path.join(__dirname, "../editor/proof-outline.js"), "utf8"), context);
  assert.equal(typeof context.window.Algo2LeanProofOutline.create, "function");
  assert.equal(typeof context.window.Algo2LeanProofOutline.declarations, "function");
});

test("Kruskal exposes distinct total and after-sorting running-time results", () => {
  const source = fs.readFileSync(path.join(__dirname, "../examples/kruskal/analysis/kruskal.lean"), "utf8");
  const { container, outline } = surface();
  outline.update(source);
  const buttons = mainButtons(container);
  assert.deepEqual(new Set(buttons.map((button) => button.textContent)),
    new Set(["Correctness", "Running time (total)", "Running time (after sorting)"]));
  assert.equal(buttons.length, 3, "helpers should not crowd out the two runtime statements");
  const total = buttons.find((button) => button.textContent === "Running time (total)");
  total.click();
  assert.match(tag(preview(container), "PRE")[0].textContent, /kruskal\.Call/);
  assert.doesNotMatch(tag(preview(container), "PRE")[0].textContent, /SortedPermutation/);
  const sorted = buttons.find((button) => button.textContent === "Running time (after sorting)");
  sorted.click();
  assert.match(tag(preview(container), "PRE")[0].textContent, /kruskal_sorted\.Call/);
  assert.match(tag(preview(container), "PRE")[0].textContent, /SortedPermutation/);
  assert.match(tag(preview(container), "PRE")[0].textContent, /KruskalSortedAnalysis\.runtimeScale/);
});
