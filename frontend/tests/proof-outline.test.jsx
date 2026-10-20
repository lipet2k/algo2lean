import { test } from "vitest";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fireEvent, render } from "@testing-library/react";
import { ProofOutline } from "../src/components/ProofOutline.jsx";
import { declarations } from "../src/lib/proof-outline.js";
import { leanFiles } from "./proof-outline-declarations.test.js";
import { ROOT } from "./support/paths.js";

function surface() {
  const jumps = [];
  let examples = [];
  const props = () => ({ exampleSources: examples, onJump: (...position) => jumps.push(position), catalog: new Map() });
  const view = render(<ProofOutline source="" {...props()} />);
  let current = "";
  const outline = {
    setExamples(sources) { examples = sources; view.rerender(<ProofOutline source={current} {...props()} />); },
    update(source) { current = source; view.rerender(<ProofOutline source={current} {...props()} />); },
  };
  return { container: view.container, outline, jumps, unmount: () => view.unmount() };
}

function descendants(element) { return [element, ...Array.from(element.children).flatMap(descendants)]; }
function text(element) { return element.textContent; }
function tag(element, name) { return descendants(element).filter((node) => node.tagName === name); }
function preview(element) { return element.querySelector('[id="analysis-theorem-preview"]'); }
function mainButtons(element) { return Array.from(element.querySelector(".proof-main-results").children); }
function select(element) { return tag(element, "SELECT")[0]; }
function change(element, value) { fireEvent.change(element, { target: { value } }); }

test("all bundled main-result markers identify declarations with full statement previews", () => {
  const root = path.join(ROOT, "examples");
  let markedFiles = 0;
  for (const file of leanFiles(root)) {
    const source = fs.readFileSync(file, "utf8");
    const labels = [...source.matchAll(/^--\s*Main result:\s*(.+?)\s*$/gm)].map((match) => match[1]);
    if (!labels.length) continue;
    markedFiles++;
    const { container, outline, unmount } = surface();
    outline.setExamples([source]);
    outline.update(source);
    const buttons = mainButtons(container);
    assert.ok(buttons.length <= 3, `${file}: correctness and at most two runtime statements`);
    assert.ok(buttons.every((button) => ["Correctness", "Running time",
      "Running time (total)", "Running time (after sorting)"].includes(button.textContent)),
      `${file}: result buttons use short category names`);
    unmount();
  }
  assert.ok(markedFiles >= 30, "The public example collection exposes its main results");
});

test("the first main result automatically previews its exact statement and navigates only on request", () => {
  const { container, outline, jumps } = surface();
  outline.update("theorem helper : True := by trivial\n" +
    "-- Main result: Exact result\n/-- Returns the supplied value. -/\ntheorem exact_value (n : Nat) : n = n := by rfl\n");
  assert.equal(container.querySelector('[id="analysis-outline"]').hidden, false);
  assert.equal(tag(container, "H3")[0].textContent, "Main results");
  const button = mainButtons(container)[0];
  assert.equal(button.type, "button");
  assert.deepEqual(jumps, []);
  assert.equal(preview(container).hidden, false);
  assert.equal(button.getAttribute("aria-pressed"), "true");
  assert.equal(button.getAttribute("aria-controls"), preview(container).id);
  assert.equal(select(container).value, "1");
  assert.ok(text(preview(container)).includes("Returns the supplied value."));
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem exact_value (n : Nat) : n = n");
  const initialPreview = text(preview(container));
  fireEvent.click(button);
  assert.equal(text(preview(container)), initialPreview, "the default preview matches clicking the result");
  assert.deepEqual(jumps, []);
  fireEvent.click(tag(preview(container), "BUTTON")[0]);
  assert.deepEqual(jumps, [[4, 1]]);
});

test("main-result updates preserve the chosen theorem and fall back when it is removed", () => {
  const { container, outline, jumps } = surface();
  const first = "-- Main result: Correctness\ntheorem correct : True := by trivial\n";
  const second = "-- Main result: Running time\ntheorem running_time : 1 = 1 := by rfl\n";
  outline.update(first + second);
  fireEvent.click(mainButtons(container)[1]);
  outline.update("-- Additional explanation\n" + first + second.replace("1 = 1", "2 = 2"));
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem running_time : 2 = 2");
  assert.equal(select(container).value, "1");
  assert.deepEqual(mainButtons(container).map((button) => button.getAttribute("aria-pressed")), ["false", "true"]);
  assert.deepEqual(jumps, []);
  outline.update(first);
  assert.equal(preview(container).hidden, false);
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem correct : True");
  assert.equal(select(container).value, "0");
  assert.equal(mainButtons(container)[0].getAttribute("aria-pressed"), "true");
  assert.deepEqual(jumps, []);
});

test("a combined result has two short buttons sharing one exact statement", () => {
  const { container, outline, jumps } = surface();
  outline.update("-- Main result: Correctness and running time\n" +
    "theorem result (n : Nat) : n = n := by rfl\n");
  const buttons = mainButtons(container);
  assert.deepEqual(buttons.map((button) => button.textContent), ["Correctness", "Running time"]);
  assert.ok(buttons.every((button) => button.getAttribute("aria-pressed") === "true"));
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem result (n : Nat) : n = n");
  for (const button of buttons) {
    fireEvent.click(button);
    assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem result (n : Nat) : n = n");
    assert.ok(buttons.every((item) => item.getAttribute("aria-pressed") === "true"));
    assert.equal(select(container).value, "0");
  }
  fireEvent.click(tag(preview(container), "BUTTON")[0]);
  assert.deepEqual(jumps, [[2, 1]]);
  change(select(container), "");
  assert.ok(buttons.every((button) => button.getAttribute("aria-pressed") === "false"));
});

test("each category appears once while alternate results remain in All theorems", () => {
  const { container, outline } = surface();
  outline.update("-- Main result: Correctness and running time\n" +
    "theorem first : True := by trivial\n" +
    "-- Main result: Correctness and running time\ntheorem second : True := by trivial\n");
  assert.deepEqual(mainButtons(container).map((button) => button.textContent), ["Correctness", "Running time"]);
  assert.equal(tag(select(container), "OPTION").length, 3);
  change(select(container), "1");
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem second : True");
  assert.ok(mainButtons(container).every((button) => button.getAttribute("aria-pressed") === "false"));
});

test("custom unmarked proofs remain navigable through the theorem chooser", () => {
  const { container, outline, jumps } = surface();
  outline.update("theorem helper : True := by trivial\nlemma unfinished :\n");
  assert.equal(tag(container, "H3")[0].textContent, "Main results");
  assert.match(text(container), /Main result:/);
  assert.equal(mainButtons(container).length, 0);
  assert.equal(preview(container).hidden, true);
  assert.equal(select(container).getAttribute("aria-label"), "Find a theorem");
  assert.equal(tag(select(container), "OPTION").length, 3);
  change(select(container), "1");
  assert.match(text(preview(container)), /Open this declaration/);
  fireEvent.click(tag(preview(container), "BUTTON")[0]);
  assert.deepEqual(jumps, [[2, 1]]);
  change(select(container), "");
  assert.equal(preview(container).hidden, true);
});

test("source edits refresh statement text and navigation without switching duplicate theorem names", () => {
  const { container, outline, jumps } = surface();
  const source = "namespace A\ntheorem result : True := by trivial\nend A\n" +
    "namespace B\ntheorem result : 1 = 1 := rfl\nend B\n";
  outline.update(source);
  change(select(container), "1");
  assert.match(text(preview(container)), /1 = 1/);
  outline.update("-- Added explanation\n" + source.replace("1 = 1", "2 = 2"));
  assert.match(text(preview(container)), /2 = 2/);
  assert.equal(select(container).value, "1");
  fireEvent.click(tag(preview(container), "BUTTON")[0]);
  assert.deepEqual(jumps, [[6, 1]]);
  outline.update("theorem different : True := by trivial\n");
  assert.equal(preview(container).hidden, true);
  outline.update("def noTheorem := 1\n");
  assert.equal(container.querySelector('[id="analysis-outline"]').hidden, false);
  assert.equal(tag(container, "H3")[0].textContent, "Main results");
  assert.match(text(container), /theorem/i);
});

test("the main-results panel remains visible and explains how to add results in an empty proof", () => {
  const { container, outline } = surface();
  outline.update("");
  assert.equal(container.querySelector('[id="analysis-outline"]').hidden, false);
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
  assert.equal(preview(container).hidden, false);
  assert.equal(mainButtons(container)[0].getAttribute("aria-pressed"), "true");
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem result (n : Nat) : n = n");
  fireEvent.click(tag(preview(container), "BUTTON")[0]);
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
    const { container, outline, unmount } = surface();
    const marker = "-- Main result: Exact result\n";
    const marked = canonical.replace("theorem ", marker + "theorem ");
    outline.setExamples([marked]);
    outline.update(canonical);
    assert.equal(mainButtons(container).length, 1, canonical);
    outline.update(changed);
    assert.equal(mainButtons(container).length, 0, changed);
    unmount();
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
  fireEvent.click(buttons[1]);
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem result : True");
  fireEvent.click(tag(preview(container), "BUTTON")[0]);
  assert.deepEqual(jumps, [[4, 1]]);
  assert.equal(tag(select(container), "OPTION").length, 3);
  assert.equal(declarations(saved)[0].label, "Reusable call contract", "saved proof comments remain intact");
});

test("matching bundled analyses with no principal results clear obsolete highlights", () => {
  const { container, outline } = surface();
  const theorem = "theorem helper : True := by trivial\n";
  outline.setExamples([theorem]);
  outline.update("-- Main result: Reusable call contract\n" + theorem);
  assert.equal(mainButtons(container).length, 0);
  assert.equal(tag(select(container), "OPTION").length, 2);
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
  fireEvent.click(mainButtons(container)[0]);
  assert.equal(tag(preview(container), "PRE")[0].textContent, "theorem correct (n : Nat) : n = n");
  fireEvent.click(tag(preview(container), "BUTTON")[0]);
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
  fireEvent.click(mainButtons(container)[0]);
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
    const { container, outline, unmount } = surface();
    const theorem = `theorem correct : ${before} = ${before} := by rfl\n`;
    outline.setExamples(["namespace Sorting\n-- Main result: Correctness\n" + theorem + "end Sorting\n"]);
    outline.update("namespace Sorting\n" + theorem.replaceAll(before, after) + "end Sorting\n");
    assert.equal(mainButtons(container).length, 0, `${before} → ${after}`);
    unmount();
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
  fireEvent.click(mainButtons(container)[0]);
  assert.ok(text(container).includes("<img src=x onerror=run()>"));
  assert.ok(text(container).includes("<script>run()</script>"));
  assert.ok(text(container).includes("«<b>result</b>»"));
  assert.ok(!descendants(container).some((node) => ["IMG", "SCRIPT", "B"].includes(node.tagName)));
});

test("Kruskal exposes distinct total and after-sorting running-time results", () => {
  const source = fs.readFileSync(path.join(ROOT, "examples/kruskal/analysis/kruskal.lean"), "utf8");
  const { container, outline } = surface();
  outline.update(source);
  const buttons = mainButtons(container);
  assert.deepEqual(new Set(buttons.map((button) => button.textContent)),
    new Set(["Correctness", "Running time (total)", "Running time (after sorting)"]));
  assert.equal(buttons.length, 3, "helpers should not crowd out the two runtime statements");
  const total = buttons.find((button) => button.textContent === "Running time (total)");
  fireEvent.click(total);
  assert.match(tag(preview(container), "PRE")[0].textContent, /kruskal\.Call/);
  assert.doesNotMatch(tag(preview(container), "PRE")[0].textContent, /SortedPermutation/);
  const sorted = buttons.find((button) => button.textContent === "Running time (after sorting)");
  fireEvent.click(sorted);
  assert.match(tag(preview(container), "PRE")[0].textContent, /kruskal_sorted\.Call/);
  assert.match(tag(preview(container), "PRE")[0].textContent, /SortedPermutation/);
  assert.match(tag(preview(container), "PRE")[0].textContent, /KruskalSortedAnalysis\.runtimeScale/);
});
