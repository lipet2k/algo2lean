import { test } from "vitest";
import assert from "node:assert/strict";
import { fireEvent, render } from "@testing-library/react";
import { InterfacePanel } from "../src/components/InterfacePanel.jsx";
import { createCatalog } from "../src/lib/interface.js";
import { FUNCTIONS } from "./support/interface-fixtures.js";

function surface(functions, options = {}) {
  const { key, ...props } = options;
  const view = render(<InterfacePanel key={key} functions={functions} catalog={createCatalog(functions)} {...props} />);
  return { view, container: view.container };
}

function descendants(element) { return [element, ...Array.from(element.children).flatMap(descendants)]; }
function withClass(container, name) {
  return descendants(container).filter((node) => (node.className || "").split(" ").includes(name));
}
function text(container) { return container.textContent; }

test("obsolete metadata prompts a compiler update instead of showing removed names", () => {
  const functions = [{ name: "Counter_add", display_name: "Counter.add",
    parameters: [{ name: "self", type: "Counter" }], return_type: "Int",
    cost_relation: "is_OutputWithCost_Counter_add",
    points: [{ name: "changed", relation: "At_Counter_add_changed", line: 8 }] }];
  const { container } = surface(functions);
  assert.equal(withClass(container, "interface-button").length, 0);
  assert.match(text(container), /current compiler/);
  assert.doesNotMatch(text(container), /is_Output|At_Counter/);
  assert.ok(!text(container).includes("Counter →"));
});

test("generic dependencies and escaped names are displayed exactly as supplied", () => {
  const signature = "Counter.«match».Call (dependencies : Dependencies) (before : Heap) (input : ObjectRef) (after : Heap) (output : Int) : Prop";
  const { container } = surface([{ name: "Counter_match", interface_entries: [{
    name: "Counter.«match».Call", category: "execution", signature, file_kind: "core",
    arguments: [{ name: "dependencies", type: "Dependencies", meaning: "Implementations of imported interfaces." }],
  }] }]);
  assert.equal(withClass(container, "interface-button")[0].textContent, "Counter.«match».Call");
  assert.ok(text(container).includes(signature));
  assert.ok(text(container).includes("Implementations of imported interfaces."));
});

test("argument details distinguish implicit binders from unnamed positional inputs", () => {
  const { container } = surface([{ name: "work", interface_entries: [{ name: "work.At.start", category: "location",
    signature: "work.At.start : Configuration → Prop", arguments: [
      { name: "state", type: "Configuration", anonymous: true, meaning: "The configuration to inspect." },
    ] }, { name: "work.Call.run", category: "helper", signature: "work.Call.run {h : Heap} : Prop",
    arguments: [{ name: "h", type: "Heap", implicit: true, meaning: "The initial heap." }] }] }]);
  assert.ok(text(container).includes("(positional argument)"));
  assert.ok(text(container).includes("{h : Heap}"));
});

test("native category disclosures and entry buttons provide an inline accessible specification", () => {
  const { container } = surface(FUNCTIONS, { generatedFile: "WorkGenerated.lean", pointsFile: "WorkGeneratedPoints.lean", factsFile: "WorkFacts.lean" });
  const groups = withClass(container, "interface-group");
  assert.ok(groups.every((group) => group.tagName === "DETAILS" && group.children[0].tagName === "SUMMARY"));
  assert.deepEqual(groups.map((group) => group.open), [true, false, false, false, false]);
  const buttons = withClass(container, "interface-button");
  const panels = withClass(container, "interface-spec");
  assert.ok(buttons.every((button) => button.tagName === "BUTTON" && button.type === "button"));
  assert.ok(panels.every((panel) => panel.hidden));
  const button = buttons[0];
  const panel = panels[0];
  assert.equal(button.getAttribute("aria-controls"), panel.id);
  assert.equal(panel.getAttribute("aria-labelledby"), button.id);
  assert.equal(panel.getAttribute("role"), "region");
  fireEvent.click(button);
  assert.equal(panel.hidden, false);
  assert.equal(button.getAttribute("aria-expanded"), "true");
  assert.equal(withClass(container, "is-open").length, 1);
  assert.ok(text(panel).includes("input : Int"));
  assert.ok(text(panel).includes("The input integer."));
  assert.ok(text(panel).includes("WorkGenerated.lean"));
  const call = buttons.find((candidate) => candidate.textContent === "work.Call");
  fireEvent.click(call);
  assert.equal(panel.hidden, true);
  assert.equal(button.getAttribute("aria-expanded"), "false");
  assert.equal(panels.filter((candidate) => !candidate.hidden).length, 1);
  const callPanel = panels.find((candidate) => candidate.id === call.getAttribute("aria-controls"));
  const prevented = !fireEvent.keyDown(callPanel, { key: "Escape" });
  assert.equal(prevented, true);
  assert.equal(callPanel.hidden, true);
  assert.equal(document.activeElement, call);
  assert.equal(withClass(container, "is-open").length, 0);
});

test("opening a location only shows its specification; source navigation is a separate action", () => {
  const jumps = [];
  const { container } = surface(FUNCTIONS, { pointsFile: "WorkPoints.lean", onGoToSource: (...position) => jumps.push(position) });
  const button = withClass(container, "interface-button").find((candidate) => candidate.textContent === "work.At.charge");
  fireEvent.click(button);
  assert.deepEqual(jumps, []);
  const panel = withClass(container, "interface-spec").find((candidate) => candidate.id === button.getAttribute("aria-controls"));
  assert.ok(text(panel).includes("WorkPoints.lean"));
  assert.ok(text(panel).includes("without requiring reachability"));
  fireEvent.click(withClass(panel, "interface-source-button")[0]);
  assert.deepEqual(jumps, [[3, 5]]);
  assert.equal(panel.hidden, false);
});

test("rerendering removes stale entries and empty metadata hides the interface", () => {
  const { view, container } = surface(FUNCTIONS, { key: 1 });
  const oldId = withClass(container, "interface-button")[0].id;
  const fresh = [{ name: "fresh", output_relation: "fresh.Returns" }];
  view.rerender(<InterfacePanel key={2} functions={fresh} catalog={createCatalog(fresh)} />);
  assert.equal(container.querySelector('[id="relations"]').hidden, false);
  assert.ok(!text(container).includes("work.Call"));
  assert.notEqual(withClass(container, "interface-button")[0].id, oldId);
  view.rerender(<InterfacePanel key={3} functions={[]} catalog={createCatalog([])} />);
  assert.equal(container.querySelector('[id="relations"]').hidden, true);
  assert.equal(container.querySelector('[id="relations"]').children.length, 0);
});

test("repeated observations are deduplicated and malformed metadata cannot add markup", () => {
  const entry = { name: "<script>run()</script>", category: "observation", file_kind: "points",
    signature: "<img src=x onerror=run()>", meaning: "<b>Meaning</b>", line: -1,
    arguments: [null, { name: "state", type: "<type>", meaning: "<em>Argument</em>" }] };
  const functions = [null, { name: "a", interface_entries: [entry, null, { name: "" }, entry] }];
  const { container } = surface(functions);
  assert.equal(withClass(container, "interface-button").length, 1);
  assert.ok(text(container).includes("<script>run()</script>"));
  assert.ok(!descendants(container).some((node) => ["SCRIPT", "IMG", "B", "EM"].includes(node.tagName)));
});
