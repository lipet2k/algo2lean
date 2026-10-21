"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const { normalizeEntries, groupEntries, render } = require("../editor/interface.js");

const FUNCTIONS = [{ name: "work", interface_entries: [
  { name: "work.Returns", category: "output", file_kind: "core",
    signature: "work.Returns (input : Int) (output : Int) : Prop",
    meaning: "A completed run returns this output.",
    arguments: [{ name: "input", type: "Int", meaning: "The input integer." },
      { name: "output", type: "Int", meaning: "The returned integer." }] },
  { name: "work.Call", category: "execution", file_kind: "core",
    signature: "work.Call (before : Heap) (input : Int) (after : Heap) (output : Int) : Prop",
    meaning: "The call completes under any caller stack.", arguments: [] },
  { name: "work.Run.eq_of_call", category: "helper", file_kind: "facts",
    signature: "work.Run.eq_of_call {before input after expected output result} : Prop",
    meaning: "A run agrees with the result specified by a call guarantee.", arguments: [] },
  { name: "work.ValidTranscript", category: "transcript", file_kind: "core",
    signature: "work.ValidTranscript (input : Int) (trace : Transcript) : Prop",
    meaning: "This is a valid finite history, possibly unfinished.", arguments: [] },
  { name: "work.At.charge", category: "location", file_kind: "points",
    signature: "work.At.charge (state : Configuration) : Prop", line: 3, column: 5,
    meaning: "The state is before the named statement, without requiring reachability.",
    arguments: [{ name: "state", type: "Configuration", meaning: "The configuration to inspect." }] },
  { name: "work.Local.i", category: "observation", file_kind: "points",
    signature: "work.Local.i (state : Configuration) : Option Int",
    meaning: "Read the initialized local variable, if available.", arguments: [] },
  { name: "work.ValidInput", category: "input", file_kind: "core",
    signature: "work.ValidInput (heap : Heap) (input : Int) : Prop",
    meaning: "The references in the input are valid in the supplied heap.", arguments: [] },
] }];

class Element {
  constructor(tag, ownerDocument) {
    this.tagName = tag.toUpperCase();
    this.ownerDocument = ownerDocument;
    this.children = [];
    this.attributes = new Map();
    this.listeners = new Map();
    this.textContent = "";
    this.hidden = false;
    this.open = false;
    this.focused = false;
  }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = children; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  getAttribute(name) { return this.attributes.get(name); }
  addEventListener(name, callback) { this.listeners.set(name, callback); }
  click() { this.listeners.get("click")?.({ target: this }); }
  focus() { this.focused = true; }
  keydown(key) {
    const event = { key, defaultPrevented: false, preventDefault() { this.defaultPrevented = true; } };
    this.listeners.get("keydown")?.(event);
    return event;
  }
}

function surface() {
  const document = { createElement: (tag) => new Element(tag, document) };
  return { document, container: document.createElement("div") };
}

function descendants(element) { return [element, ...element.children.flatMap(descendants)]; }
function withClass(container, name) {
  return descendants(container).filter((node) => (node.className || "").split(" ").includes(name));
}
function text(container) { return descendants(container).map((node) => node.textContent).join("\n"); }

test("compiler entries retain exact scoped signatures and group without modifying metadata", () => {
  const before = JSON.stringify(FUNCTIONS);
  const entries = normalizeEntries(FUNCTIONS);
  assert.equal(entries[0].signature, FUNCTIONS[0].interface_entries[0].signature);
  assert.equal(entries[4].line, 3);
  assert.equal(entries[4].column, 5);
  assert.deepEqual(groupEntries(entries).map((group) => [group.title, group.entries.length]), [
    ["Outputs", 1], ["Calls", 2], ["Transcripts", 1], ["Named locations and values", 2], ["Inputs", 1],
  ]);
  assert.equal(JSON.stringify(FUNCTIONS), before);
});

test("output and cost conversion helpers stay with output relations", () => {
  const groups = groupEntries(normalizeEntries([{ name: "work", interface_entries: [
    { name: "work.Returns", category: "output" },
    { name: "work.Returns.withCost", category: "output" },
    { name: "work.ReturnsWithCost.returns", category: "output" },
    { name: "work.Call.run", category: "helper" },
  ] }]));
  assert.deepEqual(groups.map((group) => [group.title, group.entries.map((entry) => entry.name)]), [
    ["Outputs", ["work.Returns", "work.Returns.withCost", "work.ReturnsWithCost.returns"]],
    ["Calls", ["work.Call.run"]],
  ]);
});

test("probability declarations form their own value group with the companion filename", () => {
  const members = ["outputProbability", "terminationProbability", "expectedCost", "returnProbability", "law", "outcome"];
  const functions = [{ name: "roll", interface_entries: members.map((member) => ({
    name: `roll.${member}`, category: "probability", file_kind: "probability",
    signature: `roll.${member} (heap : Heap) (input : Unit) : ENNReal`,
    meaning: "Uses the optional Mathlib probability companion.", arguments: [],
  })) }];
  const entries = normalizeEntries(functions);
  assert.ok(entries.every((entry) => entry.file_kind === "probability"));
  assert.deepEqual(groupEntries(entries).map((group) => [group.title, group.entries.length]), [["Probability", 6]]);
  const { container } = surface();
  render(container, functions, { probabilityFile: "DiceGeneratedProbability.lean" });
  const buttons = withClass(container, "interface-button");
  assert.equal(buttons.length, 6);
  assert.ok(buttons.every((button) => button.className.includes("interface-definition")));
  buttons[0].click();
  const panel = withClass(container, "interface-spec").find((candidate) => !candidate.hidden);
  assert.ok(text(panel).includes("DiceGeneratedProbability.lean"));
  assert.ok(text(panel).includes("Mathlib"));
  render(container, FUNCTIONS);
  assert.ok(!withClass(container, "interface-group-title").some((heading) => heading.textContent === "Probability"));
});

test("obsolete metadata prompts a compiler update instead of showing removed names", () => {
  const functions = [{ name: "Counter_add", display_name: "Counter.add",
    parameters: [{ name: "self", type: "Counter" }], return_type: "Int",
    cost_relation: "is_OutputWithCost_Counter_add",
    points: [{ name: "changed", relation: "At_Counter_add_changed", line: 8 }] }];
  const entries = normalizeEntries(functions);
  assert.deepEqual(entries, []);
  const { container } = surface();
  render(container, functions);
  assert.equal(withClass(container, "interface-button").length, 0);
  assert.match(text(container), /current compiler/);
  assert.doesNotMatch(text(container), /is_Output|At_Counter/);
  assert.ok(!text(container).includes("Counter →"));
});

test("generic dependencies and escaped names are displayed exactly as supplied", () => {
  const signature = "Counter.«match».Call (dependencies : Dependencies) (before : Heap) (input : ObjectRef) (after : Heap) (output : Int) : Prop";
  const { container } = surface();
  render(container, [{ name: "Counter_match", interface_entries: [{
    name: "Counter.«match».Call", category: "execution", signature, file_kind: "core",
    arguments: [{ name: "dependencies", type: "Dependencies", meaning: "Implementations of imported interfaces." }],
  }] }]);
  assert.equal(withClass(container, "interface-button")[0].textContent, "Counter.«match».Call");
  assert.ok(text(container).includes(signature));
  assert.ok(text(container).includes("Implementations of imported interfaces."));
});

test("argument details distinguish implicit binders from unnamed positional inputs", () => {
  const { container } = surface();
  render(container, [{ name: "work", interface_entries: [{ name: "work.At.start", category: "location",
    signature: "work.At.start : Configuration → Prop", arguments: [
      { name: "state", type: "Configuration", anonymous: true, meaning: "The configuration to inspect." },
    ] }, { name: "work.Call.run", category: "helper", signature: "work.Call.run {h : Heap} : Prop",
    arguments: [{ name: "h", type: "Heap", implicit: true, meaning: "The initial heap." }] }] }]);
  assert.ok(text(container).includes("(positional argument)"));
  assert.ok(text(container).includes("{h : Heap}"));
});

test("native category disclosures and entry buttons provide an inline accessible specification", () => {
  const { container } = surface();
  render(container, FUNCTIONS, { generatedFile: "WorkGenerated.lean", pointsFile: "WorkGeneratedPoints.lean", factsFile: "WorkFacts.lean" });
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
  button.click();
  assert.equal(panel.hidden, false);
  assert.equal(button.getAttribute("aria-expanded"), "true");
  assert.equal(withClass(container, "is-open").length, 1);
  assert.ok(text(panel).includes("input : Int"));
  assert.ok(text(panel).includes("The input integer."));
  assert.ok(text(panel).includes("WorkGenerated.lean"));
  const call = buttons.find((candidate) => candidate.textContent === "work.Call");
  call.click();
  assert.equal(panel.hidden, true);
  assert.equal(button.getAttribute("aria-expanded"), "false");
  assert.equal(panels.filter((candidate) => !candidate.hidden).length, 1);
  const callPanel = panels.find((candidate) => candidate.id === call.getAttribute("aria-controls"));
  const event = callPanel.keydown("Escape");
  assert.equal(event.defaultPrevented, true);
  assert.equal(callPanel.hidden, true);
  assert.equal(call.focused, true);
  assert.equal(withClass(container, "is-open").length, 0);
});

test("opening a location only shows its specification; source navigation is a separate action", () => {
  const { container } = surface();
  const jumps = [];
  render(container, FUNCTIONS, { pointsFile: "WorkPoints.lean", goToSource: (...position) => jumps.push(position) });
  const button = withClass(container, "interface-button").find((candidate) => candidate.textContent === "work.At.charge");
  button.click();
  assert.deepEqual(jumps, []);
  const panel = withClass(container, "interface-spec").find((candidate) => candidate.id === button.getAttribute("aria-controls"));
  assert.ok(text(panel).includes("WorkPoints.lean"));
  assert.ok(text(panel).includes("without requiring reachability"));
  withClass(panel, "interface-source-button")[0].click();
  assert.deepEqual(jumps, [[3, 5]]);
  assert.equal(panel.hidden, false);
});

test("rerendering removes stale entries and empty metadata hides the interface", () => {
  const { container, document } = surface();
  // Also support the editor's older test DOM, which has no ownerDocument.
  delete container.ownerDocument;
  render(container, FUNCTIONS, { document });
  const oldId = withClass(container, "interface-button")[0].id;
  render(container, [{ name: "fresh", output_relation: "fresh.Returns" }], { document });
  assert.equal(container.hidden, false);
  assert.ok(!text(container).includes("work.Call"));
  assert.notEqual(withClass(container, "interface-button")[0].id, oldId);
  render(container, [], { document });
  assert.equal(container.hidden, true);
  assert.equal(container.children.length, 0);
});

test("repeated observations are deduplicated and malformed metadata cannot add markup", () => {
  const entry = { name: "<script>run()</script>", category: "observation", file_kind: "points",
    signature: "<img src=x onerror=run()>", meaning: "<b>Meaning</b>", line: -1,
    arguments: [null, { name: "state", type: "<type>", meaning: "<em>Argument</em>" }] };
  const functions = [null, { name: "a", interface_entries: [entry, null, { name: "" }, entry] }];
  assert.equal(normalizeEntries(functions).length, 1);
  assert.equal(normalizeEntries(functions)[0].line, null);
  const { container } = surface();
  render(container, functions);
  assert.ok(text(container).includes("<script>run()</script>"));
  assert.ok(!descendants(container).some((node) => ["SCRIPT", "IMG", "B", "EM"].includes(node.tagName)));
});

test("the browser script exposes its renderer without requiring a module loader", () => {
  const context = { window: {} };
  vm.runInNewContext(fs.readFileSync(path.join(__dirname, "../editor/interface.js"), "utf8"), context);
  assert.equal(typeof context.window.Algo2LeanInterface.render, "function");
});
