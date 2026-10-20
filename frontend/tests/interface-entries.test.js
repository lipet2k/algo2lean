import { test } from "vitest";
import assert from "node:assert/strict";
import { normalizeEntries, groupEntries } from "../src/lib/interface.js";
import { FUNCTIONS } from "./support/interface-fixtures.js";

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

test("obsolete metadata yields no entries instead of removed names", () => {
  const functions = [{ name: "Counter_add", display_name: "Counter.add",
    parameters: [{ name: "self", type: "Counter" }], return_type: "Int",
    cost_relation: "is_OutputWithCost_Counter_add",
    points: [{ name: "changed", relation: "At_Counter_add_changed", line: 8 }] }];
  assert.deepEqual(normalizeEntries(functions), []);
});

test("repeated observations are deduplicated and malformed line numbers are dropped", () => {
  const entry = { name: "<script>run()</script>", category: "observation", file_kind: "points",
    signature: "<img src=x onerror=run()>", meaning: "<b>Meaning</b>", line: -1,
    arguments: [null, { name: "state", type: "<type>", meaning: "<em>Argument</em>" }] };
  const functions = [null, { name: "a", interface_entries: [entry, null, { name: "" }, entry] }];
  assert.equal(normalizeEntries(functions).length, 1);
  assert.equal(normalizeEntries(functions)[0].line, null);
  assert.equal(normalizeEntries(functions)[0].arguments.length, 1);
});


test("probability declarations preserve their file kind and own value group", () => {
  const members = ["outputProbability", "terminationProbability", "expectedCost", "returnProbability", "law", "outcome"];
  const functions = [{ name: "roll", interface_entries: members.map((member) => ({
    name: `roll.${member}`, category: "probability", file_kind: "probability",
    signature: `roll.${member} (heap : Heap) (input : Unit) : ENNReal`,
    meaning: "Uses the optional Mathlib probability companion.", arguments: [],
  })) }];
  const entries = normalizeEntries(functions);
  assert.ok(entries.every((entry) => entry.file_kind === "probability"));
  assert.deepEqual(groupEntries(entries).map((group) => [group.title, group.entries.length]), [["Probability", 6]]);
});
