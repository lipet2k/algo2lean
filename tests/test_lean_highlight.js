"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const { tokenize, createCatalog, highlight, classify } = require("../editor/interface.js");

const FUNCTIONS = [{ name: "work", interface_entries: [
  { name: "work.Returns", category: "output", signature: "work.Returns (input output : Int) : Prop" },
  { name: "work.ReturnsWithCost", category: "output", signature: "work.ReturnsWithCost (input output : Int) (costs : Clocks) : Prop" },
  { name: "work.Returns.withCost", category: "output", signature: "work.Returns.withCost {input output} : Prop" },
  { name: "work.ReturnsWithCost.returns", category: "output", signature: "work.ReturnsWithCost.returns {input output costs} : Prop" },
  { name: "work.Call", category: "execution", signature: "work.Call (before : Heap) (input : Int) (after : Heap) (output : Int) : Prop" },
  { name: "work.Run", category: "execution", signature: "work.Run (before : Heap) (input : Int) (after : Heap) (output : Int) : Prop" },
  { name: "work.Call.run", category: "helper", signature: "work.Call.run {before input after output} : Prop" },
  { name: "work.Run.eq_of_call", category: "helper", signature: "work.Run.eq_of_call {before input after expected output} : Prop", file_kind: "facts" },
  { name: "work.ValidTranscript", category: "transcript", signature: "work.ValidTranscript (input : Int) (trace : Transcript) : Prop" },
  { name: "work.ValidInput", category: "input", signature: "work.ValidInput (heap : Heap) (input : Int) : Prop" },
  { name: "work.initial", category: "input", signature: "work.initial (heap : Heap) (input : Int) : Configuration" },
  { name: "work.load", category: "input", signature: "work.load (input : Int) : Heap × Int" },
  { name: "work.At.Call", category: "location", signature: "work.At.Call : Configuration → Prop", file_kind: "points" },
  { name: "work.Local.Returns", category: "observation", signature: "work.Local.Returns : Configuration → Option Int", file_kind: "points" },
  { name: "work.Element.Call", category: "observation", signature: "work.Element.Call (state : Configuration) (index : Int) : Option Int", file_kind: "points" },
] }];

const GENERATED = `namespace Algo.worker
namespace Algo2LeanGenerated
inductive Frame where
  | fn_work : Nat → Frame
inductive Step : Nat → Nat → Prop where
  | done : Step 0 1
end Algo2LeanGenerated
open Algo2LeanGenerated
def work.ValidInput (_h : Heap) (_input : Int) : Prop := True
def work.initial (h : Heap) (input : Int) : Configuration := start h input
def work.Run (h : Heap) (input : Int) (h' : Heap) (output : Int) : Prop := True
def work.Call (h : Heap) (input : Int) (h' : Heap) (output : Int) : Prop := True
def work.Returns (my_input my_output : Int) : Prop := True
def work.ReturnsWithCost (my_input my_output : Int) (costs : Clocks) : Prop := True
theorem work.Call.run {before input after output}
    (call : work.Call before input after output) : work.Run before input after output := by
  trivial
theorem work.ReturnsWithCost.returns {input output costs}
    (run : work.ReturnsWithCost input output costs) : work.Returns input output := by
  trivial
theorem work.Returns.withCost {input output}
    (run : work.Returns input output) : ∃ costs, work.ReturnsWithCost input output costs := by
  exact ⟨{}, True.intro⟩
end Algo.worker
`;

function unescapeHtml(value) {
  return value.replace(/&(amp|lt|gt|quot|#39);/g, (match, entity) => ({
    amp: "&", lt: "<", gt: ">", quot: '"', "#39": "'",
  })[entity]);
}

function visibleText(html) {
  return unescapeHtml(html.replace(/<[^>]*>/g, ""));
}

function coloredNames(html) {
  const result = [];
  for (const match of html.matchAll(/<span\b([^>]*)>([^<]*)<\/span>/g)) {
    const kind = match[1].match(/\binterface-(proposition|theorem|definition|type)\b/)?.[1];
    if (kind) result.push({ text: unescapeHtml(match[2]), kind });
  }
  return result;
}

function names(source, catalog) {
  return coloredNames(highlight(source, catalog));
}

function syntaxTypes(html) {
  return [...html.matchAll(/<span\b([^>]*)>([^<]*)<\/span>/g)]
    .filter((match) => /\btoken-type\b/.test(match[1]))
    .map((match) => unescapeHtml(match[2]));
}

test("interface colors distinguish declarations within the same display group", () => {
  const expected = ["proposition", "proposition", "theorem", "theorem", "proposition", "proposition",
    "theorem", "theorem", "proposition", "proposition", "definition", "definition", "proposition",
    "definition", "definition"];
  assert.deepEqual(FUNCTIONS[0].interface_entries.map(classify), expected);
  assert.equal(classify({ name: "Returns.Returns", category: "output" }), "proposition");
  assert.equal(classify({ name: "Box.Call.run", category: "helper" }), "theorem");
});

test("probability values retain their interface color in generated and importing Lean", () => {
  const members = ["outcome", "law", "returnProbability", "outputProbability", "terminationProbability", "expectedCost"];
  const source = "namespace Algo.dice\n" + members.map((member) =>
    `def roll.${member} : ENNReal := 0\n`).join("") + "end Algo.dice\n";
  const catalog = createCatalog([], [source]);
  assert.deepEqual(names(source, catalog), members.map((member) => ({ text: `roll.${member}`, kind: "definition" })));
  const proof = "open Algo.dice\n" + members.map((member) => `#check roll.${member}\n`).join("");
  assert.deepEqual(names(proof, catalog), members.map((member) => ({ text: `roll.${member}`, kind: "definition" })));
  assert.deepEqual(syntaxTypes(highlight("ENNReal MeasureTheory.Measure Algo2LeanProbability.Run", catalog)),
    ["ENNReal", "MeasureTheory.Measure", "Algo2LeanProbability.Run"]);
  assert.equal(classify({ name: "roll.expectedCost", category: "probability" }), "definition");
});

test("token offsets preserve every original character, including Unicode and line endings", () => {
  const source = "namespace «Wrapped»\r\n\tdef Box.«match».Call (α₁ : Int) (heap' : Heap) : Prop := α₁ = 12\r\nend «Wrapped»\n";
  const tokens = tokenize(source);
  assert.ok(tokens.length > 0);
  assert.equal(tokens.map((token) => token.text).join(""), source);
  let cursor = 0;
  for (const token of tokens) {
    assert.equal(token.start, cursor);
    assert.ok(token.end > token.start);
    assert.equal(token.text, source.slice(token.start, token.end));
    cursor = token.end;
  }
  assert.equal(cursor, source.length);
  const identifiers = tokens.filter((token) => token.kind === "identifier").map((token) => token.text);
  assert.ok(identifiers.includes("Box.«match».Call"));
  assert.ok(identifiers.includes("α₁"));
  assert.ok(identifiers.includes("heap'"));
  assert.equal(tokens.find((token) => token.text === "namespace").kind, "keyword");
  assert.equal(tokens.find((token) => token.text === "12").kind, "number");
});

test("nested comments, escaped strings, and character literals never become interface identifiers", () => {
  const source = String.raw`-- work.Returns
/- work.Call /- work.Returns.withCost -/ work.Run -/
"work.Returns \" work.Call"
'"' '\n' '\''
work.Returns heap'
`;
  const identifiers = tokenize(source).filter((token) => token.kind === "identifier").map((token) => token.text);
  assert.deepEqual(identifiers, ["work.Returns", "heap'"]);
  assert.deepEqual(names(source, createCatalog(FUNCTIONS, [])), [
    { text: "work.Returns", kind: "proposition" },
  ]);
});

test("quoted identifier components remain opaque to punctuation and comment scanning", () => {
  const source = "«name--with/-punctuation».«part.with.dot» _root_.«_root_·».Returns";
  const tokens = tokenize(source);
  assert.equal(tokens.map((token) => token.text).join(""), source);
  assert.deepEqual(tokens.filter((token) => token.kind === "identifier").map((token) => token.text), [
    "«name--with/-punctuation».«part.with.dot»", "_root_.«_root_·».Returns",
  ]);
  assert.ok(!tokens.some((token) => token.kind === "comment"));
});

test("metadata colors whole public names and retains all conversion helpers", () => {
  const original = JSON.stringify(FUNCTIONS);
  const catalog = createCatalog(FUNCTIONS, []);
  for (const entry of FUNCTIONS[0].interface_entries) {
    assert.deepEqual(names(entry.name, catalog), [{ text: entry.name, kind: classify(entry) }]);
  }
  assert.equal(JSON.stringify(FUNCTIONS), original);
  assert.deepEqual(names("work.ReturnsExtra work.ReturnsWithCostExtra work.Call.runExtra other.work.Returns Returns Call", catalog), []);
});

test("qualified names resolve declared generated namespaces without matching arbitrary suffixes", () => {
  const catalog = createCatalog([], [GENERATED]);
  const source = `_root_.Algo.worker.work.Returns Algo.worker.work.Call
Algo.worker.work.Returns.withCost Algo.worker.work.initial
Unknown.work.Returns Algo.other.work.Call work.Returns
Algo.worker.Algo2LeanGenerated.Step Algo.worker.Algo2LeanGenerated.Frame
`;
  assert.deepEqual(names(source, catalog), [
    { text: "_root_.Algo.worker.work.Returns", kind: "proposition" },
    { text: "Algo.worker.work.Call", kind: "proposition" },
    { text: "Algo.worker.work.Returns.withCost", kind: "theorem" },
    { text: "Algo.worker.work.initial", kind: "definition" },
    { text: "Algo.worker.Algo2LeanGenerated.Step", kind: "proposition" },
    { text: "Algo.worker.Algo2LeanGenerated.Frame", kind: "type" },
  ]);
});

test("local namespaces and opened imported modules resolve source-facing references", () => {
  const imported = `namespace Algo.library
def imported.Call (h : Heap) (input : Int) (h' : Heap) (output : Int) : Prop := True
theorem imported.Call.run {h input h' output}
    (call : imported.Call h input h' output) : True := True.intro
end Algo.library
`;
  const catalog = createCatalog([], [GENERATED, imported]);
  assert.deepEqual(names(`namespace Algo.worker
work.Returns work.Call.run
end Algo.worker
open Algo.library
imported.Call imported.Call.run Algo.worker.work.Call
`, catalog), [
    { text: "work.Returns", kind: "proposition" },
    { text: "work.Call.run", kind: "theorem" },
    { text: "imported.Call", kind: "proposition" },
    { text: "imported.Call.run", kind: "theorem" },
    { text: "Algo.worker.work.Call", kind: "proposition" },
  ]);
});

test("namespace-local open directives do not leak into later scopes", () => {
  const catalog = createCatalog([], [GENERATED]);
  assert.deepEqual(names(`namespace Proof
open Algo.worker
work.Returns
end Proof
work.Returns
namespace Algo
worker.work.Call
end Algo
worker.work.Call
`, catalog), [
    { text: "work.Returns", kind: "proposition" },
    { text: "worker.work.Call", kind: "proposition" },
  ]);
});

test("object methods, constructors, quoted source names, and named observations keep their kinds", () => {
  const generated = `namespace «Wrapped»
def Box.Call (h : Heap) (input : Unit) (h' : Heap) (output : Ref_Box) : Prop := True
def Box.«match».Call (h : Heap) (input : Ref_Box) (h' : Heap) (output : Int) : Prop := True
def «lemma».At.«by» : Configuration → Prop
  | _ => True
def «lemma».Local.«theorem» : Configuration → Option Int
  | _ => none
def «lemma».Element.Call (state : Configuration) (index : Int) : Option Int := none
end «Wrapped»
`;
  const catalog = createCatalog([], [generated]);
  const source = `open «Wrapped»
Box.Call Box.«match».Call «lemma».At.«by» «lemma».Local.«theorem» «lemma».Element.Call
_root_.«Wrapped».Box.«match».Call
`;
  assert.deepEqual(names(source, catalog), [
    { text: "Box.Call", kind: "proposition" },
    { text: "Box.«match».Call", kind: "proposition" },
    { text: "«lemma».At.«by»", kind: "proposition" },
    { text: "«lemma».Local.«theorem»", kind: "definition" },
    { text: "«lemma».Element.Call", kind: "definition" },
    { text: "_root_.«Wrapped».Box.«match».Call", kind: "proposition" },
  ]);
});

test("declaration discovery ignores public-looking names inside comments and literals", () => {
  const generated = `/-
def ghost.Returns (input output : Int) : Prop := True
/- theorem ghost.Call.run : True := True.intro -/
-/
def message : String := "def fake.Returns : Prop := True"
def actual.Returns (input output : Int) : Prop := True
`;
  assert.deepEqual(names("ghost.Returns ghost.Call.run fake.Returns actual.Returns", createCatalog([], [generated])), [
    { text: "actual.Returns", kind: "proposition" },
  ]);
});

test("highlighting only changes markup and escapes HTML in code, comments, and metadata", () => {
  const source = '\twork.Returns (<value> : Int)\r\n-- <img src=x onerror="run()"> & work.Call\n"<script>work.Call</script>"\n';
  const html = highlight(source, createCatalog(FUNCTIONS, []));
  assert.equal(visibleText(html), source);
  assert.doesNotMatch(html, /<(?:img|script)\b/i);
  assert.match(html, /&lt;img/);
  assert.match(html, /&amp;/);
  assert.deepEqual(coloredNames(html), [{ text: "work.Returns", kind: "proposition" }]);
  const malformed = [{ name: "bad", interface_entries: [
    { name: '<img src=x onerror="run()">', category: "output", signature: "<script>run()</script>" },
  ] }];
  const unsafeSource = '<img src=x onerror="run()">';
  const unsafeHtml = highlight(unsafeSource, createCatalog(malformed, []));
  assert.equal(visibleText(unsafeHtml), unsafeSource);
  assert.doesNotMatch(unsafeHtml, /<(?:img|script)\b/i);
});

test("empty and unfinished editor input still round-trips safely", () => {
  const catalog = createCatalog(FUNCTIONS, []);
  for (const source of ["", " ", "/- work.Returns", '"work.Call', "«work.Returns", "work.Returns\r\n\t"]) {
    assert.equal(visibleText(highlight(source, catalog)), source);
    assert.equal(tokenize(source).map((token) => token.text).join(""), source);
  }
});

test("advanced execution and typed storage are curated, while generated slots stay private", () => {
  const source = `namespace Algo.demo.Algo2LeanGenerated
structure State_work where
  v0 : Int
inductive Frame where
  | fn_work : Nat → State_work → Frame
abbrev Configuration := Algo2LeanCore.Config Heap Frame Result
inductive Step : Configuration → Configuration → Prop where
  | done : Step a b
abbrev Ref_Box := ObjectRef
def is_Box (h : Heap) (r : Ref_Box) : Prop := True
def field_Box_value (h : Heap) (r : Ref_Box) : Option Int := none
@[simp] theorem field_Box_value_set (h : Heap) (r : Ref_Box) (v : Int)
    (valid : is_Box h r) : field_Box_value h r = some v := by sorry
def seq_Box : SequenceType Ref_Box where
  name := "Box"
end Algo.demo.Algo2LeanGenerated
`;
  const catalog = createCatalog([], [source]);
  const body = "Step Configuration Frame State_work Frame.fn_work s.v0 Ref_Box is_Box field_Box_value field_Box_value_set seq_Box";
  assert.deepEqual(coloredNames(highlight(body, catalog, "open Algo.demo.Algo2LeanGenerated\n")), [
    { text: "Step", kind: "proposition" }, { text: "Configuration", kind: "type" },
    { text: "Frame", kind: "type" }, { text: "Ref_Box", kind: "type" },
    { text: "is_Box", kind: "proposition" }, { text: "field_Box_value", kind: "definition" },
    { text: "field_Box_value_set", kind: "theorem" }, { text: "seq_Box", kind: "definition" },
  ]);
  const getter = catalog.extraEntries.find(x => x.name.endsWith('.field_Box_value'));
  assert.equal(getter.category, 'storage');
  assert.equal(getter.signature, 'def field_Box_value (h : Heap) (r : Ref_Box) : Option Int');
  assert.match(catalog.extraEntries.find(x => x.name.endsWith('.Step')).meaning, /no whole execution/);
  assert.equal(catalog.extraEntries.some(x => /State_work|fn_work|\.v0/.test(x.name)), false);
});

test("real shared-library declarations supply exact headers and nested namespace kinds", () => {
  const fs = require('node:fs');
  const path = require('node:path');
  const library = fs.readFileSync(path.join(__dirname, '../Algo2Lean.lean'), 'utf8');
  const catalog = createCatalog([], [library]);
  assert.equal(catalog.get('Algo2LeanGenerated.SequenceType.valid'), 'proposition');
  assert.equal(catalog.get('Algo2LeanGenerated.SequenceType.get'), 'definition');
  assert.equal(catalog.get('Algo2LeanCore.Config.heap'), 'definition');
  for (const name of ['Heap', 'Seq', 'SeqRef', 'ObjectRef', 'CollectionRef', 'Clocks', 'SequenceType']) {
    assert.equal(catalog.get('Algo2LeanGenerated.' + name), 'type');
  }
  assert.equal(catalog.get('Algo2LeanCore.Config'), 'type');
  assert.equal(catalog.get('Algo2LeanCore.Stack'), 'type');
  const headers = new Map(catalog.extraEntries.map(x => [x.name, x.signature]));
  assert.equal(headers.get('Algo2LeanCore.Config.heap'), 'def Config.heap : Config Heap Frame Result → Heap');
  assert.equal(headers.get('Algo2LeanGenerated.SequenceType.valid'), 'def valid (h : Heap) (ref : CollectionRef) : Prop');
  assert.equal(headers.get('Algo2LeanGenerated.SeqRef'), 'abbrev SeqRef := Nat');
  assert.equal(catalog.get('Algo2LeanGenerated.ObjectValue.asInt'), undefined);
});

test("previews retain preceding open and namespace context without displaying it", () => {
  const catalog = createCatalog([], [GENERATED]);
  const prefix = 'namespace Algo.worker\nopen Algo2LeanGenerated\n';
  const statement = 'theorem helper (h : work.Call a b c d) (s : Configuration) : work.Returns x y';
  const html = highlight(statement, catalog, prefix);
  assert.equal(visibleText(html), statement);
  assert.deepEqual(coloredNames(html).map(x => x.text), ['work.Call', 'work.Returns']);
  assert.equal(visibleText(highlight('work.Returns', catalog, prefix + 'end Algo.worker\n')), 'work.Returns');
  assert.deepEqual(coloredNames(highlight('work.Returns', catalog, prefix + 'end Algo.worker\n')), []);
});

test("example theorem and helper statements avoid generated storage and numbered control details", () => {
  const fs = require('node:fs');
  const path = require('node:path');
  const { declarations } = require('../editor/proof-outline.js');
  const root = path.join(__dirname, '../examples');
  const violations = [];
  let checked = 0;
  function visit(directory) {
    for (const item of fs.readdirSync(directory, { withFileTypes: true })) {
      if (item.name.includes(' 2.') || item.name.startsWith('.')) continue;
      const filename = path.join(directory, item.name);
      if (item.isDirectory()) visit(filename);
      else if (item.name.endsWith('.lean')) {
        for (const declaration of declarations(fs.readFileSync(filename, 'utf8'))) {
          checked++;
          const code = tokenize(declaration.statement || '').filter(x => !['comment', 'string'].includes(x.kind)).map(x => x.text).join('');
          if (/\bState_|\.(?:v\d+|t\d+|fn_\w+)\b|\bSummary\s+Step/.test(code)) violations.push(`${path.relative(root, filename)}:${declaration.line} ${declaration.name}`);
        }
      }
    }
  }
  visit(root);
  assert.ok(checked > 2000, 'audit includes the complete example collection');
  assert.deepEqual(violations, []);
});

test("quoted project namespace components resolve through normal Lean spellings", () => {
  const source = 'namespace Algo.«library».Algo2LeanGenerated\nabbrev Ref_Box := ObjectRef\nabbrev Ref__a2l_import_0_Box := ObjectRef\nend Algo.«library».Algo2LeanGenerated\nnamespace Algo.«library»\ndef work.Call : Prop := True\nend Algo.«library»\n';
  const catalog = createCatalog([], [source]);
  assert.deepEqual(names('Algo.library.work.Call Algo.«library».work.Call', catalog).map(x=>x.kind), ['proposition', 'proposition']);
  assert.deepEqual(names('open Algo.library.Algo2LeanGenerated\nRef_Box Ref__a2l_import_0_Box', catalog), [{text:'Ref_Box',kind:'type'}]);
  assert.equal(catalog.extraEntries.some(x => x.name.includes('_a2l_import_')), false);
});

test("shared interface types are distinct from getters and other values", () => {
  const catalog = createCatalog([], [GENERATED]);
  const source = 'open Algo2LeanGenerated\nHeap Seq Clocks SeqRef SequenceType Heap.read Heap.write SequenceType.get Clocks.single';
  assert.deepEqual(names(source, catalog), [
    { text: 'Heap', kind: 'type' },
    { text: 'Seq', kind: 'type' },
    { text: 'Clocks', kind: 'type' },
    { text: 'SeqRef', kind: 'type' },
    { text: 'SequenceType', kind: 'type' },
    { text: 'Heap.read', kind: 'definition' },
    { text: 'Heap.write', kind: 'definition' },
    { text: 'SequenceType.get', kind: 'definition' },
    { text: 'Clocks.single', kind: 'definition' },
  ]);
});

test("imported Adjacency resolves as a syntax type through its namespace", () => {
  const source = `import Algo2LeanLib.Dijkstra
Adjacency Other.Adjacency
namespace Proof
open Algo2Lean.Dijkstra
Adjacency
end Proof
Adjacency Algo2Lean.Dijkstra.Adjacency _root_.Algo2Lean.Dijkstra.Adjacency
`;
  const html = highlight(source, createCatalog());
  assert.deepEqual(syntaxTypes(html), [
    'Adjacency', 'Algo2Lean.Dijkstra.Adjacency', '_root_.Algo2Lean.Dijkstra.Adjacency',
  ]);
  assert.deepEqual(coloredNames(html), []);
  assert.equal(visibleText(html), source);
});

test("local data declarations and aliases receive type syntax without joining the public interface", () => {
  const prefix = `namespace Local
structure Packet where
  key : Int
inductive Choice where
  | first
  | second
def Explicit : Type := Int
abbrev Count := Int
abbrev CountAlias := Count
abbrev Adjacency := Int → List (Int × Int)
abbrev Edges := Int → Int → Int → Prop
abbrev Nested := (Int → Nat) × List (Int × Int)
`;
  const source = 'Packet Choice Explicit Count CountAlias Adjacency Edges Nested';
  const html = highlight(source, createCatalog(), prefix);
  assert.deepEqual(syntaxTypes(html), source.split(' '));
  assert.deepEqual(coloredNames(html), []);
  assert.equal(visibleText(html), source);
});

test("data types from catalog sources resolve in imported namespaces and previews", () => {
  const library = `namespace Library
structure Packet where
  key : Int
abbrev PacketAlias := Packet
end Library
`;
  const catalog = createCatalog([], [library]);
  const source = 'Packet PacketAlias Library.Packet Other.Packet';
  const html = highlight(source, catalog, 'namespace Proof\nopen Library\n');
  assert.deepEqual(syntaxTypes(html), ['Packet', 'PacketAlias', 'Library.Packet']);
  assert.deepEqual(coloredNames(html), []);
  assert.equal(visibleText(html), source);
  assert.deepEqual(syntaxTypes(highlight('Packet', catalog, 'namespace Proof\nopen Library\nend Proof\n')), []);
});

test("propositions and ordinary uppercase values are not inferred to be data types", () => {
  const prefix = `structure Evidence : Prop where
  holds : True
inductive Route : Int → Prop where
  | start : Route 0
def Predicate (n : Int) : Prop := n = 0
def UpperValue : Int := 7
abbrev CountValue := 7
abbrev Truth := True
abbrev Equality := Int = Int
abbrev EmptyPredicate := Nat → False
`;
  const source = 'Evidence Route Predicate UpperValue CountValue Truth Equality EmptyPredicate UnknownType';
  const html = highlight(source, createCatalog(), prefix);
  assert.deepEqual(syntaxTypes(html), []);
  assert.deepEqual(coloredNames(html), []);
  assert.equal(visibleText(html), source);
});

test("type discovery ignores declarations hidden in comments and strings", () => {
  const prefix = `/-- structure Ghost where -/
/- abbrev Hidden := Int /- structure Nested where -/ -/
def message : String := "abbrev Fake := Int"
structure Actual where
  key : Int
`;
  const source = 'Ghost Hidden Nested Fake Actual';
  const html = highlight(source, createCatalog(), prefix);
  assert.deepEqual(syntaxTypes(html), ['Actual']);
  assert.deepEqual(coloredNames(html), []);
  assert.equal(visibleText(html), source);
});

test("exact real and singleton tuple types have ordinary type syntax", () => {
  const source = "Real ℝ Tuple1 Int Set";
  assert.deepEqual(syntaxTypes(highlight(source, createCatalog())), source.split(" "));
});

test("finite storage operations are colored and described only when imported", () => {
  const prefix = "import Algo2LeanLib.FiniteCollections\nopen Algo2LeanGenerated\n";
  const catalog = createCatalog([], [prefix]);
  const source = "SetType DictType SetType.valid DictType.valid SetType.contains DictType.get DictType.set";
  assert.deepEqual(coloredNames(highlight(source, catalog, prefix)), [
    { text: "SetType", kind: "type" }, { text: "DictType", kind: "type" },
    { text: "SetType.valid", kind: "proposition" }, { text: "DictType.valid", kind: "proposition" },
    { text: "SetType.contains", kind: "definition" }, { text: "DictType.get", kind: "definition" },
    { text: "DictType.set", kind: "definition" },
  ]);
  const get = catalog.extraEntries.find(entry => entry.name === "Algo2LeanGenerated.DictType.get");
  assert.equal(get.fileLabel, "Algo2LeanLib/FiniteCollections.lean");
  assert.match(get.meaning, /optional value/);
  const ordinary = createCatalog([], ["import Algo2Lean\n"]);
  assert.equal(ordinary.extraEntries.some(entry => /\.(?:SetType|DictType)(?:\.|$)/.test(entry.name)), false);
});

test("nested finite descriptor namespaces retain declaration previews", () => {
  const source = `namespace Algo2LeanGenerated
namespace DictType
def get (heap : Heap) (ref : CollectionRef) (key : Int) : Option Int := none
end DictType
end Algo2LeanGenerated
`;
  const catalog = createCatalog([], [source]);
  const get = catalog.extraEntries.find(entry => entry.name === "Algo2LeanGenerated.DictType.get");
  assert.ok(get.signature.startsWith("def get"));
  assert.equal(get.fileLabel, "Algo2LeanLib/FiniteCollections.lean");
});


test("parallel call contracts retain proposition coloring in generated Lean", () => {
  const source = "def sum.ParallelCall : Nat → Prop := fun _ => True\ntheorem sum.ParallelCall.call : True := True.intro\n";
  const catalog = createCatalog([], [source]);
  assert.ok(names(source, catalog).some((entry) => entry.text === "sum.ParallelCall" && entry.kind === "proposition"));
  assert.ok(names(source, catalog).some((entry) => entry.text === "sum.ParallelCall.call" && entry.kind === "theorem"));
});


test("deterministic probability adapters retain theorem coloring", () => {
  const source = "theorem f.Call.hasLaw : True := True.intro\ntheorem f.Call.expectedReturn : True := True.intro\n";
  const catalog = createCatalog([], [source]);
  assert.ok(names(source, catalog).some((entry) => entry.text === "f.Call.hasLaw" && entry.kind === "theorem"));
  assert.ok(names(source, catalog).some((entry) => entry.text === "f.Call.expectedReturn" && entry.kind === "theorem"));
});
