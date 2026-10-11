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
    const kind = match[1].match(/\binterface-(proposition|theorem|definition)\b/)?.[1];
    if (kind) result.push({ text: unescapeHtml(match[2]), kind });
  }
  return result;
}

function names(source, catalog) {
  return coloredNames(highlight(source, catalog));
}

test("interface colors distinguish declarations within the same display group", () => {
  const expected = ["proposition", "proposition", "theorem", "theorem", "proposition", "proposition",
    "theorem", "theorem", "proposition", "proposition", "definition", "definition", "proposition",
    "definition", "definition"];
  assert.deepEqual(FUNCTIONS[0].interface_entries.map(classify), expected);
  assert.equal(classify({ name: "Returns.Returns", category: "output" }), "proposition");
  assert.equal(classify({ name: "Box.Call.run", category: "helper" }), "theorem");
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
    { text: "Algo.worker.Algo2LeanGenerated.Frame", kind: "definition" },
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
    { text: "Step", kind: "proposition" }, { text: "Configuration", kind: "definition" },
    { text: "Frame", kind: "definition" }, { text: "Ref_Box", kind: "definition" },
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
  assert.deepEqual(names('open Algo.library.Algo2LeanGenerated\nRef_Box Ref__a2l_import_0_Box', catalog), [{text:'Ref_Box',kind:'definition'}]);
  assert.equal(catalog.extraEntries.some(x => x.name.includes('_a2l_import_')), false);
});
