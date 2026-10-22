import { test } from "vitest";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { declarations } from "../src/lib/proof-outline.js";

import { ROOT } from "./support/paths.js";

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
  assert.deepEqual(declarations("/- theorem hidden : True := by trivial"), []);
  assert.deepEqual(declarations('def text := "unterminated\ntheorem hidden : True := by trivial'), []);
  assert.deepEqual(declarations("theorem"), []);
});

export function leanFiles(directory) {
  return fs.readdirSync(directory, { withFileTypes: true }).flatMap((entry) => {
    const file = path.join(directory, entry.name);
    return entry.isDirectory() ? leanFiles(file) : file.endsWith(".lean") ? [file] : [];
  });
}

test("all bundled main-result markers identify declarations with full statement previews", () => {
  const root = path.join(ROOT, "examples");
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
  }
  assert.ok(markedFiles >= 30, "The public example collection exposes its main results");
});
