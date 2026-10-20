import { test } from "vitest";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./support/paths.js";

// Untrusted text (source, proofs, compiler metadata, citations) is always
// rendered as React text, never parsed as markup.
function files(directory) {
  return fs.readdirSync(directory, { withFileTypes: true }).flatMap((entry) => {
    const file = path.join(directory, entry.name);
    return entry.isDirectory() ? files(file) : /\.(?:js|jsx)$/.test(entry.name) ? [file] : [];
  });
}

test("the editor source never injects markup", () => {
  const offenders = [];
  for (const file of files(path.join(ROOT, "frontend/src"))) {
    const text = fs.readFileSync(file, "utf8");
    if (/innerHTML|outerHTML|dangerouslySetInnerHTML|insertAdjacentHTML|document\.write/.test(text)) offenders.push(path.relative(ROOT, file));
  }
  assert.deepEqual(offenders, []);
});
