import { test } from "vitest";
import assert from "node:assert/strict";
import { matches } from "../src/lib/code-search.js";

test("literal case-insensitive matching preserves actual Unicode and punctuation offsets", () => {
  assert.deepEqual(matches("Call call CALL", "call"), [{ start: 0, end: 4 }, { start: 5, end: 9 }, { start: 10, end: 14 }]);
  assert.deepEqual(matches("a.b axb a.b", "a.b"), [{ start: 0, end: 3 }, { start: 8, end: 11 }]);
  assert.deepEqual(matches("[a] + [a]", "[a]"), [{ start: 0, end: 3 }, { start: 6, end: 9 }]);
  assert.deepEqual(matches("İ 𝒂 = 𝒂", "𝒂"), [{ start: 2, end: 4 }, { start: 7, end: 9 }]);
  assert.deepEqual(matches("anything", ""), []);
});
