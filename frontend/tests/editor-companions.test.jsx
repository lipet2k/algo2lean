import { test } from "vitest";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { editor, fireEvent, tick } from "./support/editor-harness.jsx";
import { ROOT } from "./support/paths.js";

const RANDOM = "def sample() -> Int:\n    return randint(0, 2)\n";

// Exercise the real compiler/export boundary, so interface conventions cannot
// drift unnoticed behind a frontend-only mock. No Lean installation is needed.
function nativeRequest(url, body) {
  return JSON.parse(execFileSync(process.env.PYTHON || "python3", ["-c", `
import json, sys
from editor.analysis_export import request
url, body = json.load(sys.stdin)
print(json.dumps(request(url, body, "project_sources" in body)))
`], { cwd: ROOT, input: JSON.stringify([url, body]), encoding: "utf8", maxBuffer: 8 * 1024 * 1024 }));
}

function compilerBackend({ probabilityChecked = false } = {}) {
  return (url, request) => {
    if (!["/api/compile", "/api/check", "/api/analysis-export"].includes(url)) return;
    const body = JSON.parse(request.body);
    if (!["coin.algo", "client.algo"].includes(body.filename)) return;
    const response = nativeRequest(url === "/api/check" ? "/api/compile" : url, body);
    if (url === "/api/check") Object.assign(response.body, { ok: true, available: true, probability_checked: probabilityChecked });
    return { ok: response.status === 200, status: response.status, json: async () => response.body,
      blob: async () => new Blob([Buffer.from(response.body, "base64")], { type: response.content_type }) };
  };
}

async function openProject(app, files, name = "companions") {
  await app.click("open-project-button");
  await app.chooseFiles("project-picker", Object.entries(files).map(([filename, text]) => ({
    name: filename, webkitRelativePath: `${name}/${filename}`, size: text.length, text: async () => text,
  })));
  await app.ready();
}

test("a new randomized project starter exports a real Lean package without Facts", async () => {
  const app = editor(undefined, undefined, { fetch: compilerBackend() });
  await app.ready();
  await openProject(app, { "coin.algo": RANDOM });
  assert.match(app.byId("analysis").value, /^import Algo.coin.Generated\nimport Algo.coin.Points\n/);
  assert.doesNotMatch(app.byId("analysis").value, /Algo.coin.Facts/);
  await app.click("analysis-save-button");
  assert.match(app.text("analysis-file-message"), /^Downloaded/);
  assert.equal(app.downloads.at(-1).name, "coin.zip");
  assert.ok(app.downloads.at(-1).content.size > 1000);
  await app.flush();
  assert.doesNotMatch(app.store.projectSnapshot().files["coin.algo"].analysis, /Algo.coin.Facts/);
  // Switching the same source back to deterministic restores the valid helpers.
  await app.edit("def sample() -> Int:\n    return 1\n");
  await app.click("compile-button");
  assert.match(app.byId("analysis").value, /import Algo.coin.Facts/);
});

test("recompiling randomized source preserves handwritten analysis", async () => {
  const app = editor(undefined, undefined, { fetch: compilerBackend() });
  await app.ready();
  await openProject(app, { "coin.algo": RANDOM });
  const proof = "import Algo.coin.Generated\n-- my own proof\n";
  await app.editAnalysis(proof);
  await app.click("compile-button");
  assert.equal(app.byId("analysis").value, proof);
  await app.click("analysis-save-button");
  await app.click("compile-button");
  assert.equal(app.byId("analysis").value, proof, "even a saved proof must not be replaced");
});

test("probability browsing exports the companion and distinguishes its check from definitions", async () => {
  const app = editor(undefined, undefined, { fetch: compilerBackend() });
  await app.ready();
  await app.openFile("file-picker", "coin.algo", RANDOM);
  await app.click("compile-button");
  const proof = app.byId("analysis").value;
  assert.ok(app.children("generated-view").some((option) => option.textContent === "Probability interface"));
  assert.match(app.text("relations"), /Probability/);
  assert.match(app.text("relations"), /CoinGeneratedProbability.lean/);
  await app.select("generated-view", "probability");
  const probability = app.store.state.lastResult.lean;
  assert.match(probability, /import Algo2LeanProbability/);
  assert.equal(app.byId("lean-selection").value, probability);
  assert.equal(app.byId("points-output").hidden, true);
  assert.equal(app.byId("standalone-button").disabled, true);
  assert.equal(app.byId("analysis").value, proof);
  await app.click("export-button");
  assert.deepEqual(app.downloads.at(-1), { name: "CoinGeneratedProbability.lean", content: probability });
  await app.click("check-button");
  assert.equal(app.byId("generated-view").value, "probability");
  assert.equal(app.text("lean-state"), "Requires Mathlib check");
  assert.match(app.text("diagnostics"), /separate Mathlib check/);
  await app.select("generated-view", "public");
  assert.equal(app.text("lean-state"), "Lean checked");
  assert.equal(app.byId("standalone-button").disabled, false);
  await app.select("generated-view", "probability");
  await app.edit(RANDOM + "# changed\n");
  assert.equal(app.text("lean-state"), "Source changed");
});

test("a companion is marked checked only when its own result says so", async () => {
  const app = editor(undefined, undefined, { fetch: compilerBackend({ probabilityChecked: true }) });
  await app.ready();
  await app.openFile("file-picker", "coin.algo", RANDOM);
  await app.click("check-button");
  await app.select("generated-view", "probability");
  assert.equal(app.text("lean-state"), "Lean checked");
});

test("imported parallel contracts remain browsable with correct filenames and proof imports", async () => {
  const app = editor(undefined, undefined, { fetch: compilerBackend() });
  await app.ready();
  const files = Object.fromEntries(["client.algo", "helper.algo"].map((name) =>
    [name, fs.readFileSync(path.join(ROOT, "tests/fixtures/parallel_imports", name), "utf8")]));
  await openProject(app, files);
  const proof = app.byId("analysis").value;
  assert.ok(app.children("generated-view").some((option) => option.textContent === "Parallel contracts"));
  assert.match(app.text("relations"), /Algo.client.Parallel.lean/);
  await app.select("generated-view", "parallel");
  assert.equal(app.text("lean-pane-filename"), "Algo/client/Parallel.lean");
  assert.match(app.byId("lean-selection").value, /ParallelCall/);
  assert.equal(app.byId("points-output").hidden, true);
  assert.equal(app.byId("analysis").value, proof);
  await app.click("compile-button");
  assert.equal(app.byId("generated-view").value, "parallel");
  await app.select("generated-view", "public");
  assert.equal(app.text("lean-pane-filename"), "Algo/client/Generated.lean");
});

test("unsupported probability companions explain limitations without offering an empty view", async () => {
  const diagnostic = "Probability semantics for abstract interface dependencies are not supported yet.";
  const app = editor(undefined, undefined, { fetch: (url) => url === "/api/compile" ? {
    ok: true, json: async () => ({ ok: true, module: "Algo.main.Generated", points_module: "Algo.main.Points",
      lean: "-- possible executions", points_lean: "-- points", functions: [], randomized: true,
      probability_lean: "", probability_diagnostic: diagnostic }),
  } : undefined });
  await app.ready();
  await openProject(app, { "main.algo": RANDOM });
  assert.doesNotMatch(app.byId("analysis").value, /Algo.main.Facts/);
  assert.ok(app.text("diagnostics").includes(diagnostic));
  assert.equal(app.byId("generated-view-control").hidden, true);
});

test("both editors describe the Escape route and release focus when it is used", async () => {
  const app = editor();
  await app.ready();
  for (const [id, helpId] of [["source", "editor-help"], ["analysis", "analysis-editor-help"]]) {
    const input = app.byId(id);
    assert.ok(input.getAttribute("aria-describedby").split(" ").includes(helpId));
    assert.match(app.text(helpId), /Tab: .* spaces · Esc: leave editor/);
    input.focus();
    fireEvent.keyDown(input, { key: "Tab" });
    await tick();
    assert.equal(document.activeElement, input);
    fireEvent.keyDown(input, { key: "Escape" });
    await tick();
    assert.notEqual(document.activeElement, input);
  }
});
