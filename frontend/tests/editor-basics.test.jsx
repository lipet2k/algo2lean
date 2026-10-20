import { test } from "vitest";
import assert from "node:assert/strict";
import { descendants, draftAction, editor, fireEvent, MemoryStorage, tick } from "./support/editor-harness.jsx";
import { PREFIX } from "../src/lib/drafts.js";

async function openProject(app, name = "sample", files) {
  await app.click("open-project-button");
  await app.chooseFiles("project-picker", Object.entries(files).map(([path, text]) => ({
    name: path.split("/").pop(), webkitRelativePath: name + "/" + path, size: text.length, text: async () => text })));
  await app.ready();
}

test("the editor shows scoped function, method, and point relations without rewriting a proof", async () => {
  const sourceText = "def work(n: Int) -> Int:\n    # @charge\n    tick(\"work\", n)\n    return n\n";
  const proof = "-- Keep my existing compatibility proof.\ntheorem old_proof : is_Output_work 0 0 := by\n  sorry\n";
  const functions = [
    { name: "work", lean_name: "work", output_relation: "work.Returns",
      transcript_relation: "work.ValidTranscript", cost_relation: "work.ReturnsWithCost",
      parameters: [{ type: "Int" }], return_type: "Int",
      points: [{ relation: "work.At.charge", line: 3, column: 5 }] },
    { name: "Counter_add", display_name: "Counter.add", lean_name: "Counter.add",
      output_relation: "Counter.add.Returns", transcript_relation: "Counter.add.ValidTranscript",
      lean_input_type: "ObjectRef × Int", lean_output_type: "Unit" },
    { name: "match", lean_name: "«match»", output_relation: "«match».Returns",
      transcript_relation: "«match».ValidTranscript", parameters: [], return_type: "Int" },
  ];
  const app = editor(new MemoryStorage(), new MemoryStorage(), { fetch: async (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({ ok: true, lean: "-- compiled", points_lean: "-- points", functions }) };
  } });
  await app.ready();
  await app.edit(sourceText);
  await app.editAnalysis(proof);
  await app.click("compile-button");
  const text = app.text("relations");
  for (const expected of ["work.Returns", "work.ValidTranscript", "work.ReturnsWithCost", "work.At.charge",
    "Counter.add.Returns", "Counter.add.ValidTranscript", "«match».Returns"]) assert.ok(text.includes(expected), expected);
  assert.ok(!text.includes("is_Output_"));
  assert.ok(!text.includes("Counter_add"));
  const point = descendants(app.byId("relations")).find((element) => element.tagName === "BUTTON" && element.textContent === "work.At.charge");
  const before = app.byId("source").selectionStart;
  fireEvent.click(point);
  assert.equal(point.getAttribute("aria-expanded"), "true");
  assert.equal(app.byId("source").selectionStart, before);
  const jump = descendants(app.byId("relations")).find((element) => element.tagName === "BUTTON" && element.textContent.startsWith("Go to source"));
  fireEvent.click(jump);
  await tick(2);
  assert.equal(app.byId("source").selectionStart, sourceText.indexOf('tick("work"'));
  assert.equal(app.byId("analysis").value, proof);
});

test("an older compiler requests an update without exposing removed interface names", async () => {
  const app = editor(new MemoryStorage(), new MemoryStorage(), { fetch: async (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({ ok: true, lean: "-- compiled", functions: [
      { name: "plain", return_type: "Int" },
      { name: "Counter_add", display_name: "Counter.add", return_type: "Int" },
      { name: "Counter", display_name: "Counter.__init__", return_type: "Counter" },
    ] }) };
  } });
  await app.ready();
  const starter = app.byId("analysis").value;
  assert.ok(starter.includes("public relations shown by the compiler"));
  assert.ok(!starter.includes("f.Returns"));
  await app.click("compile-button");
  const text = app.text("relations");
  assert.match(text, /current compiler/);
  assert.doesNotMatch(text, /is_Output_|is_Transcript_/);
  assert.ok(!text.includes(".Returns"));
  assert.equal(app.byId("analysis").value, starter);
});

test("Escape leaves each code box without changing text or selection", async () => {
  const app = editor();
  await app.ready();
  await app.editAnalysis("theorem proof : True := by\n  trivial\n");
  for (const id of ["source", "analysis", "lean-selection", "points-selection", "shared-output", "check-output", "analysis-output"]) {
    const box = app.byId(id);
    const before = { value: box.value, text: box.textContent };
    if (box.setSelectionRange) box.setSelectionRange(2, 6);
    box.focus();
    assert.equal(document.activeElement, box, `${id} focusable`);
    fireEvent.keyDown(box, { key: "Escape" });
    assert.notEqual(document.activeElement, box, `${id} should release focus for page scrolling`);
    assert.deepEqual({ value: box.value, text: box.textContent }, before);
    if (box.setSelectionRange) {
      assert.equal(box.selectionStart, 2);
      assert.equal(box.selectionEnd, 6);
    }
  }
});

test("generated text controls contain the exact current Lean in both panes", async () => {
  let generation = 1;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      lean: `-- version ${generation}\nexample : 1 < 2 := by decide\n`,
      points_lean: `-- points ${generation}\ndef label := "<named>"\n`, functions: [],
    }) };
  } });
  await app.ready();
  for (generation of [1, 2]) {
    await app.click("compile-button");
    const core = app.byId("lean-selection").value;
    const points = app.byId("points-selection").value;
    assert.equal(core, `-- version ${generation}\nexample : 1 < 2 := by decide\n`);
    assert.equal(points, `-- points ${generation}\ndef label := "<named>"\n`);
    // A measuring line after the real trailing newline keeps EOF selection in
    // the shared scroll surface instead of internally scrolling the textarea.
    assert.ok(app.text("lean-code").endsWith("\n\n"));
    assert.ok(app.text("points-code").endsWith("\n\n"));
    await app.click("export-button");
    await app.click("export-points-button");
    assert.equal(app.downloads.at(-2).content, core);
    assert.equal(app.downloads.at(-1).content, points);
  }
});

test("pane filenames follow standalone renames and example changes without relabeling stale output", async () => {
  const app = editor();
  await app.ready();
  const label = (id) => app.text(id + "-pane-filename");
  await app.click("compile-button");
  assert.equal(label("source"), "merge_sort.algo");
  assert.equal(label("lean"), "MergeSortGenerated.lean");
  assert.equal(label("points"), "MergeSortGeneratedPoints.lean");
  assert.equal(label("analysis"), "Analysis.lean");
  assert.match(app.text("shared-summary"), /Algo2Lean\.lean/);

  const previousOutput = app.byId("lean-selection").value;
  await app.rename("filename", "renamed_sort");
  await app.rename("analysis-filename", "SortProof");
  assert.equal(label("source"), "renamed_sort.algo");
  assert.equal(label("analysis"), "SortProof.lean");
  assert.equal(app.byId("lean-selection").value, previousOutput);
  assert.equal(label("lean"), "MergeSortGenerated.lean");
  assert.equal(label("points"), "MergeSortGeneratedPoints.lean");
  await app.click("compile-button");
  assert.equal(label("lean"), "RenamedSortGenerated.lean");
  assert.equal(label("points"), "RenamedSortGeneratedPoints.lean");

  await app.select("examples", "0");
  await app.ready();
  assert.equal(label("source"), "other.algo");
  assert.equal(label("lean"), "OtherGenerated.lean");
  assert.equal(label("points"), "OtherGeneratedPoints.lean");
  assert.equal(label("analysis"), "Analysis.lean");
});

test("shared execution browsing preserves public proof imports and exports the displayed files", async () => {
  const publicModule = "Algo.even.Generated";
  const publicPoints = "Algo.even.Points";
  const sharedModule = "Algo._a2l_groups.Gtest.Generated";
  const sharedPoints = "Algo._a2l_groups.Gtest.Points";
  const files = {
    [publicModule]: `import ${sharedModule}\n-- public even interface\n`,
    [publicPoints]: `import ${sharedPoints}\n-- public named points\n`,
    [sharedModule]: "-- shared transitions for even and odd\n",
    [sharedPoints]: "-- shared named points for even and odd\n",
  };
  let cyclic = true;
  const app = editor(undefined, undefined, { fetch: (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      ok: true, lean: files[publicModule], points_lean: files[publicPoints], functions: [],
      module: publicModule, points_module: publicPoints, project_files: files,
      implementation_module: cyclic ? sharedModule : null,
      implementation_points_module: cyclic ? sharedPoints : null,
    }) };
  } });
  await app.ready();
  await openProject(app, "mutual", {
    "even.algo": "from odd import odd\ndef even(n: Int) -> Int:\n    return odd(n)\n",
    "odd.algo": "from even import even\ndef odd(n: Int) -> Int:\n    return even(n)\n",
  });
  await app.click("compile-button");
  const proof = app.byId("analysis").value;
  assert.equal(app.byId("generated-view-control").hidden, false);
  assert.equal(app.byId("lean-selection").value, files[publicModule]);
  assert.equal(app.text("lean-pane-filename"), "Algo/even/Generated.lean");
  assert.equal(app.text("points-pane-filename"), "Algo/even/Points.lean");
  await app.select("generated-view", "execution");
  assert.equal(app.byId("lean-selection").value, files[sharedModule]);
  assert.equal(app.byId("points-selection").value, files[sharedPoints]);
  assert.equal(app.text("lean-pane-filename"), "Algo/_a2l_groups/Gtest/Generated.lean");
  assert.equal(app.text("points-pane-filename"), "Algo/_a2l_groups/Gtest/Points.lean");
  assert.equal(app.store.state.generatedModule, publicModule);
  assert.equal(app.store.state.generatedPointsModule, publicPoints);
  assert.equal(app.byId("analysis").value, proof);
  await app.click("export-button");
  await app.click("export-points-button");
  assert.equal(app.downloads.at(-2).name, sharedModule + ".lean");
  assert.equal(app.downloads.at(-1).name, sharedPoints + ".lean");
  assert.equal(app.downloads.at(-2).content, files[sharedModule]);
  assert.equal(app.downloads.at(-1).content, files[sharedPoints]);
  await app.click("compile-button");
  assert.equal(app.byId("generated-view").value, "execution");
  assert.equal(app.byId("lean-selection").value, files[sharedModule]);
  await app.edit("-- edit source\n");
  assert.equal(app.byId("generated-view").disabled, true);
  cyclic = false;
  await app.click("compile-button");
  assert.equal(app.byId("generated-view-control").hidden, true);
  assert.equal(app.byId("lean-selection").value, files[publicModule]);
  assert.equal(app.text("lean-pane-filename"), "Algo/even/Generated.lean");
  assert.equal(app.text("points-pane-filename"), "Algo/even/Points.lean");
});

test("named-point navigation scrolls the shared source viewport only after the explicit source action", async () => {
  const sourceText = ["def work(n: Int) -> Int:", ...Array(12).fill("    n = n + 1"),
    "    if n > 0:", "        if n > 1:", "            if n > 2:", "                if n > 3:",
    "                    # @answer", "                    return n", "    return 0", ""].join("\n");
  const app = editor(new MemoryStorage(), new MemoryStorage(), { fetch: async (url) => {
    if (url === "/api/compile") return { ok: true, json: async () => ({
      ok: true, lean: "-- compiled", functions: [{ name: "work", points: [{ relation: "work.At.answer", line: 19, column: 21 }] }],
    }) };
  } });
  await app.ready();
  await app.edit(sourceText);
  await app.click("compile-button");
  const source = app.byId("source");
  const viewport = app.byId("source-editor");
  let scrolledIntoView = false;
  viewport.scrollIntoView = () => { scrolledIntoView = true; };
  // Only the shared viewport owns scrolling; the textarea's offsets are unrelated.
  source.scrollTop = 73;
  source.scrollLeft = 29;
  viewport.scrollTop = 0;
  viewport.scrollLeft = 0;
  const buttons = () => descendants(app.byId("relations")).filter((element) => element.tagName === "BUTTON");
  const before = source.selectionStart;
  fireEvent.click(buttons().find((button) => button.textContent === "work.At.answer"));
  assert.equal(viewport.scrollTop, 0);
  assert.equal(viewport.scrollLeft, 0);
  assert.equal(source.selectionStart, before);
  fireEvent.click(buttons().find((button) => button.textContent.startsWith("Go to source")));
  await tick(2);
  assert.equal(source.selectionStart, sourceText.indexOf("return n"));
  assert.equal(document.activeElement, source);
  assert.ok(viewport.scrollTop > 0);
  assert.ok(viewport.scrollLeft > 0);
  assert.equal(scrolledIntoView, true);
  assert.equal(source.scrollTop, 73);
  assert.equal(source.scrollLeft, 29);
});

test("analysis measurement follows edits, opened files, and empty proofs without stale content", async () => {
  const app = editor();
  await app.ready();
  const analysis = app.byId("analysis");
  const measuredText = () => app.text("analysis-measure");
  assert.equal(measuredText(), analysis.value + "\n");
  const longProof = "-- " + "wide proof ".repeat(50) + "\ntheorem test : True := by\n  trivial\n\n";
  await app.editAnalysis(longProof);
  assert.equal(measuredText(), longProof + "\n");
  assert.equal(app.text("analysis-line-numbers"), "1\n2\n3\n4\n5");
  await app.openFile("analysis-file-picker", "NewProof.lean", "-- new proof\r\nexample : True := by trivial\r\n");
  assert.equal(measuredText(), "-- new proof\nexample : True := by trivial\n\n");
  assert.equal(measuredText(), analysis.value + "\n");
  await app.editAnalysis("");
  assert.equal(measuredText(), "\n");
  assert.equal(app.text("analysis-line-numbers"), "1");
});

test("editor unchanged close cannot erase another tab's debounced edit", async () => {
  const local = new MemoryStorage();
  const stale = editor(local);
  const active = editor(local);
  await stale.ready();
  await active.ready();
  await active.edit("def important() -> Int:\n    return 42\n");
  await active.flush();
  const before = [...local.data];
  await stale.dispatchWindow("beforeunload");
  stale.setVisibility("hidden");
  await stale.dispatchDocument("visibilitychange");
  assert.deepEqual([...local.data], before);
  assert.ok(active.records().some((record) => record.source.includes("important")));
});

test("editor flushes pending edits on hide and close without extra unchanged saves", async () => {
  const app = editor();
  await app.ready();
  await app.edit("pending when hidden");
  app.setVisibility("hidden");
  await app.dispatchDocument("visibilitychange");
  assert.ok(app.records().some((record) => record.source === "pending when hidden"));
  const writes = app.local.writes.length;
  await app.dispatchWindow("beforeunload");
  await app.flush();
  assert.equal(app.local.writes.length, writes);
  await app.edit("pending when closed");
  await app.dispatchWindow("beforeunload");
  assert.ok(app.records().some((record) => record.source === "pending when closed"));
});

test("two editor tabs save their own changes after their shared starting point", async () => {
  const local = new MemoryStorage();
  const writer = editor(local);
  await writer.ready();
  await writer.edit("shared original");
  await writer.flush();
  writer.unmount();
  const a = editor(local);
  const b = editor(local);
  await a.ready();
  await b.ready();
  await a.edit("tab A changes");
  await b.edit("tab B changes");
  await a.flush();
  await b.flush();
  assert.deepEqual(a.records().map((record) => record.source).sort(), ["shared original", "tab A changes", "tab B changes"]);
});

test("multiple drafts remain folded by default and recover only when explicitly selected", async () => {
  const local = new MemoryStorage();
  const seeded = editor(local);
  await seeded.ready();
  await seeded.edit("first preview");
  await seeded.flush();
  const first = seeded.records()[0];
  await seeded.select("examples", "0");
  await seeded.edit("second preview");
  await seeded.flush();
  seeded.unmount();
  const app = editor(local);
  await app.ready();
  assert.equal(app.byId("draft-picker").open, false);
  assert.equal(app.byId("filename").value, "merge_sort.algo");
  assert.equal(app.text("draft-count"), "2");
  await app.click("drafts-button");
  assert.equal(app.byId("draft-picker").open, true);
  const before = [...local.data];
  await draftAction(app, "first preview", "Recover").click();
  assert.equal(app.byId("source").value, first.source);
  assert.equal(app.byId("filename").value, first.filename);
  assert.equal(app.byId("draft-picker").open, false);
  await app.dispatchWindow("beforeunload");
  assert.deepEqual([...local.data], before);
  await app.edit("changed recovery");
  await app.flush();
  assert.equal(app.records().find((record) => record.id === first.id).source, first.source);
  assert.equal(app.records().length, 3);
});

test("recovering the current draft flushes pending edits before reading its latest source", async () => {
  const app = editor();
  await app.ready();
  await app.edit("last saved content");
  await app.flush();
  const draft = app.records()[0];
  await app.edit("pending newer content");
  await draftAction(app, "last saved content", "Recover").click();
  assert.equal(app.byId("source").value, "pending newer content");
  assert.equal(app.records().find((record) => record.id === draft.id).source, "pending newer content");
  assert.equal(app.records().length, 1);
  await app.flush();
  assert.equal(app.byId("source").value, "pending newer content");
});

test("editor Discard removes the chosen copy and pending unchanged close does not recreate it", async () => {
  const app = editor();
  await app.ready();
  await app.edit("saved before discard");
  await app.flush();
  await app.edit("pending at discard");
  await draftAction(app, "saved before discard", "Discard").click();
  assert.equal(app.records().length, 0);
  assert.equal(app.byId("source").value, "pending at discard");
  const close = await app.dispatchWindow("beforeunload");
  assert.equal(close.defaultPrevented, true);
  await app.flush();
  assert.equal(app.records().length, 0);
  await app.edit("new edit after discard");
  await app.flush();
  assert.equal(app.records()[0].source, "new edit after discard");
});

test("loading an example saves the pending document before switching to a fresh one", async () => {
  const app = editor();
  await app.ready();
  await app.edit("pending previous document");
  await app.select("examples", "0");
  assert.equal(app.byId("filename").value, "other.algo");
  assert.ok(app.records().some((record) => record.source === "pending previous document"));
  await app.edit("new example changes");
  await app.flush();
  assert.deepEqual(app.records().map((record) => record.source).sort(),
    ["new example changes", "pending previous document"]);
});

test("cross-tab storage notifications refresh recovery choices without replacing editor text", async () => {
  const local = new MemoryStorage();
  const app = editor(local);
  await app.ready();
  await app.edit("local pending edit");
  const other = editor(local);
  await other.ready();
  await other.edit("foreign edit");
  await other.flush();
  const foreign = other.records().find((record) => record.source === "foreign edit");
  other.unmount();
  await app.dispatchWindow("storage", { key: PREFIX + foreign.id });
  assert.equal(app.byId("source").value, "local pending edit");
  assert.equal(app.text("draft-count"), "1");
  assert.ok(draftAction(app, "foreign edit", "Recover"));
});

test("a draft discarded in another tab stays deleted and warns before losing its unsaved text", async () => {
  const app = editor();
  await app.ready();
  await app.edit("unsaved text removed elsewhere");
  await app.flush();
  const draft = app.records()[0];
  app.local.removeItem(PREFIX + draft.id);
  await app.dispatchWindow("storage", { key: PREFIX + draft.id });
  const close = await app.dispatchWindow("beforeunload");
  assert.equal(close.defaultPrevented, true);
  assert.equal(app.records().length, 0);
  let asked = false;
  app.confirm.answer = () => { asked = true; return false; };
  await app.select("examples", "0");
  assert.equal(asked, true);
  assert.equal(app.byId("source").value, draft.source);
  assert.equal(app.records().length, 0);
});

test("editing then undoing before debounce leaves no draft and no saving status", async () => {
  const app = editor();
  await app.ready();
  const initial = app.byId("source").value;
  await app.edit("temporary edit");
  await app.edit(initial);
  await app.flush();
  assert.equal(app.records().length, 0);
  assert.doesNotMatch(app.text("draft-status"), /Saving browser draft/);
  const close = await app.dispatchWindow("beforeunload");
  assert.notEqual(close.defaultPrevented, true);
});

test("canceling document replacement after a failed draft save preserves current source", async () => {
  const app = editor();
  await app.ready();
  await app.edit("unsaved source that must remain");
  app.local.fail.add("write");
  app.confirm.answer = () => false;
  await app.select("examples", "0");
  assert.equal(app.byId("source").value, "unsaved source that must remain");
  assert.equal(app.byId("filename").value, "merge_sort.algo");
});

test("editor handles blocked browser storage and warns before closing unsaved work", async () => {
  const app = editor(undefined, undefined, { blockStorageAccess: true });
  await app.ready();
  assert.match(app.text("draft-status"), /unavailable|could not|cannot/i);
  await app.edit("keep me despite blocked storage");
  await app.flush();
  const close = await app.dispatchWindow("beforeunload");
  assert.equal(close.defaultPrevented, true);
  assert.equal(app.byId("source").value, "keep me despite blocked storage");
});

test("Find opens from the analysis toolbar, highlights the match, and Escape returns to the editor", async () => {
  const app = editor();
  await app.ready();
  await app.click("analysis-find-button");
  const bar = app.container.querySelector("[role=search]");
  const input = bar.querySelector("input[type=search]");
  assert.equal(bar.hidden, false);
  assert.equal(document.activeElement, input);
  fireEvent.input(input, { target: { value: "import" } });
  await tick(2);
  assert.match(bar.querySelector("[role=status]").textContent, /^1 of /);
  assert.equal(app.container.querySelector(".code-search-highlight mark").textContent, "import");
  fireEvent.keyDown(input, { key: "Escape" });
  await tick(2);
  assert.equal(bar.hidden, true);
  assert.equal(document.activeElement, app.byId("analysis"));
  assert.equal(app.container.querySelector(".code-search-highlight"), null);
  await app.click("analysis-find-button");
  assert.equal(bar.hidden, false);
  assert.equal(document.activeElement, input);
});
