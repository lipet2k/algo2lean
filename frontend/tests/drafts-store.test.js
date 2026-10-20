import { test } from "vitest";
import assert from "node:assert/strict";
import { Store, PREFIX, LEGACY_KEY } from "../src/lib/drafts.js";
import { MemoryStorage } from "./support/memory-storage.js";

let serial = 0;
function store(local = new MemoryStorage(), session = new MemoryStorage()) {
  let time = 100;
  return new Store(local, session, {
    makeId: () => `draft-${++serial}`,
    now: () => ++time,
  });
}

function snapshot(source = "original", filename = "example.algo") {
  return { source, filename, savedSource: "original", savedFilename: "example.algo" };
}

function pairedSnapshot(source = "original", analysis = "-- saved proof", overrides = {}) {
  return {
    ...snapshot(source), analysis, analysisFilename: "Proof.lean",
    savedAnalysis: "-- saved proof", savedAnalysisFilename: "Proof.lean", ...overrides,
  };
}

function seed(local, source = "recover me", session = new MemoryStorage()) {
  const writer = store(local, session);
  writer.start(snapshot());
  writer.write(snapshot(source));
  return writer.read(writer.activeId);
}

test("an untouched tab cannot replace a newer browser draft when it closes", () => {
  const local = new MemoryStorage();
  const older = store(local);
  const newer = store(local);
  older.start(snapshot());
  newer.start(snapshot());
  newer.write(snapshot("new work"));
  const beforeClose = [...local.data];
  assert.equal(older.write(snapshot()), false);
  assert.deepEqual([...local.data], beforeClose);
  assert.equal(newer.list()[0].source, "new work");
});

test("two actively edited tabs keep independent records through alternating writes", () => {
  const local = new MemoryStorage();
  const a = store(local);
  const b = store(local);
  a.start(snapshot());
  b.start(snapshot());
  a.write(snapshot("A first"));
  b.write(snapshot("B first"));
  const aId = a.activeId;
  const bId = b.activeId;
  assert.notEqual(aId, bId);
  a.write(snapshot("A final"));
  b.write(snapshot("B final"));
  assert.equal(a.read(aId).source, "A final");
  assert.equal(b.read(bId).source, "B final");
  assert.equal(a.list().length, 2);
});

test("reloads and duplicated session pointers fork on edit without overwriting recovery", () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  const original = seed(local, "before reload", session);
  const reloaded = store(local, session);
  const duplicate = store(local, session.copy());
  assert.equal(reloaded.preferredId(), original.id);
  assert.equal(duplicate.preferredId(), original.id);
  reloaded.start(original, original.id);
  duplicate.start(original, original.id);
  const unchanged = [...local.data];
  assert.equal(reloaded.write(original), false);
  assert.equal(duplicate.write(original), false);
  assert.deepEqual([...local.data], unchanged);
  reloaded.write({ ...original, source: "reload changes" });
  duplicate.write({ ...original, source: "duplicate changes" });
  assert.notEqual(reloaded.activeId, duplicate.activeId);
  assert.notEqual(reloaded.activeId, original.id);
  assert.notEqual(duplicate.activeId, original.id);
  assert.equal(reloaded.read(original.id).source, "before reload");
  assert.equal(reloaded.list().length, 3);
});

test("selecting recovery drafts does not change their content or timestamps", () => {
  const local = new MemoryStorage();
  const first = seed(local, "first document");
  const second = seed(local, "second document");
  const reader = store(local);
  const before = [...local.data];
  for (const saved of [first, second, first]) {
    reader.start(saved, saved.id);
    assert.equal(reader.hasChanges(saved), false);
    assert.equal(reader.write(saved), false);
  }
  assert.deepEqual([...local.data], before);
});

test("only content or file-save state changes update a draft timestamp", () => {
  const local = new MemoryStorage();
  const writer = store(local);
  writer.start(snapshot());
  assert.equal(writer.hasChanges(snapshot()), false);
  assert.equal(writer.write(snapshot("edit")), true);
  const first = writer.read(writer.activeId);
  const writes = local.writes.length;
  assert.equal(writer.write(snapshot("edit")), false);
  assert.equal(local.writes.length, writes);
  assert.equal(writer.read(writer.activeId).updatedAt, first.updatedAt);
  assert.equal(writer.write({ ...snapshot("edit"), savedSource: "edit" }), true);
  const saved = writer.read(writer.activeId);
  assert.equal(saved.savedSource, "edit");
  assert.ok(saved.updatedAt > first.updatedAt);
  assert.equal(writer.write({ ...snapshot("edit"), savedSource: "edit", filename: "renamed.algo" }), true);
  assert.equal(writer.read(writer.activeId).filename, "renamed.algo");
});

test("switching documents leaves the prior document recoverable", () => {
  const writer = store();
  writer.start(snapshot());
  writer.write(snapshot("first edited"));
  const firstId = writer.activeId;
  writer.start(snapshot("second original", "second.algo"));
  writer.write(snapshot("second edited", "second.algo"));
  assert.notEqual(writer.activeId, firstId);
  assert.equal(writer.read(firstId).source, "first edited");
  assert.equal(writer.list().length, 2);
});

test("explicitly discarded active drafts stay discarded until another edit", () => {
  const writer = store();
  writer.start(snapshot());
  writer.write(snapshot("edited"));
  const oldId = writer.activeId;
  writer.remove(oldId);
  assert.equal(writer.read(oldId), null);
  assert.equal(writer.write(snapshot("edited")), false);
  assert.equal(writer.list().length, 0);
  writer.write(snapshot("a later edit"));
  assert.notEqual(writer.activeId, oldId);
  assert.equal(writer.list().length, 1);
});

test("failed local writes preserve the recoverable copy and keep edits pending for retry", () => {
  const local = new MemoryStorage();
  const writer = store(local);
  writer.start(snapshot());
  writer.write(snapshot("last persisted"));
  const id = writer.activeId;
  local.fail.add("write");
  assert.throws(() => writer.write(snapshot("pending")), /unavailable/);
  assert.equal(writer.read(id).source, "last persisted");
  assert.equal(writer.hasChanges(snapshot("pending")), true);
  local.fail.clear();
  assert.equal(writer.write(snapshot("pending")), true);
  assert.equal(writer.read(writer.activeId).source, "pending");
});

test("disabled session storage still allows independent and recoverable drafts", () => {
  const local = new MemoryStorage();
  const session = new MemoryStorage();
  session.fail = new Set(["read", "write", "remove"]);
  const a = store(local, session);
  const b = store(local, session);
  a.start(snapshot());
  b.start(snapshot());
  assert.equal(a.write(snapshot("A")), true);
  assert.equal(b.write(snapshot("B")), true);
  assert.notEqual(a.activeId, b.activeId);
  assert.deepEqual(a.list().map((record) => record.source).sort(), ["A", "B"]);
  assert.doesNotThrow(() => a.preferredId());
});

test("local storage read and removal failures are visible to the caller", () => {
  const local = new MemoryStorage();
  const saved = seed(local);
  const reader = store(local);
  local.fail.add("read");
  assert.throws(() => reader.list(), /unavailable/);
  assert.throws(() => reader.read(saved.id), /unavailable/);
  local.fail.clear();
  local.fail.add("remove");
  assert.throws(() => reader.remove(saved.id), /unavailable/);
  assert.equal(reader.read(saved.id).source, saved.source);
});

test("a legacy draft is migrated once with file-save state intact", () => {
  const legacy = { ...snapshot("legacy edit"), updatedAt: 42 };
  const local = new MemoryStorage([[LEGACY_KEY, JSON.stringify(legacy)]]);
  const writer = store(local);
  const migrated = writer.migrateLegacy();
  assert.equal(migrated.source, legacy.source);
  assert.equal(migrated.savedSource, legacy.savedSource);
  assert.equal(migrated.updatedAt, 42);
  assert.equal(local.getItem(LEGACY_KEY), null);
  assert.equal(writer.list().length, 1);
  assert.equal(writer.migrateLegacy(), null);
  assert.equal(writer.list().length, 1);
});

test("legacy migration keeps the original when writing or verifying the copy fails", () => {
  for (const failure of ["write", "verify"]) {
    const raw = JSON.stringify({ ...snapshot("legacy work"), updatedAt: 42 });
    const local = new MemoryStorage([[LEGACY_KEY, raw]]);
    if (failure === "write") local.fail.add("write");
    else {
      const originalGet = local.getItem.bind(local);
      local.getItem = (key) => key.startsWith(PREFIX) ? null : originalGet(key);
    }
    assert.throws(() => store(local).migrateLegacy());
    assert.equal(local.getItem(LEGACY_KEY), raw);
  }
});

test("a failed legacy removal leaves both copies recoverable", () => {
  const raw = JSON.stringify({ ...snapshot("legacy work"), updatedAt: 42 });
  const local = new MemoryStorage([[LEGACY_KEY, raw]]);
  local.fail.add("remove");
  const writer = store(local);
  assert.throws(() => writer.migrateLegacy(), /unavailable/);
  assert.equal(local.getItem(LEGACY_KEY), raw);
  assert.equal(writer.list()[0].source, "legacy work");
});

test("malformed legacy records remain untouched and do not become new drafts", () => {
  for (const raw of ["not JSON", "null", '{"source":2,"filename":"bad.algo"}']) {
    const local = new MemoryStorage([[LEGACY_KEY, raw]]);
    const writer = store(local);
    assert.equal(writer.migrateLegacy(), null);
    assert.equal(local.getItem(LEGACY_KEY), raw);
    assert.equal(writer.list().length, 0);
  }
});

test("one malformed or foreign record does not hide valid recovery records", () => {
  const local = new MemoryStorage();
  const valid = seed(local, "still recoverable");
  local.setItem(PREFIX + "broken", "not JSON");
  local.setItem(PREFIX + "wrong-type", JSON.stringify({ ...valid, id: "wrong-type", source: 7 }));
  local.setItem(PREFIX + "wrong-id", JSON.stringify(valid));
  local.setItem(PREFIX + "bad-time", JSON.stringify({ ...valid, id: "bad-time", updatedAt: -1 }));
  local.setItem("unrelated.setting", "true");
  const reader = store(local);
  assert.deepEqual(reader.list().map((record) => record.id), [valid.id]);
  assert.equal(reader.read("broken"), null);
  assert.equal(reader.read("wrong-id"), null);
  assert.equal(local.getItem("unrelated.setting"), "true");
});

test("analysis content, names, and save baselines independently trigger a paired snapshot", () => {
  const writer = store();
  let current = pairedSnapshot();
  writer.start(current);
  for (const [field, value] of [
    ["analysis", "-- edited proof"], ["analysisFilename", "Renamed.lean"],
    ["savedAnalysis", "-- edited proof"], ["savedAnalysisFilename", "Renamed.lean"],
  ]) {
    current = { ...current, [field]: value };
    assert.equal(writer.hasChanges(current), true, field);
    assert.equal(writer.write(current), true, field);
    const saved = writer.read(writer.activeId);
    for (const [key, expected] of Object.entries(current)) assert.equal(saved[key], expected, key);
    assert.equal(writer.write(current), false);
  }
});

test("source-only v2 records remain recoverable without changing their on-disk content", () => {
  const legacyV2 = { id: "older-v2", ...snapshot("old source"), updatedAt: 42 };
  const raw = JSON.stringify(legacyV2);
  const local = new MemoryStorage([[PREFIX + legacyV2.id, raw]]);
  const reader = store(local);
  const recovered = reader.read(legacyV2.id);
  assert.equal(recovered.source, "old source");
  assert.equal(recovered.analysis, undefined);
  assert.equal(recovered.savedAnalysis, undefined);
  reader.start(recovered, recovered.id);
  assert.equal(reader.write(recovered), false);
  assert.equal(local.getItem(PREFIX + legacyV2.id), raw);
  reader.write({ ...recovered, analysis: "-- new proof", analysisFilename: "Proof.lean" });
  assert.notEqual(reader.activeId, legacyV2.id);
  assert.equal(reader.read(reader.activeId).analysis, "-- new proof");
  assert.equal(local.getItem(PREFIX + legacyV2.id), raw);
});

test("migrating a paired legacy record preserves all analysis save state", () => {
  const legacy = { ...pairedSnapshot("legacy source", "-- unsaved proof", {
    filename: "Legacy.algo", analysisFilename: "LegacyProof.lean", savedAnalysis: "-- downloaded proof",
    savedAnalysisFilename: "Downloaded.lean",
  }), updatedAt: 42 };
  const local = new MemoryStorage([[LEGACY_KEY, JSON.stringify(legacy)]]);
  const migrated = store(local).migrateLegacy();
  for (const [key, expected] of Object.entries(legacy)) assert.equal(migrated[key], expected, key);
  assert.equal(local.getItem(LEGACY_KEY), null);
});

test("a failed paired write retains the last complete source-and-analysis snapshot", () => {
  const local = new MemoryStorage();
  const writer = store(local);
  writer.start(pairedSnapshot());
  writer.write(pairedSnapshot("persisted source", "-- persisted analysis"));
  const id = writer.activeId;
  const pending = pairedSnapshot("pending source", "-- pending analysis");
  local.fail.add("write");
  assert.throws(() => writer.write(pending), /unavailable/);
  assert.equal(writer.read(id).source, "persisted source");
  assert.equal(writer.read(id).analysis, "-- persisted analysis");
  assert.equal(writer.hasChanges(pending), true);
  local.fail.clear();
  writer.write(pending);
  assert.equal(writer.read(id).source, "pending source");
  assert.equal(writer.read(id).analysis, "-- pending analysis");
});
