// Browser draft records: one localStorage entry per source-and-analysis pair.
export const PREFIX = "algo2lean.editor.draft.v2.";
export const LEGACY_KEY = "algo2lean.editor.draft.v1";
export const SESSION_KEY = "algo2lean.editor.active.v2";
const FIELDS = ["source", "filename", "savedSource", "savedFilename"];
const ANALYSIS_FIELDS = ["analysis", "analysisFilename", "savedAnalysis", "savedAnalysisFilename"];

function snapshot(value) {
  if (!value || !FIELDS.every((field) => typeof value[field] === "string")) {
    throw new TypeError("A draft requires source, filename, savedSource, and savedFilename strings.");
  }
  const result = Object.fromEntries(FIELDS.map((field) => [field, value[field]]));
  // Preserve the difference between a source-only draft with no analysis field
  // and a paired draft whose analysis was intentionally cleared.
  if (typeof value.analysis === "string") {
    result.analysis = value.analysis;
    result.analysisFilename = typeof value.analysisFilename === "string" ? value.analysisFilename : "Analysis.lean";
    result.savedAnalysis = typeof value.savedAnalysis === "string" ? value.savedAnalysis : "";
    result.savedAnalysisFilename = typeof value.savedAnalysisFilename === "string" ? value.savedAnalysisFilename : "";
  }
  return result;
}

function timestamp(value) {
  return typeof value === "number" && Number.isFinite(value) && value >= 0;
}

function parse(raw, id) {
  if (raw === null) return null;
  let value;
  try { value = JSON.parse(raw); } catch (_) { return null; }
  if (!value || value.id !== id || !timestamp(value.updatedAt) ||
      !FIELDS.every((field) => typeof value[field] === "string")) return null;
  return { id, ...snapshot(value), updatedAt: value.updatedAt };
}

export class Store {
  constructor(storage, sessionStorage, { makeId = () => globalThis.crypto.randomUUID(), now = Date.now } = {}) {
    this.storage = storage;
    this.sessionStorage = sessionStorage;
    this.makeId = makeId;
    this.now = now;
    this.baseline = null;
    this.ownedId = null;
    this.recoveredId = null;
  }

  get activeId() {
    return this.ownedId || this.recoveredId;
  }

  preferredId() {
    try { return this.sessionStorage.getItem(SESSION_KEY) || null; }
    catch (_) { return null; }
  }

  setPreferredId(id) {
    // The session pointer is only a convenience; the durable record is sufficient.
    try {
      if (id) this.sessionStorage.setItem(SESSION_KEY, id);
      else this.sessionStorage.removeItem(SESSION_KEY);
    } catch (_) { /* Private browsing may disable session storage separately. */ }
  }

  newId() {
    for (let attempt = 0; attempt < 20; attempt += 1) {
      const id = this.makeId();
      if (typeof id !== "string" || !id) throw new Error("Could not create a draft ID.");
      if (this.storage.getItem(PREFIX + id) === null) return id;
    }
    throw new Error("Could not create a unique draft ID.");
  }

  read(id) {
    if (typeof id !== "string" || !id) return null;
    return parse(this.storage.getItem(PREFIX + id), id);
  }

  list() {
    const ids = new Set();
    for (let index = 0; index < this.storage.length; index += 1) {
      const key = this.storage.key(index);
      if (key && key.startsWith(PREFIX)) ids.add(key.slice(PREFIX.length));
    }
    return Array.from(ids, (id) => this.read(id)).filter(Boolean)
      .sort((a, b) => b.updatedAt - a.updatedAt || a.id.localeCompare(b.id));
  }

  start(value, recoveredId = null) {
    this.baseline = snapshot(value);
    // A reload or duplicated tab may share a session pointer, never writer ownership.
    this.ownedId = null;
    this.recoveredId = recoveredId || null;
    this.setPreferredId(this.recoveredId);
  }

  hasChanges(value) {
    const current = snapshot(value);
    return !this.baseline || [...FIELDS, ...ANALYSIS_FIELDS].some((field) => current[field] !== this.baseline[field]);
  }

  write(value) {
    const current = snapshot(value);
    if (!this.hasChanges(current)) return false;
    let id = this.ownedId;
    // An explicitly discarded record must not reappear under its old ID.
    if (!id || this.storage.getItem(PREFIX + id) === null) id = this.newId();
    const updatedAt = this.now();
    if (!timestamp(updatedAt)) throw new Error("Could not determine the draft save time.");
    const record = { id, ...current, updatedAt };
    this.storage.setItem(PREFIX + id, JSON.stringify(record));
    // Quota and access errors leave the comparison baseline unchanged for retry.
    this.baseline = current;
    this.ownedId = id;
    this.setPreferredId(id);
    return true;
  }

  remove(id) {
    if (typeof id !== "string" || !id) return;
    this.storage.removeItem(PREFIX + id);
    if (id === this.activeId) {
      this.ownedId = null;
      this.recoveredId = null;
    } else if (id === this.recoveredId) {
      this.recoveredId = null;
    }
    // Retain the baseline so an unchanged page cannot resurrect a discarded draft.
    if (this.preferredId() === id) this.setPreferredId(this.activeId);
  }

  migrateLegacy() {
    const raw = this.storage.getItem(LEGACY_KEY);
    if (raw === null) return null;
    let legacy;
    try { legacy = JSON.parse(raw); } catch (_) { return null; }
    if (!legacy || typeof legacy.source !== "string" || typeof legacy.filename !== "string") return null;
    const id = this.newId();
    const updatedAt = timestamp(legacy.updatedAt) ? legacy.updatedAt : this.now();
    if (!timestamp(updatedAt)) throw new Error("Could not determine the draft save time.");
    const record = { id, ...snapshot({ ...legacy,
      savedSource: typeof legacy.savedSource === "string" ? legacy.savedSource : "",
      savedFilename: typeof legacy.savedFilename === "string" ? legacy.savedFilename : "",
    }), updatedAt };
    const encoded = JSON.stringify(record);
    this.storage.setItem(PREFIX + id, encoded);
    // Delete the old copy only after verifying the replacement and checking for edits.
    if (this.storage.getItem(PREFIX + id) !== encoded) throw new Error("Could not verify the migrated draft.");
    if (this.storage.getItem(LEGACY_KEY) === raw) this.storage.removeItem(LEGACY_KEY);
    return record;
  }
}
