// A Storage double with controllable failures, shared by the draft and editor tests.
export class MemoryStorage {
  constructor(entries = []) {
    this.data = new Map(entries);
    this.writes = [];
    this.fail = new Set();
  }

  check(operation) {
    if (this.fail.has(operation)) throw new Error(`Storage ${operation} unavailable`);
  }

  get length() { this.check("read"); return this.data.size; }
  key(index) { this.check("read"); return [...this.data.keys()][index] ?? null; }
  getItem(key) { this.check("read"); return this.data.get(key) ?? null; }
  setItem(key, value) {
    this.check("write");
    this.writes.push([key, String(value)]);
    this.data.set(key, String(value));
  }
  removeItem(key) { this.check("remove"); this.data.delete(key); }
  copy() { return new MemoryStorage(this.data); }
}
