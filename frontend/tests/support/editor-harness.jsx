// Render the complete editor with injected storage, timers, backend, and
// window events, mirroring the browser facilities the store depends on.
import { act, fireEvent, render } from "@testing-library/react";
import { createRequire } from "node:module";
import path from "node:path";
import App from "../../src/App.jsx";
import { EditorStore } from "../../src/editor/store.js";
import { Store as DraftStore } from "../../src/lib/drafts.js";
import { MemoryStorage } from "./memory-storage.js";
import { ROOT } from "./paths.js";

const require = createRequire(path.join(ROOT, "frontend/tests/support/editor-harness.jsx"));
export const browserHost = require("../../../editor/browser-host.js");

let serial = 0;

export function archiveResponse(content = "zip bytes") {
  return { ok: true, blob: async () => new Blob([content], { type: "application/zip" }) };
}

export async function tick(rounds = 40) {
  await act(async () => { for (let index = 0; index < rounds; index++) await Promise.resolve(); });
}

export function editor(local = new MemoryStorage(), session = new MemoryStorage(), options = {}) {
  const requests = [];
  const downloads = [];
  const timers = new Map();
  let timerId = 0;
  let visibility = "visible";
  const windowEvents = new EventTarget();
  const documentEvents = new EventTarget();
  const confirm = { answer: () => true };
  const fetchImpl = async (url, request) => {
    requests.push({ url, request, body: request?.body ? JSON.parse(request.body) : null });
    if (options.fetch) {
      const custom = await options.fetch(url, request);
      if (custom) return custom;
    }
    if (url === "/api/analysis-export" || url === "/api/project-export") return archiveResponse();
    const body = request?.body ? JSON.parse(request.body) : {};
    const module = body.project_sources ? "Algo." + body.filename.replace(/\.algo$/, "").replace(/\//g, ".") : null;
    return { ok: true, blob: async () => new Blob(["zip bytes"], { type: "application/zip" }),
      json: async () => url === "/api/capabilities" ? { project_protocol: 1 } : url === "/api/examples"
        ? { examples: [{ name: "Other", source: "def other() -> Int:\n    return 5\n", filename: "other.algo",
          module: "OtherGenerated", analysis: "import OtherGenerated\nimport OtherGeneratedPoints\n-- example proof\n" }] }
        : url === "/api/publication" ? { version: "0.0.0-test", status: "development", authors: [] }
        : { lean: "def test := 1", points_lean: "-- named-line interface", shared_lean: "-- shared library",
          program_lean: "def test := 1", diagnostics: [], functions: [], ok: true,
          ...(module ? { module: module + ".Generated", points_module: module + ".Points", namespace: module } : {}) },
    };
  };
  const blocked = () => { throw new Error("Storage disabled"); };
  const store = new EditorStore({
    request: fetchImpl,
    hosted: Boolean(options.hosted),
    compareFiles: options.hosted ? browserHost.compareFiles : undefined,
    localStorage: options.blockStorageAccess ? blocked : () => local,
    sessionStorage: options.blockStorageAccess ? blocked : () => session,
    confirm: (message) => confirm.answer(message),
    showDirectoryPicker: null,
    setTimeout: (callback) => { timers.set(++timerId, callback); return timerId; },
    clearTimeout: (id) => timers.delete(id),
    now: () => Date.now(),
    makeId: () => `browser-${++serial}`,
    download: (content, name) => downloads.push({ name, content }),
    clipboard: { writeText: async () => {} },
    platform: "",
    windowEvents, documentEvents,
    getVisibilityState: () => visibility,
    activeElement: () => document.activeElement,
    fetchSiteConfig: async () => ({ ok: false }),
  });
  const view = render(<App store={store} />);
  act(() => { store.start(); });
  const byId = (id) => {
    const element = view.container.querySelector(`[id="${id}"]`);
    if (!element) throw new Error(`Unknown editor element #${id}`);
    return element;
  };
  const app = {
    store, local, session, requests, downloads, timers, windowEvents, documentEvents, confirm,
    container: view.container, byId,
    children: (id) => Array.from(byId(id).children),
    text: (id) => byId(id).textContent,
    ready: () => tick(),
    click: async (id) => { fireEvent.click(byId(id)); await tick(); },
    edit: async (text) => { fireEvent.input(byId("source"), { target: { value: text } }); await tick(4); },
    editAnalysis: async (text) => { fireEvent.input(byId("analysis"), { target: { value: text } }); await tick(4); },
    rename: async (id, name) => { fireEvent.input(byId(id), { target: { value: name } }); await tick(4); },
    openFile: async (id, name, text) => {
      fireEvent.change(byId(id), { target: { files: [{ name, size: text.length, text: async () => text }] } });
      await tick();
    },
    chooseFiles: async (id, files) => { fireEvent.change(byId(id), { target: { files } }); await tick(); },
    select: async (id, value) => { fireEvent.change(byId(id), { target: { value } }); await tick(); },
    flush: async () => {
      const pending = [...timers.values()];
      timers.clear();
      await act(async () => { for (const callback of pending) await callback(); });
      await tick(4);
    },
    records: () => new DraftStore(local, session).list(),
    setVisibility: (value) => { visibility = value; },
    dispatchWindow: async (type, fields = {}) => {
      const event = new Event(type, { cancelable: true });
      for (const [key, value] of Object.entries(fields)) Object.defineProperty(event, key, { value });
      await act(async () => { windowEvents.dispatchEvent(event); await Promise.resolve(); });
      await tick(4);
      return event;
    },
    dispatchDocument: async (type) => {
      await act(async () => { documentEvents.dispatchEvent(new Event(type)); await Promise.resolve(); });
      await tick(4);
    },
    unmount: () => { store.stop(); view.unmount(); },
  };
  return app;
}

export function descendants(element) {
  return [element, ...Array.from(element.children || []).flatMap(descendants)];
}

export function draftAction(app, sourceText, action) {
  const card = app.children("draft-list").find((candidate) =>
    descendants(candidate).some((element) => element.tagName === "PRE" && element.textContent === sourceText));
  if (!card) throw new Error(`Missing draft card for ${sourceText}`);
  const button = descendants(card).find((element) => element.tagName === "BUTTON" && element.textContent === action);
  if (!button) throw new Error(`Missing ${action} button`);
  return { click: async () => { fireEvent.click(button); await tick(); } };
}

export { fireEvent, act, MemoryStorage };
