// The editor's state and actions, independent of React. Components subscribe to
// immutable state snapshots and call actions; imperative needs (selection,
// scrolling, focus) are expressed as intents that the components apply.
import { createCatalog } from "../lib/interface.js";
import { Store as DraftStore } from "../lib/drafts.js";
import { moduleForFilename, starterAnalysis } from "../lib/names.js";
import { request as hostRequest, isHosted, compareFiles as hostCompareFiles } from "../lib/backend.js";
import { INITIAL_SOURCE, INITIAL_FILENAME, INITIAL_ANALYSIS_FILENAME } from "./defaults.js";
import { documents } from "./documents.js";
import { drafts } from "./drafts.js";
import { projects } from "./projects.js";
import { compilation } from "./compile.js";
import { analysis } from "./analysis.js";
import { exports as exportActions } from "./exports.js";
import { generation } from "./generation.js";

function browserDownload(content, name) {
  const blob = content instanceof Blob ? content : new Blob([content], { type: "text/plain;charset=utf-8" });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = name;
  document.body.append(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function defaultOptions(options) {
  const win = typeof window === "undefined" ? null : window;
  return {
    request: hostRequest,
    fetchSiteConfig: () => fetch(new URL("release-config.json", document.baseURI), { cache: "no-cache" }),
    hosted: isHosted(),
    compareFiles: hostCompareFiles,
    localStorage: () => globalThis.localStorage,
    sessionStorage: () => globalThis.sessionStorage,
    confirm: (message) => win ? win.confirm(message) : true,
    showDirectoryPicker: win?.showDirectoryPicker ? (settings) => win.showDirectoryPicker(settings) : null,
    setTimeout: (...args) => globalThis.setTimeout(...args),
    clearTimeout: (id) => globalThis.clearTimeout(id),
    now: () => Date.now(),
    makeId: () => globalThis.crypto.randomUUID(),
    download: browserDownload,
    clipboard: typeof navigator === "undefined" ? null : navigator.clipboard,
    platform: typeof navigator === "undefined" ? "" : navigator.platform || "",
    windowEvents: win,
    documentEvents: typeof document === "undefined" ? null : document,
    getVisibilityState: () => (typeof document === "undefined" ? "visible" : document.visibilityState),
    activeElement: () => (typeof document === "undefined" ? null : document.activeElement),
    ...options,
  };
}

export function initialState(options) {
  const generatedModule = moduleForFilename(INITIAL_FILENAME);
  const starter = starterAnalysis(generatedModule);
  return {
    hosted: Boolean(options.hosted),
    apple: /Mac|iPhone|iPad/.test(options.platform || ""),
    revision: 0,
    source: INITIAL_SOURCE, filename: INITIAL_FILENAME, savedSource: INITIAL_SOURCE, savedFilename: INITIAL_FILENAME,
    analysis: starter, analysisFilename: INITIAL_ANALYSIS_FILENAME, savedAnalysis: starter, savedAnalysisFilename: INITIAL_ANALYSIS_FILENAME,
    saveStateLabel: "Example", analysisSaveStateLabel: "Starter",
    toast: null,
    generatedModule, generatedPointsModule: `${generatedModule}Points`,
    examples: [], examplesUnavailable: false, exampleSelection: "", exampleAnalyses: [],
    busy: false, busyCheck: false,
    compileStatus: { text: "Ready to compile", tone: "" },
    leanState: { text: "Not generated", tone: "" },
    diagnostics: { note: "Compile your source to describe its valid inputs and outputs in Lean.", items: [] },
    lastResult: null,
    catalog: createCatalog(),
    outputSummary: "Generated code is read only", pointsSummary: "Generated code is read only",
    checkOutput: null, checkOpen: false,
    sharedVisible: false, sharedOpen: false, sharedSummary: "Shared Lean library · Algo2Lean.lean",
    relations: null, relationsHidden: true,
    fileMessage: { text: "", error: false },
    draftStatus: { text: "Local draft", failed: false },
    analysisBusy: false,
    analysisStatus: { text: "Write theorems here, then check them against the current source.", tone: "", badge: "Not checked" },
    analysisDiagnostics: [], analysisOutput: null, analysisOpen: false,
    analysisFileMessage: { text: "", error: false },
    analysisSaving: false,
    drafts: [], projectDrafts: [], draftPickerVisible: false, draftPickerOpen: false, undoClearAvailable: false,
    project: null, projectExporting: false, openingFolder: false,
    newFileOpen: false, newFileName: "", newFileHelp: { text: "Choose a name ending in .algo.", error: false },
    generationStatus: "An exact match identifies the compiler output. It does not check a Lean proof or prove the compiler's semantics correct.",
    generationDetails: "",
    sourceIntent: null, analysisIntent: null, findSerial: 0,
  };
}

export class EditorStore {
  constructor(options = {}) {
    this.options = defaultOptions(options);
    this.state = initialState(this.options);
    this.listeners = new Set();
    this.elements = new Map();
    this.batchDepth = 0;
    this.pendingNotify = false;
    this.hosted = this.state.hosted;
    // Request bookkeeping and baselines are not rendered.
    this.requestSerial = 0;
    this.activeRequest = null;
    this.draftTimer = null;
    this.draftFailed = false;
    this.draftStore = null;
    this.draftBaseline = "";
    this.clearedDrafts = new Map();
    this.analysisRevision = 0;
    this.analysisRequestSerial = 0;
    this.activeAnalysisRequest = null;
    this.analysisExport = null;
    this.generationController = null;
    this.analysisTouched = false;
    this.project = null;
    this.standaloneDocument = null;
    this.projectBaseline = "";
    this.projectWritable = false;
    this.projectOpening = 0;
    this.folderOpening = null;
    this.projectExport = null;
    this.cleanup = [];
  }

  subscribe(listener) {
    this.listeners.add(listener);
    return () => this.listeners.delete(listener);
  }

  getState() {
    return this.state;
  }

  update(patch) {
    this.state = { ...this.state, ...patch };
    this.notify();
  }

  notify() {
    if (this.batchDepth) { this.pendingNotify = true; return; }
    for (const listener of [...this.listeners]) listener(this.state);
  }

  batch(work) {
    this.batchDepth += 1;
    try { return work(); }
    finally {
      this.batchDepth -= 1;
      if (!this.batchDepth && this.pendingNotify) { this.pendingNotify = false; this.notify(); }
    }
  }

  get revision() { return this.state.revision; }
  set revision(value) { this.update({ revision: value }); }

  attach(name, element) { if (element) this.elements.set(name, element); }
  detach(name, element) { if (!element || this.elements.get(name) === element) this.elements.delete(name); }
  element(name) { return this.elements.get(name) || null; }

  // Selection, scroll, and focus requests for the code editors. The component
  // applies them after the matching text has been committed to the DOM.
  intent(target, fields) {
    const key = `${target}Intent`;
    this.update({ [key]: { ...fields, serial: (this.state[key]?.serial || 0) + 1 } });
  }

  // Brief confirmations shown by the Toast component; a new message replaces
  // the previous one and the timer is injectable for the tests.
  showToast(text, { tone = "success", duration = 3200 } = {}) {
    this.options.clearTimeout(this.toastTimer);
    const toast = { id: (this.state.toast?.id || 0) + 1, text, tone };
    this.update({ toast });
    this.toastTimer = this.options.setTimeout(() => { if (this.state.toast?.id === toast.id) this.update({ toast: null }); }, duration);
  }

  dismissToast() {
    this.options.clearTimeout(this.toastTimer);
    if (this.state.toast) this.update({ toast: null });
  }

  request(path, init) { return this.options.request(path, init); }
  session() { return this.options.sessionStorage(); }
  storage() { return this.options.localStorage(); }
  withSession(work) { try { work(this.session()); } catch (_) { /* Session storage is an optional convenience. */ } }

  start() {
    const { windowEvents, documentEvents } = this.options;
    const listen = (target, type, handler) => {
      if (!target) return;
      target.addEventListener(type, handler);
      this.cleanup.push(() => target.removeEventListener(type, handler));
    };
    listen(windowEvents, "storage", (event) => this.handleStorageEvent(event));
    listen(windowEvents, "beforeunload", (event) => {
      this.writeDraft();
      if (this.workspaceDirty() && !this.hasDraftBackup()) { event.preventDefault(); event.returnValue = ""; }
    });
    listen(documentEvents, "visibilitychange", () => { if (this.options.getVisibilityState() === "hidden") this.writeDraft(); });
    listen(documentEvents, "keydown", (event) => {
      if (event.isComposing || !(event.metaKey || event.ctrlKey) || event.altKey) return;
      const inAnalysis = Boolean(this.options.activeElement()?.closest?.("#analysis-workspace"));
      if (event.key.toLowerCase() === "s") { event.preventDefault(); inAnalysis ? this.saveAnalysis() : this.saveSource(); }
      if (event.key === "Enter") { event.preventDefault(); inAnalysis ? this.analyze() : this.compile(false); }
    });
    return this.initialize();
  }

  stop() {
    for (const dispose of this.cleanup.splice(0)) dispose();
    this.options.clearTimeout(this.draftTimer);
    this.options.clearTimeout(this.toastTimer);
    this.activeRequest?.abort();
    this.activeAnalysisRequest?.abort();
    this.generationController?.abort();
  }

  async initialize() {
    // Every page load starts with merge sort. Saved work is opened explicitly
    // from Browser drafts, including drafts remembered by this tab's session.
    this.draftBaseline = JSON.stringify(this.draftSnapshot());
    let migrationFailed = false;
    try {
      let session = null;
      try { session = this.session(); } catch (_) { /* Recovery still works through the picker. */ }
      this.draftStore = new DraftStore(this.storage(), session, { makeId: this.options.makeId, now: this.options.now });
      try { this.draftStore.migrateLegacy(); }
      catch (_) { migrationFailed = true; }
      this.draftStore.start(this.draftSnapshot());
      this.updateSaveState("Example");
      this.draftStatus("Draft stays in this browser");
      this.refreshDrafts();
      if (migrationFailed) this.draftStatus("Existing draft could not be migrated. Open Browser drafts to recover it.", true);
    } catch (_) {
      this.draftStore = null;
      this.updateSaveState();
      this.draftStatus("Browser draft unavailable. Save source and analysis to keep your work.", true);
    }
    const initialRevision = this.revision;
    const initialProjectOpening = this.projectOpening;
    const initialDocument = JSON.stringify(this.draftSnapshot());
    this.updateAnalysisSaveState("Starter");
    this.compile(false);
    try {
      const response = await this.request("/api/examples");
      if (!response.ok) throw new Error("Examples unavailable");
      const data = await response.json();
      const examples = (data.examples || []).filter((item) => typeof item.source === "string");
      this.update({ examples, exampleAnalyses: examples.map((example) => example.analysis).filter((text) => typeof text === "string") });
      const defaultExample = examples.find((example) => !example.project_id && example.filename === INITIAL_FILENAME);
      if (defaultExample && !this.project && !this.analysisTouched && this.revision === initialRevision &&
          this.projectOpening === initialProjectOpening && JSON.stringify(this.draftSnapshot()) === initialDocument) {
        // Fetch the current source and proof together without replacing work
        // opened or edited while the example catalog was loading.
        this.loadDocument(defaultExample.source, defaultExample.filename, "Example", { example: defaultExample });
        this.update({ exampleSelection: String(examples.indexOf(defaultExample)) });
        if (migrationFailed) this.draftStatus("Existing draft could not be migrated. Open Browser drafts to recover it.", true);
        this.compile(false);
      }
    } catch (_) { this.update({ examplesUnavailable: true }); }
  }
}

Object.assign(EditorStore.prototype, documents, drafts, projects, compilation, analysis, exportActions, generation);
