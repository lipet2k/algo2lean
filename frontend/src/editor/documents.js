// Loading, editing, and replacing the standalone source and analysis documents.
import { safeFilename, moduleForFilename, starterAnalysis, analysisForExample } from "../lib/names.js";
import { INITIAL_SOURCE, INITIAL_FILENAME } from "./defaults.js";
import { EXAMPLE_SESSION, PROJECT_SESSION } from "./constants.js";
import { currentExample } from "./selectors.js";

export const documents = {
  dirty() {
    const state = this.state;
    return state.source !== state.savedSource || state.filename !== state.savedFilename;
  },

  analysisDirty() {
    const state = this.state;
    return state.analysis !== state.savedAnalysis || state.analysisFilename !== state.savedAnalysisFilename;
  },

  workspaceDirty() {
    if (!this.project) return this.dirty() || this.analysisDirty();
    return Object.values(this.projectSnapshot().files).some((file) => file.source !== file.savedSource || file.analysis !== file.savedAnalysis);
  },

  setModule(module, pointsModule = `${module}Points`) {
    const state = this.state;
    if (!module || (module === state.generatedModule && pointsModule === state.generatedPointsModule)) return;
    const wasStarter = !this.analysisDirty() && [true, false].some((facts) => state.analysis === starterAnalysis(state.generatedModule, facts));
    this.update({ generatedModule: module, generatedPointsModule: pointsModule });
    if (wasStarter) {
      const text = starterAnalysis(module, !(state.lastResult?.publicModule === module && state.lastResult.randomized));
      this.update({ analysis: text, savedAnalysis: text });
      this.invalidateAnalysis("Generated module changed. Check the analysis again.");
      this.scheduleDraft();
    }
  },

  updateSaveState(label) {
    this.update({ saveStateLabel: label || "Saved file" });
  },

  updateAnalysisSaveState(label) {
    this.update({ analysisSaveStateLabel: label || "Saved file" });
  },

  fileMessage(text, error = false) {
    this.update({ fileMessage: { text, error } });
  },

  analysisFileMessage(text, error = false) {
    this.update({ analysisFileMessage: { text, error } });
  },

  // Source edits from the editor component.
  edit(source) {
    this.batch(() => {
      this.update({ source });
      this.invalidate();
      this.updateSaveState();
      this.scheduleDraft();
    });
  },

  rename(filename) {
    this.batch(() => {
      this.update({ filename });
      this.invalidate();
      this.updateSaveState();
      this.scheduleDraft();
    });
  },

  editAnalysis(analysis) {
    this.batch(() => {
      this.analysisTouched = true;
      this.update({ analysis });
      this.invalidateAnalysis();
      this.updateAnalysisSaveState();
      this.scheduleDraft();
    });
  },

  renameAnalysis(analysisFilename) {
    this.batch(() => {
      this.analysisTouched = true;
      this.update({ analysisFilename });
      this.updateAnalysisSaveState();
      this.scheduleDraft();
    });
  },

  canReplace() {
    this.writeDraft();
    return !this.workspaceDirty() || this.hasDraftBackup() || this.options.confirm(this.project
      ? "Some project edits have no complete browser backup. Replace the project anyway? Choose Cancel and download the project first to keep every module."
      : "The current source and analysis have no complete browser backup. Replace them anyway? Choose Cancel and save each file first to keep your changes.");
  },

  // focus moves the caret into the editor with the reset, in one intent.
  loadDocument(text, name, label, { draft = null, example = null, focus = false } = {}) {
    this.batch(() => {
      this.options.clearTimeout(this.draftTimer);
      this.closeNewFileForm(false);
      this.project = null;
      this.standaloneDocument = null;
      this.projectControls();
      this.withSession((session) => session.removeItem(PROJECT_SESSION));
      this.withSession((session) => {
        if (example && !draft) session.setItem(EXAMPLE_SESSION, example.filename);
        else session.removeItem(EXAMPLE_SESSION);
      });
      const source = draft ? text : text.replace(/\r\n?/g, "\n");
      const filename = draft ? name : safeFilename(name, ".algo");
      const generatedModule = example?.module || moduleForFilename(filename);
      this.update({ source, filename,
        savedSource: draft ? draft.savedSource : source, savedFilename: draft ? draft.savedFilename : filename,
        generatedModule, generatedPointsModule: `${generatedModule}Points` });
      if (draft && typeof draft.analysis === "string") {
        this.loadAnalysis(draft.analysis, typeof draft.analysisFilename === "string" ? draft.analysisFilename : "Analysis.lean", "Recovered draft", draft);
      } else {
        const matching = draft ? null : example || this.state.examples.find((item) => !item.project_id && item.source === source);
        this.loadAnalysis(analysisForExample(matching, generatedModule), "Analysis.lean", matching?.analysis ? "Example" : "Starter");
      }
      this.draftBaseline = JSON.stringify(this.draftSnapshot());
      if (this.draftStore) this.draftStore.start(this.draftSnapshot(), draft ? draft.id : null);
      this.intent("source", { selection: [0, 0], scrollTop: 0, scrollLeft: 0, focus });
      this.update({ lastResult: null });
      this.invalidate();
      this.setLeanState("Not generated");
      this.update({ outputSummary: "Generated code is read only", pointsSummary: "Generated code is read only" });
      this.updateSaveState(label);
      this.draftStatus(draft ? "Browser draft restored" : "Draft stays in this browser", !this.draftStore);
      this.refreshDrafts();
      this.fileMessage("");
    });
  },

  loadAnalysis(text, name, label, draft = null, { focus = false } = {}) {
    this.batch(() => {
      const analysis = draft ? text : text.replace(/\r\n?/g, "\n");
      this.update({
        analysis,
        analysisFilename: draft || this.project ? name : safeFilename(name, ".lean"),
        savedAnalysis: draft ? (typeof draft.savedAnalysis === "string" ? draft.savedAnalysis : "") : analysis,
        savedAnalysisFilename: draft ? (typeof draft.savedAnalysisFilename === "string" ? draft.savedAnalysisFilename : "") : (draft || this.project ? name : safeFilename(name, ".lean")),
      });
      this.analysisTouched = true;
      this.intent("analysis", { selection: [0, 0], scrollTop: 0, scrollLeft: 0, focus });
      this.invalidateAnalysis("Check this analysis against the current source.");
      this.updateAnalysisSaveState(label);
      this.analysisFileMessage("");
    });
  },

  async chooseExample(index) {
    const example = this.state.examples[Number(index)];
    this.update({ exampleSelection: "" });
    if (!example || !this.canReplace()) return;
    if (example.project_id) { await this.openProjectExample(example); return; }
    this.loadDocument(example.source, example.filename, "Example", { example });
    this.compile(false);
  },

  loadCurrentExample() {
    const example = currentExample(this.state);
    if (!example) return Promise.resolve();
    return this.chooseExample(this.state.examples.indexOf(example));
  },

  // Open a standalone .algo file chosen with the file picker.
  async openFile(file) {
    if (!file) return;
    if (file.size > 1024 * 1024) { this.fileMessage("Choose an Algo2Lean file smaller than 1 MB.", true); return; }
    const opening = { revision: this.revision, analysisRevision: this.analysisRevision, analysisFilename: this.state.analysisFilename };
    try {
      const text = await file.text();
      if (this.revision !== opening.revision || this.analysisRevision !== opening.analysisRevision || opening.analysisFilename !== this.state.analysisFilename) {
        this.fileMessage("The workspace changed while the file was opening. Open the file again when you are ready.", true);
        return;
      }
      if (!this.canReplace()) return;
      this.loadDocument(text, file.name, "Opened file", { focus: true });
      this.compile(false);
    } catch (error) { this.fileMessage(`Could not open the file: ${error.message}`, true); }
  },

  async openAnalysisFile(file) {
    if (!file) return;
    if (file.size > 1024 * 1024) { this.analysisFileMessage("Choose a Lean file smaller than 1 MB.", true); return; }
    const opening = { revision: this.revision, analysisRevision: this.analysisRevision, analysisFilename: this.state.analysisFilename };
    try {
      const text = await file.text();
      if (opening.revision !== this.revision || opening.analysisRevision !== this.analysisRevision || opening.analysisFilename !== this.state.analysisFilename) {
        this.analysisFileMessage("The workspace changed while the file was opening. Open it again when you are ready.", true);
        return;
      }
      if (!this.canReplace()) return;
      // Keep the previous source/analysis pair available under its original ID.
      if (!this.project && this.draftStore) this.draftStore.start(this.draftSnapshot());
      this.loadAnalysis(text, this.project ? this.state.analysisFilename : file.name, "Opened file", null, { focus: true });
      this.writeDraft();
    } catch (error) { this.analysisFileMessage(`Could not open the analysis: ${error.message}`, true); }
  },

  closeProject() {
    if (!this.project || !this.canReplace()) return;
    const previous = this.standaloneDocument;
    if (previous) this.loadDocument(previous.source, previous.filename, "Restored file", { draft: previous });
    else this.loadDocument(INITIAL_SOURCE, INITIAL_FILENAME, "Example");
    this.compile(false);
  },

  openFind() {
    this.update({ findSerial: this.state.findSerial + 1 });
  },
};
