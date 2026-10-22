// Browser draft recovery for standalone documents, and the shared draft list.
import { LEGACY_KEY, PREFIX } from "../lib/drafts.js";
import { starterAnalysis, moduleForFilename } from "../lib/names.js";
import { PROJECT_PREFIX, PROJECT_SESSION, DRAFT_DELAY } from "./constants.js";

export const drafts = {
  draftSnapshot() {
    const state = this.state;
    return { source: state.source, filename: state.filename, savedSource: state.savedSource, savedFilename: state.savedFilename,
      analysis: state.analysis, analysisFilename: state.analysisFilename, savedAnalysis: state.savedAnalysis, savedAnalysisFilename: state.savedAnalysisFilename };
  },

  draftNeedsSaving() {
    if (this.project) return JSON.stringify(this.projectSnapshot()) !== this.projectBaseline;
    return this.draftStore ? this.draftStore.hasChanges(this.draftSnapshot()) : JSON.stringify(this.draftSnapshot()) !== this.draftBaseline;
  },

  hasDraftBackup() {
    try {
      if (this.project) {
        const record = JSON.parse(this.storage().getItem(PROJECT_PREFIX + this.project.id));
        return this.validProjectRecord(record) && JSON.stringify(record.data) === JSON.stringify(this.projectSnapshot());
      }
      const draft = this.draftStore && (this.draftStore.read(this.draftStore.activeId) ||
        JSON.parse(this.storage().getItem(LEGACY_KEY)));
      if (!draft || draft.source !== this.state.source || draft.filename !== this.state.filename) return false;
      // Source-only drafts can reconstruct their untouched starter analysis.
      const text = typeof draft.analysis === "string" ? draft.analysis : starterAnalysis(moduleForFilename(draft.filename));
      const name = typeof draft.analysisFilename === "string" ? draft.analysisFilename : "Analysis.lean";
      return text === this.state.analysis && name === this.state.analysisFilename;
    } catch (_) { return false; }
  },

  draftStatus(text, failed = false) {
    this.draftFailed = failed;
    this.update({ draftStatus: { text, failed } });
  },

  writeDraft() {
    this.options.clearTimeout(this.draftTimer);
    if (this.project) return this.writeProjectDraft();
    if (!this.draftNeedsSaving()) return true;
    try {
      if (!this.draftStore) throw new Error("Browser storage unavailable");
      this.draftStore.write(this.draftSnapshot());
      this.draftStatus("Draft saved in this browser");
      this.refreshDrafts();
      return true;
    } catch (_) {
      this.draftStatus("Draft could not be saved. Save source and analysis to keep your work.", true);
      return false;
    }
  },

  scheduleDraft() {
    this.options.clearTimeout(this.draftTimer);
    if (!this.draftNeedsSaving()) {
      this.draftStatus(this.hasDraftBackup() ? "Draft saved in this browser" : "No pending draft changes");
      return;
    }
    if (!this.draftFailed) this.update({ draftStatus: { text: "Saving browser draft…", failed: false } });
    this.draftTimer = this.options.setTimeout(() => this.writeDraft(), DRAFT_DELAY);
  },

  legacyDraft() {
    try {
      const draft = JSON.parse(this.storage().getItem(LEGACY_KEY));
      if (!draft || typeof draft.source !== "string" || typeof draft.filename !== "string") return null;
      return { ...draft, id: null,
        savedSource: typeof draft.savedSource === "string" ? draft.savedSource : "",
        savedFilename: typeof draft.savedFilename === "string" ? draft.savedFilename : "" };
    } catch (_) { return null; }
  },

  refreshDrafts() {
    if (!this.draftStore) return [];
    try {
      const list = this.draftStore.list();
      // Quota failures can prevent migration; keep the original recoverable
      // without replacing the default example or requiring another write.
      const legacy = this.legacyDraft();
      if (legacy) list.push(legacy);
      const projects = this.projectDrafts();
      const activeId = this.draftStore.activeId;
      this.update({
        drafts: list.map((draft) => ({ ...draft, active: Boolean(draft.id && draft.id === activeId) })),
        projectDrafts: projects,
        draftPickerVisible: this.state.draftPickerVisible || list.length + projects.length > 0,
      });
      return list;
    } catch (_) {
      this.fileMessage("Browser drafts could not be listed. Save source and analysis to keep your current work.", true);
      return [];
    }
  },

  showDrafts() {
    this.refreshDrafts();
    this.update({ draftPickerVisible: true, draftPickerOpen: true });
    this.intent("drafts", { focus: true });
  },

  setDraftPickerOpen(open) {
    if (this.state.draftPickerOpen !== open) this.update({ draftPickerOpen: open });
  },

  recoverDraft(id) {
    try {
      if (!this.canReplace()) return;
      const latest = id ? this.draftStore.read(id) : this.legacyDraft();
      if (!latest) { this.refreshDrafts(); this.fileMessage("This draft was discarded in another tab."); return; }
      this.loadDocument(latest.source, latest.filename, "Recovered draft", { draft: latest, focus: true });
      this.update({ draftPickerOpen: false });
      this.compile(false);
    } catch (_) { this.fileMessage("This draft could not be read. Browser storage may be unavailable.", true); }
  },

  discardDraft(id, filename) {
    if (!this.options.confirm(`Discard the browser draft for ${filename}? This cannot be undone. Any open editor text will remain.`)) return;
    try {
      const active = id && id === this.draftStore.activeId;
      if (id) this.draftStore.remove(id);
      else this.storage().removeItem(LEGACY_KEY);
      if (active) {
        this.options.clearTimeout(this.draftTimer);
        this.draftStore.start(this.draftSnapshot());
        this.draftStatus("Draft discarded. Edit to create a new draft, or save source and analysis.");
      }
      this.refreshDrafts();
      this.element("drafts-button")?.focus();
      this.fileMessage(`Discarded the browser draft for ${filename}.`);
    } catch (_) { this.fileMessage("The draft could not be discarded. Try again when browser storage is available.", true); }
  },

  clearDrafts() {
    try {
      // Read every record before deleting any. The archive lives only in this
      // page's memory and supports Undo until the page is closed or reloaded.
      const storage = this.storage();
      const records = [];
      for (let index = 0; index < storage.length; index += 1) {
        const key = storage.key(index);
        if (key === LEGACY_KEY || key?.startsWith(PREFIX) || key?.startsWith(PROJECT_PREFIX)) {
          records.push([key, storage.getItem(key)]);
        }
      }
      for (const [key, value] of records) {
        this.clearedDrafts.set(key, value);
        storage.removeItem(key);
      }
      this.options.clearTimeout(this.draftTimer);
      this.draftBaseline = JSON.stringify(this.draftSnapshot());
      this.draftStore?.start(this.draftSnapshot());
      if (this.project) {
        this.project.id = null;
        this.projectWritable = false;
        this.projectBaseline = JSON.stringify(this.projectSnapshot());
      }
      if (this.standaloneDocument) this.standaloneDocument.id = null;
      this.withSession((session) => session.removeItem(PROJECT_SESSION));
      this.draftStatus("Browser drafts cleared. New edits create a new draft.");
      this.fileMessage("All browser drafts cleared. Open code is unchanged. Undo clear is available until you reload or close this page.");
    } catch (_) {
      this.fileMessage("Some drafts could not be cleared. Undo clear can restore any removed drafts; try again when browser storage is available.", true);
    }
    this.update({ undoClearAvailable: this.clearedDrafts.size > 0 });
    this.refreshDrafts();
  },

  undoClearDrafts() {
    try {
      const storage = this.storage();
      for (const [key, value] of this.clearedDrafts) {
        // Later edits have their own records. Never overwrite a newer record.
        const current = storage.getItem(key);
        if (current === null) storage.setItem(key, value);
        if (current === null || current === value) this.clearedDrafts.delete(key);
      }
      this.fileMessage(this.clearedDrafts.size ? "Restored available drafts. Newer records were kept." : "Browser drafts restored. Use Recover to open one.");
    } catch (_) {
      this.fileMessage("Some drafts could not be restored. Keep this page open and try Undo clear again when browser storage is available.", true);
    }
    this.update({ undoClearAvailable: this.clearedDrafts.size > 0 });
    this.refreshDrafts();
  },

  handleStorageEvent(event) {
    if (event.key === null || event.key.startsWith(PROJECT_PREFIX)) {
      this.refreshDrafts();
      if (this.project && !this.draftNeedsSaving() && !this.hasDraftBackup()) this.draftStatus("This project draft is no longer stored. Download the project to keep your edits.", true);
    }
    if (event.key === null || event.key.startsWith(PREFIX)) {
      this.refreshDrafts();
      if (this.draftStore && this.draftStore.activeId && !this.draftNeedsSaving() && !this.hasDraftBackup()) {
        this.draftStatus("This draft is no longer stored. Edit to create a new draft, or save source and analysis.", true);
      }
    }
  },
};
