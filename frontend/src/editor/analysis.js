// Checking and packaging the handwritten Lean analysis.
import { safeFilename } from "../lib/names.js";
import { currentOutput } from "./selectors.js";

export const analysis = {
  setAnalysisStatus(text, tone = "", badge = "Not checked") {
    this.update({ analysisStatus: { text, tone, badge } });
  },

  setAnalysisBusy(busy) {
    this.update({ analysisBusy: busy });
  },

  invalidateAnalysis(message = "Analysis changed. Check it again to verify these changes.") {
    this.batch(() => {
      this.invalidateGeneration();
      this.analysisRevision += 1;
      this.analysisRequestSerial += 1;
      if (this.activeAnalysisRequest) this.activeAnalysisRequest.abort();
      this.activeAnalysisRequest = null;
      this.setAnalysisBusy(false);
      this.update({ analysisOutput: null, analysisDiagnostics: [] });
      this.setAnalysisStatus(message, "stale", "Needs check");
    });
  },

  showAnalysisDiagnostics(items) {
    this.update({ analysisDiagnostics: items || [] });
  },

  jumpToAnalysis(line, column) {
    const text = this.state.analysis;
    const lines = text.split("\n");
    const safeLine = Math.max(1, Math.min(line, lines.length));
    const start = lines.slice(0, safeLine - 1).reduce((total, item) => total + item.length + 1, 0);
    const position = start + Math.min(Math.max(column - 1, 0), lines[safeLine - 1].length);
    this.intent("analysis", { focus: true, preventScroll: true, selection: [position, Math.min(position + 1, text.length)],
      scrollTop: Math.max(0, (safeLine - 3) * 24), scrollLeft: Math.max(0, (column - 12) * 8.4), scrollIntoView: true });
  },

  toggleAnalysisDetails(open) {
    if (this.state.analysisOpen !== open) this.update({ analysisOpen: open });
  },

  toggleCheckDetails(open) {
    if (this.state.checkOpen !== open) this.update({ checkOpen: open });
  },

  toggleShared(open) {
    if (this.state.sharedOpen !== open) this.update({ sharedOpen: open });
  },

  async analyze() {
    if (this.hosted) {
      this.setAnalysisStatus("Save this analysis and check it in the local Algo2Lean editor with Lean installed.", "", "Local checking required");
      return;
    }
    if (this.activeAnalysisRequest) this.activeAnalysisRequest.abort();
    const serial = ++this.analysisRequestSerial;
    const snapshot = { source: this.state.source, filename: this.state.filename, revision: this.revision,
      analysis: this.state.analysis, analysisRevision: this.analysisRevision };
    const controller = new AbortController();
    this.activeAnalysisRequest = controller;
    this.batch(() => {
      this.setAnalysisBusy(true);
      this.setAnalysisStatus("Checking your analysis against the current algorithm…", "", "Checking…");
      this.update({ analysisOutput: null, analysisDiagnostics: [] });
      this.analysisFileMessage("");
    });
    const isCurrent = () => serial === this.analysisRequestSerial && snapshot.revision === this.revision && snapshot.analysisRevision === this.analysisRevision;
    try {
      if (this.project) await this.requireProjectSupport(controller.signal);
      if (!isCurrent()) return;
      const response = await this.request("/api/analyze", {
        method: "POST", headers: this.requestHeaders(),
        body: JSON.stringify(this.projectRequest(snapshot)), signal: controller.signal,
      });
      let result;
      try { result = await response.json(); }
      catch (_) { throw new Error("The analysis checker returned an unreadable response. Restart the local editor server and try again."); }
      if (!isCurrent()) return;
      if (result.scope === "setup") {
        this.setStatus("Compiler setup needs attention", "error");
        this.setLeanState("Compilation unavailable", "error");
        this.rejectOutput();
        this.setAnalysisStatus("Compiler setup needs attention. Your source and analysis remain available to save.", "error", "Not checked");
        this.showAnalysisDiagnostics([{ message: result.message || "Check the compiler installation and try again." }]);
        return;
      }
      if (typeof result.lean === "string" && !currentOutput(this.state)) {
        this.showGenerated(result, snapshot);
        this.setLeanState("Generated", "generated");
        this.setStatus("Compilation successful", "success");
      }
      if (!isCurrent()) return;
      if (result.diagnostics?.length) {
        this.showDiagnostics(result.diagnostics);
        this.setStatus("Source errors to resolve", "error");
        this.setLeanState("Compilation failed", "error");
        this.rejectOutput();
        this.setAnalysisStatus("Fix the source errors in the Lean Interface panel, then check the analysis again.", "error", "Source error");
        return;
      }
      this.showAnalysisDiagnostics(result.analysis_diagnostics);
      this.update({ analysisOutput: result.output || result.message || result.error || (result.ok ? "Lean completed without errors." : "No checker output was returned."),
        analysisOpen: !result.ok });
      if (result.available === false) {
        this.setAnalysisStatus("Lean checker unavailable. Your source and analysis remain available to save.", "", "Not checked");
      } else if (response.ok && result.ok) {
        this.setAnalysisStatus("Lean accepted this analysis for the current source.", "success", "Lean checked");
      } else {
        this.setAnalysisStatus(result.error || result.message || "Lean reported a problem in the analysis. Review the messages below.", "error", "Check failed");
      }
    } catch (error) {
      if (error.name === "AbortError" || !isCurrent()) return;
      this.setAnalysisStatus(error.name === "ServerUpdateError" ? "Editor server needs restarting." : "Could not reach the analysis checker.", "error", "Not checked");
      this.showAnalysisDiagnostics([{ message: error.message || "Start the local editor server and try again." }]);
    } finally {
      if (serial === this.analysisRequestSerial) { this.activeAnalysisRequest = null; this.setAnalysisBusy(false); }
    }
  },

  async saveAnalysis() {
    const state = this.state;
    const name = safeFilename(state.analysisFilename, ".lean");
    const reserved = ["Algo2Lean.lean", `${state.generatedModule}.lean`, `${state.generatedPointsModule}.lean`];
    if (reserved.some((file) => file.toLowerCase() === name.toLowerCase())) {
      this.analysisFileMessage(`Choose an analysis filename different from ${reserved.join(", ")}.`, true);
      this.element("analysis-filename")?.focus();
      return;
    }
    if (this.analysisExport) this.analysisExport.abort();
    const controller = new AbortController();
    this.analysisExport = controller;
    const project = this.project;
    const snapshot = { source: state.source, filename: state.filename, analysis: state.analysis,
      analysisFilename: state.analysisFilename, revision: this.revision, analysisRevision: this.analysisRevision };
    const unchanged = () => !controller.signal.aborted && project === this.project &&
      snapshot.revision === this.revision && snapshot.analysisRevision === this.analysisRevision &&
      snapshot.filename === this.state.filename && snapshot.analysisFilename === this.state.analysisFilename;
    this.batch(() => {
      this.update({ analysisSaving: true });
      this.analysisFileMessage("Preparing your proof, generated definitions, and shared Lean libraries…");
    });
    try {
      const payload = { ...this.projectRequest(snapshot), analysis_filename: name };
      const response = await this.request("/api/analysis-export", { method: "POST", headers: this.requestHeaders(),
        body: JSON.stringify(payload), signal: controller.signal });
      if (!response.ok) {
        if (response.status === 404) throw new Error("Restart the local editor with python3 -m editor.server to enable full analysis packages.");
        const error = await response.json();
        throw new Error(error.message || error.error || error.analysis_diagnostics?.[0]?.message || error.diagnostics?.[0]?.message || "Analysis export failed.");
      }
      const archive = await response.blob();
      if (!unchanged()) {
        if (project === this.project) this.analysisFileMessage("The workspace changed while the package was being prepared. Save analysis again to download the current files.");
        return;
      }
      const packageName = name.replace(/\.lean$/i, "") + ".zip";
      this.download(archive, packageName);
      this.batch(() => {
        const patch = { savedAnalysis: this.state.analysis, savedAnalysisFilename: this.project ? this.state.analysisFilename : name };
        if (!this.project) patch.analysisFilename = name;
        this.update(patch);
        this.updateAnalysisSaveState("Downloaded");
        this.writeDraft();
        this.analysisFileMessage(`Downloaded ${packageName}, including the shared Lean libraries and all resolved imports. Extract the ZIP, open its folder in your Lean editor, and run lake build to check the analysis. Downloading does not check the proof.`);
      });
    } catch (error) {
      if (error.name !== "AbortError" && unchanged()) this.analysisFileMessage(`Could not save the analysis package: ${error.message}`, true);
    } finally {
      if (this.analysisExport === controller) {
        this.analysisExport = null;
        this.update({ analysisSaving: false });
      }
    }
  },
};
