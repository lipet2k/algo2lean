// Downloads and clipboard actions for the source and generated files.
import { safeFilename } from "../lib/names.js";
import { currentOutput } from "./selectors.js";

export const exports = {
  download(content, name) {
    this.options.download(content, name);
  },

  leanFilename() {
    return `${this.state.lastResult.module}.lean`;
  },

  saveSource() {
    const name = safeFilename(this.state.filename, ".algo");
    if (!this.project && this.state.filename !== name) {
      this.update({ filename: name });
      this.invalidate();
    }
    try {
      this.download(this.state.source, name);
      this.batch(() => {
        this.update({ savedSource: this.state.source, savedFilename: this.project ? this.state.filename : name });
        this.updateSaveState("Downloaded");
        this.writeDraft();
        this.fileMessage(this.project ? `Downloaded ${name}. Save it as ${this.state.filename} in your project folder.` : `Downloaded ${name}. Your browser chooses where the file is saved.`);
      });
    } catch (error) { this.fileMessage(`Could not download the source: ${error.message}`, true); }
  },

  exportLean() {
    if (!currentOutput(this.state)) { this.fileMessage("Compile the current source before exporting Lean.", true); return; }
    const result = this.state.lastResult;
    const name = this.leanFilename();
    try {
      this.download(result.lean, name);
      this.fileMessage(result.view === "probability"
        ? `Downloaded probability interface ${name}. Check it with the matching algorithm definitions and the optional probability/ Mathlib project.`
        : result.view === "parallel"
          ? `Downloaded parallel contracts ${name}. Keep it with its generated project dependencies.`
          : `Downloaded algorithm definitions ${name}. Include Algo2Lean.lean in your Lean project; export ${result.pointsModule}.lean separately for named-line helpers.`);
    } catch (error) { this.fileMessage(`Could not export Lean: ${error.message}`, true); }
  },

  exportPoints() {
    const result = this.state.lastResult;
    if (!currentOutput(this.state) || !result.points) { this.fileMessage("Compile the current source before exporting the named-line interface.", true); return; }
    const name = `${result.pointsModule}.lean`;
    try {
      this.download(result.points, name);
      this.fileMessage(`Downloaded named-line interface ${name}. This file imports ${result.module}; keep it alongside ${this.leanFilename()} in your Lean project.`);
    } catch (error) { this.fileMessage(`Could not export the named-line interface: ${error.message}`, true); }
  },

  downloadLibrary() {
    if (!currentOutput(this.state)) return;
    this.download(this.state.lastResult.shared, "Algo2Lean.lean");
    this.fileMessage("Downloaded Algo2Lean.lean. Add it to your Lean project and build the library before checking generated imports.");
  },

  exportStandalone() {
    if (!currentOutput(this.state) || this.state.lastResult.view === "probability") return;
    const result = this.state.lastResult;
    const name = this.leanFilename();
    this.download(result.shared.trimEnd() + "\n\n" + result.program, name);
    this.fileMessage(`Downloaded standalone algorithm definitions ${name}, including the shared library. Export ${result.pointsModule}.lean separately if your proof uses named-line helpers.`);
  },

  async copyLean() {
    if (!currentOutput(this.state)) { this.fileMessage("Compile the current source before copying Lean.", true); return; }
    try { await this.options.clipboard.writeText(this.state.lastResult.lean); this.fileMessage(this.state.lastResult.view === "probability" ? "Probability interface copied to the clipboard."
      : this.state.lastResult.view === "parallel" ? "Parallel contracts copied to the clipboard." : "Algorithm definitions copied to the clipboard."); }
    catch (_) { this.fileMessage("Clipboard access is unavailable. Select the generated code to copy it, or Export .lean.", true); }
  },

  async copyPoints() {
    if (!currentOutput(this.state) || !this.state.lastResult.points) { this.fileMessage("Compile the current source before copying the named-line interface.", true); return; }
    try { await this.options.clipboard.writeText(this.state.lastResult.points); this.fileMessage("Named-line interface copied to the clipboard."); }
    catch (_) { this.fileMessage("Clipboard access is unavailable. Select the named-line interface to copy it, or Export .lean.", true); }
  },
};
