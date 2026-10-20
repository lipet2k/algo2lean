// Compilation requests and the generated Lean output they produce.
import { createCatalog } from "../lib/interface.js";
import { moduleForFilename, projectModule, starterAnalysis } from "../lib/names.js";

export const compilation = {
  setStatus(text, tone = "") {
    this.update({ compileStatus: { text, tone } });
  },

  setLeanState(text, tone = "") {
    this.update({ leanState: { text, tone } });
  },

  setBusy(busy, check = false) {
    this.update({ busy, busyCheck: check });
  },

  showDiagnostics(items) {
    this.update({ diagnostics: { note: null, items } });
  },

  diagnosticNote(note, probabilityNote = null) {
    this.update({ diagnostics: { note, probabilityNote, items: [] } });
  },

  rejectOutput() {
    const result = this.state.lastResult;
    this.update({ lastResult: result ? { ...result, available: false } : result, sharedVisible: false, relationsHidden: true });
  },

  invalidate() {
    this.batch(() => {
      this.revision += 1;
      this.invalidateAnalysis("Source changed. Check the analysis against the updated algorithm.");
      const filename = this.state.filename;
      this.setModule(this.project ? projectModule(filename) + ".Generated" : moduleForFilename(filename),
        this.project ? projectModule(filename) + ".Points" : undefined);
      if (this.activeRequest) {
        this.activeRequest.abort();
        this.activeRequest = null;
        this.requestSerial += 1;
        this.setBusy(false);
      }
      if (this.state.lastResult) {
        this.setLeanState("Source changed", "stale");
        this.update({ outputSummary: "Compile again to update this output", pointsSummary: "Compile again to update this output" });
      }
      this.rejectOutput();
      this.update({ checkOutput: null });
      this.diagnosticNote("Source changed. Compile to update the generated Lean code.");
      this.setStatus("Changes awaiting compilation");
    });
  },

  jumpTo(line, column) {
    const source = this.state.source;
    const lines = source.split("\n");
    const safeLine = Math.max(1, Math.min(line, lines.length));
    const start = lines.slice(0, safeLine - 1).reduce((total, text) => total + text.length + 1, 0);
    const position = start + Math.min(Math.max(column - 1, 0), lines[safeLine - 1].length);
    this.intent("source", { focus: true, preventScroll: true, selection: [position, Math.min(position + 1, source.length)],
      scrollTop: Math.max(0, (safeLine - 3) * 24), scrollLeft: Math.max(0, (column - 12) * 8.4), scrollIntoView: true });
  },

  jumpToDiagnostic(diagnostic) {
    if (this.project && diagnostic.file && Object.hasOwn(this.project.files, diagnostic.file)) {
      this.selectProjectModule(diagnostic.file, { compileNow: false });
    }
    if (!this.project || !diagnostic.file || diagnostic.file === this.state.filename) this.jumpTo(diagnostic.line, diagnostic.column || 1);
  },

  showRelations(functions) {
    this.update({ relations: { functions, serial: (this.state.relations?.serial || 0) + 1 }, relationsHidden: false });
  },

  showGenerated(result, snapshot) {
    this.batch(() => {
      const refreshStarter = !this.analysisDirty() && [true, false].some((facts) =>
        this.state.analysis === starterAnalysis(this.state.generatedModule, facts));
      const catalog = createCatalog(result.functions,
        [result.shared_lean, result.lean, result.points_lean, result.probability_lean, result.parallel_lean, ...Object.values(result.project_files || {})]);
      const module = result.module || moduleForFilename(snapshot.filename);
      const pointsModule = result.points_module || `${module}Points`;
      const previous = this.state.lastResult;
      const previousView = previous?.publicModule === module ? previous.view : "public";
      const views = { public: { lean: result.lean, points: result.points_lean || "", module, pointsModule } };
      const implementation = result.implementation_module;
      const implementationPoints = result.implementation_points_module;
      if (typeof result.project_files?.[implementation] === "string" && typeof result.project_files?.[implementationPoints] === "string") {
        views.execution = { lean: result.project_files[implementation], points: result.project_files[implementationPoints],
          module: implementation, pointsModule: implementationPoints };
      }
      if (result.probability_module && result.probability_lean) {
        views.probability = { lean: result.probability_lean, points: "", module: result.probability_module, pointsModule };
      }
      if (result.parallel_module && result.parallel_lean) {
        views.parallel = { lean: result.parallel_lean, points: "", module: result.parallel_module, pointsModule };
      }
      const lastResult = { lean: result.lean, shared: result.shared_lean || "", program: result.program_lean || "",
        points: result.points_lean || "", pointsModule, module, publicModule: module, views, view: "public",
        randomized: Boolean(result.randomized), probabilityChecked: result.probability_checked === true,
        probabilityModule: result.probability_module || "", parallelModule: result.parallel_module || "",
        source: snapshot.source, filename: snapshot.filename, revision: snapshot.revision, available: true };
      this.update({ catalog, lastResult });
      // Browsing the shared implementation does not change an analysis's imports
      // or the source-facing names in its interface list.
      this.setModule(module, pointsModule);
      const starter = starterAnalysis(module, !lastResult.randomized);
      if (refreshStarter && this.state.analysis !== starter) {
        this.update({ analysis: starter, savedAnalysis: starter });
        this.invalidateAnalysis("Generated interfaces changed. Check the analysis again.");
        this.scheduleDraft();
      }
      this.selectGeneratedView(views[previousView] ? previousView : "public");
      this.update({ sharedVisible: Boolean(lastResult.shared),
        sharedSummary: `Shared Lean library · Algo2Lean.lean · ${result.stats?.shared_lines || 0} reusable lines` });
      this.showRelations(result.functions);
    });
  },

  selectGeneratedView(view) {
    const result = this.state.lastResult;
    if (!result?.views[view]) return;
    const updated = { ...result, ...result.views[view], view };
    const modulePath = (name) => (this.project ? name.replace(/\./g, "/") : name);
    const pointsLines = updated.points ? updated.points.trimEnd().split("\n").length : 0;
    this.update({ lastResult: updated,
      outputSummary: `${updated.lean.trimEnd().split("\n").length} ${view === "probability" ? "probability" : "program"} lines · ${modulePath(updated.module)}.lean`,
      pointsSummary: `${pointsLines} interface lines · ${modulePath(updated.pointsModule)}.lean` });
    this.intent("output", { scrollTop: 0, scrollLeft: 0 });
  },

  async compile(check = false) {
    if (check && this.hosted) {
      this.setStatus("Lean checking requires the local editor.");
      this.fileMessage("Download the generation bundle to check these files with the pinned Lean toolchain. This website verifies generation, not Lean proofs.");
      return;
    }
    if (this.activeRequest) this.activeRequest.abort();
    const serial = ++this.requestSerial;
    const snapshot = { source: this.state.source, filename: this.state.filename, revision: this.revision };
    const controller = new AbortController();
    this.activeRequest = controller;
    this.batch(() => {
      this.setBusy(true, check);
      this.setStatus(check ? "Checking generated definitions with Lean…" : "Compiling source…");
      this.fileMessage("");
      this.update({ checkOutput: null });
    });
    try {
      if (this.project) await this.requireProjectSupport(controller.signal);
      if (serial !== this.requestSerial || snapshot.revision !== this.revision) return;
      const response = await this.request(check ? "/api/check" : "/api/compile", {
        method: "POST", headers: this.requestHeaders(),
        body: JSON.stringify(this.projectRequest(snapshot)), signal: controller.signal,
      });
      let result;
      try { result = await response.json(); }
      catch (_) { throw new Error("The compiler returned an unreadable response. Restart the local editor server and try again."); }
      if (serial !== this.requestSerial || snapshot.revision !== this.revision) return;
      if (result.scope === "setup") {
        this.setStatus("Compiler setup needs attention", "error");
        this.setLeanState("Compilation unavailable", "error");
        this.rejectOutput();
        this.showDiagnostics([{ message: result.message || "Check the compiler installation and try again." }]);
        return;
      }
      if (typeof result.lean === "string") this.showGenerated(result, snapshot);
      if (result.diagnostics && result.diagnostics.length) {
        this.showDiagnostics(result.diagnostics);
        this.setStatus(`${result.diagnostics.length} ${result.diagnostics.length === 1 ? "error" : "errors"} to resolve`, "error");
        this.setLeanState(this.state.lastResult ? "Compilation failed" : "Not generated", "error");
        this.rejectOutput();
        return;
      }
      if (!response.ok && !check) throw new Error(result.error || result.message || `Compilation failed (HTTP ${response.status}).`);
      if (!result.lean && !check) throw new Error(result.error || result.message || "The compiler did not return Lean code.");
      let note;
      if (check && result.available === false) {
        this.setStatus("Lean checker unavailable");
        this.setLeanState("Generated · unchecked", "generated");
        note = this.project ? "The project files were generated. A local Lean installation is needed to check the definitions." : "Both Lean files were generated. A local Lean installation is needed to check the definitions.";
      } else if (check && result.ok) {
        this.setStatus("Lean accepted the generated definitions", "success");
        this.setLeanState("Lean checked", "checked");
        note = result.randomized ? "Lean checked the algorithm definitions and named locations. Probability companions require their separate Mathlib check." : this.project ? "Lean checked the generated modules and their named-line interfaces. This checks the definitions; it does not prove termination or a specification." : "Lean checked both generated files successfully. This checks the definitions; it does not prove termination or a specification.";
      } else if (check) {
        this.setStatus("Lean reported a problem", "error");
        this.setLeanState("Lean check failed", "error");
        note = "Lean could not accept the generated definitions. See the checker output below.";
      } else {
        this.setStatus("Compilation successful", "success");
        this.setLeanState("Generated · unchecked", "generated");
        note = this.hosted ? "Generated in your browser. Verify claimed files or download a generation bundle below. Lean proof checking requires a local installation." : this.project ? "The selected module and its dependencies were compiled. Check project to validate their definitions and named-line interfaces." : "Algorithm definitions and the named-line interface were generated separately. Check both files to validate the Lean definitions.";
      }
      this.diagnosticNote(note, result.randomized
        ? result.probability_diagnostic || "Probability companions use the optional Mathlib project and require a separate check. Returns and Call describe possible outcomes; they do not assert probabilities."
        : null);
      if (check) {
        this.update({ checkOutput: result.output || result.message || (result.ok ? "Lean completed without errors." : "No checker output was returned."),
          checkOpen: !result.ok });
      }
    } catch (error) {
      if (error.name === "AbortError" || serial !== this.requestSerial || snapshot.revision !== this.revision) return;
      this.setStatus(error.name === "ServerUpdateError" ? "Editor server needs restarting" : "Could not reach the compiler", "error");
      this.setLeanState("Compilation failed", "error");
      this.rejectOutput();
      this.showDiagnostics([{ message: error.message || "Start the local editor server and try again." }]);
    } finally {
      if (serial === this.requestSerial) { this.activeRequest = null; this.setBusy(false); }
    }
  },
};
