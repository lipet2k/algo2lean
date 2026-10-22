// Hosted-only generation records: exact comparison of claimed generated files,
// and downloads of the generation bundle and manifest.
export const generation = {
  invalidateGeneration() {
    if (!this.generationController) return;
    this.generationController.abort();
    this.generationController = null;
    this.update({ generationStatus: "Workspace changed. Verify generated files again for the current source.", generationDetails: "" });
  },

  verifyFiles(fileList) {
    const files = Array.from(fileList || []).filter((file) => file.name.endsWith(".lean"));
    if (files.length) return this.generation("verify", files);
    return Promise.resolve();
  },

  async generation(action, files = []) {
    this.generationController?.abort();
    const controller = new AbortController();
    this.generationController = controller;
    const snapshot = { source: this.state.source, filename: this.state.filename, revision: this.revision,
      analysis: this.state.analysis, analysisRevision: this.analysisRevision };
    const project = this.project;
    this.update({ generationStatus: action === "verify" ? "Compiling and comparing every selected file…" : "Preparing generation records…", generationDetails: "" });
    try {
      const payload = { ...this.projectRequest(snapshot), archive: action === "archive" };
      const response = await this.request("/api/generation", { method: "POST", headers: this.requestHeaders(),
        body: JSON.stringify(payload), signal: controller.signal });
      if (!response.ok) {
        const result = await response.json();
        throw new Error(result.message || result.error || result.diagnostics?.[0]?.message || "Resolve source errors before generating a record.");
      }
      const stillCurrent = () => this.generationController === controller && project === this.project &&
        snapshot.revision === this.revision && snapshot.analysisRevision === this.analysisRevision;
      if (!stillCurrent()) throw new Error("The workspace changed. Try this action again for the current source.");
      if (action === "archive") {
        const archive = await response.blob();
        if (!stillCurrent()) throw new Error("The workspace changed. Download again for the current source.");
        this.download(archive, "Algo2Lean-generation.zip");
        this.update({ generationStatus: "Downloaded the source, generated Lean files, shared libraries, and generation manifest." });
        return;
      }
      const result = await response.json();
      if (!stillCurrent()) throw new Error("The workspace changed. Try this action again for the current source.");
      if (action === "manifest") {
        this.download(JSON.stringify(result.manifest, null, 2) + "\n", "generation.json");
        this.update({ generationStatus: "Downloaded the compiler identity, source hashes, settings, and output hashes." });
        return;
      }
      const comparison = await this.options.compareFiles(result.files, files, result.libraries, controller.signal);
      if (!stillCurrent()) throw new Error("The workspace changed during comparison. Verify again for the current source.");
      this.update({
        generationStatus: comparison.exact
          ? `Exact match: all ${comparison.compared} selected generated and library files are byte-for-byte identical. This verifies generation only; it does not check a Lean proof or establish compiler correctness.`
          : "Files do not exactly match this compilation. Review the differences below.",
        generationDetails: [
          ["Missing", comparison.missing], ["Extra or unrecognized", comparison.extra],
          ["Different contents", comparison.different], ["Duplicate", comparison.duplicate],
        ].filter(([, names]) => names.length).map(([label, names]) => label + ":\n" + names.join("\n")).join("\n\n"),
      });
    } catch (error) {
      if (this.generationController === controller && !controller.signal.aborted && error.name !== "AbortError") {
        this.update({ generationStatus: error.message });
      }
    }
  },
};
