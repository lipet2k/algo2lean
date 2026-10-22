// Project folders: multiple source modules with companion analyses, opened from a
// folder, a bundled example, or a browser recovery record.
import { starterAnalysis, projectModule, validProjectPath } from "../lib/names.js";
import { PROJECT_PREFIX, PROJECT_SESSION, PROJECT_BYTES } from "./constants.js";

const FILE_FIELDS = ["source", "filename", "savedSource", "savedFilename", "analysis", "analysisFilename", "savedAnalysis", "savedAnalysisFilename"];
const SKIPPED_FOLDERS = ["node_modules", "build", "dist"];

export const projects = {
  projectSnapshot() {
    this.project.files[this.project.selected] = this.draftSnapshot();
    return { version: 1, name: this.project.name, selected: this.project.selected,
      files: this.project.files, analyses: this.project.analyses };
  },

  validProjectRecord(record) {
    const data = record?.data;
    if (!record || typeof record.id !== "string" || !/^[A-Za-z0-9_-]+$/.test(record.id) || !data || data.version !== 1 ||
        typeof data.name !== "string" || typeof data.files !== "object" || !data.files || Array.isArray(data.files)) return false;
    const paths = Object.keys(data.files);
    if (!paths.length || paths.length > 256 || !paths.includes(data.selected) || JSON.stringify(data).length > 4 * PROJECT_BYTES) return false;
    if (!paths.every((path) => validProjectPath(path, ".algo") && FILE_FIELDS.every((key) => typeof data.files[path]?.[key] === "string"))) return false;
    return data.analyses && typeof data.analyses === "object" && !Array.isArray(data.analyses) && Object.entries(data.analyses).every(([name, text]) => /^Algo(?:\.[A-Za-z_][A-Za-z_0-9]*)+\.Analysis$/.test(name) && typeof text === "string");
  },

  projectDrafts() {
    const records = [];
    const storage = this.storage();
    for (let index = 0; index < storage.length; index += 1) {
      const key = storage.key(index);
      if (!key?.startsWith(PROJECT_PREFIX)) continue;
      try {
        const record = JSON.parse(storage.getItem(key));
        if (this.validProjectRecord(record) && key === PROJECT_PREFIX + record.id) records.push(record);
      } catch (_) { /* Leave unreadable records untouched. */ }
    }
    return records.sort((a, b) => (b.updatedAt || 0) - (a.updatedAt || 0));
  },

  writeProjectDraft() {
    const data = this.projectSnapshot();
    const snapshot = JSON.stringify(data);
    if (snapshot === this.projectBaseline) return true;
    try {
      // Recoveries and duplicated tabs fork before their first write.
      const id = this.projectWritable ? this.project.id : this.options.makeId();
      this.storage().setItem(PROJECT_PREFIX + id, JSON.stringify({ id, updatedAt: this.options.now(), data }));
      this.project.id = id;
      this.projectWritable = true;
      this.projectBaseline = snapshot;
      this.withSession((session) => session.setItem(PROJECT_SESSION, id));
      this.draftStatus("Project draft saved in this browser");
      this.refreshDrafts();
      return true;
    } catch (_) {
      this.draftStatus("Project draft could not be saved. Download the project to keep all module edits.", true);
      return false;
    }
  },

  // Mirror the structural project fields into the rendered state.
  projectControls() {
    const project = this.project;
    this.update({ project: project ? { name: project.name, selected: project.selected, paths: Object.keys(project.files).sort() } : null });
  },

  selectProjectModule(path, { save = true, compileNow = true } = {}) {
    if (!this.project || !Object.hasOwn(this.project.files, path)) return;
    this.batch(() => {
      this.closeNewFileForm(false);
      if (save) this.projectSnapshot();
      this.project.selected = path;
      const file = this.project.files[path];
      const module = projectModule(path);
      this.update({ source: file.source, filename: path, savedSource: file.savedSource, savedFilename: path,
        generatedModule: module + ".Generated", generatedPointsModule: module + ".Points" });
      this.loadAnalysis(file.analysis, file.analysisFilename, "Project file", file);
      this.intent("source", { selection: [0, 0], scrollTop: 0, scrollLeft: 0 });
      this.update({ lastResult: null });
      this.invalidate();
      this.setLeanState("Not generated");
      this.updateSaveState("Project file");
      this.projectControls();
      this.scheduleDraft();
    });
    if (compileNow) this.compile(false);
  },

  closeNewFileForm(focusButton = true) {
    this.update({ newFileOpen: false });
    if (focusButton) this.element("new-file-button")?.focus();
  },

  newFileMessage(message, failed = false) {
    this.update({ newFileHelp: { text: message, error: failed } });
  },

  setNewFileName(value) {
    this.update({ newFileName: value });
  },

  newFileError(path) {
    const project = this.project;
    if (!validProjectPath(path, ".algo") || (!project && path.includes("/"))) {
      return project
        ? "Use a .algo filename with letters, numbers, and underscores, such as helpers/search.algo. Start each folder and filename with a letter or underscore."
        : "Use a .algo filename with letters, numbers, and underscores, such as search.algo. Start with a letter or underscore.";
    }
    if (path.split("/")[0].replace(/\.algo$/, "").toLowerCase() === "_a2l_groups") {
      return "The name _a2l_groups is reserved for generated files. Choose another name.";
    }
    if (!project) return null;
    if (Object.hasOwn(project.files, path)) return "A file with this name already exists. Choose another name.";
    const module = projectModule(path) + ".Analysis";
    if (Object.hasOwn(project.analyses, module)) return "An analysis already uses this file's name. Choose another name to keep that proof intact.";
    const names = [...Object.keys(project.files).map(projectModule),
      ...Object.keys(project.analyses).map((name) => name.slice(0, -9))];
    const parts = projectModule(path).split(".");
    for (let length = 2; length <= parts.length; length += 1) {
      const prefix = parts.slice(0, length).join(".");
      if (names.some((name) => {
        const existing = name.split(".").slice(0, length).join(".");
        return existing.toLowerCase() === prefix.toLowerCase() && existing !== prefix;
      })) return "A file or folder already uses this name with different letter case. Use the same folder spelling and a unique filename.";
    }
    if (Object.keys(project.files).length >= 256) return "A project can contain at most 256 source files.";
    if (new Set([...Object.keys(project.analyses), ...Object.keys(project.files).map((name) => projectModule(name) + ".Analysis"), module]).size > 256) {
      return "A project can contain at most 256 analysis files, including one companion for each source file.";
    }
    return null;
  },

  openNewFileForm() {
    const project = this.project;
    const folder = project ? project.selected.slice(0, project.selected.lastIndexOf("/") + 1) : "";
    const used = new Set(project ? Object.keys(project.files) : [this.state.filename]);
    if (!project) {
      try { for (const draft of this.draftStore?.list() || []) used.add(draft.filename); } catch (_) { /* A name can still be chosen without storage. */ }
    } else {
      for (const name of Object.keys(project.analyses)) used.add(name.slice(5, -9).replace(/\./g, "/") + ".algo");
    }
    let name = folder + "untitled.algo";
    for (let index = 2; [...used].some((path) => path.toLowerCase() === name.toLowerCase()); index += 1) name = `${folder}untitled_${index}.algo`;
    this.batch(() => {
      this.update({ newFileName: name, newFileOpen: true });
      this.newFileMessage(project ? "Add a .algo file to this project. Use / to create a folder." : "Create a standalone .algo file. Your current edits stay in Browser drafts.");
      this.intent("newFile", { focus: true, selection: [folder.length, name.length - 5] });
    });
  },

  createNewFile() {
    let name = this.state.newFileName.trim();
    if (name && !name.endsWith(".algo")) name += ".algo";
    const error = this.newFileError(name);
    if (error) { this.newFileMessage(error, true); return; }
    this.writeDraft();
    if (!this.project && this.workspaceDirty() && !this.hasDraftBackup()) {
      this.newFileMessage("The current source and analysis could not be backed up. Save both files before creating a new file.", true);
      return;
    }
    if (this.project) {
      const proof = starterAnalysis(projectModule(name) + ".Generated");
      const proofName = "analysis/" + name.replace(/\.algo$/, ".lean");
      const file = { source: "", filename: name, savedSource: "", savedFilename: name,
        analysis: proof, analysisFilename: proofName, savedAnalysis: "", savedAnalysisFilename: proofName };
      const data = this.projectSnapshot();
      const proofs = { ...data.analyses, [projectModule(name) + ".Analysis"]: proof };
      for (const [path, document] of Object.entries(data.files)) proofs[projectModule(path) + ".Analysis"] = document.analysis;
      if (new Blob([...Object.values(data.files).map((document) => document.source), ...Object.values(proofs)]).size > PROJECT_BYTES) {
        this.newFileMessage("This project is too large to add a file. Download it and open a smaller project folder.", true);
        return;
      }
      this.project.files[name] = file;
      this.selectProjectModule(name, { save: false, compileNow: false });
    } else {
      this.loadDocument("", name, "New file");
      // A new file gets its own draft immediately, even before the first edit.
      this.update({ savedFilename: "", savedAnalysis: "" });
      this.updateSaveState();
      this.updateAnalysisSaveState();
    }
    this.projectOpening += 1;
    this.closeNewFileForm(false);
    const saved = this.writeDraft();
    this.fileMessage(saved ? (this.project ? `Created ${name}. Download project to save all files together.` : `Created ${name}. Use Save .algo to download it.`)
      : `Created ${name}. Browser backup is unavailable; save your files before closing this page.`, !saved);
    this.intent("source", { focus: true });
  },

  loadProject(data, record = null) {
    if (!this.project) this.standaloneDocument = { ...this.draftSnapshot(), id: this.draftStore?.activeId || null };
    this.project = { ...data, id: record?.id || null };
    this.projectWritable = false;
    this.projectBaseline = record ? JSON.stringify(data) : "";
    this.selectProjectModule(data.selected, { save: false, compileNow: false });
    this.writeDraft();
    if (this.project.id) this.withSession((session) => session.setItem(PROJECT_SESSION, this.project.id));
    this.fileMessage(`Opened ${data.name}. Each module keeps its own source and analysis draft.`);
  },

  recoverProject(id) {
    if (!this.canReplace()) return;
    try {
      const latest = JSON.parse(this.storage().getItem(PROJECT_PREFIX + id));
      if (!this.validProjectRecord(latest)) throw new Error("This project draft is no longer available.");
      this.loadProject(latest.data, latest);
      this.update({ draftPickerOpen: false });
      this.compile(false);
    } catch (error) { this.fileMessage(error.message, true); }
  },

  discardProject(id, name) {
    if (!this.options.confirm(`Discard the browser project draft for ${name}? Open editor text will remain.`)) return;
    try {
      this.storage().removeItem(PROJECT_PREFIX + id);
      if (this.project?.id === id) {
        this.projectBaseline = JSON.stringify(this.projectSnapshot());
        this.project.id = null;
        this.projectWritable = false;
        this.options.clearTimeout(this.draftTimer);
      }
      this.refreshDrafts();
    } catch (_) { this.fileMessage("This project draft could not be discarded.", true); }
  },

  projectRequest(snapshot) {
    const payload = { source: snapshot.source, filename: snapshot.filename };
    if (typeof snapshot.analysis === "string") payload.analysis = snapshot.analysis;
    if (this.project) {
      const project = this.projectSnapshot();
      payload.project_sources = {};
      payload.project_analyses = { ...project.analyses };
      for (const [path, file] of Object.entries(project.files)) {
        payload.project_sources[path] = file.source;
        payload.project_analyses[projectModule(path) + ".Analysis"] = file.analysis;
      }
      if (Object.keys(payload.project_analyses).length > 256) throw new Error("A project can contain at most 256 analysis modules, including a companion for each source file.");
      if (new Blob([JSON.stringify(payload)]).size > 8 * 1024 * 1024) throw new Error("This project exceeds the 8 MB request limit. Open a smaller project folder.");
    }
    return payload;
  },

  requestHeaders() {
    return { "Content-Type": "application/json", ...(this.project ? { "X-Algo2Lean-Project": "1" } : {}) };
  },

  async requireProjectSupport(signal) {
    const response = await this.request("/api/capabilities", { signal });
    const capabilities = response.ok ? await response.json() : null;
    if (capabilities?.project_protocol !== 1) {
      const error = new Error("This editor server is older than the project compiler. Stop the existing server, run python3 -m algo2lean serve --open from the Algo2Lean project folder, then reload this page.");
      error.name = "ServerUpdateError";
      throw error;
    }
  },

  async readProjectFiles(files, name) {
    const sources = {}, analyses = {}, proofPaths = {}, spellings = new Map();
    const relevant = files.filter(({ path }) => path.endsWith(".algo") || (path.endsWith(".lean") && !path.startsWith("Algo/")));
    const sourceFiles = relevant.filter(({ path }) => path.endsWith(".algo"));
    if (!sourceFiles.length) throw new Error("Choose a folder containing .algo source files.");
    if (sourceFiles.length > 256 || relevant.length > 512) throw new Error("Choose a project with at most 256 source modules and 256 companion analyses.");
    let bytes = 0;
    for (const { path, file } of relevant.sort((a, b) => a.path.localeCompare(b.path))) {
      if (path.startsWith("Algo/") && path.endsWith(".lean")) continue;
      const isSource = path.endsWith(".algo");
      const relative = !isSource && path.startsWith("analysis/") ? path.slice(9) : path;
      if (!validProjectPath(relative, isSource ? ".algo" : ".lean")) {
        if (isSource) throw new Error(`Source paths must use identifier names: ${path}`);
        continue;
      }
      const module = relative.replace(/\.(algo|lean)$/, "").replace(/\//g, ".");
      const parts = module.split(".");
      for (let length = 1; length <= parts.length; length += 1) {
        const prefix = parts.slice(0, length).join(".");
        const previous = spellings.get(prefix.toLowerCase());
        if (previous && previous !== prefix) throw new Error(`Module paths differ only in letter case: ${previous} and ${prefix}.`);
        spellings.set(prefix.toLowerCase(), prefix);
      }
      bytes += file.size;
      if (file.size > (isSource ? 256 * 1024 : 1024 * 1024) || bytes > PROJECT_BYTES) throw new Error("Choose sources smaller than 256 KB, analyses smaller than 1 MB, and a project smaller than 6 MB.");
      const text = (await file.text()).replace(/\r\n?/g, "\n");
      if (isSource) {
        if (Object.hasOwn(sources, path)) throw new Error(`The project contains duplicate source path ${path}.`);
        sources[path] = text;
      } else {
        const key = `Algo.${module}.Analysis`;
        if (Object.hasOwn(analyses, key)) throw new Error(`Two companion analyses have the same module: ${proofPaths[key]} and ${path}.`);
        analyses[key] = text;
        proofPaths[key] = path;
      }
    }
    const proofModules = new Set([...Object.keys(analyses), ...Object.keys(sources).map((path) => projectModule(path) + ".Analysis")]);
    if (proofModules.size > 256) throw new Error("Choose a project with at most 256 analysis modules, including a companion for each source file.");
    const documents = {};
    for (const path of Object.keys(sources).sort()) {
      const module = projectModule(path);
      const proof = analyses[module + ".Analysis"] ?? starterAnalysis(module + ".Generated");
      const proofPath = proofPaths[module + ".Analysis"] || "analysis/" + path.replace(/\.algo$/, ".lean");
      documents[path] = { source: sources[path], filename: path, savedSource: sources[path], savedFilename: path,
        analysis: proof, analysisFilename: proofPath, savedAnalysis: proof, savedAnalysisFilename: proofPath };
    }
    return { version: 1, name, selected: Object.keys(documents).includes("main.algo") ? "main.algo" : Object.keys(documents)[0], files: documents, analyses };
  },

  openingSnapshot() {
    return { serial: ++this.projectOpening, revision: this.revision, analysisRevision: this.analysisRevision,
      filename: this.state.filename, analysisFilename: this.state.analysisFilename };
  },

  openingStale(opening) {
    return opening.serial !== this.projectOpening || opening.revision !== this.revision || opening.analysisRevision !== this.analysisRevision ||
      opening.filename !== this.state.filename || opening.analysisFilename !== this.state.analysisFilename;
  },

  async finishProjectOpen(files, name, opening, selected = null) {
    const data = await this.readProjectFiles(files, name);
    if (selected !== null) {
      if (!Object.hasOwn(data.files, selected)) throw new Error("The example's entry module is missing.");
      data.selected = selected;
    }
    if (this.openingStale(opening)) {
      this.fileMessage("The workspace changed while the folder was opening. Open the project again when you are ready.", true);
      return;
    }
    if (!this.canReplace()) return;
    this.loadProject(data);
    this.compile(false);
  },

  async openProjectExample(example) {
    const opening = this.openingSnapshot();
    this.fileMessage("Loading the example and its imported files…");
    try {
      await this.requireProjectSupport();
      const response = await this.request(`/api/example-project/${encodeURIComponent(example.project_id)}`);
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.error || error.message || error.diagnostics?.[0]?.message || "This project example could not be loaded. Restart the editor server and try again.");
      }
      const project = await response.json();
      if (!project.sources || !project.analyses || typeof project.entry !== "string") throw new Error("The project example is incomplete.");
      const files = [];
      const add = (path, text) => {
        if (typeof text !== "string") throw new Error("The project example contains an invalid file.");
        files.push({ path, file: { size: new Blob([text]).size, text: async () => text } });
      };
      for (const [path, text] of Object.entries(project.sources)) add(path, text);
      for (const [module, text] of Object.entries(project.analyses)) {
        if (!/^Algo(?:\.[A-Za-z_][A-Za-z_0-9]*)+\.Analysis$/.test(module)) throw new Error("The project example contains an invalid analysis name.");
        add("analysis/" + module.slice(5, -9).replace(/\./g, "/") + ".lean", text);
      }
      await this.finishProjectOpen(files, project.name || example.name, opening, project.entry);
    } catch (error) {
      if (opening.serial === this.projectOpening) this.fileMessage(`Could not open the example: ${error.message}`, true);
    }
  },

  async openProjectFolder() {
    const opening = this.openingSnapshot();
    if (!this.options.showDirectoryPicker) {
      this.folderOpening = opening;
      this.element("project-picker")?.click();
      return;
    }
    this.update({ openingFolder: true });
    try {
      const directory = await this.options.showDirectoryPicker({ mode: "read" });
      const files = [];
      let entries = 0;
      async function visit(handle, prefix = "", depth = 0) {
        if (depth > 32) throw new Error("Project folders can be at most 32 levels deep.");
        for await (const entry of handle.values()) {
          if (++entries > 4096) throw new Error("This folder has too many entries. Choose a smaller project folder.");
          if (entry.name.startsWith(".") || SKIPPED_FOLDERS.includes(entry.name)) continue;
          const path = prefix + entry.name;
          if (entry.kind === "directory") await visit(entry, path + "/", depth + 1);
          else if (/\.(algo|lean)$/.test(path)) files.push({ path, file: await entry.getFile() });
        }
      }
      this.fileMessage("Reading the selected project folder…");
      await visit(directory);
      await this.finishProjectOpen(files, directory.name, opening);
    } catch (error) {
      if (error.name !== "AbortError") this.fileMessage(`Could not open the project: ${error.message}`, true);
    } finally { this.update({ openingFolder: false }); }
  },

  // Files chosen with the fallback folder input.
  async openProjectFiles(chosen) {
    if (!chosen.length) return;
    const opening = this.folderOpening || this.openingSnapshot();
    this.folderOpening = null;
    this.update({ openingFolder: true });
    try {
      if (chosen.length > 4096) throw new Error("This folder has too many entries. Choose a smaller project folder.");
      const rootName = chosen[0].webkitRelativePath?.split("/")[0];
      if (!rootName) throw new Error("Choose a folder using Open project.");
      const files = [];
      for (const file of chosen) {
        const parts = file.webkitRelativePath.split("/");
        if (parts.shift() !== rootName) throw new Error("Choose one project folder at a time.");
        if (parts.some((part) => part.startsWith(".") || SKIPPED_FOLDERS.includes(part))) continue;
        files.push({ path: parts.join("/"), file });
      }
      await this.finishProjectOpen(files, rootName, opening);
    } catch (error) { this.fileMessage(`Could not open the project: ${error.message}`, true); }
    finally { this.update({ openingFolder: false }); }
  },

  async downloadProject() {
    if (!this.project) return;
    if (this.projectExport) this.projectExport.abort();
    const controller = new AbortController();
    this.projectExport = controller;
    const project = this.project;
    const snapshot = { source: this.state.source, filename: this.state.filename, analysis: this.state.analysis,
      revision: this.revision, analysisRevision: this.analysisRevision };
    this.update({ projectExporting: true });
    try {
      await this.requireProjectSupport(controller.signal);
      if (project !== this.project || snapshot.revision !== this.revision || snapshot.analysisRevision !== this.analysisRevision) return;
      const response = await this.request("/api/project-export", { method: "POST", headers: this.requestHeaders(),
        body: JSON.stringify(this.projectRequest(snapshot)), signal: controller.signal });
      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.error || error.message || error.diagnostics?.[0]?.message || "Project export failed.");
      }
      const archive = await response.blob();
      if (controller.signal.aborted || project !== this.project || snapshot.revision !== this.revision || snapshot.analysisRevision !== this.analysisRevision) return;
      this.download(archive, "Algo2Lean-project.zip");
      this.writeDraft();
      this.fileMessage("Downloaded all project drafts. The archive README describes generated files and any export diagnostics.");
    } catch (error) {
      if (error.name !== "AbortError") this.fileMessage(`Could not download the project: ${error.message}`, true);
    } finally {
      if (this.projectExport === controller) {
        this.projectExport = null;
        this.update({ projectExporting: false });
      }
    }
  },
};
