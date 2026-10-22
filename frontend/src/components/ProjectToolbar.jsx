import { useMemo } from "react";
import { Button } from "./Button.jsx";
import { cx, selectClass } from "./classes.js";
import { useEditorState, useStore } from "./store-context.jsx";

export function ProjectToolbar() {
  const store = useStore();
  const { project, projectExporting } = useEditorState();
  const folders = useMemo(() => {
    if (!project) return [];
    const groups = new Map();
    for (const path of project.paths) {
      const separator = path.lastIndexOf("/");
      const folder = path.slice(0, separator + 1);
      if (!groups.has(folder)) groups.set(folder, []);
      groups.get(folder).push({ path, name: path.slice(separator + 1) });
    }
    return [...groups.keys()].sort().map((folder) => ({ folder, label: folder || "Project root", files: groups.get(folder) }));
  }, [project]);
  return (
    <section id="project-toolbar" className="flex items-center flex-wrap gap-x-5 gap-y-2.5 mb-4 px-4 py-3 border border-navy-100 rounded-xl bg-paper shadow-panel" aria-label="Project files" hidden={!project}>
      <div className="flex items-center gap-2.5 min-w-0">
        <span className="text-muted text-xs">Project</span>
        <strong id="project-name" className="text-ink [overflow-wrap:anywhere]">{project?.name}</strong>
        <span id="project-count" className="text-muted text-xs min-w-12">{project ? `${project.paths.length} files` : ""}</span>
      </div>
      <div className="flex items-center gap-2.5 min-w-0 flex-1 max-tablet:basis-full">
        <label htmlFor="project-module" className="text-muted text-[13px] whitespace-nowrap">Project file</label>
        <select id="project-module" aria-describedby="project-help" value={project?.selected || ""} onChange={(event) => store.selectProjectModule(event.target.value)}
          className={cx(selectClass, "w-full max-w-[480px] min-w-[120px] min-h-11 font-mono max-tablet:max-w-none")}>
          {folders.map((group) => (
            <optgroup key={group.folder} label={group.label}>
              {group.files.map((file) => <option key={file.path} value={file.path}>{file.name}</option>)}
            </optgroup>
          ))}
        </select>
      </div>
      <div className="flex items-center gap-2.5 min-w-0 max-tablet:flex-wrap max-phone:grid max-phone:grid-cols-2 max-phone:w-full">
        <Button id="project-export-button" className="min-h-11" disabled={projectExporting} onClick={() => store.downloadProject()}>{projectExporting ? "Preparing download…" : "Download project"}</Button>
        <Button id="close-project-button" className="min-h-11" onClick={() => store.closeProject()}>Close project</Button>
      </div>
      <p id="project-help" className="basis-full text-muted text-xs leading-[1.6]">Files are grouped by folder. Switch files to edit their source and analysis, or use New file to add one. Download the project to keep all your changes.</p>
    </section>
  );
}
