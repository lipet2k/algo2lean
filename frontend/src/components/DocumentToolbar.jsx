import { useRef } from "react";
import { dirty, saveStateText } from "../editor/selectors.js";
import { Button } from "./Button.jsx";
import { cx, fieldLabelClass, selectClass } from "./classes.js";
import { useEditorState, useRegistered, useStore } from "./store-context.jsx";

const FILENAME_INPUT = "w-[180px] min-h-10 border border-transparent rounded-lg p-2 text-ink font-semibold bg-transparent hover:bg-paper hover:border-navy-200 focus:bg-paper focus:border-navy-400 read-only:cursor-default read-only:text-muted max-desktop:w-[150px] max-phone:flex-1 max-phone:w-auto max-phone:min-w-0 max-phone:bg-paper max-phone:border-navy-200 max-phone:min-h-11 max-phone:text-base";

export function DocumentToolbar() {
  const store = useStore();
  const state = useEditorState();
  const fileRef = useRef(null);
  const projectRef = useRegistered("project-picker");
  const draftsRef = useRegistered("drafts-button");
  const newFileRef = useRegistered("new-file-button");
  const groups = [["Project folders", true], ["Single files", false]].map(([label, isProject]) => ({
    label,
    options: state.examples.map((example, index) => ({ example, index })).filter(({ example }) => Boolean(example.project_id) === isProject),
  })).filter((group) => group.options.length);
  return (
    <section id="editor" className="flex flex-col items-stretch gap-3 mb-4 min-h-11 scroll-mt-5 max-phone:gap-2.5" aria-label="Document controls">
      <div className="flex items-center flex-wrap gap-x-3 gap-y-2 min-w-0 pb-3 border-b border-navy-100 max-phone:gap-y-1.5">
        <label htmlFor="examples" className={fieldLabelClass}>Examples</label>
        <select id="examples" aria-label="Load an example" disabled={state.examplesUnavailable}
          className={cx(selectClass, "w-[370px] max-phone:flex-1 max-phone:w-auto")}
          value={state.exampleSelection} onChange={(event) => { if (event.target.value !== "") store.chooseExample(event.target.value); }}>
          <option value="">{state.examplesUnavailable ? "Examples unavailable" : "Choose an example…"}</option>
          {groups.map((group) => (
            <optgroup key={group.label} label={group.label}>
              {group.options.map(({ example, index }) => (
                <option key={index} value={String(index)} title={example.description || undefined}>
                  {(example.name || example.filename) + (example.folder ? ` · ${example.folder}/` : "")}
                </option>
              ))}
            </optgroup>
          ))}
        </select>
      </div>
      <div className="flex items-center gap-2 min-w-0 flex-wrap max-desktop:gap-1 max-phone:flex-col max-phone:items-stretch max-phone:gap-2.5">
        <div className="flex items-center gap-2.5 min-w-0 max-phone:gap-2">
          <label htmlFor="filename" className={fieldLabelClass}>File</label>
          <input id="filename" className={FILENAME_INPUT} value={state.filename} readOnly={Boolean(state.project)} maxLength={255}
            spellCheck={false} autoComplete="off" aria-describedby="save-state" onChange={(event) => store.rename(event.target.value)} />
          <span id="save-state" className={cx("text-xs min-w-12 max-phone:text-[11px] max-phone:min-w-0 max-phone:shrink-0", dirty(state) ? "text-warning" : "text-muted")}>{saveStateText(state)}</span>
        </div>
        <span className="h-5 w-px bg-navy-200 mx-1.5 max-phone:hidden" aria-hidden="true" />
        <div className="flex items-center gap-1 flex-wrap max-phone:grid max-phone:grid-cols-2 max-phone:gap-2">
          <Button id="new-file-button" ref={newFileRef} aria-controls="new-file-form" aria-expanded={String(state.newFileOpen)} onClick={() => store.openNewFileForm()}>New file</Button>
          <Button id="open-button" onClick={() => fileRef.current?.click()}>Open</Button>
          <Button id="open-project-button" disabled={state.openingFolder} onClick={() => store.openProjectFolder()}>Open project</Button>
          <Button id="save-button" title="Save source file (⌘ / Ctrl S)" onClick={() => store.saveSource()}>Save .algo</Button>
          <Button id="drafts-button" ref={draftsRef} className="max-phone:col-span-2" aria-controls="draft-picker" onClick={() => store.showDrafts()}>Browser drafts</Button>
        </div>
        <input id="file-picker" ref={fileRef} className="sr-only" type="file" accept=".algo,text/plain" tabIndex={-1}
          onChange={(event) => { const file = event.target.files?.[0]; event.target.value = ""; store.openFile(file); }} />
        <input id="project-picker" ref={projectRef} className="sr-only" type="file" webkitdirectory="" multiple tabIndex={-1} aria-label="Choose a project folder"
          onChange={(event) => { const chosen = Array.from(event.target.files || []); event.target.value = ""; store.openProjectFiles(chosen); }} />
      </div>
    </section>
  );
}
