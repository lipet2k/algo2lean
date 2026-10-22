import { useLayoutEffect, useRef } from "react";
import { Button } from "./Button.jsx";
import { cx } from "./classes.js";
import { useEditorState, useStore } from "./store-context.jsx";

export function NewFileForm() {
  const store = useStore();
  const state = useEditorState();
  const inputRef = useRef(null);
  const applied = useRef(0);
  useLayoutEffect(() => {
    const intent = state.newFileIntent;
    if (!intent || intent.serial === applied.current || !state.newFileOpen) return;
    applied.current = intent.serial;
    const input = inputRef.current;
    if (!input) return;
    if (intent.focus) input.focus();
    if (intent.selection) input.setSelectionRange(intent.selection[0], intent.selection[1]);
  }, [state.newFileIntent, state.newFileOpen]);
  return (
    <form id="new-file-form" className="flex flex-wrap items-center gap-x-4 gap-y-2.5 p-4 mb-4 border border-navy-100 rounded-xl bg-paper shadow-panel max-phone:p-3"
      aria-label="Create a source file" hidden={!state.newFileOpen} noValidate
      onSubmit={(event) => { event.preventDefault(); store.createNewFile(); }}
      onKeyDown={(event) => { if (event.key === "Escape") { event.preventDefault(); store.closeNewFileForm(); } }}>
      <div className="flex items-center flex-1 gap-3 min-w-0 max-phone:basis-full">
        <label htmlFor="new-file-name" className="text-muted whitespace-nowrap">File name</label>
        <input id="new-file-name" ref={inputRef} value={state.newFileName} onChange={(event) => store.setNewFileName(event.target.value)}
          maxLength={255} spellCheck={false} autoComplete="off" aria-describedby="new-file-help" aria-invalid={String(state.newFileHelp.error)} placeholder="untitled.algo"
          className="w-full min-w-0 min-h-11 px-3 py-2 border border-navy-200 rounded-lg font-mono bg-paper focus:border-navy-400 aria-invalid:border-error max-phone:text-base" />
      </div>
      <div className="flex gap-2">
        <Button variant="primary" type="submit">Create file</Button>
        <Button id="cancel-new-file-button" onClick={() => store.closeNewFileForm()}>Cancel</Button>
      </div>
      <p id="new-file-help" className={cx("basis-full text-xs", state.newFileHelp.error ? "text-error" : "text-muted")} role="status" aria-live="polite">{state.newFileHelp.text}</p>
    </form>
  );
}
