import { useLayoutEffect, useRef } from "react";
import { Button } from "./Button.jsx";
import { useEditorState, useRegistered, useStore } from "./store-context.jsx";

const CARD = "min-w-0 p-3 border border-navy-100 rounded-lg bg-linear-to-b from-navy-50 to-paper";
const PREVIEW = "my-2.5 font-mono text-[11px] leading-[1.6] whitespace-pre-wrap [overflow-wrap:anywhere]";
const HELP = "mt-2.5 text-muted text-xs";

function preview(text, fallback) {
  return (text || "").split("\n").slice(0, 4).join("\n").slice(0, 500) || fallback;
}

function DraftCard({ draft }) {
  const store = useStore();
  const name = draft.filename || "untitled.algo";
  let detail = new Date(draft.updatedAt).toLocaleString() + (draft.active ? " · Loaded in this tab" : "");
  if (typeof draft.analysis === "string") detail += ` · ${draft.analysisFilename || "Analysis.lean"}`;
  return (
    <article className={CARD}>
      <h3 className="text-[13px] font-semibold [overflow-wrap:anywhere]">{name}</h3>
      <p className="mt-1 text-[11px] text-muted">{detail}</p>
      <pre className={PREVIEW}>{preview(draft.source, "(Empty source)")}</pre>
      {typeof draft.analysis === "string" && <pre className={PREVIEW}>{preview(draft.analysis, "(Empty analysis)")}</pre>}
      <div className="flex gap-1.5">
        <Button aria-label={`Recover ${draft.filename}`} onClick={() => store.recoverDraft(draft.id)}>Recover</Button>
        <Button variant="danger" aria-label={`Discard ${draft.filename}`} onClick={() => store.discardDraft(draft.id, draft.filename)}>Discard</Button>
      </div>
    </article>
  );
}

function ProjectCard({ record }) {
  const store = useStore();
  return (
    <article className={CARD}>
      <h3 className="text-[13px] font-semibold [overflow-wrap:anywhere]">{record.data.name} · Project</h3>
      <p className="mt-1 text-[11px] text-muted">{Object.keys(record.data.files).length} modules · {new Date(record.updatedAt).toLocaleString()}</p>
      <pre className={PREVIEW}>{Object.keys(record.data.files).slice(0, 5).join("\n")}</pre>
      <div className="flex gap-1.5">
        <Button onClick={() => store.recoverProject(record.id)}>Recover project</Button>
        <Button variant="danger" onClick={() => store.discardProject(record.id, record.data.name)}>Discard</Button>
      </div>
    </article>
  );
}

export function DraftPicker() {
  const store = useStore();
  const state = useEditorState();
  const summaryRef = useRegistered("draft-summary");
  const appliedIntent = useRef(0);
  const count = state.drafts.length + state.projectDrafts.length;

  // The summary of a hidden <details> cannot take focus, so focus requests
  // apply once the picker has been committed visible.
  useLayoutEffect(() => {
    const intent = state.draftsIntent;
    if (!intent || intent.serial === appliedIntent.current || !state.draftPickerVisible) return;
    appliedIntent.current = intent.serial;
    if (intent.focus) summaryRef.current?.focus();
  }, [state.draftsIntent, state.draftPickerVisible]);
  return (
    <details id="draft-picker" className="mb-4 px-[18px] py-[14px] border border-navy-100 rounded-xl bg-paper shadow-panel max-phone:px-3"
      hidden={!state.draftPickerVisible} open={state.draftPickerOpen} onToggle={(event) => store.setDraftPickerOpen(event.currentTarget.open)}>
      <summary ref={summaryRef} className="text-ink font-semibold">Browser drafts <span id="draft-count" className="ml-2 text-muted font-normal">{count}</span></summary>
      <p className={HELP}>Each refresh opens merge sort. Recover a source and analysis pair or project here to continue editing. Each tab saves separately; drafts stay until you discard them.</p>
      <div className="flex gap-1.5 mt-2.5">
        <Button id="clear-drafts-button" onClick={() => store.clearDrafts()}>Clear all drafts</Button>
        <Button id="undo-clear-drafts-button" hidden={!state.undoClearAvailable} onClick={() => store.undoClearDrafts()}>Undo clear</Button>
      </div>
      <p id="draft-empty" className={HELP} hidden={count !== 0}>No saved drafts yet. Your edits will appear here.</p>
      <div id="draft-list" className="grid grid-cols-[repeat(auto-fit,minmax(min(100%,260px),1fr))] gap-3 mt-3 max-h-[360px] overflow-auto p-1">
        {state.drafts.map((draft) => <DraftCard key={draft.id || "legacy"} draft={draft} />)}
        {state.projectDrafts.map((record) => <ProjectCard key={record.id} record={record} />)}
      </div>
    </details>
  );
}
