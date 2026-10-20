import { useMemo } from "react";
import { algoTokens } from "../lib/algo-highlight.js";
import { highlightTokens } from "../lib/interface.js";
import { checkButtonLabel, currentOutput, generatedLeanState, outputEnabled, paneFilenames, viewControlVisible } from "../editor/selectors.js";
import { Button } from "./Button.jsx";
import { CodeEditor } from "./CodeEditor.jsx";
import { GeneratedOutput } from "./GeneratedOutput.jsx";
import { cx, dotClass, paneFilenameClass, paneFooterClass, paneHeadingClass, paneHeadingTextClass, paneTitleClass, selectClass, stateTagClass, subtleLabelClass } from "./classes.js";
import { useEditorState, useStore } from "./store-context.jsx";

const OUTPUT_DESCRIPTION = "px-[18px] py-[9px] text-muted text-xs leading-[1.6] border-b border-navy-100";
const OUTPUT_ACTION = "px-[9px] py-[7px] max-desktop:p-[7px]";

function SourcePane() {
  const store = useStore();
  const state = useEditorState();
  const tokens = useMemo(() => algoTokens(state.source + "\n"), [state.source]);
  const filenames = paneFilenames(state);
  return (
    <section className="pane source-pane min-w-0 bg-paper flex flex-col border-r border-border max-tablet:border-r-0 max-tablet:border-b max-tablet:border-b-navy-200" aria-labelledby="source-heading">
      <div className={paneHeadingClass}>
        <div className="min-w-0 flex-1">
          <div className={paneTitleClass}>
            <span className={dotClass(false)} aria-hidden="true" />
            <h2 id="source-heading" className={paneHeadingTextClass}>.algo</h2>
            <span className={subtleLabelClass}>Source</span>
          </div>
          <code id="source-pane-filename" className={paneFilenameClass}>{filenames.source}</code>
        </div>
        <Button id="compile-button" variant="primary" className="max-phone:w-full" disabled={state.busy} title="Compile to Lean (⌘ / Ctrl Enter)" onClick={() => store.compile(false)}>
          <svg viewBox="0 0 16 16" aria-hidden="true"><path d="m5 3 7 5-7 5Z" fill="currentColor" /></svg>
          <span>{state.busy && !state.busyCheck ? "Compiling…" : "Compile"}</span>
          <kbd className="text-navy-200 text-[11px] font-normal ml-3 max-desktop:hidden">{state.apple ? "⌘ ↵" : "Ctrl ↵"}</kbd>
        </Button>
      </div>
      <CodeEditor id="source" viewportId="source-editor" measureId="highlight" codeId="highlight-code" lineNumbersId="line-numbers"
        value={state.source} onChange={(value) => store.edit(value)} tokens={tokens} label="Algo2Lean source code"
        describedBy="source-pane-filename editor-help" indentSize={4} indentPattern={/^\s*/}
        autoIndent={(line) => /:\s*(?:#.*)?$/.test(line)} intent={state.sourceIntent} viewportClassName="source-editor"
        textClassName="code-text-algo" registerName="source"
        footer={(cursor) => (
          <div className={paneFooterClass}>
            <span id="cursor-position">Ln {cursor.line}, Col {cursor.column}</span>
            <span id="editor-help" className="text-right max-phone:text-[10px] max-phone:max-w-[195px]">Tab: 4 spaces · Esc: leave editor</span>
          </div>
        )} />
    </section>
  );
}

function GeneratedPane({ kind }) {
  const store = useStore();
  const state = useEditorState();
  const result = state.lastResult;
  const text = kind === "lean" ? result?.lean || "" : result?.points || "";
  const tokens = useMemo(() => highlightTokens(text + "\n", state.catalog), [text, state.catalog]);
  const filenames = paneFilenames(state);
  const enabled = outputEnabled(state);
  const inProject = Boolean(state.project);
  const views = result?.views || {};
  const isLean = kind === "lean";
  const visible = isLean ? Boolean(result) : Boolean(result?.points);
  const badge = isLean ? generatedLeanState(state) : state.leanState;
  const title = result?.view === "probability" ? "Probability interface" : result?.view === "parallel" ? "Parallel contracts" : "Algorithm definitions";
  return (
    <section className={cx("pane min-w-0 bg-surface flex flex-col", !isLean && "border-t border-navy-200")} aria-labelledby={`${kind}-heading`}>
      <div className={cx(paneHeadingClass, "bg-linear-to-b from-navy-50 to-paper flex-wrap")}>
        <div className="min-w-0 flex-1 basis-[260px]">
          <div className={paneTitleClass}>
            <span className={dotClass(true)} aria-hidden="true" />
            <h2 id={`${kind}-heading`} className={paneHeadingTextClass}>{isLean ? title : "Named-line interface"}</h2>
            <span id={`${kind}-state`} className={stateTagClass(badge.tone)}>{badge.text}</span>
          </div>
          <code id={`${kind}-pane-filename`} className={paneFilenameClass}>{isLean ? filenames.lean : filenames.points}</code>
        </div>
        <div className="flex items-center gap-1 max-phone:gap-2 max-phone:justify-end">
          <Button id={isLean ? "copy-button" : "copy-points-button"} className={OUTPUT_ACTION} disabled={isLean ? !enabled : !enabled || !result?.points}
            onClick={() => (isLean ? store.copyLean() : store.copyPoints())}>Copy</Button>
          <Button id={isLean ? "export-button" : "export-points-button"} className={OUTPUT_ACTION} hidden={inProject} disabled={isLean ? !enabled : !enabled || !result?.points}
            onClick={() => (isLean ? store.exportLean() : store.exportPoints())}>Export .lean</Button>
        </div>
      </div>
      <p className={OUTPUT_DESCRIPTION}>{isLean
        ? result?.view === "probability" ? "Probability laws and expectations. Check this companion separately with the optional Mathlib project."
          : result?.view === "parallel" ? "Reusable fork–join contracts for imported algorithms, including work, span, and access independence."
          : "Outputs and execution semantics. This file stays identical when only line names change."
        : "Imports the algorithm definitions and adds locations and local observations for your proofs."}</p>
      {isLean && (
        <div id="generated-view-control" className="flex flex-wrap items-center gap-x-3 gap-y-2 px-[18px] py-2.5 border-b border-border text-xs text-muted" hidden={!viewControlVisible(state)}>
          <label htmlFor="generated-view">Show</label>
          <select id="generated-view" className={cx(selectClass, "max-phone:w-full")} aria-describedby="generated-view-help" disabled={!enabled} value={result?.view || "public"}
            onChange={(event) => { if (currentOutput(state)) store.selectGeneratedView(event.target.value); }}>
            {views.public && <option value="public">Public interface</option>}
            {views.execution && <option value="execution">Shared execution</option>}
            {views.probability && <option value="probability">Probability interface</option>}
            {views.parallel && <option value="parallel">Parallel contracts</option>}
          </select>
          <p id="generated-view-help" className="basis-full">Browse generated interfaces without changing your analysis imports. Shared execution is available for mutually recursive files.</p>
        </div>
      )}
      <GeneratedOutput id={isLean ? "lean-output" : "points-output"} codeId={isLean ? "lean-code" : "points-code"} selectionId={isLean ? "lean-selection" : "points-selection"}
        text={text} tokens={tokens} visible={visible} busy={state.busy} intent={state.outputIntent}
        label={isLean ? `Generated ${title.toLowerCase()}, read only` : "Generated named-line interface, read only"}
        describedBy={`${kind}-pane-filename`} emptyId={isLean ? "output-empty" : "points-empty"}
        empty={isLean ? (
          <>
            <h3 className="text-[17px] font-[550] text-ink leading-[1.4] mb-2.5">A precise meaning for the algorithm</h3>
            <p className="text-muted text-sm leading-[1.7]">Compile to generate an output relation for each function. Nonterminating executions have no valid output.</p>
          </>
        ) : (
          <>
            <h3 className="text-[17px] font-[550] text-ink leading-[1.4] mb-2.5">Name the steps you want to reason about</h3>
            <p className="text-muted text-sm leading-[1.7]">Put <code># @name</code> on its own line directly above a statement, at the same indentation. It names the state before that statement. Compilation puts its proof interface in this separate file.</p>
          </>
        )} />
      <div className={cx(paneFooterClass, "flex-wrap")}>
        <span id={isLean ? "output-summary" : "points-summary"} className="[overflow-wrap:anywhere]">{isLean ? state.outputSummary : state.pointsSummary}</span>
        {isLean && (
          <button id="check-button" type="button" disabled={state.busy} onClick={() => store.compile(true)}
            className="border-0 pl-2 py-1 text-navy-600 text-xs bg-transparent font-[550] whitespace-nowrap hover:enabled:underline hover:enabled:underline-offset-[3px] max-phone:min-h-11">
            {checkButtonLabel(state)}{!state.hosted && <span className="ml-[5px]" aria-hidden="true">↗</span>}
          </button>
        )}
      </div>
    </section>
  );
}

export function Workbench() {
  return (
    <div className="grid grid-cols-2 border border-navy-200 rounded-xl overflow-hidden shadow-workbench bg-paper max-tablet:grid-cols-1 max-phone:rounded-lg">
      <SourcePane />
      <div className="min-w-0 flex flex-col">
        <GeneratedPane kind="lean" />
        <GeneratedPane kind="points" />
      </div>
    </div>
  );
}
