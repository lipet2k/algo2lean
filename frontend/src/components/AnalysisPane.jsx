import { useMemo, useRef } from "react";
import { highlightTokens } from "../lib/interface.js";
import { analysisForExample } from "../lib/names.js";
import { analysisDirty, analysisSaveStateText, currentExample, paneFilenames } from "../editor/selectors.js";
import { Button } from "./Button.jsx";
import { CodeEditor } from "./CodeEditor.jsx";
import { useCodeSearch } from "./CodeSearch.jsx";
import { Diagnostic } from "./FeedbackPanel.jsx";
import { ProofOutline } from "./ProofOutline.jsx";
import { blurOnEscape, cx, detailsSummaryClass, dotClass, fieldLabelClass, fileMessageClass, paneFilenameClass, paneFooterClass, paneHeadingClass, paneHeadingTextClass, paneTitleClass, stateTagClass, statusToneClass } from "./classes.js";
import { useEditorState, useRegistered, useStore } from "./store-context.jsx";

const FILENAME_INPUT = "w-[180px] min-h-10 border border-transparent rounded-lg p-2 text-ink font-semibold bg-transparent hover:bg-paper hover:border-navy-200 focus:bg-paper focus:border-navy-400 read-only:cursor-default read-only:text-muted max-desktop:w-[150px] max-phone:flex-1 max-phone:w-auto max-phone:min-w-0 max-phone:bg-paper max-phone:border-navy-200 max-phone:min-h-11 max-phone:text-base";

export function AnalysisPane() {
  const store = useStore();
  const state = useEditorState();
  const textareaRef = useRef(null);
  const viewportRef = useRef(null);
  const pickerRef = useRef(null);
  const filenameRef = useRegistered("analysis-filename");
  const search = useCodeSearch({ text: state.analysis, textareaRef, viewportRef, label: "analysis", openSignal: state.findSerial });
  const tokens = useMemo(() => highlightTokens(state.analysis + "\n", state.catalog), [state.analysis, state.catalog]);
  const filenames = paneFilenames(state);
  const example = currentExample(state);
  const differs = Boolean(example && (state.source !== example.source || state.analysis !== analysisForExample(example, state.generatedModule)));
  const badgeTone = state.analysisStatus.tone === "success" ? "checked" : state.analysisStatus.tone;
  return (
    <section id="analysis-workspace" className="mt-[22px] border border-navy-200 rounded-xl overflow-hidden bg-paper flex flex-col shadow-workbench max-phone:rounded-lg" aria-labelledby="analysis-heading" onKeyDown={search.handleKeyDown}>
      <div className={cx(paneHeadingClass, "bg-linear-to-b from-navy-50 to-paper flex-wrap")}>
        <div className="min-w-0 flex-1">
          <div className={paneTitleClass}>
            <span className={dotClass(true)} aria-hidden="true" />
            <h2 id="analysis-heading" className={paneHeadingTextClass}>Lean analysis</h2>
            <span id="analysis-state" className={stateTagClass(badgeTone)}>{state.analysisStatus.badge}</span>
          </div>
          <code id="analysis-pane-filename" className={paneFilenameClass}>{filenames.analysis}</code>
        </div>
        <Button id="analyze-button" variant="primary" className="max-phone:w-full" disabled={state.analysisBusy}
          title={state.hosted ? "Lean checking requires the local editor" : "Check analysis (⌘ / Ctrl Enter in the analysis editor)"} onClick={() => store.analyze()}>
          {state.analysisBusy ? "Checking analysis… " : "Check analysis "}<kbd className="text-navy-200 text-[11px] font-normal ml-3 max-desktop:hidden">{state.apple ? "⌘ ↵" : "Ctrl ↵"}</kbd>
        </Button>
      </div>
      <p id="hosted-proof-notice" className="m-0 px-[18px] py-[14px] border-b border-border bg-navy-50 text-ink text-[13px] leading-[1.7]" hidden={!state.hosted}>
        <strong>Proof checking is not currently available on this website.</strong> Use Save analysis to download a complete Lean project, including the proof and shared libraries. Extract the ZIP and open its folder in your Lean editor, or run <code>lake build</code> with Lean installed.
      </p>
      <div className="px-[18px] py-2.5 border-b border-border flex flex-wrap items-center justify-between gap-x-[18px] gap-y-1.5 max-tablet:items-start max-phone:px-3 max-phone:py-3">
        <div className="flex items-center gap-2 min-w-0 flex-wrap max-tablet:w-full max-phone:flex-col max-phone:items-stretch max-phone:gap-2.5">
          <div className="flex items-center gap-2.5 max-phone:gap-2">
            <label htmlFor="analysis-filename" className={fieldLabelClass}>Analysis file</label>
            <input id="analysis-filename" ref={filenameRef} className={FILENAME_INPUT} value={state.analysisFilename} readOnly={Boolean(state.project)} maxLength={255}
              spellCheck={false} autoComplete="off" aria-describedby="analysis-save-state" onChange={(event) => store.renameAnalysis(event.target.value)} />
          </div>
          <span id="analysis-save-state" className={cx("text-xs min-w-12 max-phone:min-w-0 max-phone:shrink-0", analysisDirty(state) ? "text-warning" : "text-muted")}>{analysisSaveStateText(state)}</span>
          <div className="flex items-center gap-1 flex-wrap max-phone:grid max-phone:grid-cols-3 max-phone:gap-2">
            <Button id="analysis-open-button" onClick={() => pickerRef.current?.click()}>Open .lean</Button>
            <Button id="analysis-save-button" disabled={state.analysisSaving} title="Download analysis and all Lean dependencies as a ZIP (⌘ / Ctrl S)" onClick={() => store.saveAnalysis()}>
              {state.analysisSaving ? "Preparing package…" : "Save analysis"}
            </Button>
            <Button id="analysis-find-button" title="Find in analysis (⌘ / Ctrl F)" onClick={() => store.openFind()}>Find</Button>
          </div>
          <input id="analysis-file-picker" ref={pickerRef} className="sr-only" type="file" accept=".lean,text/plain" tabIndex={-1}
            onChange={(event) => { const file = event.target.files?.[0]; event.target.value = ""; store.openAnalysisFile(file); }} />
        </div>
      </div>
      <div id="example-update" className="flex items-center justify-between flex-wrap gap-2.5 px-[18px] py-3 border-b border-border bg-navy-50" hidden={!differs}>
        <p id="example-update-message" className="flex-[1_1_260px] m-0 text-[13px] text-ink">{differs
          ? `This copy differs from the current ${example.name || example.filename} example. Your saved drafts remain in Browser drafts.` : ""}</p>
        <Button id="load-current-example" className="whitespace-normal" onClick={() => store.loadCurrentExample()}>Load current example</Button>
      </div>
      <ProofOutline source={state.analysis} exampleSources={state.exampleAnalyses} catalog={state.catalog} onJump={(line, column) => store.jumpToAnalysis(line, column)} />
      {search.bar}
      <CodeEditor id="analysis" viewportId="analysis-editor" measureId="analysis-measure" lineNumbersId="analysis-line-numbers"
        value={state.analysis} onChange={(value) => store.editAnalysis(value)} tokens={tokens} label="Lean analysis code"
        describedBy="analysis-pane-filename analysis-editor-help" indentSize={2} indentPattern={/^ */}
        autoIndent={(line) => /\b(by|where|do)\s*$/.test(line)} intent={state.analysisIntent} busy={state.analysisBusy}
        viewportClassName="analysis-editor" textClassName="code-text-lean" layerClassName="code-layer-lean" searchMatch={search.match}
        registerName="analysis" refs={{ textarea: textareaRef, viewport: viewportRef }}
        footer={(cursor) => (
          <div className={paneFooterClass}>
            <span id="analysis-cursor-position">Ln {cursor.line}, Col {cursor.column}</span>
            <span id="analysis-editor-help" className="text-right max-phone:text-[10px] max-phone:max-w-[195px]">Tab: 2 spaces · Esc: leave editor</span>
          </div>
        )} />
      <div className="px-[18px] pt-[15px] pb-[18px] border-t border-border max-phone:px-3">
        <p id="analysis-status" className={cx("text-[13px]", statusToneClass(state.analysisStatus.tone))} role="status" aria-live="polite">{state.analysisStatus.text}</p>
        <div id="analysis-diagnostics" className="text-[13px] text-muted mt-2.5 empty:mt-0">
          {state.analysisDiagnostics.map((diagnostic, index) => (
            <Diagnostic key={index} diagnostic={diagnostic} fallback="Lean reported a problem with the analysis."
              locationLabel={(item) => `Analysis.lean · ${item.line}:${item.column || 1}`} onJump={(item) => store.jumpToAnalysis(item.line, item.column || 1)} />
          ))}
        </div>
        <details id="analysis-details" className="mt-[14px] text-xs" hidden={state.analysisOutput === null} open={state.analysisOpen}
          onToggle={(event) => store.toggleAnalysisDetails(event.currentTarget.open)}>
          <summary className={detailsSummaryClass}>Analysis checker output</summary>
          <pre id="analysis-output" className="details-output" tabIndex={0} aria-label="Analysis checker output" onKeyDown={blurOnEscape}>{state.analysisOutput}</pre>
        </details>
        <p id="analysis-file-message" className={fileMessageClass(state.analysisFileMessage.error)} role="status" hidden={!state.analysisFileMessage.text}>{state.analysisFileMessage.text}</p>
      </div>
    </section>
  );
}
