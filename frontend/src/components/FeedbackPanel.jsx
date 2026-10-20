import { useMemo } from "react";
import { highlightTokens } from "../lib/interface.js";
import { outputEnabled } from "../editor/selectors.js";
import { Button } from "./Button.jsx";
import { InterfacePanel } from "./InterfacePanel.jsx";
import { Tokens } from "./Tokens.jsx";
import { blurOnEscape, cx, detailsSummaryClass, feedbackPanelClass, fileMessageClass, statusToneClass } from "./classes.js";
import { useEditorState, useStore } from "./store-context.jsx";

export const DIAGNOSTIC = "flex items-baseline gap-3 w-full text-left mt-2 px-3 py-2.5 text-error border border-[#edc4c0] bg-error-soft rounded text-[13px] max-phone:gap-[7px] max-phone:flex-wrap";
export const DIAGNOSTIC_LOCATION = "whitespace-nowrap font-mono text-[11px] text-[#8f302d]";

export function Diagnostic({ diagnostic, locationLabel, fallback, onJump }) {
  const hasLocation = Number.isInteger(diagnostic.line) && diagnostic.line > 0;
  const message = <span className="[overflow-wrap:anywhere]">{diagnostic.message || fallback}</span>;
  if (!hasLocation) return <div className={DIAGNOSTIC}>{message}</div>;
  return (
    <button type="button" className={cx(DIAGNOSTIC, "hover:bg-[#ffe6e3]")} onClick={() => onJump(diagnostic)}>
      <span className={DIAGNOSTIC_LOCATION}>{locationLabel(diagnostic)}</span>
      {message}
    </button>
  );
}

export function FeedbackPanel() {
  const store = useStore();
  const state = useEditorState();
  const result = state.lastResult;
  const enabled = outputEnabled(state);
  const sharedTokens = useMemo(() => (state.sharedOpen && state.sharedVisible && result?.shared
    ? highlightTokens(result.shared, state.catalog) : []), [state.sharedOpen, state.sharedVisible, result?.shared, state.catalog]);
  const generatedModule = state.generatedModule;
  return (
    <section className={feedbackPanelClass} aria-labelledby="feedback-heading">
      <div className="flex items-center gap-[14px] flex-wrap max-phone:gap-2">
        <h2 id="feedback-heading" className="text-[13px] font-[650]">Lean Interface</h2>
        <span id="compile-status" className={cx("text-xs pl-[14px] border-l border-border max-phone:pl-2", statusToneClass(state.compileStatus.tone))} role="status" aria-live="polite">{state.compileStatus.text}</span>
        <span id="draft-status" className={cx("ml-auto text-xs max-phone:basis-full max-phone:ml-0", state.draftStatus.failed ? "text-error font-[550]" : "text-muted")} role="status" aria-live="polite">{state.draftStatus.text}</span>
      </div>
      <div id="diagnostics" className="text-[13px] text-muted mt-2.5">
        {state.diagnostics.note && <p className="leading-[1.65]">{state.diagnostics.note}</p>}
        {state.diagnostics.probabilityNote && <p className="leading-[1.65]">{state.diagnostics.probabilityNote}</p>}
        {state.diagnostics.items.map((diagnostic, index) => (
          <Diagnostic key={index} diagnostic={diagnostic} fallback="Compilation failed."
            locationLabel={(item) => `${item.file || "Line"} ${item.line}:${item.column || 1}`} onJump={(item) => store.jumpToDiagnostic(item)} />
        ))}
      </div>
      <InterfacePanel key={state.relations?.serial || 0} hidden={state.relationsHidden || !state.relations} functions={state.relations?.functions}
        catalog={state.catalog} generatedFile={`${generatedModule}.lean`} pointsFile={`${state.generatedPointsModule}.lean`}
        probabilityFile={result?.probabilityModule ? `${result.probabilityModule}.lean` : undefined}
        parallelFile={result?.parallelModule ? `${result.parallelModule}.lean` : undefined}
        factsFile={generatedModule.endsWith(".Generated") && !result?.randomized ? `${generatedModule.slice(0, -10)}.Facts.lean` : undefined}
        onGoToSource={(line, column) => store.jumpTo(line, column)} />
      <details id="lean-details" className="mt-[14px] text-xs" hidden={state.checkOutput === null} open={state.checkOpen}
        onToggle={(event) => store.toggleCheckDetails(event.currentTarget.open)}>
        <summary className={detailsSummaryClass}>Lean checker output</summary>
        <pre id="check-output" className="details-output" tabIndex={0} aria-label="Lean checker output" onKeyDown={blurOnEscape}>{state.checkOutput}</pre>
      </details>
      <details id="shared-details" className="mt-[14px] text-xs" hidden={!state.sharedVisible} open={state.sharedOpen}
        onToggle={(event) => store.toggleShared(event.currentTarget.open)}>
        <summary id="shared-summary" className={detailsSummaryClass}>{state.sharedSummary}</summary>
        <p className="leading-[1.6]">The algorithm definitions import <code>Algo2Lean</code>. Keep the library in your Lean project, or export the algorithm definitions with the library included. The named-line interface stays in its separate file.</p>
        <div className="flex gap-2 flex-wrap my-2.5">
          <Button id="library-button" disabled={!enabled || !result?.shared} onClick={() => store.downloadLibrary()}>Download Algo2Lean.lean</Button>
          <Button id="standalone-button" hidden={Boolean(state.project)} disabled={!enabled || !result?.shared || result?.view === "probability"} onClick={() => store.exportStandalone()}>Export standalone algorithm</Button>
        </div>
        <pre id="shared-output" className="details-output shared-output" tabIndex={0} aria-label="Shared Lean library, read only" aria-describedby="shared-summary" onKeyDown={blurOnEscape}>
          <code id="shared-code"><Tokens tokens={sharedTokens} /></code>
        </pre>
      </details>
      <p id="file-message" className={fileMessageClass(state.fileMessage.error)} role="status" hidden={!state.fileMessage.text}>{state.fileMessage.text}</p>
    </section>
  );
}
