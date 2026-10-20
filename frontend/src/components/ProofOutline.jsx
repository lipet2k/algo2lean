import { useEffect, useMemo, useState } from "react";
import { buildExampleIndex, declarations, labelEntries, mainResultButtons } from "../lib/proof-outline.js";
import { highlightTokens } from "../lib/interface.js";
import { Tokens } from "./Tokens.jsx";
import { Button } from "./Button.jsx";
import { cx, selectClass } from "./classes.js";

// Main results and theorem navigation for the analysis. Previews are navigation
// aids, not proof checking results.
export function ProofOutline({ source, exampleSources, onJump, catalog }) {
  const index = useMemo(() => buildExampleIndex(exampleSources || []), [exampleSources]);
  const entries = useMemo(() => labelEntries(declarations(source), source, index), [source, index]);
  const main = useMemo(() => entries.filter((entry) => entry.label), [entries]);
  const buttons = useMemo(() => mainResultButtons(entries), [entries]);
  const [selected, setSelected] = useState(null);
  const [cleared, setCleared] = useState(false);
  useEffect(() => { setCleared(false); }, [entries]);
  const current = cleared ? null : (entries.find((entry) => entry.id === selected) || main[0] || null);
  useEffect(() => { if (current && current.id !== selected) setSelected(current.id); }, [current, selected]);
  const previewTokens = useMemo(() => (current?.statement
    ? highlightTokens(current.statement, catalog, source.slice(0, current.start)) : []), [current, catalog, source]);

  const show = (entry) => { setCleared(false); setSelected(entry.id); };
  const selectValue = current ? String(entries.indexOf(current)) : "";

  return (
    <div id="analysis-outline" className="proof-outline px-[18px] py-[14px] border-b border-border bg-surface scroll-mt-4">
      <div className="flex items-center justify-between flex-wrap gap-2.5">
        <h3 className="text-[13px] text-ink font-semibold">Main results</h3>
        <label className="text-muted text-xs flex items-center gap-2 min-w-0 max-phone:w-full">All theorems{" "}
          <select aria-label="Find a theorem" disabled={entries.length === 0} value={selectValue}
            className={cx(selectClass, "max-w-[min(380px,60vw)] min-h-[38px] py-1.5 pl-2.5 font-mono text-xs max-phone:max-w-none max-phone:w-full")}
            onChange={(event) => {
              const value = event.target.value;
              if (value !== "" && entries[Number(value)]) show(entries[Number(value)]);
              else { setSelected(null); setCleared(true); }
            }}>
            <option value="">Choose a theorem ({entries.length})</option>
            {entries.map((entry, position) => <option key={entry.id} value={String(position)}>{entry.name} · line {entry.line}</option>)}
          </select>
        </label>
      </div>
      <div className="proof-main-results flex flex-wrap gap-1.5 mt-2.5 empty:hidden">
        {buttons.map(({ label, entry }, position) => (
          <Button key={position} title={entry.name} aria-controls="analysis-theorem-preview"
            aria-pressed={String(current === entry)} onClick={() => show(entry)}
            className="whitespace-normal text-left aria-pressed:bg-navy-900 aria-pressed:border-navy-900">
            {label}
          </Button>
        ))}
      </div>
      <section id="analysis-theorem-preview" className="proof-statement p-4 mt-3 border border-border rounded bg-paper" hidden={!current}>
        {current && (
          <>
            <h4 className="mb-2.5 font-mono text-sm leading-6 font-semibold [overflow-wrap:anywhere]">{current.name}</h4>
            {current.description && <p className="mb-2.5 text-muted text-[13px] whitespace-pre-wrap">{current.description}</p>}
            {current.statement
              ? <pre className="my-2.5 font-mono text-sm leading-6 whitespace-pre-wrap [overflow-wrap:anywhere]"><Tokens tokens={previewTokens} /></pre>
              : <p className="mb-2.5 text-muted text-[13px] whitespace-pre-wrap">Open this declaration in the proof editor to read its full statement.</p>}
            <Button onClick={() => onJump(current.line, 1)}>Go to proof · line {current.line}</Button>
          </>
        )}
      </section>
      {!main.length && (
        <p className="proof-outline-hint mt-2.5 text-muted text-xs">{entries.length
          ? "No main results are marked in this analysis. Choose a theorem above, or add a comment like ‘-- Main result: Correctness’ before a theorem."
          : "Load an example with a Lean analysis, or write a theorem to see its statement here."}</p>
      )}
    </div>
  );
}
