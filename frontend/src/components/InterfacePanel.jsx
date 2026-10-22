import { useId, useMemo, useRef, useState } from "react";
import { KINDS, classify, groupEntries, highlightTokens, panelEntries } from "../lib/interface.js";
import { Tokens } from "./Tokens.jsx";
import { cx } from "./classes.js";

const KIND_BUTTON = {
  proposition: "min-h-[38px] px-3 py-2 text-sm leading-6 rounded-lg",
  theorem: "min-h-[26px] px-[7px] py-0.5 text-xs leading-5 rounded",
  definition: "min-h-[26px] px-[7px] py-0.5 text-xs leading-5 rounded",
  type: "min-h-[26px] px-[7px] py-0.5 text-xs leading-5 rounded",
};

function InterfaceEntry({ id, entry, kind, catalog, files, expanded, onToggle, onClose, onGoToSource }) {
  const buttonRef = useRef(null);
  const tokens = useMemo(() => highlightTokens(entry.signature || entry.name, catalog, entry.namespace ? `namespace ${entry.namespace}\n` : ""),
    [entry.signature, entry.name, entry.namespace, catalog]);
  return (
    <div className={cx("interface-entry max-w-full", expanded && "is-open basis-full")}>
      <button ref={buttonRef} type="button" id={`${id}-button`} title={KINDS[kind]} aria-label={`${entry.name}, ${KINDS[kind]}`}
        aria-expanded={String(expanded)} aria-controls={`${id}-spec`} onClick={onToggle}
        className={cx("interface-button block max-w-full text-left bg-surface border border-navy-200 font-mono [overflow-wrap:anywhere]",
          "hover:bg-navy-50 hover:border-navy-400 aria-expanded:bg-navy-100 aria-expanded:border-navy-400 aria-expanded:shadow-[0_0_0_3px_rgba(58,110,165,.12)] max-narrow:min-h-11", KIND_BUTTON[kind], `interface-${kind}`)}>
        {entry.name}
      </button>
      <div id={`${id}-spec`} className="interface-spec mt-2 px-[18px] py-4 border border-border rounded-md bg-surface text-[13px] leading-[1.7] [overflow-wrap:anywhere] max-narrow:p-3"
        hidden={!expanded} role="region" aria-labelledby={`${id}-button`}
        onKeyDown={(event) => { if (event.key === "Escape") { event.preventDefault(); onClose(); buttonRef.current?.focus(); } }}>
        <p className={cx("mb-[5px] text-xs font-semibold", `interface-${kind}`)}>{KINDS[kind]}</p>
        <pre className="mb-3 text-ink font-mono text-sm leading-6 whitespace-pre-wrap [overflow-wrap:anywhere]"><code><Tokens tokens={tokens} /></code></pre>
        <p className="max-w-[90ch]">{entry.meaning}</p>
        {!entry.signature && (
          <p className="mt-3 text-muted text-xs">{entry.fileLabel
            ? "For exact arguments and types, see this declaration in the shared library included with the downloaded project."
            : "This compiler did not provide a signature. Inspect the declaration in the generated file for its exact arguments and types."}</p>
        )}
        {entry.arguments.length > 0 && (
          <dl className="grid grid-cols-[minmax(130px,1fr)_3fr] gap-x-[22px] gap-y-2 my-4 max-narrow:grid-cols-1 max-narrow:gap-[3px]">
            {entry.arguments.map((argument, index) => {
              const binding = argument.name + (argument.type ? ` : ${argument.type}` : "");
              return [
                <dt key={`name-${index}`} className="font-mono text-sm leading-6 text-ink">
                  <code>{argument.implicit ? `{${binding}}` : binding}</code>
                  {argument.anonymous && <span> (positional argument)</span>}
                </dt>,
                <dd key={`meaning-${index}`} className="m-0 text-muted max-narrow:mb-[9px]">{argument.meaning}</dd>,
              ];
            })}
          </dl>
        )}
        <p className="mt-3 text-muted text-xs"><span>Defined in </span><code>{entry.fileLabel || files[entry.file_kind]}</code></p>
        {entry.category === "location" && entry.line && typeof onGoToSource === "function" && (
          <button type="button" className="interface-source-button mt-[14px] min-h-[38px] px-3 py-[7px] bg-navy-600 text-white border border-navy-600 rounded text-xs font-[550] hover:bg-navy-500 hover:border-navy-500 max-narrow:min-h-11"
            onClick={() => onGoToSource(entry.line, entry.column)}>
            Go to source · line {entry.line}
          </button>
        )}
      </div>
    </div>
  );
}

export function InterfacePanel({ functions, catalog, generatedFile, pointsFile, factsFile, probabilityFile, parallelFile, onGoToSource, hidden = false }) {
  const prefix = useId();
  const [expanded, setExpanded] = useState(null);
  const { entries, missing } = useMemo(() => panelEntries(functions, catalog), [functions, catalog]);
  const groups = useMemo(() => groupEntries(entries), [entries]);
  const files = { core: generatedFile || "Algorithm definitions", points: pointsFile || "Named-line interface", facts: factsFile || "Generated facts",
    probability: probabilityFile || "Probability companion · requires Mathlib", parallel: parallelFile || "Parallel contracts" };
  const visible = !hidden && (entries.length > 0 || missing);
  if (!visible) return <div id="relations" hidden />;
  return (
    <div id="relations" className="mt-[14px]">
      {entries.length > 0 && (
        <p className="interface-legend flex flex-wrap gap-x-[22px] gap-y-2 mb-3 text-xs" aria-label="Interface color key">
          {Object.entries(KINDS).map(([kind, label]) => (
            <span key={kind} className={`interface-${kind}`}>
              <span aria-hidden="true" className="inline-block w-[7px] h-[7px] mr-1.5 rounded-full bg-current align-middle" />{label}
            </span>
          ))}
        </p>
      )}
      {groups.map((group) => (
        <details key={group.id} className="interface-group border-t border-border" open={group.id === "outputs"} aria-labelledby={`${prefix}-${group.id}`}>
          <summary id={`${prefix}-${group.id}`} className="interface-group-title min-h-11 py-3 text-[13px] font-semibold text-ink">{group.title}</summary>
          <div className="grid gap-2 pb-4">
            {Object.entries(KINDS).filter(([kind]) => group.entries.some((entry) => classify(entry) === kind)).map(([kind, label]) => (
              <div key={kind} className="flex flex-wrap items-start gap-2 min-w-0" role="group" aria-label={label}>
                {group.entries.filter((entry) => classify(entry) === kind).map((entry) => {
                  const id = `${prefix}-entry-${entries.indexOf(entry)}`;
                  return (
                    <InterfaceEntry key={id} id={id} entry={entry} kind={kind} catalog={catalog} files={files}
                      expanded={expanded === id} onToggle={() => setExpanded(expanded === id ? null : id)}
                      onClose={() => setExpanded(null)} onGoToSource={onGoToSource} />
                  );
                })}
              </div>
            ))}
          </div>
        </details>
      ))}
      {missing && <p className="interface-unavailable mt-3 text-muted text-xs">Interface metadata is unavailable. Restart the editor server with the current compiler.</p>}
    </div>
  );
}
