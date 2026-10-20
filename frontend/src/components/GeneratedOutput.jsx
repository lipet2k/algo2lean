import { useLayoutEffect, useRef } from "react";
import { Tokens } from "./Tokens.jsx";
import { blurOnEscape } from "./classes.js";

// Read-only generated Lean: a highlighted layer under a transparent textarea so
// the text can be selected and copied, scrolling together.
export function GeneratedOutput({ id, codeId, selectionId, text, tokens, label, describedBy, busy, visible, emptyId, empty, intent }) {
  const viewportRef = useRef(null);
  const applied = useRef(0);
  useLayoutEffect(() => {
    if (!intent || intent.serial === applied.current) return;
    applied.current = intent.serial;
    const viewport = viewportRef.current;
    if (!viewport) return;
    if (intent.scrollTop !== undefined) viewport.scrollTop = intent.scrollTop;
    if (intent.scrollLeft !== undefined) viewport.scrollLeft = intent.scrollLeft;
  }, [intent]);
  return (
    <div className="output-container">
      <div id={emptyId} className="max-w-[440px] px-[26px] pt-6 pb-6 mx-auto flex flex-col items-start justify-center h-full" hidden={visible}>
        {empty}
      </div>
      <div id={id} ref={viewportRef} className="lean-output code-viewport" hidden={!visible} aria-busy={String(busy)}>
        <div className="generated-canvas code-content">
          <pre className="generated-text generated-highlight" aria-hidden="true"><code id={codeId}><Tokens tokens={tokens} /></code></pre>
          <textarea id={selectionId} className="generated-text generated-selection" readOnly value={text} aria-label={label}
            aria-describedby={describedBy} wrap="off" spellCheck={false} onKeyDown={blurOnEscape} />
        </div>
      </div>
    </div>
  );
}
