import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { Tokens } from "./Tokens.jsx";
import { cx } from "./classes.js";
import { useStore } from "./store-context.jsx";

// A textarea with a line gutter and a highlighted mirror sharing one scroll
// surface. Selection, focus, and scrolling requests arrive as intents from the
// store and are applied after the matching text has been committed.
export function CodeEditor({
  id, viewportId, measureId, codeId, lineNumbersId, value, onChange, tokens, label, describedBy,
  indentSize, indentPattern, autoIndent, intent, busy = false, viewportClassName, textClassName = "",
  layerClassName = "", searchMatch = null, footer, registerName, refs = null,
}) {
  const store = useStore();
  const textareaRef = useRef(null);
  const viewportRef = useRef(null);
  const appliedIntent = useRef(0);
  const lastSeen = useRef(value);
  const [cursor, setCursor] = useState({ line: 1, column: 1 });

  useEffect(() => {
    const textarea = textareaRef.current;
    const viewport = viewportRef.current;
    store.attach(registerName, textarea);
    store.attach(`${registerName}-viewport`, viewport);
    return () => { store.detach(registerName, textarea); store.detach(`${registerName}-viewport`, viewport); };
  }, [store, registerName]);

  useEffect(() => { lastSeen.current = value; }, [value]);

  useEffect(() => {
    if (!refs) return;
    refs.textarea.current = textareaRef.current;
    refs.viewport.current = viewportRef.current;
  });

  const updateCursor = useCallback(() => {
    const textarea = textareaRef.current;
    if (!textarea) return;
    const before = textarea.value.slice(0, textarea.selectionStart);
    setCursor({ line: before.split("\n").length, column: before.length - before.lastIndexOf("\n") });
  }, []);

  useLayoutEffect(() => {
    if (!intent || intent.serial === appliedIntent.current) return;
    appliedIntent.current = intent.serial;
    const textarea = textareaRef.current;
    const viewport = viewportRef.current;
    if (!textarea || !viewport) return;
    if (intent.selection) textarea.setSelectionRange(intent.selection[0], intent.selection[1]);
    if (intent.focus) textarea.focus({ preventScroll: Boolean(intent.preventScroll) });
    if (intent.scrollTop !== undefined) viewport.scrollTop = intent.scrollTop;
    if (intent.scrollLeft !== undefined) viewport.scrollLeft = intent.scrollLeft;
    if (intent.scrollIntoView) viewport.scrollIntoView?.({ block: "nearest" });
    updateCursor();
  }, [intent, value, updateCursor]);

  const handleChange = (event) => {
    lastSeen.current = event.target.value;
    onChange(event.target.value);
  };

  // Native insertText retains the textarea undo history in browsers that support it.
  const insertText = (text, start, end) => {
    const textarea = textareaRef.current;
    const from = start ?? textarea.selectionStart;
    const to = end ?? textarea.selectionEnd;
    textarea.focus();
    textarea.setSelectionRange(from, to);
    let inserted = false;
    try { inserted = document.execCommand("insertText", false, text); } catch (_) { /* setRangeText handles browsers without native insertion. */ }
    if (!inserted) textarea.setRangeText(text, from, to, "end");
    if (textarea.value !== lastSeen.current) {
      lastSeen.current = textarea.value;
      onChange(textarea.value);
    }
  };

  const handleKeyDown = (event) => {
    if (event.isComposing) return;
    const textarea = textareaRef.current;
    if (event.key === "Escape") { event.preventDefault(); textarea.blur(); return; }
    if (event.key === "Tab") {
      event.preventDefault();
      const start = textarea.selectionStart;
      const end = textarea.selectionEnd;
      const lineStart = textarea.value.lastIndexOf("\n", start - 1) + 1;
      if (start === end && !event.shiftKey) {
        insertText(" ".repeat(indentSize - ((start - lineStart) % indentSize)));
      } else {
        const selected = textarea.value.slice(lineStart, end);
        const outdent = new RegExp(`^( {1,${indentSize}}|\\t)`);
        const unit = " ".repeat(indentSize);
        const transformed = selected.split("\n").map((line, index, lines) => {
          if (index === lines.length - 1 && !line && end > start) return line;
          return event.shiftKey ? line.replace(outdent, "") : unit + line;
        }).join("\n");
        insertText(transformed, lineStart, end);
        textarea.setSelectionRange(lineStart, lineStart + transformed.length);
      }
      updateCursor();
    } else if (event.key === "Enter" && !event.metaKey && !event.ctrlKey && !event.altKey) {
      event.preventDefault();
      const before = textarea.value.slice(0, textarea.selectionStart);
      const line = before.slice(before.lastIndexOf("\n") + 1);
      const indent = line.match(indentPattern)[0];
      insertText("\n" + indent + (autoIndent(line) ? " ".repeat(indentSize) : ""));
    }
  };

  const lineCount = useMemo(() => value.split("\n").length, [value]);
  const lineNumbers = useMemo(() => Array.from({ length: lineCount }, (_, index) => index + 1).join("\n"), [lineCount]);

  return (
    <>
      <div id={viewportId} ref={viewportRef} className={cx("code-viewport", viewportClassName)}>
        <div className="code-canvas">
          <div className="line-gutter" aria-hidden="true"><pre id={lineNumbersId}>{lineNumbers}</pre></div>
          <div className="code-content">
            <pre id={measureId} className={cx("code-text code-layer", textClassName, layerClassName)} aria-hidden="true">
              <code id={codeId}><Tokens tokens={tokens} /></code>
            </pre>
            {searchMatch && (
              <pre className={cx("code-text code-search-highlight", textClassName)} aria-hidden="true">
                {value.slice(0, searchMatch.start)}<mark>{value.slice(searchMatch.start, searchMatch.end)}</mark>
              </pre>
            )}
            <textarea
              id={id} ref={textareaRef} className={cx("code-text code-input", textClassName)} value={value}
              onChange={handleChange} onKeyDown={handleKeyDown} onClick={updateCursor} onKeyUp={updateCursor} onSelect={updateCursor}
              aria-label={label} aria-describedby={describedBy} aria-busy={busy ? "true" : undefined}
              wrap="off" spellCheck={false} autoCapitalize="off" autoComplete="off" autoCorrect="off"
            />
          </div>
        </div>
      </div>
      {footer ? footer(cursor) : null}
    </>
  );
}
