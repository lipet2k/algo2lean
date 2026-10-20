import { useCallback, useEffect, useRef, useState } from "react";
import { matches } from "../lib/code-search.js";
import { Button } from "./Button.jsx";

function number(value, fallback) {
  return Number.parseFloat(value) || fallback;
}

// Scroll the shared viewport so the match is visible. Metrics come from the
// textarea's computed style; the canvas measures proportional text when available.
function reveal(textarea, viewport, match) {
  textarea.setSelectionRange(match.start, match.end);
  const view = textarea.ownerDocument?.defaultView;
  const style = view?.getComputedStyle?.(textarea) || {};
  const fontSize = number(style.fontSize, 14);
  const lineHeight = number(style.lineHeight, fontSize * 1.5);
  const prefix = textarea.value.slice(0, match.start);
  const lines = prefix.split("\n");
  let context = null;
  try { context = textarea.ownerDocument.createElement("canvas").getContext?.("2d") || null; } catch (_) { context = null; }
  if (context) context.font = style.font || `${fontSize}px ${style.fontFamily || "monospace"}`;
  const width = (text) => (context ? context.measureText(text).width : text.length * fontSize * 0.6);
  const tabWidth = width(" ") * number(style.tabSize, 4);
  let column = 0;
  lines.at(-1).split("\t").forEach((part, index) => {
    if (index) column = (Math.floor(column / tabWidth) + 1) * tabWidth;
    column += width(part);
  });
  const editorRect = textarea.getBoundingClientRect();
  const viewportRect = viewport.getBoundingClientRect();
  const x = editorRect.left - viewportRect.left + viewport.scrollLeft + number(style.paddingLeft, 0) + column;
  const y = editorRect.top - viewportRect.top + viewport.scrollTop + number(style.paddingTop, 0) + (lines.length - 1) * lineHeight;
  const gutter = Math.max(0, editorRect.left - viewportRect.left + viewport.scrollLeft);
  const targetWidth = width(textarea.value.slice(match.start, match.end).split("\n")[0]);
  if (y < viewport.scrollTop || y + lineHeight > viewport.scrollTop + viewport.clientHeight) {
    viewport.scrollTop = Math.max(0, y - (viewport.clientHeight - lineHeight) / 2);
  }
  if (x < viewport.scrollLeft + gutter || x + targetWidth > viewport.scrollLeft + viewport.clientWidth) {
    viewport.scrollLeft = Math.max(0, x - gutter - 24);
  }
}

// Find within a code editor. The hook returns the bar to render, a keydown
// handler for the editor's section, and the current match for the mirror layer.
export function useCodeSearch({ text, textareaRef, viewportRef, label = "code", openSignal = 0 }) {
  const [open, setOpen] = useState(false);
  const [query, setQuery] = useState("");
  const [found, setFound] = useState([]);
  const [current, setCurrent] = useState(-1);
  const inputRef = useRef(null);
  const barRef = useRef(null);
  const lastSeen = useRef({ text: null, query: null });
  const pendingReveal = useRef(false);

  const refresh = useCallback((options = {}) => {
    const textarea = textareaRef.current;
    const viewport = viewportRef.current;
    if (!textarea) return;
    const queryValue = inputRef.current ? inputRef.current.value : query;
    let list = found;
    let index = current;
    if (textarea.value !== lastSeen.current.text || queryValue !== lastSeen.current.query) {
      list = matches(textarea.value, queryValue);
      index = list.findIndex((match) => match.start >= textarea.selectionStart);
      if (index < 0 && list.length) index = 0;
      lastSeen.current = { text: textarea.value, query: queryValue };
      setFound(list);
      setCurrent(index);
    }
    if (options.reveal && index >= 0 && viewport) reveal(textarea, viewport, list[index]);
  }, [textareaRef, viewportRef, query, found, current]);

  // Editing and programmatic loads refresh matches without moving the caret.
  useEffect(() => {
    if (!open) return;
    if (pendingReveal.current) { pendingReveal.current = false; refresh({ reveal: true }); }
    else refresh();
  }, [text, open, query, refresh]);

  const openSearch = useCallback((value) => {
    const textarea = textareaRef.current;
    if (typeof value === "string") setQuery(value);
    else if (!open && textarea) {
      const selected = textarea.value.slice(textarea.selectionStart, textarea.selectionEnd);
      if (selected && selected.length <= 200 && !selected.includes("\n")) setQuery(selected);
    }
    lastSeen.current = { text: null, query: null };
    pendingReveal.current = true;
    setOpen(true);
  }, [open, textareaRef]);

  useEffect(() => {
    if (!open) return;
    inputRef.current?.focus({ preventScroll: true });
    inputRef.current?.select();
    barRef.current?.scrollIntoView?.({ block: "nearest" });
  }, [open]);

  // Each toolbar request opens the bar once; closing it must not replay the request.
  const handledSignal = useRef(0);
  useEffect(() => {
    if (openSignal && openSignal !== handledSignal.current) {
      handledSignal.current = openSignal;
      openSearch();
    }
  }, [openSignal, openSearch]);

  const close = useCallback(() => {
    setOpen(false);
    textareaRef.current?.focus({ preventScroll: true });
  }, [textareaRef]);

  const navigate = useCallback((direction) => {
    if (!open) { openSearch(); return; }
    const textarea = textareaRef.current;
    const viewport = viewportRef.current;
    if (!textarea) return;
    let list = found;
    let index = current;
    const queryValue = inputRef.current ? inputRef.current.value : query;
    if (textarea.value !== lastSeen.current.text || queryValue !== lastSeen.current.query) {
      list = matches(textarea.value, queryValue);
      index = list.findIndex((match) => match.start >= textarea.selectionStart);
      if (index < 0 && list.length) index = 0;
      lastSeen.current = { text: textarea.value, query: queryValue };
      setFound(list);
    }
    if (!list.length) { setCurrent(index); return; }
    index = (index + direction + list.length) % list.length;
    setCurrent(index);
    if (viewport) reveal(textarea, viewport, list[index]);
  }, [open, openSearch, textareaRef, viewportRef, found, current, query]);

  const handleKeyDown = useCallback((event) => {
    if (event.defaultPrevented || event.isComposing) return;
    if ((event.ctrlKey || event.metaKey) && !event.altKey && !event.shiftKey && event.key.toLowerCase() === "f") {
      event.preventDefault();
      event.stopPropagation();
      openSearch();
    } else if (open && event.key === "Escape") {
      event.preventDefault();
      event.stopPropagation();
      close();
    } else if (open && event.target === inputRef.current && event.key === "Enter") {
      event.preventDefault();
      event.stopPropagation();
      navigate(event.shiftKey ? -1 : 1);
    }
  }, [open, openSearch, close, navigate]);

  const match = open && current >= 0 ? found[current] || null : null;
  const count = !query ? "Type to find" : found.length ? `${current + 1} of ${found.length}` : "No matches";
  const bar = (
    <div ref={barRef} className="code-search flex flex-wrap items-center gap-2 px-[18px] py-2.5 border-b border-border bg-navy-50 max-phone:px-3"
      hidden={!open} role="search" aria-label={`Find in ${label}`}>
      <label className="flex flex-[1_1_210px] items-center gap-2 text-ink text-[13px] max-phone:basis-full">Find
        <input ref={inputRef} type="search" autoComplete="off" spellCheck={false} aria-label={`Find in ${label}`} placeholder="Text to find"
          className="w-full min-w-20 min-h-[38px] border border-navy-200 rounded-lg px-2.5 py-[7px] bg-paper text-ink font-mono text-[13px] focus-visible:outline-2 focus-visible:outline-navy-500 focus-visible:outline-offset-2 max-phone:text-base"
          value={query} onChange={(event) => { setQuery(event.target.value); pendingReveal.current = true; }} />
      </label>
      <span className="min-w-[76px] text-muted text-xs text-center max-phone:mr-auto max-phone:text-left" role="status" aria-live="polite" aria-atomic="true">{count}</span>
      <Button className="px-2.5" aria-label="Previous match (Shift+Enter)" disabled={!found.length} onClick={() => { navigate(-1); inputRef.current?.focus({ preventScroll: true }); }}>Previous</Button>
      <Button className="px-2.5" aria-label="Next match (Enter)" disabled={!found.length} onClick={() => { navigate(1); inputRef.current?.focus({ preventScroll: true }); }}>Next</Button>
      <Button className="px-2.5" aria-label="Close find (Escape)" onClick={close}>Close</Button>
    </div>
  );
  return { bar, handleKeyDown, match, open: openSearch, close };
}
