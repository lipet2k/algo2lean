(function (root, factory) {
  "use strict";
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.Algo2LeanCodeSearch = api;
})(typeof window === "undefined" ? globalThis : window, function () {
  "use strict";

  function matches(text, query) {
    if (!query) return [];
    const expression = new RegExp(query.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"), "giu");
    return [...text.matchAll(expression)].map((match) => ({ start: match.index, end: match.index + match[0].length }));
  }

  function create({ textarea, viewport, document, scope = textarea, label = "code" }) {
    const view = document.defaultView;
    const bar = document.createElement("div");
    bar.className = "code-search";
    bar.hidden = true;
    bar.setAttribute("role", "search");
    bar.setAttribute("aria-label", `Find in ${label}`);
    const field = document.createElement("label");
    field.className = "code-search-field";
    field.textContent = "Find";
    const input = document.createElement("input");
    input.type = "search";
    input.autocomplete = "off";
    input.spellcheck = false;
    input.setAttribute("aria-label", `Find in ${label}`);
    input.setAttribute("placeholder", "Text to find");
    const count = document.createElement("span");
    count.className = "code-search-count";
    count.setAttribute("role", "status");
    count.setAttribute("aria-live", "polite");
    count.setAttribute("aria-atomic", "true");
    function button(text, meaning) {
      const element = document.createElement("button");
      element.type = "button";
      element.className = "button button-quiet";
      element.textContent = text;
      element.setAttribute("aria-label", meaning);
      return element;
    }
    const previousButton = button("Previous", "Previous match (Shift+Enter)");
    const nextButton = button("Next", "Next match (Enter)");
    const closeButton = button("Close", "Close find (Escape)");
    field.append(input);
    bar.append(field, count, previousButton, nextButton, closeButton);

    // Native textarea selection is not consistently painted while the search
    // field has focus. A pointer-transparent mirror keeps the current match visible.
    const highlight = document.createElement("pre");
    highlight.className = "code-search-highlight";
    highlight.setAttribute("aria-hidden", "true");
    highlight.hidden = true;
    textarea.parentElement.insertBefore(highlight, textarea);
    let found = [], current = -1, lastText = null, lastQuery = null;
    let canvas = null;
    const listeners = [];
    const listen = (element, name, handler) => {
      element.addEventListener(name, handler);
      listeners.push([element, name, handler]);
    };
    const computed = () => view?.getComputedStyle?.(textarea) || {};
    const number = (value, fallback) => Number.parseFloat(value) || fallback;

    function paint() {
      previousButton.disabled = nextButton.disabled = !found.length;
      count.textContent = !input.value ? "Type to find" : found.length ? `${current + 1} of ${found.length}` : "No matches";
      highlight.hidden = bar.hidden || current < 0;
      if (highlight.hidden) return;
      const style = computed();
      for (const property of ["font", "fontSize", "fontFamily", "fontWeight", "fontStyle", "lineHeight", "letterSpacing", "padding", "tabSize", "textAlign"]) {
        if (style[property]) highlight.style[property] = style[property];
      }
      const match = found[current];
      highlight.textContent = textarea.value.slice(0, match.start);
      const mark = document.createElement("mark");
      mark.textContent = textarea.value.slice(match.start, match.end);
      highlight.append(mark);
    }

    function reveal() {
      if (current < 0) return;
      const match = found[current];
      textarea.setSelectionRange(match.start, match.end);
      const style = computed();
      const fontSize = number(style.fontSize, 14);
      const lineHeight = number(style.lineHeight, fontSize * 1.5);
      const prefix = textarea.value.slice(0, match.start);
      const lines = prefix.split("\n");
      if (!canvas) canvas = document.createElement("canvas");
      const context = canvas.getContext?.("2d");
      if (context) context.font = style.font || `${fontSize}px ${style.fontFamily || "monospace"}`;
      const width = (text) => context ? context.measureText(text).width : text.length * fontSize * 0.6;
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

    function refresh({ reveal: move = false } = {}) {
      if (bar.hidden) return;
      if (textarea.value !== lastText || input.value !== lastQuery) {
        found = matches(textarea.value, input.value);
        current = found.findIndex((match) => match.start >= textarea.selectionStart);
        if (current < 0 && found.length) current = 0;
        lastText = textarea.value;
        lastQuery = input.value;
      }
      paint();
      if (move) reveal();
    }

    function open(query) {
      const opening = bar.hidden;
      if (typeof query === "string") input.value = query;
      else if (opening) {
        const selected = textarea.value.slice(textarea.selectionStart, textarea.selectionEnd);
        if (selected && selected.length <= 200 && !selected.includes("\n")) input.value = selected;
      }
      bar.hidden = false;
      lastText = null;
      input.focus({ preventScroll: true });
      input.select();
      refresh({ reveal: true });
      bar.scrollIntoView?.({ block: "nearest" });
    }

    function close() {
      bar.hidden = true;
      highlight.hidden = true;
      textarea.focus({ preventScroll: true });
    }

    function navigate(direction) {
      if (bar.hidden) open();
      refresh();
      if (!found.length) return;
      current = (current + direction + found.length) % found.length;
      paint();
      reveal();
    }

    function keydown(event) {
      if (event.defaultPrevented || event.isComposing) return;
      if ((event.ctrlKey || event.metaKey) && !event.altKey && !event.shiftKey && event.key.toLowerCase() === "f") {
        event.preventDefault();
        event.stopPropagation();
        open();
      } else if (!bar.hidden && event.key === "Escape") {
        event.preventDefault();
        event.stopPropagation();
        close();
      } else if (!bar.hidden && event.target === input && event.key === "Enter") {
        event.preventDefault();
        event.stopPropagation();
        navigate(event.shiftKey ? -1 : 1);
      }
    }
    listen(scope, "keydown", keydown);
    listen(bar, "keydown", keydown);
    listen(input, "input", () => refresh({ reveal: true }));
    listen(textarea, "input", () => refresh());
    listen(previousButton, "click", () => { navigate(-1); input.focus({ preventScroll: true }); });
    listen(nextButton, "click", () => { navigate(1); input.focus({ preventScroll: true }); });
    listen(closeButton, "click", close);
    paint();
    return { element: bar, open, close, refresh, next: () => navigate(1), previous: () => navigate(-1),
      destroy() {
        for (const [element, name, handler] of listeners) element.removeEventListener(name, handler);
        highlight.remove();
        bar.remove();
      } };
  }
  return { matches, create };
});
