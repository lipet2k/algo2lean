import { test } from "vitest";
import assert from "node:assert/strict";
import { useRef, useState } from "react";
import { act, fireEvent, render } from "@testing-library/react";
import { useCodeSearch } from "../src/components/CodeSearch.jsx";

function Harness({ initial, api, openSignal = 0 }) {
  const [text, setText] = useState(initial);
  const textareaRef = useRef(null);
  const viewportRef = useRef(null);
  const search = useCodeSearch({ text, textareaRef, viewportRef, label: "analysis", openSignal });
  api.current = { ...search, setText };
  return (
    <section onKeyDown={search.handleKeyDown}>
      {search.bar}
      <div ref={viewportRef} data-testid="viewport">
        <div>
          <textarea ref={textareaRef} value={text} onChange={(event) => setText(event.target.value)} />
          {search.match && <pre className="code-search-highlight" aria-hidden="true">{text.slice(0, search.match.start)}<mark>{text.slice(search.match.start, search.match.end)}</mark></pre>}
        </div>
      </div>
    </section>
  );
}

function surface(text = "alpha beta alpha", openSignal = 0) {
  const api = { current: null };
  const view = render(<Harness initial={text} api={api} openSignal={openSignal} />);
  const { container } = view;
  const query = (selector) => container.querySelector(selector);
  return {
    container, view,
    get search() { return api.current; },
    textarea: () => query("textarea:not([type])") || container.querySelectorAll("textarea")[0],
    viewport: () => query("[data-testid=viewport]"),
    bar: () => query("[role=search]"),
    input: () => query("input[type=search]"),
    count: () => query("[role=status]"),
    buttons: () => Array.from(query("[role=search]").querySelectorAll("button")),
    mark: () => query(".code-search-highlight mark"),
    open: (value) => act(() => { api.current.open(value); }),
    close: () => act(() => { api.current.close(); }),
    setText: (value) => act(() => { api.current.setText(value); }),
  };
}

test("search selects from the caret, wraps in both directions, and keeps find-field focus", async () => {
  const page = surface();
  const textarea = page.textarea();
  textarea.setSelectionRange(6, 6);
  await page.open("alpha");
  assert.equal(page.count().textContent, "2 of 2");
  assert.deepEqual([textarea.selectionStart, textarea.selectionEnd], [11, 16]);
  assert.equal(document.activeElement, page.input());
  fireEvent.click(page.buttons()[1]);
  assert.deepEqual([textarea.selectionStart, textarea.selectionEnd], [0, 5]);
  assert.equal(page.count().textContent, "1 of 2");
  fireEvent.click(page.buttons()[0]);
  assert.equal(textarea.selectionStart, 11);
  assert.equal(document.activeElement, page.input());
});

test("Ctrl/Cmd+F opens only the scoped editor, and Enter/Shift+Enter/Escape work", async () => {
  const page = surface();
  const textarea = page.textarea();
  textarea.setSelectionRange(0, 5);
  assert.equal(fireEvent.keyDown(textarea, { key: "f", metaKey: true }), false);
  assert.equal(page.input().value, "alpha");
  assert.equal(page.bar().hidden, false);
  assert.equal(fireEvent.keyDown(page.input(), { key: "Enter" }), false);
  assert.equal(textarea.selectionStart, 11);
  fireEvent.keyDown(page.input(), { key: "Enter", shiftKey: true });
  assert.equal(textarea.selectionStart, 0);
  assert.equal(fireEvent.keyDown(page.buttons()[2], { key: "Enter" }), true, "buttons retain their own Enter action");
  assert.equal(fireEvent.keyDown(page.input(), { key: "Escape" }), false);
  assert.equal(page.bar().hidden, true);
  assert.equal(document.activeElement, textarea);
  assert.equal(fireEvent.keyDown(textarea, { key: "f", ctrlKey: true }), false);
  await page.close();
  assert.equal(fireEvent.keyDown(textarea, { key: "f", ctrlKey: true, shiftKey: true }), true);
  assert.equal(page.bar().hidden, true);
  const outside = document.createElement("input");
  document.body.append(outside);
  assert.equal(fireEvent.keyDown(outside, { key: "f", metaKey: true }), true);
  outside.remove();
});

test("typing updates counts without moving focus, and no matches disable navigation", async () => {
  const page = surface();
  const textarea = page.textarea();
  await page.open();
  assert.equal(page.count().textContent, "Type to find");
  fireEvent.input(page.input(), { target: { value: "beta" } });
  assert.equal(page.count().textContent, "1 of 1");
  assert.deepEqual([textarea.selectionStart, textarea.selectionEnd], [6, 10]);
  assert.equal(document.activeElement, page.input());
  assert.ok(page.mark());
  assert.equal(page.mark().textContent, "beta");
  fireEvent.input(page.input(), { target: { value: "missing" } });
  assert.equal(page.count().textContent, "No matches");
  assert.equal(page.buttons()[0].disabled, true);
  assert.equal(page.buttons()[1].disabled, true);
  assert.equal(page.mark(), null);
  fireEvent.input(page.input(), { target: { value: "" } });
  assert.equal(page.count().textContent, "Type to find");
});

test("editing and programmatic loads refresh matches without rewriting code or the editing caret", async () => {
  const page = surface();
  await page.open("alpha");
  const textarea = page.textarea();
  fireEvent.input(textarea, { target: { value: "beta alpha" } });
  textarea.setSelectionRange(2, 2);
  await act(async () => { await Promise.resolve(); });
  assert.equal(page.count().textContent, "1 of 1");
  assert.equal(textarea.selectionStart, 2);
  assert.equal(textarea.value, "beta alpha");
  await page.setText("new document");
  assert.equal(page.count().textContent, "No matches");
  await page.setText("alpha restored");
  assert.equal(page.count().textContent, "1 of 1");
  assert.equal(textarea.value, "alpha restored");
});

test("a distant match scrolls the shared viewport vertically and horizontally", async () => {
  const page = surface("line\n".repeat(40) + "\t" + " ".repeat(100) + "needle");
  await page.open("needle");
  const viewport = page.viewport();
  const textarea = page.textarea();
  assert.ok(viewport.scrollTop > 850, String(viewport.scrollTop));
  assert.ok(viewport.scrollLeft > 500, String(viewport.scrollLeft));
  assert.equal(textarea.value.slice(textarea.selectionStart, textarea.selectionEnd), "needle");
  await page.close();
});

test("closing and unmounting release highlights and keyboard listeners", async () => {
  const page = surface();
  await page.open("alpha");
  const textarea = page.textarea();
  fireEvent.click(page.buttons()[2]);
  assert.equal(page.mark(), null);
  assert.equal(document.activeElement, textarea);
  page.view.unmount();
  const loose = document.createElement("textarea");
  document.body.append(loose);
  assert.equal(fireEvent.keyDown(loose, { key: "f", ctrlKey: true }), true);
  loose.remove();
});

test("a toolbar request opens the bar once and Escape closes it without replaying the request", async () => {
  const page = surface("alpha beta alpha", 1);
  await act(async () => { await Promise.resolve(); });
  assert.equal(page.bar().hidden, false);
  assert.equal(document.activeElement, page.input());
  fireEvent.input(page.input(), { target: { value: "beta" } });
  assert.equal(fireEvent.keyDown(page.input(), { key: "Escape" }), false);
  await act(async () => { await Promise.resolve(); });
  assert.equal(page.bar().hidden, true);
  assert.equal(document.activeElement, page.textarea());
  page.view.rerender(<Harness initial="alpha beta alpha" api={{ current: null }} openSignal={2} />);
  await act(async () => { await Promise.resolve(); });
  assert.equal(page.bar().hidden, false);
});
