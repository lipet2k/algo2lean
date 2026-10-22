// Toast confirmations: shown by store.showToast, dismissed by a timer or a click.
import { test } from "vitest";
import assert from "node:assert/strict";
import { act, editor } from "./support/editor-harness.jsx";

test("a toast announces a message, replaces an earlier one, and goes away on its timer or a click", async () => {
  const app = editor();
  await app.ready();
  const region = app.byId("toast-region");
  assert.equal(region.getAttribute("role"), "status");
  assert.equal(region.getAttribute("aria-live"), "polite");
  assert.equal(app.container.querySelector('[id="toast"]'), null);

  act(() => { app.store.showToast("Citation copied"); });
  assert.equal(app.text("toast"), "Citation copied");
  assert.ok(app.byId("toast").className.includes("bg-success"), "success toasts are green");
  act(() => { app.store.showToast("Could not copy", { tone: "error" }); });
  assert.equal(app.text("toast"), "Could not copy");
  assert.ok(app.byId("toast").className.includes("bg-error"), "failure toasts are red");

  await app.flush();
  assert.equal(app.container.querySelector('[id="toast"]'), null, "the timer clears the toast");

  act(() => { app.store.showToast("BibTeX copied"); });
  await app.click("toast");
  assert.equal(app.container.querySelector('[id="toast"]'), null, "a click dismisses the toast");
  await app.flush();
  app.unmount();
});
