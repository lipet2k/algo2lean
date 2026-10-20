// Vitest setup: React Testing Library cleans up between tests automatically when
// globals are enabled; keep an explicit cleanup for clarity.
import { afterEach } from "vitest";
import { cleanup } from "@testing-library/react";

// jsdom has no canvas and logs "not implemented" for getContext. The find bar
// measures text with a canvas when one exists and otherwise falls back to the
// textarea's computed style, which is the path these tests exercise.
if (typeof HTMLCanvasElement !== "undefined") {
  HTMLCanvasElement.prototype.getContext = () => null;
}

afterEach(() => cleanup());
