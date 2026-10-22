import path from "node:path";

// Vitest runs from the repository root (vitest.config.mjs). Under the jsdom
// environment import.meta.url is not a file URL, so derive the root from the
// module directory when the runner provides it and from the working directory otherwise.
export const ROOT = typeof __dirname === "string" ? path.resolve(__dirname, "../../..") : process.cwd();
