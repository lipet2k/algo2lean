#!/usr/bin/env node
/** Check that the committed editor build is current and deterministic.
 * Usage: node scripts/check_editor_build.mjs
 * Builds frontend/ into a temporary directory with the repository's Vite
 * configuration and compares the result byte for byte with editor/index.html,
 * editor/app.js, and editor/styles.css. The build must produce exactly those
 * files: the local server's asset allowlist and the site builders know no
 * others. The comparison reads the working tree, so it also works before the
 * rebuilt files are staged. CI runs the same check on each change.
 */

import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readdirSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const EXPECTED = ["index.html", "app.js", "styles.css"];

function listFiles(directory, prefix = "") {
  const names = [];
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    const name = prefix ? `${prefix}/${entry.name}` : entry.name;
    if (entry.isDirectory()) names.push(...listFiles(join(directory, entry.name), name));
    else names.push(name);
  }
  return names.sort();
}

function check(output) {
  const vite = join(root, "node_modules", "vite", "bin", "vite.js");
  if (!existsSync(vite)) {
    console.error("Run npm ci to install the editor toolchain first.");
    return 2;
  }
  const build = spawnSync(process.execPath, [vite, "build", "--outDir", output, "--logLevel", "warn"],
                          { cwd: root, stdio: "inherit" });
  if (build.status !== 0) {
    console.error("The editor build failed.");
    return build.status ?? 1;
  }
  const produced = listFiles(output);
  const problems = produced
    .filter((name) => !EXPECTED.includes(name))
    .map((name) => `${name}: the build produced a file that the server and site builders do not serve`);
  for (const name of EXPECTED) {
    if (!produced.includes(name)) {
      problems.push(`editor/${name}: the build did not produce this file`);
      continue;
    }
    const committed = join(root, "editor", name);
    if (!existsSync(committed) || !readFileSync(committed).equals(readFileSync(join(output, name)))) {
      problems.push(`editor/${name}: differs from a fresh build of frontend/; run npm run build and commit the result`);
    }
  }
  if (problems.length) {
    console.error(problems.join("\n"));
    return 1;
  }
  console.log(`editor/${EXPECTED.join(", editor/")} match a fresh build of frontend/.`);
  return 0;
}

const temporary = mkdtempSync(join(tmpdir(), "algo2lean-editor-build-"));
let status = 1;
try {
  status = check(temporary);
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
process.exit(status);
