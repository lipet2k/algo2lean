#!/usr/bin/env node
/** Check native/WASM byte equality with an already downloaded Pyodide runtime.
 * Usage: node scripts/check_browser_runtime.mjs /path/to/pyodide [python3]
 * Uses Node built-ins only. The script never downloads a runtime or package.
 */

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const runtime = process.argv[2] && resolve(process.argv[2]);
const python = process.argv[3] || "python3";
if (!runtime || process.argv.length > 4) {
  console.error("Usage: node scripts/check_browser_runtime.mjs /path/to/pyodide [python3]");
  process.exit(2);
}
const temporary = mkdtempSync(join(tmpdir(), "algo2lean-wasm-parity-"));

// Prepare the same release resource closure as the static-site builder. Native
// expectations come from the actual compiler bridge, without invoking Lean.
const prepare = String.raw`
import hashlib, json, sys
from pathlib import Path
from algo2lean.browser import request
from algo2lean.editor_examples import load_example_project
from algo2lean.project import load_project
from scripts.build_site import compiler_files, zip_bytes

root, target = Path(sys.argv[1]), Path(sys.argv[2])
runtime = json.loads((root / "browser-runtime.json").read_text())
payload = compiler_files(root)
payload["release-manifest.json"] = json.dumps({
    "version": json.loads(payload["publication.json"])["version"],
    "pyodide_version": runtime["version"], "commit": None, "bundle_sha256": None,
}).encode()
(target / "compiler.zip").write_bytes(zip_bytes(payload))
fixtures = []
def add(name, body, project=False):
    response = request("/api/generation", body, project=project)
    if response["status"] != 200:
        raise RuntimeError(name + ": " + str(response))
    fixtures.append({"name": name, "body": body, "project": project,
                     "expected": response["body"]})

for name in ("factorial", "merge_sort", "object_sequences", "weighted_ticks"):
    filename = name + ".algo"
    add(name, {"filename": filename, "source": (root / "examples" / filename).read_text()})
add("standalone", {"filename": "example.algo", "standalone": True,
    "source": "# caf\u00e9\r\ndef f(n: Int) -> Int:\r\n    # @result\r\n    return n + 1\r\n"})

entry = "use_direct.algo"
project = load_project(root / "examples/interfaces" / entry, root=root / "examples/interfaces")
sources = {module.path.relative_to(project.root).as_posix(): module.source
           for module in project.modules.values()}
add("interface imports", {"filename": entry, "source": sources[entry], "project_sources": sources}, True)

recursive = load_example_project("mutual-recursion-imports")
add("mutually recursive imports", {"filename": recursive["entry"],
    "source": recursive["sources"][recursive["entry"]], "project_sources": recursive["sources"]}, True)

catalogs = {identifier: load_example_project(identifier)
            for identifier in ("modules", "interfaces", "mutual-recursion-imports", "dijkstra")}
for identifier in ("modules", "interfaces"):
    project = catalogs[identifier]
    add(identifier + " project folder", {"filename": project["entry"],
        "source": project["sources"][project["entry"]], "project_sources": project["sources"]}, True)

catalog = load_example_project("dijkstra")
for backend in ("binary", "fibonacci"):
    entry = "composable_dijkstra/dijkstra_" + backend + ".algo"
    add(backend + " Dijkstra imports", {"filename": entry, "source": catalog["sources"][entry],
                                     "project_sources": catalog["sources"]}, True)
(target / "fixtures.json").write_text(json.dumps({"runtime": runtime["version"],
    "fixtures": fixtures, "catalogs": catalogs}), encoding="utf-8")
`;

function sameFiles(actual, expected, context) {
  assert.deepEqual(Object.keys(actual).sort(), Object.keys(expected).sort(), `${context}: file names`);
  for (const [name, contents] of Object.entries(expected)) {
    assert.ok(Buffer.from(actual[name], "utf8").equals(Buffer.from(contents, "utf8")), `${context}: byte mismatch in ${name}`);
  }
}

try {
  const native = spawnSync(python, ["-c", prepare, root, temporary], {
    cwd: root, encoding: "utf8", maxBuffer: 4 * 1024 * 1024,
  });
  if (native.error || native.status !== 0) throw new Error(native.error?.message || native.stderr || "Native fixture preparation failed.");
  const configuration = JSON.parse(readFileSync(join(temporary, "fixtures.json"), "utf8"));
  // All Python/runtime resources must be present locally; accidental package or
  // CDN fetches should fail this offline reproducibility check immediately.
  globalThis.fetch = async url => { throw new Error(`Unexpected network request: ${url}`); };
  const { loadPyodide } = await import(pathToFileURL(join(runtime, "pyodide.mjs")).href);
  const pyodide = await loadPyodide({ indexURL: runtime + "/" });
  assert.equal(pyodide.version, configuration.runtime, "Pinned runtime version");
  pyodide.FS.writeFile("/compiler.zip", readFileSync(join(temporary, "compiler.zip")));
  await pyodide.runPythonAsync(`
import base64, hashlib, io, json, sys, zipfile
zipfile.ZipFile('/compiler.zip').extractall('/release')
sys.path.insert(0, '/release')
from algo2lean.browser import request

def _request_json(encoded):
    value = json.loads(encoded)
    return json.dumps(request(value['path'], value.get('body'), value.get('project', False)))

def _archive_summary(encoded):
    raw = base64.b64decode(encoded)
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        names = archive.namelist()
        return json.dumps({'names': names,
            'hashes': {name: hashlib.sha256(archive.read(name)).hexdigest() for name in names},
            'manifest': json.loads(archive.read('generation.json'))})
`);
  const requestJson = pyodide.globals.get("_request_json");
  const archiveSummary = pyodide.globals.get("_archive_summary");
  const call = (path, body, project = false) => JSON.parse(requestJson(JSON.stringify({ path, body, project })));
  const ok = (response, context) => {
    assert.equal(response.status, 200, `${context}: ${JSON.stringify(response.body).slice(0, 400)}`);
    return response.body;
  };
  try {
    const capabilities = ok(call("/api/capabilities"), "Capabilities");
    assert.equal(capabilities.browser_compiler, true);
    assert.equal(capabilities.lean_check, false);
    assert.ok(ok(call("/api/examples"), "Examples").examples.length >= 20);
    assert.ok(ok(call("/api/publication"), "Publication").title);
    assert.ok(ok(call("/CITATION.cff"), "Citation").includes("cff-version:"));
    for (const [identifier, project] of Object.entries(configuration.catalogs)) {
      const imported = ok(call(`/api/example-project/${identifier}`), "Project example");
      assert.equal(imported.entry, project.entry);
      sameFiles(imported.sources, project.sources, `${identifier}: project catalog sources`);
      sameFiles(imported.analyses, project.analyses, `${identifier}: project catalog proofs`);
    }
    console.log("PASS catalog, metadata, citation, and imported project loading");

    for (const fixture of configuration.fixtures) {
      const data = ok(call("/api/generation", fixture.body, fixture.project), fixture.name);
      sameFiles(data.files, fixture.expected.files, fixture.name);
      sameFiles(data.libraries, fixture.expected.libraries, `${fixture.name} shared libraries`);
      for (const field of ["sources", "outputs", "libraries", "options", "compiler", "lean_toolchain"]) {
        assert.deepEqual(data.manifest[field], fixture.expected.manifest[field], `${fixture.name}: manifest ${field}`);
      }
      assert.equal(data.manifest.runtime.pyodide, configuration.runtime);
      const compiled = ok(call("/api/compile", fixture.body, fixture.project), fixture.name + " compile");
      const core = compiled.module.replaceAll(".", "/") + ".lean";
      assert.equal(compiled.lean, fixture.expected.files[core]);
      const check = ok(call("/api/check", fixture.body, fixture.project), fixture.name + " check availability");
      assert.equal(check.available, false);
      assert.equal(check.ok, false);
      assert.equal(check.lean, compiled.lean);
      console.log(`PASS ${fixture.name}: ${Object.keys(data.files).length} generated files match native bytes`);
    }

    for (const fixture of [configuration.fixtures[1], configuration.fixtures.at(-1)]) {
      const response = call("/api/generation", { ...fixture.body, archive: true }, fixture.project);
      ok(response, fixture.name + " archive");
      assert.equal(response.encoding, "base64");
      const archive = JSON.parse(archiveSummary(response.body));
      for (const [name, identity] of Object.entries({ ...fixture.expected.manifest.outputs, ...fixture.expected.manifest.libraries })) {
        assert.equal(archive.hashes[name], identity.sha256, `${fixture.name}: archived bytes ${name}`);
      }
      assert.ok(archive.names.includes("lakefile.toml"));
      assert.ok(archive.names.includes("lean-toolchain"));
      assert.deepEqual(archive.names.filter(name => name.endsWith(".lean")).sort(),
        Object.keys({ ...fixture.expected.files, ...fixture.expected.libraries }).sort(),
        `${fixture.name}: complete generation folder can be verified`);
      assert.deepEqual(archive.manifest.outputs, fixture.expected.manifest.outputs);
      console.log(`PASS ${fixture.name}: generation ZIP contents and manifest`);
    }
    const projectFixture = configuration.fixtures.at(-1);
    const projectExport = call("/api/project-export", projectFixture.body, true);
    ok(projectExport, "Project export");
    assert.equal(projectExport.encoding, "base64");
    const invalid = call("/api/compile", { source: "import os\n" });
    assert.equal(invalid.status, 400);
    const traversal = call("/api/compile", { filename: "main.algo", source: "def f() -> Int:\n    return 0\n",
      project_sources: { "main.algo": "def f() -> Int:\n    return 0\n", "../bad.algo": "" } }, true);
    assert.equal(traversal.status, 400);
    const analysis = ok(call("/api/analyze", { ...configuration.fixtures[0].body, analysis: "-- proof\n" }), "Analysis availability");
    assert.equal(analysis.available, false);
    console.log("PASS project export, invalid inputs, and unavailable Lean checking");
  } finally {
    requestJson.destroy();
    archiveSummary.destroy();
  }
  console.log(`Browser runtime parity passed with Pyodide ${pyodide.version}; no network access.`);
} catch (error) {
  console.error(error.stack || String(error));
  process.exitCode = 1;
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
