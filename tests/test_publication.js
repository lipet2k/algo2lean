"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");

const script = fs.readFileSync(path.join(__dirname, "../editor/publication.js"), "utf8");
const CONFIGURED = {
  title: "Algo2Lean", version: "0.1.0", status: "release",
  authors: [{ given_names: "Ada", family_names: "Example" },
    { given_names: "Grace", family_names: "Sample" }],
  creators: [{ given_names: "Ada", family_names: "Example", website: "https://example.com/ada" }],
  contributors: [{ given_names: "Grace", family_names: "Sample", website: "https://example.com/grace" }],
  repository_url: "https://github.com/example/algo2lean",
  doi: "10.1234/example-release",
  citation: "Ada Example; Grace Sample. Algo2Lean (version 0.1.0) [Computer software].",
  bibtex: "@software{algo2lean,\n  title = {Algo2Lean},\n  version = {0.1.0},\n}\n",
  citation_url: "/CITATION.cff",
};

class Element {
  constructor(id) {
    this.id = id;
    this.textContent = "";
    this.hidden = false;
    this.disabled = false;
    this.listeners = new Map();
  }
  set innerHTML(_) { throw new Error("Publication text must not be parsed as markup"); }
  set textContent(value) { this.children = []; this.text = value; }
  get textContent() { return this.text + this.children.map((child) => child.textContent).join(""); }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.text = ""; this.children = children; }
  addEventListener(name, callback) { this.listeners.set(name, callback); }
  async click() { if (!this.disabled) await this.listeners.get("click")?.(); }
}

async function surface(data = CONFIGURED, options = {}) {
  const ids = ["citation-text", "citation-status", "project-version", "citation-version-note",
    "project-authors", "project-contributors", "github-link", "release-doi", "copy-citation", "download-citation",
    "citation-bibtex", "bibtex-details", "copy-bibtex"];
  const elements = new Map(ids.map((id) => [id, new Element(id)]));
  const byId = (id) => elements.get(id);
  for (const id of ["project-authors", "project-contributors", "github-link", "release-doi", "download-citation", "bibtex-details"]) {
    byId(id).hidden = true;
  }
  byId("copy-citation").disabled = true;
  byId("project-version").textContent = "Development build";
  byId("citation-version-note").textContent = "This is a development build.";
  byId("citation-text").textContent = "Loading citation details…";
  if (options.noPanel) elements.delete("citation-text");
  const requests = [];
  const copied = [];
  // A source draft is deliberately outside the citation surface. Publication
  // loading must neither read it nor change it, including when a request fails.
  const editor = { source: "def algorithm() -> Int:\n    return 1\n", canCompile: true };
  const context = {
    document: { getElementById(id) {
      if (id === "source") throw new Error("Publication requested the source draft");
      return byId(id);
    }, createElement: (tag) => new Element(tag), createTextNode: (text) => ({ textContent: text }) },
    URL,
    navigator: { clipboard: { async writeText(value) {
      if (options.clipboardFailure) throw new Error("Clipboard unavailable");
      copied.push(value);
    } } },
    async fetch(url) {
      requests.push(url);
      if (options.fetchFailure) throw new Error("Network unavailable");
      return {
        ok: options.ok !== false,
        async json() {
          if (options.invalidJson) throw new Error("Invalid JSON");
          return data;
        },
      };
    },
    editor,
  };
  if (options.hosted) {
    context.Algo2LeanBackend = { hosted: true, request: context.fetch };
    context.fetch = async () => { throw new Error("Hosted publication must use the browser backend"); };
  }
  vm.runInNewContext(script, context);
  await new Promise((resolve) => setImmediate(resolve));
  return { byId, requests, copied, editor };
}

test("publication details keep creator, contributor and citation credit distinct", async () => {
  const { byId, requests } = await surface();
  assert.deepEqual(requests, ["/api/publication"]);
  assert.equal(byId("project-version").textContent, "0.1.0");
  assert.equal(byId("project-authors").textContent, "Created by Ada Example.");
  assert.equal(byId("project-authors").hidden, false);
  assert.equal(byId("project-contributors").textContent, "Contributors: Grace Sample.");
  assert.equal(byId("project-contributors").hidden, false);
  assert.equal(byId("project-authors").children[1].href, "https://example.com/ada");
  assert.equal(byId("project-contributors").children[1].href, "https://example.com/grace");
  assert.equal(byId("project-authors").children[1].rel, "noopener noreferrer");
  assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  assert.equal(byId("citation-bibtex").textContent, CONFIGURED.bibtex);
  assert.equal(byId("bibtex-details").hidden, false);
  assert.equal(byId("copy-citation").disabled, false);
  assert.match(byId("citation-version-note").textContent, /Cite this version/);
});

test("citation coauthors are never inferred to be creators or contributors", async () => {
  const { creators, contributors, ...citationOnly } = CONFIGURED;
  const { byId } = await surface(citationOnly);
  assert.equal(byId("project-authors").hidden, true);
  assert.equal(byId("project-contributors").hidden, true);
  assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  assert.equal(byId("copy-citation").disabled, false);
});

test("creator and contributor credit does not require a software citation", async () => {
  const { byId } = await surface({ ...CONFIGURED, authors: [], citation: null, bibtex: null, citation_url: null });
  assert.equal(byId("project-authors").textContent, "Created by Ada Example.");
  assert.equal(byId("project-contributors").textContent, "Contributors: Grace Sample.");
  assert.equal(byId("copy-citation").disabled, true);
});

test("citation and BibTeX copy actions preserve exact text and announce success", async () => {
  const { byId, copied } = await surface();
  await byId("copy-citation").click();
  assert.deepEqual(copied, [CONFIGURED.citation]);
  assert.equal(byId("citation-status").textContent, "Citation copied.");
  await byId("copy-bibtex").click();
  assert.deepEqual(copied, [CONFIGURED.citation, CONFIGURED.bibtex]);
  assert.equal(byId("citation-status").textContent, "BibTeX copied.");
});

test("only configured publication destinations and the local citation download are shown", async () => {
  const { byId } = await surface();
  assert.equal(byId("github-link").href, CONFIGURED.repository_url);
  assert.equal(byId("release-doi").href, "https://doi.org/10.1234/example-release");
  assert.equal(byId("download-citation").href, "/CITATION.cff");
  for (const id of ["github-link", "release-doi", "download-citation"]) {
    assert.equal(byId(id).hidden, false);
  }
});

test("unconfigured authors and destinations do not invent a citation or public links", async () => {
  const { byId, copied } = await surface({
    version: "0.1.0-dev", status: "development", authors: [],
    repository_url: null, doi: null, citation: null, bibtex: null, citation_url: null,
  });
  assert.equal(byId("project-version").textContent, "0.1.0-dev · Development build");
  assert.equal(byId("copy-citation").disabled, true);
  assert.equal(byId("copy-citation").listeners.size, 0);
  assert.match(byId("citation-text").textContent, /available with the public release/);
  assert.match(byId("citation-version-note").textContent, /development build/);
  for (const id of ["project-authors", "project-contributors", "github-link", "release-doi", "download-citation", "bibtex-details"]) {
    assert.equal(byId(id).hidden, true);
  }
  await byId("copy-citation").click();
  assert.deepEqual(copied, []);
});

test("a readable citation can exist before a DOI, repository or BibTeX is available", async () => {
  const { byId } = await surface({ ...CONFIGURED, doi: null, repository_url: null,
    bibtex: null, citation_url: null });
  assert.equal(byId("copy-citation").disabled, false);
  assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  for (const id of ["github-link", "release-doi", "download-citation", "bibtex-details"]) {
    assert.equal(byId(id).hidden, true);
  }
});

test("network and response failures leave the editor usable with honest fallback text", async () => {
  for (const options of [{ fetchFailure: true }, { ok: false }, { invalidJson: true }]) {
    const { byId, editor } = await surface(CONFIGURED, options);
    assert.match(byId("citation-text").textContent, /could not be loaded/);
    assert.equal(byId("copy-citation").disabled, true);
    assert.equal(byId("github-link").hidden, true);
    assert.deepEqual(editor, { source: "def algorithm() -> Int:\n    return 1\n", canCompile: true });
  }
});

test("null or malformed publication metadata degrades to the same fallback", async () => {
  for (const data of [null, {}, { version: 1, authors: [] }, { version: "0.1", authors: null }]) {
    const { byId } = await surface(data);
    assert.match(byId("citation-text").textContent, /could not be loaded/);
    assert.equal(byId("copy-citation").disabled, true);
  }
});

test("clipboard failure explains manual copying without losing citation text", async () => {
  const { byId, copied } = await surface(CONFIGURED, { clipboardFailure: true });
  await byId("copy-citation").click();
  assert.match(byId("citation-status").textContent, /Select and copy the citation text above/);
  assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  await byId("copy-bibtex").click();
  assert.match(byId("citation-status").textContent, /Select and copy the bibtex text above/);
  assert.equal(byId("citation-bibtex").textContent, CONFIGURED.bibtex);
  assert.deepEqual(copied, []);
});

test("non-HTTPS, credentialed and malformed external destinations stay hidden", async () => {
  for (const repository_url of ["javascript:alert(1)", "data:text/html,test", "http://example.org",
    "https://user:password@example.org", "//example.org/project", "/project", "not a URL"]) {
    const { byId } = await surface({ ...CONFIGURED, repository_url,
      citation_url: "https://example.org/untrusted.cff" });
    assert.equal(byId("github-link").hidden, true, repository_url);
    assert.equal(byId("github-link").href, undefined, repository_url);
    assert.equal(byId("download-citation").hidden, true);
    assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  }
});

test("names and citation contents are rendered as literal text, never HTML", async () => {
  const malicious = "<img src=x onerror=run()>";
  const { byId } = await surface({ ...CONFIGURED, version: malicious,
    authors: [{ given_names: malicious, family_names: "<script>run()</script>" }],
    creators: [{ given_names: malicious, family_names: "<script>run()</script>" }],
    contributors: [{ given_names: malicious, family_names: "<script>run()</script>" }],
    citation: malicious, bibtex: malicious });
  assert.equal(byId("project-version").textContent, malicious);
  assert.equal(byId("project-authors").textContent, `Created by ${malicious} <script>run()</script>.`);
  assert.equal(byId("project-contributors").textContent, `Contributors: ${malicious} <script>run()</script>.`);
  assert.equal(byId("citation-text").textContent, malicious);
  assert.equal(byId("citation-bibtex").textContent, malicious);
});

test("pages without the citation panel do not request metadata", async () => {
  const { requests } = await surface(CONFIGURED, { noPanel: true });
  assert.deepEqual(requests, []);
});


test("hosted citation uses browser metadata and a release-relative download", async () => {
  const { byId, requests } = await surface(CONFIGURED, { hosted: true });
  assert.deepEqual(requests, ["/api/publication"]);
  assert.equal(byId("download-citation").href, "CITATION.cff");
  assert.equal(byId("copy-citation").disabled, false);
});
