import { test } from "vitest";
import assert from "node:assert/strict";
import { act, cleanup, fireEvent, render } from "@testing-library/react";
import { usePublication } from "../src/hooks/usePublication.js";
import { Header } from "../src/components/Header.jsx";
import { About } from "../src/components/About.jsx";
import { Footer } from "../src/components/Footer.jsx";

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

function Harness({ store, hosted }) {
  const publication = usePublication(store);
  return (
    <>
      <Header publication={publication} />
      <About publication={publication} hosted={hosted} store={store} />
      <Footer publication={publication} />
    </>
  );
}

async function settle() {
  await act(async () => { for (let index = 0; index < 10; index++) await Promise.resolve(); });
}

async function surface(data = CONFIGURED, options = {}) {
  cleanup();
  const requests = [];
  const copied = [];
  const toasts = [];
  const store = {
    showToast: (text, options = {}) => toasts.push({ text, ...options }),
    request: async (url) => {
      requests.push(url);
      if (options.fetchFailure) throw new Error("Network unavailable");
      return { ok: options.ok !== false, json: async () => { if (options.invalidJson) throw new Error("Invalid JSON"); return data; } };
    },
    options: { clipboard: { writeText: async (value) => {
      if (options.clipboardFailure) throw new Error("Clipboard unavailable");
      copied.push(value);
    } } },
  };
  const view = render(<Harness store={store} hosted={Boolean(options.hosted)} />);
  await settle();
  const byId = (id) => view.container.querySelector(`[id="${id}"]`);
  return { byId, requests, copied, toasts, click: async (id) => { fireEvent.click(byId(id)); await settle(); } };
}

test("publication details keep creator, contributor and citation credit distinct", async () => {
  const { byId, requests } = await surface();
  assert.deepEqual(requests, ["/api/publication"]);
  assert.equal(byId("project-version").textContent, "0.1.0");
  assert.equal(byId("project-authors").textContent, "Created by Ada Example.");
  assert.equal(byId("project-authors").hidden, false);
  assert.equal(byId("project-contributors").textContent, "Contributors: Grace Sample.");
  assert.equal(byId("project-contributors").hidden, false);
  assert.equal(byId("project-authors").querySelector("a").getAttribute("href"), "https://example.com/ada");
  assert.equal(byId("project-contributors").querySelector("a").getAttribute("href"), "https://example.com/grace");
  assert.equal(byId("project-authors").querySelector("a").rel, "noopener noreferrer");
  assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  assert.equal(byId("citation-bibtex").textContent, CONFIGURED.bibtex);
  assert.equal(byId("bibtex-details").hidden, false);
  assert.equal(byId("copy-citation").disabled, false);
  assert.equal(byId("citation-version-note").hidden, true, "release builds need no version note");
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
  const { byId, copied, toasts, click } = await surface();
  await click("copy-citation");
  assert.deepEqual(copied, [CONFIGURED.citation]);
  assert.deepEqual(toasts, [{ text: "Citation copied" }]);
  await click("copy-bibtex");
  assert.deepEqual(copied, [CONFIGURED.citation, CONFIGURED.bibtex]);
  assert.deepEqual(toasts.map((toast) => toast.text), ["Citation copied", "BibTeX copied"]);
  assert.equal(byId("copy-citation").getAttribute("aria-label"), "Copy citation");
  assert.equal(byId("copy-bibtex").getAttribute("aria-label"), "Copy BibTeX");
});

test("only configured publication destinations and the local citation download are shown", async () => {
  const { byId } = await surface();
  assert.equal(byId("github-link").getAttribute("href"), CONFIGURED.repository_url);
  assert.equal(byId("release-doi").getAttribute("href"), "https://doi.org/10.1234/example-release");
  assert.equal(byId("download-citation").getAttribute("href"), "/CITATION.cff");
  for (const id of ["github-link", "release-doi", "download-citation"]) {
    assert.equal(byId(id).hidden, false);
  }
});

test("unconfigured authors and destinations do not invent a citation or public links", async () => {
  const { byId, copied, click } = await surface({
    version: "0.1.0-dev", status: "development", authors: [],
    repository_url: null, doi: null, citation: null, bibtex: null, citation_url: null,
  });
  assert.equal(byId("project-version").textContent, "0.1.0-dev · Development build");
  assert.equal(byId("copy-citation").disabled, true);
  assert.match(byId("citation-text").textContent, /available with the public release/);
  assert.match(byId("citation-version-note").textContent, /development build/);
  for (const id of ["project-authors", "project-contributors", "github-link", "release-doi", "download-citation", "bibtex-details"]) {
    assert.equal(byId(id).hidden, true);
  }
  await click("copy-citation");
  assert.deepEqual(copied, []);
});

test("a readable citation can exist before a DOI, repository or BibTeX is available", async () => {
  const { byId } = await surface({ ...CONFIGURED, doi: null, repository_url: null, bibtex: null, citation_url: null });
  assert.equal(byId("copy-citation").disabled, false);
  assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  for (const id of ["github-link", "release-doi", "download-citation", "bibtex-details"]) {
    assert.equal(byId(id).hidden, true);
  }
});

test("network and response failures leave the editor usable with honest fallback text", async () => {
  for (const options of [{ fetchFailure: true }, { ok: false }, { invalidJson: true }]) {
    const { byId } = await surface(CONFIGURED, options);
    assert.match(byId("citation-text").textContent, /could not be loaded/);
    assert.equal(byId("copy-citation").disabled, true);
    assert.equal(byId("github-link").hidden, true);
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
  const { byId, copied, toasts, click } = await surface(CONFIGURED, { clipboardFailure: true });
  await click("copy-citation");
  assert.match(toasts.at(-1).text, /Select and copy the citation text/);
  assert.equal(toasts.at(-1).tone, "error");
  assert.equal(byId("citation-text").textContent, CONFIGURED.citation);
  await click("copy-bibtex");
  assert.match(toasts.at(-1).text, /Select and copy the bibtex text/);
  assert.equal(byId("citation-bibtex").textContent, CONFIGURED.bibtex);
  assert.deepEqual(copied, []);
});

test("non-HTTPS, credentialed and malformed external destinations stay hidden", async () => {
  for (const repository_url of ["javascript:alert(1)", "data:text/html,test", "http://example.org",
    "https://user:password@example.org", "//example.org/project", "/project", "not a URL"]) {
    const { byId } = await surface({ ...CONFIGURED, repository_url, citation_url: "https://example.org/untrusted.cff" });
    assert.equal(byId("github-link").hidden, true, repository_url);
    assert.equal(byId("github-link").hasAttribute("href"), false, repository_url);
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
  assert.equal(document.querySelectorAll("img, script").length, 0);
});

test("hosted citation uses browser metadata and a release-relative download", async () => {
  const { byId, requests } = await surface(CONFIGURED, { hosted: true });
  assert.deepEqual(requests, ["/api/publication"]);
  assert.equal(byId("download-citation").getAttribute("href"), "CITATION.cff");
  assert.equal(byId("copy-citation").disabled, false);
});
