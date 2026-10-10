"use strict";

// Publication details never inspect source, proofs, or drafts. An unavailable
// citation must not interrupt compilation.
(() => {
  const byId = (id) => document.getElementById(id);
  const citation = byId("citation-text");
  if (!citation) return;
  const status = byId("citation-status");

  function peopleCredit(id, label, people) {
    const target = byId(id);
    if (!target || !Array.isArray(people)) return;
    const entries = people.map((person) => ({
      name: [person.given_names, person.family_names].filter(Boolean).join(" "),
      website: externalUrl(person.website),
    })).filter((person) => person.name);
    if (entries.length) {
      target.replaceChildren(document.createTextNode(`${label} `));
      entries.forEach((person, index) => {
        if (index) target.append(document.createTextNode(", "));
        const name = person.website ? document.createElement("a") : document.createTextNode(person.name);
        if (person.website) {
          name.textContent = person.name;
          name.href = person.website;
          name.target = "_blank";
          name.rel = "noopener noreferrer";
        }
        target.append(name);
      });
      target.append(document.createTextNode("."));
      target.hidden = false;
    }
  }

  function externalUrl(address) {
    if (typeof address !== "string") return null;
    try {
      const url = new URL(address);
      if (url.protocol === "https:" && !url.username && !url.password) return url.href;
    } catch (_) { /* Malformed publication URLs stay hidden. */ }
    return null;
  }

  function externalLink(id, address) {
    const url = externalUrl(address);
    if (!url) return;
    const link = byId(id);
    link.href = url;
    link.hidden = false;
  }

  async function copy(text, label) {
    try {
      await navigator.clipboard.writeText(text);
      status.textContent = `${label} copied.`;
    } catch (_) {
      status.textContent = `Could not copy automatically. Select and copy the ${label.toLowerCase()} text above.`;
    }
  }

  async function load() {
    try {
      const response = await (globalThis.Algo2LeanBackend ? globalThis.Algo2LeanBackend.request("/api/publication") : fetch("/api/publication"));
      if (!response.ok) throw new Error("Publication details unavailable");
      const data = await response.json();
      if (typeof data.version !== "string" || !Array.isArray(data.authors)) {
        throw new Error("Invalid publication details");
      }
      byId("project-version").textContent = data.status === "development"
        ? `${data.version} · Development build` : data.version;
      if (data.status !== "development") {
        byId("citation-version-note").textContent = "Cite this version when it is the compiler used for the formalization.";
      }
      peopleCredit("project-authors", "Created by", data.creators);
      peopleCredit("project-contributors", "Contributors:", data.contributors);
      externalLink("github-link", data.repository_url);
      if (data.doi) externalLink("release-doi", `https://doi.org/${data.doi}`);
      if (typeof data.citation === "string" && data.citation.trim()) {
        citation.textContent = data.citation;
        byId("copy-citation").disabled = false;
        byId("copy-citation").addEventListener("click", () => copy(data.citation, "Citation"));
        if (data.citation_url === "/CITATION.cff") {
          byId("download-citation").href = globalThis.Algo2LeanBackend?.hosted ? "CITATION.cff" : data.citation_url;
          byId("download-citation").hidden = false;
        }
        if (typeof data.bibtex === "string" && data.bibtex.trim()) {
          byId("citation-bibtex").textContent = data.bibtex;
          byId("bibtex-details").hidden = false;
          byId("copy-bibtex").addEventListener("click", () => copy(data.bibtex, "BibTeX"));
        }
      } else {
        citation.textContent = "A software citation will be available with the public release.";
      }
    } catch (_) {
      citation.textContent = "Citation details could not be loaded. Use the repository's CITATION.cff file, or reload the page to try again.";
    }
  }
  load();
})();
