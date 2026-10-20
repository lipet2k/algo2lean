import { Fragment } from "react";
import { externalUrl, peopleEntries } from "../lib/publication.js";
import { Button, ClipboardIcon, buttonClass } from "./Button.jsx";
import { cx } from "./classes.js";

const PARAGRAPH = "max-w-[70ch] leading-[1.7] mb-[14px] max-phone:text-sm";
const DETAILS_PARAGRAPH = "text-muted text-[13px] mt-1.5 mb-3 max-w-[70ch] leading-[1.7]";

function People({ id, label, people, className }) {
  if (!people.length) return <p id={id} hidden />;
  return (
    <p id={id} className={cx(PARAGRAPH, className)}>
      {label}{" "}
      {people.map((person, index) => (
        <Fragment key={index}>
          {index ? ", " : ""}
          {person.website ? <a href={person.website} target="_blank" rel="noopener noreferrer" className="underline-offset-[3px]">{person.name}</a> : person.name}
        </Fragment>
      ))}.
    </p>
  );
}

export function Citation({ publication, hosted, store }) {
  const data = publication.status === "ready" ? publication.data : null;
  const citation = typeof data?.citation === "string" && data.citation.trim() ? data.citation : null;
  const bibtex = typeof data?.bibtex === "string" && data.bibtex.trim() ? data.bibtex : null;
  const doi = data?.doi ? externalUrl(`https://doi.org/${data.doi}`) : null;
  const downloadHref = citation && data.citation_url === "/CITATION.cff" ? (hosted ? "CITATION.cff" : data.citation_url) : null;
  const text = publication.status === "loading" ? "Loading citation details…"
    : publication.status === "error" ? "Citation details could not be loaded. Use the repository's CITATION.cff file, or reload the page to try again."
    : citation || "A software citation will be available with the public release.";
  const copy = async (value, label) => {
    try {
      await store.options.clipboard.writeText(value);
      store.showToast(`${label} copied`);
    } catch (_) {
      store.showToast(`Could not copy automatically. Select and copy the ${label.toLowerCase()} text instead.`, { tone: "error", duration: 6000 });
    }
  };
  return (
    <section id="cite" className="min-w-0 scroll-mt-5" aria-labelledby="cite-heading">
      <h2 id="cite-heading" className="text-ink text-xl font-semibold mb-[14px]">Cite Algo2Lean</h2>
      <p className={PARAGRAPH}>If Algo2Lean contributes to a paper or formalization, please cite the software and record the compiler version used.</p>
      <div className="relative max-w-[70ch] mb-[14px]">
        <p id="citation-text" className="p-4 pr-14 bg-paper border border-navy-100 border-l-[3px] border-l-navy-500 rounded-lg shadow-panel [overflow-wrap:anywhere] leading-[1.7]">{text}</p>
        <Button id="copy-citation" size="icon" className="absolute top-2 right-2" aria-label="Copy citation" title="Copy citation" disabled={!citation}
          onClick={() => citation && copy(citation, "Citation")}><ClipboardIcon /></Button>
      </div>
      <div className="flex items-center flex-wrap gap-3 my-3">
        <a id="download-citation" className={buttonClass("quiet", "default", "no-underline")} download="CITATION.cff" hidden={!downloadHref} href={downloadHref || undefined}>Download citation</a>
        <a id="release-doi" hidden={!doi} href={doi || undefined} rel="noopener noreferrer" target="_blank" className="underline-offset-[3px]">Archived release</a>
      </div>
      <details id="bibtex-details" hidden={!bibtex}>
        <summary className="text-ink py-2.5 font-[550]">BibTeX</summary>
        <div className="relative max-w-[70ch]">
          <pre id="citation-bibtex" className="whitespace-pre-wrap [overflow-wrap:anywhere] p-4 pr-14 bg-paper border border-navy-100 rounded-lg text-xs leading-[1.7]" tabIndex={0} aria-label="BibTeX citation">{bibtex}</pre>
          <Button id="copy-bibtex" size="icon" className="absolute top-2 right-2" aria-label="Copy BibTeX" title="Copy BibTeX"
            onClick={() => bibtex && copy(bibtex, "BibTeX")}><ClipboardIcon /></Button>
        </div>
      </details>
      <p id="citation-version-note" className="text-muted text-xs mt-3 mb-[14px]" hidden={!(data && data.status === "development")}>This is a development build. For published work, use the citation for the exact release.</p>
      <p className="text-muted text-xs mt-3">Algorithm and proof authors retain credit for their work.</p>
    </section>
  );
}

export function About({ publication, hosted, store }) {
  const data = publication.status === "ready" ? publication.data : null;
  return (
    <section id="about" className="grid grid-cols-2 gap-x-[60px] gap-y-8 pt-8 pb-5 mt-5 border-t border-border scroll-mt-5 max-tablet:grid-cols-1 max-tablet:gap-7" aria-labelledby="about-heading">
      <div>
        <h2 id="about-heading" className="text-ink text-xl font-semibold mb-[14px]">About Algo2Lean</h2>
        <p className={PARAGRAPH}>Algo2Lean connects readable algorithm code with Lean's proof language. It supports mathematical integers, shared mutable sequences, classes, imports, and explicit cost counters.</p>
        <p className={PARAGRAPH}>Compilation defines the algorithm's behavior. Correctness and running-time guarantees come from the Lean proofs written against those definitions.</p>
        <People id="project-authors" label="Created by" people={peopleEntries(data?.creators)} className="font-semibold" />
        <People id="project-contributors" label="Contributors:" people={peopleEntries(data?.contributors)} />
        <details>
          <summary className="text-ink py-2.5 font-[550]">How compilation and checking work</summary>
          <p id="compilation-description" className={DETAILS_PARAGRAPH}>{hosted
            ? "This website runs the Python compiler in your browser. Your source and proof files stay on your device; compilation does not send them to a server. The first visit downloads the pinned compiler and Python runtime. Lean proof checking requires a local Lean installation. Save or download files for a durable copy."
            : "This editor uses a Python compiler on this computer. Source is sent to that local server when compiling or checking; Lean checking requires a local Lean installation. Draft recovery uses browser storage. Save or download files for a durable copy."}</p>
          <p className={DETAILS_PARAGRAPH}>The language is a defined Python-like subset. Lean checks the generated definitions and submitted proofs; this does not itself prove that the compiler implements the intended language semantics.</p>
        </details>
      </div>
      <Citation publication={publication} hosted={hosted} store={store} />
    </section>
  );
}
