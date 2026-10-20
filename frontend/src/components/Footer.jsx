import { versionLabel } from "../lib/publication.js";

export function Footer({ publication }) {
  const label = publication.status === "ready" ? versionLabel(publication.data) : "Development build";
  return (
    <footer className="flex items-center justify-between gap-5 border-t border-navy-200 mt-[14px] pt-[18px] pb-2 text-muted text-[11px] max-phone:flex-col max-phone:items-start max-phone:gap-1">
      <span>Algo2Lean <span id="project-version" className="ml-2 text-muted">{label}</span></span>
      <span>Python-like algorithms. Lean definitions and proofs.</span>
    </footer>
  );
}
