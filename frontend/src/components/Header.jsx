import { externalUrl } from "../lib/publication.js";
import { cx } from "./classes.js";

const NAV_LINK = "shrink-0 text-navy-100 text-[13px] py-3 no-underline hover:text-white hover:underline hover:underline-offset-4 max-phone:text-xs max-phone:min-h-11 max-phone:inline-flex max-phone:items-center";

export function Header({ publication }) {
  const repository = publication.status === "ready" ? externalUrl(publication.data.repository_url) : null;
  return (
    <header className="min-h-[100px] px-9 py-[22px] flex items-center justify-between gap-6 text-paper bg-navy-900 shadow-[inset_0_-1px_0_rgba(255,255,255,.08)] max-laptop:flex-wrap max-laptop:gap-3 max-desktop:px-6 max-phone:min-h-0 max-phone:flex-col max-phone:items-stretch max-phone:gap-2 max-phone:px-4 max-phone:pt-4 max-phone:pb-1">
      <div className="flex items-center gap-[13px] max-phone:gap-2.5">
        <svg className="w-11 h-11 text-navy-300 max-phone:w-9 max-phone:h-9" viewBox="0 0 40 40" fill="none" aria-hidden="true">
          <path d="M10 10h8v8h12M10 30h8V18M27 14l4 4-4 4" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" />
          <circle cx="10" cy="10" r="3" fill="currentColor" /><circle cx="10" cy="30" r="3" fill="currentColor" />
        </svg>
        <div>
          <h1 className="text-[25px] tracking-[-0.8px] font-[650] leading-[1.2] max-phone:text-[22px]">Algo2Lean</h1>
          <p className="text-[13px] text-navy-200 mt-[5px] max-phone:text-[12px] max-phone:mt-[3px]">Algorithms, expressed as propositions.</p>
        </div>
      </div>
      <nav className="flex items-center gap-x-5 gap-y-2 flex-wrap max-laptop:gap-y-1 max-phone:flex-nowrap max-phone:gap-x-4 max-phone:-mx-4 max-phone:px-4 max-phone:scroll-row" aria-label="Main navigation">
        <a href="#editor" className={NAV_LINK}>Editor</a>
        <a href="#analysis-outline" className={NAV_LINK}>Main results</a>
        <a href="#about" className={NAV_LINK}>About</a>
        <a href="#cite" className={NAV_LINK}>Cite Algo2Lean</a>
        <a id="github-link" className={cx(NAV_LINK, "border border-navy-300/60 px-3 py-[9px] rounded-lg bg-white/5 hover:bg-white/10 hover:no-underline max-phone:py-2")} hidden={!repository}
          href={repository || undefined} rel="noopener noreferrer" target="_blank">Star on GitHub</a>
      </nav>
    </header>
  );
}
