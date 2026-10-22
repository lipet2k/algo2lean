export function Welcome({ hosted }) {
  return (
    <section className="grid grid-cols-[minmax(0,1.4fr)_minmax(0,1fr)] items-start gap-x-12 gap-y-6 pt-1.5 pb-7 max-tablet:grid-cols-[minmax(0,1fr)] max-tablet:gap-[18px] max-tablet:pb-6 max-phone:pt-1 max-phone:pb-5" aria-labelledby="welcome-heading">
      <div>
        <h2 id="welcome-heading" className="text-2xl leading-[1.3] font-semibold tracking-[-0.4px] mb-2.5 bg-linear-to-r from-navy-950 via-navy-700 to-navy-500 bg-clip-text text-transparent max-phone:text-[22px]">From algorithms to Lean proofs.</h2>
        <p className="max-w-[70ch] leading-[1.7] max-phone:text-sm">Write an algorithm in a typed, Python-like language. Generate its Lean definitions, then prove properties of its outputs, intermediate states, and running time.</p>
      </div>
      <ol className="m-0 pl-[22px] list-decimal text-muted leading-[1.8] max-phone:text-sm max-phone:leading-[1.7]" aria-label="Getting started">
        <li className="pl-1">Choose an example or open a file.</li>
        <li className="pl-1">Compile and explore the Lean interface.</li>
        <li id="proof-workflow-step" className="pl-1">{hosted ? "Explore supplied proofs or write your own Lean analysis." : "Write and check a proof in Lean analysis."}</li>
      </ol>
    </section>
  );
}
