import { useEffect, useRef, useState } from "react";
import { Button } from "./Button.jsx";
import { feedbackPanelClass } from "./classes.js";
import { useEditorState, useStore } from "./store-context.jsx";

// The archived editor links to the version list two directories up; the
// current-examples editor sits one level down and also exposes its example snapshot.
function useSiteLinks(store, hosted) {
  const [links, setLinks] = useState({ versions: "../../versions.html", current: false, version: null });
  useEffect(() => {
    if (!hosted) return undefined;
    let cancelled = false;
    (async () => {
      try {
        const response = await store.options.fetchSiteConfig();
        if (!response?.ok) return;
        const config = await response.json();
        if (!cancelled && config?.compiler_base) {
          setLinks({ versions: "../versions.html", current: true, version: typeof config.version === "string" ? config.version : null });
        }
      } catch (_) { /* The archived layout is the default. */ }
    })();
    return () => { cancelled = true; };
  }, [store, hosted]);
  return links;
}

export function GenerationTools() {
  const store = useStore();
  const state = useEditorState();
  const filesRef = useRef(null);
  const folderRef = useRef(null);
  const links = useSiteLinks(store, state.hosted);
  const verify = (event) => {
    const files = Array.from(event.target.files || []);
    event.target.value = "";
    store.verifyFiles(files);
  };
  return (
    <>
      <section id="generation-tools" className={feedbackPanelClass} aria-labelledby="generation-heading" hidden={!state.hosted}>
        <h2 id="generation-heading" className="text-[13px] font-[650]">Verify generated files</h2>
        {links.current ? (
          <>
            <p className="mt-2 text-[13px]"><a href={links.versions}>Compiler versions</a> · <a href="example-manifest.json">Example snapshot</a></p>
            <p className="text-muted text-xs">Current examples use the unchanged Algo2Lean {links.version || ""} compiler.</p>
          </>
        ) : <p className="mt-2 text-[13px]"><a href={links.versions}>Earlier compiler versions</a></p>}
        <p className="mt-2 text-[13px] leading-[1.65]">Open the original .algo source or project above, then select the claimed generated .lean files. All generated algorithm, named-line, and linking files must match exactly; shared libraries are also checked when selected. Exclude handwritten proofs. For module projects, choose their generated folder to preserve paths.</p>
        <div className="flex gap-2 flex-wrap my-2.5">
          <Button id="verify-files-button" onClick={() => filesRef.current?.click()}>Verify files</Button>
          <Button id="verify-folder-button" onClick={() => folderRef.current?.click()}>Verify folder</Button>
          <Button id="generation-bundle-button" onClick={() => store.generation("archive")}>Download generation bundle</Button>
          <Button id="generation-manifest-button" onClick={() => store.generation("manifest")}>Download manifest</Button>
        </div>
        <input id="verify-files-picker" ref={filesRef} className="sr-only" type="file" accept=".lean,text/plain" multiple tabIndex={-1} onChange={verify} />
        <input id="verify-folder-picker" ref={folderRef} className="sr-only" type="file" webkitdirectory="" multiple tabIndex={-1} aria-label="Choose generated Lean folder" onChange={verify} />
        <p id="generation-status" className="text-[13px] text-muted mt-2" role="status" aria-live="polite">{state.generationStatus}</p>
        <pre id="generation-details" className="details-output mt-2 text-xs" tabIndex={0} aria-label="Generation comparison details">{state.generationDetails}</pre>
      </section>
      <p id="browser-runtime-status" className="mt-3 text-muted text-xs" role="status" aria-live="polite" hidden={!state.hosted} />
    </>
  );
}
