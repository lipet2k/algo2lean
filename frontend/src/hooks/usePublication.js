import { useEffect, useState } from "react";
import { validPublication } from "../lib/publication.js";

// Publication details never inspect source, proofs, or drafts. An unavailable
// citation must not interrupt compilation.
export function usePublication(store) {
  const [result, setResult] = useState({ status: "loading", data: null });
  useEffect(() => {
    let cancelled = false;
    (async () => {
      try {
        const response = await store.request("/api/publication");
        if (!response.ok) throw new Error("Publication details unavailable");
        const data = await response.json();
        if (!validPublication(data)) throw new Error("Invalid publication details");
        if (!cancelled) setResult({ status: "ready", data });
      } catch (_) {
        if (!cancelled) setResult({ status: "error", data: null });
      }
    })();
    return () => { cancelled = true; };
  }, [store]);
  return result;
}
