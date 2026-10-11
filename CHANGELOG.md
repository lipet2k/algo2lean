# Change log

## 2026-10-10 — Open the first main result by default

- Display the first marked main result's description and exact Lean statement as soon as an analysis loads, using the same preview as clicking its button.
- Preserve a selected theorem across analysis edits; fall back to the first main result if that theorem disappears. Opening a preview does not scroll or jump into the proof.
- Keep the compiler version and archived releases unchanged. Leave code-box resizing unchanged after confirming that the existing handles work.

Validation: all 30 proof-outline checks pass, including default selection, statement updates, removal fallback, and unmarked analyses. Browser verification confirms that merge sort's correctness statement is visible without clicking a result.

## 2026-10-10 — State the post-sorting Kruskal bound in the result description

- Replace implementation-oriented preview text with the mathematical guarantee `T ≤ C · (V + E · α(V) + 1)`, explaining the input-independent constant and inverse Ackermann function.
- State the sorted-order precondition, minimum-spanning-forest result, instrumented cost model, inclusion of initialization and scanning, and coverage of empty/disconnected graphs in both post-sorting theorem descriptions.
- Preserve every theorem statement and proof, the compiler version, and archived releases.

Validation: all 29 proof-outline checks pass; the editor parser exposes the mathematical description and all theorem statements remain unchanged. This update changes example documentation only.

## 2026-10-10 — Separate Kruskal sorting and edge-scan runtimes

- Add `kruskal_sorted`, which accepts an already-sorted permutation of edge identifiers, initializes singleton components, and runs the textbook edge scan. The full `kruskal` sorts once and calls that entry point.
- Reuse the existing union-by-rank and full-path-compression contracts. Prove minimum-spanning-forest correctness, termination, output freshness, caller-storage preservation, and counter increments for both entry points; prove sorting clocks remain unchanged in the sorted call.
- Expose uniform main bounds `O(V + E log(E+1) + 1)` overall and `O(V + E alpha(V) + 1)` after sorting, with explicit finite bounds retained. Prove absorption of the inverse-Ackermann term without assuming connectedness or a relationship between V and E.
- Show Correctness, Running time (total), and Running time (after sorting) in the example. Preserve compiler v0.1.4 and all shared data-structure implementations.

Validation: 16 Kruskal behavior/Lean regressions, eight catalog checks, the targeted HTTP project regression, and 29 proof-outline checks pass. Independent exhaustive forest comparisons cover signed weights, parallel edges, loops, disconnected and empty graphs, and alternative tie orders. Repeated-call proofs compose both contracts from arbitrary counters. The main theorems and arithmetic bound use only standard Lean axioms.

## 2026-10-10 — Include Prim in the import-catalog regression

- Update the existing HTTP catalog regression to expect Prim in both the project identifiers and folder list.
- Preserve the algorithm sources, Lean proofs, and compiler release identity.

Validation: the focused HTTP project-catalog regression passes. GitHub's initial 531-test run identified this single outdated expectation.

## Example update — 2026-10-10

- Add Prim minimum spanning trees using the existing Fibonacci heap, with signed integer weights and a reusable correctness and running-time contract.
- Reuse the separately verified queue operations and amortized costs. The main theorem quantifies a uniform constant for O(E + V log V) measured work, preserves caller storage, and returns a fresh parent sequence.
- Include the Prim sources, proofs and guide in the website's project browser. Keep compiler version 0.1.4 and all archived releases unchanged; identify current example snapshots separately.

Validation: all eight Prim execution and Lean tests pass, including comparison with exhaustive minimum-spanning-tree search on small graphs and standard-axiom audits. Fifteen catalog/site tests and four browser-routing tests pass, including project proof imports, immutable archive preservation, and unchanged compiler/export routing.

## 0.1.4 — 2026-10-10

- Present Dijkstra's minimum-extraction and adjacency scans as explicit loops, and put Kruskal's initialization, sorted-edge loop, representative comparison and union directly in its main routine.
- Reuse the existing heap, sorting and union-find analyses. Dijkstra's public correctness and runtime contracts remain unchanged; Kruskal's explicit bound includes the additional textbook-style representative checks while retaining the inverse-Ackermann growth rate.
- Rename the Dijkstra project folder and import paths to `dijkstra`.
- Add a guide explaining how the source corresponds to CLRS pseudocode, including deliberate representation choices and the named-event cost model.

The revised examples pass their Lean 4.33.1 correctness/runtime proofs and focused regression tests. Earlier numbered releases and their archived compiler sites remain unchanged.

## 0.1.3 — 2026-10-10

- Move the complete Algo2Lean project, shared libraries, examples, and proof-checking tools to Lean 4.33.1.
- Repair proof elaboration for Lean 4.33.1 while preserving theorem statements, including the Chapter 4 matrix proofs, reusable module compositions, and abstract-interface backends.
- Recognize Lean's updated diagnostics for unfinished proofs so the local checkers continue to reject them reliably.
- Add Kruskal minimum-spanning-forest correctness and running-time proofs, with separately verified union by rank and full path compression.
- Prove reusable inverse-Ackermann amortized union-find bounds and compose them with edge sorting in Kruskal.
- Strengthen reusable Call contracts, including Dijkstra, with caller storage preservation, output allocation, and costs measured from arbitrary initial counters.
- Include Kruskal in the project browser and offline native/browser compiler-parity checks, and update the public guides for the new Lean toolchain.

Named operation counters measure the stated algorithm events; they do not measure wall-clock time or every machine instruction. The compiler is tested but is not itself formally verified for semantics preservation.

Validation: all 181 JavaScript tests pass. Offline Pyodide/native generation parity passes for 12 fixtures, including both Dijkstra variants and Kruskal; generation ZIP contents and manifests are also checked. A fresh Lean 4.33.1 site preview builds successfully and preserves all 132 files in the earlier version archives byte-for-byte. The full run and focused reruns cover all 512 Python test cases, with one filesystem-dependent skip; all 26 standalone analyses and the final 98-test regression pass on Lean 4.33.1.

## 0.1.2 — 2026-10-10

- Support mutual recursion across imported source files while preserving reusable public Lean interfaces, mutable state, and tick costs.
- Add a checked cross-file parity example whose caller reuses correctness and exact runtime proofs.
- Group examples and project files by folder; include reusable algorithms, abstract interfaces, mutual recursion, and both Dijkstra variants.
- Add New file for standalone documents and open projects, preserving existing source and proof edits.
- Remove redundant Dijkstra source wrappers and group reusable heap proofs and queue contracts under a support folder.
- Keep the general algorithm definitions unchanged when named-line annotations change.

Validation: 486 Python cases complete successfully (114 skips in the run without Lean); all 181 JavaScript tests and 11 focused Lean integration tests pass. Offline Pyodide/native generation parity passes, including recursive imports, both Dijkstra variants, and downloaded projects.

## CI maintenance — 2026-10-10

- Allow five minutes per example-analysis integration test, including dependency builds, so slower GitHub runners can finish checking the Fibonacci Dijkstra proof. Compiler behavior, proofs, and interactive checker limits are unchanged.

Validation: all nine analysis tests pass, including Lean checks of all 26 example analyses, in 184.6 seconds.

## 0.1.1 — 2026-10-10

- Add a visible notice that proof checking is not currently available on the website. Users can save the supplied proofs and check them with their own Lean installation or editor.
- Clarify the hosted getting-started instructions. Local proof checking remains available.

Validation: 42 focused website/release tests, all 169 JavaScript tests, and a live browser preview pass. Compiler semantics and Lean proofs are unchanged.

## 0.1.0 — 2026-10-09

- Compile typed Python-like algorithms to Lean definitions with shared mutable sequences, classes, imports, named locations, and weighted clocks.
- Reuse correctness and runtime analyses through module interfaces and contracts.
- Explore checked examples from loops and merge sort to Dijkstra, Fibonacci heaps, and matrix multiplication.
- Use the local editor or the hosted browser compiler at https://lunjiah.github.io/algo2lean/, with exact generation comparison, downloadable manifests, and preserved version archives.
- Include source, tests, proof modules, current guides, citation metadata, and third-party runtime notices.

The compiler is tested but not itself formally verified. Browser generation verification does not check Lean proofs; use the local checker with the pinned Lean toolchain.
