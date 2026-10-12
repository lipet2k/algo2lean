# Change log

## 2026-10-11 — Start each refresh with merge sort and collapsed drafts

- Open the current merge-sort source and proof on each refresh, regardless of the previously selected example, file, or project. Keep Browser drafts collapsed until explicitly opened.
- Preserve saved files, paired analyses, and complete projects for explicit recovery. Keep legacy drafts recoverable even when storage quota prevents migration.
- Prevent a late example-catalog response from replacing source, proof, filename, or project work started while the page loads. Leave the compiler version and generated semantics unchanged.

Validation: all 223 tracked JavaScript tests pass, including repeated refreshes, explicit project/legacy recovery, and delayed catalog responses. A browser check confirms refresh returns from Factorial to merge sort with Correctness and Running time visible, collapses the draft panel, and retains all four existing drafts.

## 2026-10-11 — Separate UI, download-package, and full proof checks

- Skip Lean for presentation and documentation updates when their proof and package inputs already passed. Check editor export and website packaging changes with three isolated downloaded-project builds instead of rerunning every algorithm proof.
- Reuse successful package checks independently while retaining a verified full-check ancestor with unchanged proof inputs. Compare cumulative changes so a later UI commit cannot hide an unchecked algorithm or proof change; record both baselines in the workflow summary.
- Preserve full checks for compiler, proofs, toolchain, CI policy, unknown files, and unavailable baseline evidence. Manual and release checks still run the complete suite without caches; website deployment still requires a successful check of current main.
- Keep compiled Lean modules across UI and test edits. Cache identity still includes the platform, toolchain, compiler/checker implementation, and each module's source and dependencies. Preserve compiler version 0.1.4 and archived releases.

Validation: planner and site/archive tests pass, covering three-tier selection, real Git histories, renames, unchecked proof changes, and failed or missing baseline evidence. All three isolated Lean package builds pass in about seven seconds locally; GitHub setup adds overhead. Actionlint accepts the workflows. The CI-policy change itself requires one full check before subsequent updates can reuse it.

## 2026-10-11 — Download complete analysis projects and label code files

- Make Save analysis download a ZIP with the current source and proof, generated definitions and named-line interfaces, transitive proof dependencies, shared Lean libraries, license, pinned toolchain, and Lake setup. Preserve import names and make the selected analysis the default build target.
- Report missing imports and source errors instead of presenting an incomplete bundle as ready to check. Keep failed or superseded downloads from marking newer edits as saved.
- Add an editor-only packaging adapter and local launcher (`python3 -m editor.server`). The current hosted editor uses that adapter with the unchanged archived compiler and runtime; no compiler files, version number, or archived release bytes change.
- Show filenames and extensions on all code panes, including generated module paths and the shared library. Update labels on renames, project/example switches, and generated-module selection.

Validation: all 219 JavaScript editor tests and 13 site-build tests pass. The export suite passes 13 tests, including three isolated Lake builds and local HTTP request protections. All 30 bundled example entries export with resolved imports; an extracted merge-sort package also builds its full analysis with `lake build`. Native and hosted browser downloads succeed, including the imported Dijkstra project; the current-site build preserves the complete archived compiler directories.

## 2026-10-11 — Consistent type colors and compact interface buttons

- Give interface types, locally declared data types, and simple type aliases the same brown as `Int`; keep values green. Recognize imported Dijkstra graph aliases by qualified namespace and keep ordinary syntax types separate from the public interface catalog.
- Use compact buttons for theorems, values, and types while preserving proposition button size and full-size code previews. Restore the regular UI font for main-result labels such as Correctness and Running time.
- Keep compiler version 0.1.4, generated Lean, and archived releases unchanged.

Validation: all 210 JavaScript editor tests pass, including type aliases, namespace scope, proposition/value exclusions, and exact code preservation. Browser checks confirm matching `Int`/`Seq`/`Heap`/`Adjacency` colors, 26 px compact buttons, unchanged 42 px proposition buttons, and full-size monospace previews with ordinary UI fonts for main-result labels.

## 2026-10-11 — Match interface and preview typography to the code editor

- Share the source/analysis editor's 14 px monospace font and 24 px line height with interface buttons, signatures, argument names, main-result buttons, and theorem code previews.
- Preserve editor text/selection metrics, interface colors, and compiler version 0.1.4.

Validation: browser-computed fonts match across both editable code panes, interface buttons/signatures, main-result buttons, and statement previews. Whitespace checks pass; this change affects CSS only.

## 2026-10-11 — Group interface buttons into rows by declaration kind

- Within each interface category, place propositions, theorems, and values/types on separate rows, in the color legend's order. Preserve source order within each kind and omit empty rows.
- Keep specifications expandable within their row and label each row for assistive technology. Leave compiler output and version 0.1.4 unchanged.

Validation: 135 interface/highlighting/editor regressions pass. Browser checks confirm one color per row, vertical separation between kinds, and correct layout with an expanded specification.

## 2026-10-11 — Highlight and document the human Lean interface

- Use one catalog and three accessible semantic colors for interface propositions, theorems, and values/types across generated code, named-line code, analysis, statement previews, and interface specifications. Add text labels and preserve code/selection geometry.
- Discover imported function and object-field interfaces, recognize quoted project namespaces, and expose shared storage tools plus a collapsed advanced execution group. Keep compiler-generated import aliases and numbered implementation details outside the documented interface.
- Retain output/cost conversion helpers and document reusable Call contracts, local At/Local/CallFrom proofs, and the limited scope of lexical highlighting.
- Add regressions for Lean comments, literals, Unicode/quoted identifiers, imported namespaces, declaration kinds, exact source preservation, and source-facing example statements. Keep compiler version 0.1.4 and archived releases unchanged.

Validation: 204 JavaScript regressions and 38 site/server tests pass. Browser checks confirm consistent generated/analysis/preview colors, imported project interfaces, and matching selection/highlight geometry after scrolling. All three colors exceed 6:1 contrast on white. Highlighting the 331 KB Fibonacci analysis takes about 38 ms in a local Node smoke check; this is not a browser rendering benchmark. The affected Lean analyses passed in the preceding commit.

## 2026-10-11 — Keep analysis helper statements source-facing

- Rewrite ten Fibonacci-heap and Kruskal sorting loop helpers using named locations, source-variable observations, configuration heap/stack projections, and CallFrom or Reaches. Keep generated states, slots, and numbered transitions inside proof bodies.
- Replace Strassen's raw Summary clock helper with a reachability lemma over configurations and reuse it at all four call sites.
- Preserve main correctness/runtime statements, source algorithms, generated semantics, conversion helpers, compiler version 0.1.4, and existing releases.

Validation: standalone and imported Fibonacci-heap analyses, keyed sorting, full Kruskal analysis, bundled Strassen analysis, all 12 Chapter 4 modules, and their axiom audit pass Lean. A scan of 2,243 example theorem/helper statements finds no generated State records, numbered slots/frame constructors, or raw Summary Step references.

## 2026-10-10 — Reuse verified Lean checks for UI updates and persist compilation caches

- Keep compiler/editor checks unconditional. Skip the Lean job only when cumulative changes from a successful full `main` check are on an explicit UI/documentation allowlist; verify repository, workflow, ancestry, and the actual Lean version/test steps.
- Default to full Lean checks for unknown files, unavailable baseline evidence, manual runs, and reusable release checks. Preserve the existing deployment requirement for a successful check of the current main commit.
- Restore content-addressed shared-library and project-module caches within a platform/toolchain/compiler/checker/test namespace. Save caches only after successful main-branch checks; manual and release checks remain cold.
- Document the fast path and clean-check option. Keep the compiler version and archived releases unchanged.

Validation: 69 targeted planner, cache, project-checking, archive, and deployment-build tests pass. Real Git histories cover unchecked proof changes followed by UI edits, renames, and nonancestor baselines. Actionlint validates all workflows; a read-only GitHub check confirms the previous UI commit reuses its successful full-check ancestor. The first run of this workflow change still performs full Lean checking and populates the cache.


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
