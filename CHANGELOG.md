# Change log

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
