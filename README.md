# Algo2Lean

Algo2Lean compiles Python-like algorithms into Lean 4 definitions for formal
verification. Write algorithms in `.algo`, then prove their correctness,
intermediate-state properties, and explicit operation counts in separate Lean
files. A local browser editor includes examples, generated interface documentation,
and proof checking.

Created by Lunjia Hu, with contributions from Chutong Yang.

## Get started

[Open the browser compiler](https://lunjiah.github.io/algo2lean/) to compile
algorithms without installing anything. Compilation stays in your browser; Lean
proof checking requires the local editor.

To run locally with Python 3.9 or newer, use the repository root:

```sh
python3 -m algo2lean serve --open
```

The editor opens with merge sort and its correctness and running-time analysis.
The **Examples** menu also offers smaller programs, mutable data structures,
and Dijkstra with binary and Fibonacci heaps. No Python packages, browser build
step, or external scripts are needed. Source stays in your browser and the local
server. To choose another port, add `--port 8766`.

Compilation requires only Python. Proof checking requires
[Lean 4 via elan](https://lean-lang.org/install/). The repository pins Lean
**4.33.1** in `lean-toolchain`, matching Prove2Me's default environment; run commands here to use that version. The generated
code and included analyses use Lean/Std and do not require Mathlib.

The [browser hosting guide](docs/HOSTING.md) explains how to build a static
compiler and version archive. Hosted compilation runs entirely in the browser;
Lean proof checking remains local. Building the site does not publish it.

## Write an algorithm and prove its properties

```python
def factorial(n: Int) -> Int:
    if n <= 0:
        return 1
    else:
        return n * factorial(n - 1)
```

Its generated proposition `factorial.Returns input output` describes a valid
returned value. For example, `factorial.Returns 5 120` describes one result,
and `factorial.Returns (-2) 1` describes the nonpositive base case. The compiler
generates the semantics; the separate analysis proves what the algorithm computes.

```sh
python3 -m algo2lean compile examples/factorial.algo -o FactorialGenerated.lean --check
python3 -m algo2lean analyze examples/factorial.algo examples/analysis/factorial.lean
```

The first command writes `FactorialGenerated.lean` with the algorithm definitions
and `FactorialGeneratedPoints.lean` with named locations and variable observations.
`--check` checks both generated files before writing them. The second command
compiles temporary modules and checks the handwritten proof, without modifying
either input. Omit `--check` when only compilation is needed.

Each algorithm imports the shared `Algo2Lean.lean` library. To use an exported
algorithm in this checkout, build the library first:

```sh
lake build
lake env lean FactorialGenerated.lean
```

For another Lean project, copy the shared library and register it as a Lean
library there, or embed it in the generated algorithm file:

```sh
python3 -m algo2lean library -o /path/to/project/Algo2Lean.lean
python3 -m algo2lean compile examples/factorial.algo --standalone -o FactorialGenerated.lean
```

The companion `Points` file always imports the algorithm file. Omit `-o` to
print the algorithm definitions, and use `--points-output` to save the named-line
interface separately.

## Language and proof interface

- **Mathematical data:** arbitrary integers and shared mutable sequences indexed
  by every integer, including negative indices. An integer sequence has infinite
  contents of type `Int → Int`; these are never materialized as an array.
- **Control flow:** conditionals, recursion, mutual recursion across files, `while`, and integer
  `range` loops. Programs may diverge; a diverging execution has no completed
  output, but finite prefixes remain available for analysis.
- **Data structures:** typed classes, constructors, methods, nullable links, and
  sequences of shared objects. Assignment and argument passing preserve aliases;
  `copy(a)` creates a separate sequence with shallow-copied entries.
- **Runtime analysis:** `tick("work", amount)` charges an explicit nonnegative
  amount to a named clock. Multiple clocks compose through calls. They represent
  an author-chosen cost model, not wall-clock time.
- **Reusable proofs:** Python-style imports preserve module identities and permit
  reuse of correctness, mutation, termination, and cost contracts. Method-only
  interfaces let a generic algorithm work with different implementations.

The main generated interfaces are:

| Interface | Meaning |
| --- | --- |
| `f.Returns input output` | The function completes with this output. |
| `f.ReturnsWithCost input output costs` | The same completed run returns this output and incurs these clock increments. |
| `f.ValidTranscript input trace` | The finite execution history is valid; it may stop before return. |
| `f.Run heap inputs finalHeap output` | A completed run with explicit references and mutation effects. |
| `f.Call heap inputs finalHeap output` | A reusable completed call, valid under any caller stack. |
| `f.At.label`, `f.Local.x`, `f.Element.a` | A named location and local observations of one configuration. |

Output interfaces load ordinary integer-sequence inputs automatically. Object
and typed non-integer sequence inputs carry their heap so sharing is expressible.
The [interface guide](docs/LEAN_INTERFACE.md) explains the precise argument types.

Place `# @name` immediately above a statement to name the state **before** it
executes. Named locations do not assert reachability. Local transition facts can
be proved independently and reused in whole-execution arguments. Adding,
removing, renaming, or moving labels leaves the general algorithm file
byte-for-byte unchanged; only its separate named-line interface changes.

## Use the editor

Write source in **.algo**. The **Lean Interface** panel groups generated
declarations and shows their signatures, meanings, and arguments when selected.
Interface names use the same three colors in this panel, generated Lean,
analysis code, and theorem previews: blue for propositions, purple for theorems,
and green for values and types. Text labels explain the colors. The collapsed
**Advanced · local execution** group exposes `Step` and configuration tools for
local proofs; ordinary contracts use the source function's `Call` or `Returns`.
The algorithm definitions and named-line interface have separate export controls.
**Check both files** checks generated definitions. **Check analysis** checks the
separate handwritten Lean proof against the current algorithm.

**Main results** previews the exact **Correctness** and **Running time**
theorems when available; **Go to proof** opens their declarations. **All theorems**
also lists helper lemmas. To mark a result in your proof, place
`-- Main result: Correctness` or `-- Main result: Running time` before its
declaration or documentation comment. Previews are navigation aids, not proof
checking results.

Drag the lower-right corner of a code box to resize it. Click inside a code box
to scroll it; press **Esc** or click outside to scroll the page. Use **Find** or
**⌘/Ctrl F** in the analysis pane to search a proof.

The **Examples** menu separates single files from **Project folders**. Projects
include reusable algorithms, abstract interfaces, mutual recursion, Dijkstra with both binary and Fibonacci heaps, Kruskal, and Prim with a
Fibonacci heap. Opening a project loads its sources and
proofs together; **Project file** groups its files by folder.

Use **Open project** to open your own folder. Use **New file** to create a
standalone `.algo` file, or to add a file to the currently open project. Project
file names may include subfolders, such as `sorting/helpers.algo`. Existing
source and analysis edits are preserved when creating a file. **Download
project** saves all project sources and proofs together.

Browser drafts recover source and analysis together;
**Browser drafts** lets you recover or discard them, and **Clear all drafts**
removes saved recovery copies. Bundled examples reopen their current version on
reload, while edited copies remain recoverable. Save source and analysis files
for durable copies; browser storage is not a substitute for saving them.

## Guides and checked examples

- [Language reference](docs/LANGUAGE.md) and [generated Lean interface](docs/LEAN_INTERFACE.md).
- [Named locations and stable theorem statements](docs/NAMED_POINTS.md).
- [Classes](docs/CLASSES.md), [typed sequences](docs/COLLECTIONS.md), and [cost counters](docs/COSTS.md).
- [Project imports](docs/MODULES.md) and [reusing an existing analysis](docs/REUSING_ANALYSES.md).
- [Cross-file mutual recursion with reusable correctness and cost proofs](examples/mutual_recursion/README.md).
- [Browser hosting, version archives, and generation verification](docs/HOSTING.md).
- [Examples](examples/README.md) and [their proved guarantees](examples/analysis/README.md).
- [Merge sort followed by binary search](examples/modules/GENERAL_SORT_THEN_SEARCH.md).
- [Generic Dijkstra with two queue implementations](examples/dijkstra/README.md).
- [Prim with a Fibonacci heap: minimum spanning trees and running time](examples/prim/README.md).
- [How the graph examples correspond to CLRS pseudocode](docs/TEXTBOOK_ALGORITHMS.md).
- [CLRS Chapter 4 matrix algorithms](docs/CLRS_CHAPTER_4.md) and [recurrence proofs](docs/RECURRENCES.md).

The examples state their assumptions and cost models explicitly. Merge sort
includes an O(n log n) operation-count bound. The two Dijkstra implementations
reuse graph and shortest-path reasoning, with verified binary-heap and
Fibonacci-heap contracts. The recurrence library covers substitution and
recursion-tree arguments for CLRS §4.3–4.4.

## Citation

Please cite Algo2Lean when it contributes to a paper or formalization and record
the compiler version used. [CITATION.cff](CITATION.cff) contains the software
citation for Lunjia Hu and Chutong Yang. The editor's **Cite Algo2Lean** panel
provides citation text, BibTeX, and the citation file. Generated Lean identifies
the compiler and its version; algorithm and proof authors retain credit for
their own work.

[`publication.json`](publication.json) supplies the citation and role-specific
credit. To refresh and check the citation after editing that metadata:

```sh
python3 -m algo2lean.publication --write-citation
python3 -m algo2lean.publication --check-citation
```

## License

Algo2Lean is available under the [Apache License 2.0](LICENSE). The bundled browser
runtime retains its [third-party licenses and notices](THIRD_PARTY_NOTICES.md).

## Development and validation

```sh
python3 -m unittest discover -v
```

Tests cover parsing, diagnostics, compilation, project imports, the local server,
and semantic proofs. Lean checks skip with an explanation if Lean is absent;
otherwise they use the pinned toolchain. Node.js 18 or newer enables the editor
regression tests without npm dependencies. Run them separately with
`node --test tests/test_*.js`.

GitHub runs compiler and editor tests on every change. For UI-only updates, it
can reuse a successful full Lean check of an ancestor on `main` when every
subsequent file change is on the UI/documentation allowlist. The workflow summary
records that baseline. Changes to algorithms, proofs, compiler code, Python tests,
toolchain, workflows, or other unlisted files require the full Lean suite; missing
history or unavailable verification also selects the full suite.

Full checks reuse compiled shared-library and project modules from successful
`main` runs. The cache is scoped to the runner platform, Lean toolchain, compiler,
and checking/test code; each module also has a source-and-dependency identity.
Pull requests can read these caches but do not publish them. Manual **Check** runs
and compiler releases run the full suite without restoring caches. Select
**Actions → Check → Run workflow** for a clean verification.

The compiler is in `algo2lean/`, the browser editor in `editor/`, shared Lean
libraries in `Algo2Lean.lean` and `Algo2LeanLib/`, and proofs alongside the examples
and under `proofs/`. Tests are in `tests/`.

The Python compiler has not been formally proved correct. Lean checks the emitted
mathematical definitions and the stated theorems about them. Compiling or checking
definitions alone does not establish an algorithm's intended correctness or
termination. Unsupported Python syntax is rejected rather than silently translated.
