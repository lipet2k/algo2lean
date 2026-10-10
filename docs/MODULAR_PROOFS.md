# Reusing a component proof in a larger algorithm

Algo2Lean supports two forms of reuse: importing separately compiled modules,
and embedding a closed component into a larger standalone compilation. New
projects should start with [project imports](MODULES.md) and
[the analysis reuse guide](REUSING_ANALYSES.md). This guide explains the shared
mathematical libraries and the embedding certificates used by the standalone
Fibonacci Dijkstra example.

## Shared mathematical contracts

`Algo2LeanLib.Dijkstra` is independent of the compiler and of any heap layout.
It provides `QueueContents`, `MinimumSelection`, `RelaxScan`, and `SearchRun`.
The complete graph correctness theorem consumes minimum selection, actual
adjacency scans, and exhaustion. The binary-heap compiled proof constructs this
shared search run and derives its final shortest-distance theorem from it.

Both binary and Fibonacci implementations construct this relation from
actual compiled executions. They also reuse the graph-storage library and
`Algo2LeanLib.DijkstraExecution`'s finite loop driver. Each heap supplies its own
proved local data-structure contracts; Fibonacci's `verifiedQueueContracts`
instantiates the complete client without assuming queue correctness or termination.
Its final results establish termination, shortest-distance output equivalence,
and an O(E + V log V) bound on the sum of the ten declared clocks.

`Algo2LeanLib.HeapFrame` adds a small reusable mutation-footprint interface.
`Heap.Modifies before after sequences objects` states that allocation counters,
collections, classes, and storage outside the listed references remain unchanged.
Its composition and primitive-update lemmas let the heap prove isolation once;
the client derives graph and distance-array preservation without examining ring
or tree transitions. Clock preservation remains a separate explicit contract.

## Reusing actual compiled function summaries

`compile_source(..., namespace="ComponentLibrary")` optionally puts both the
general interface and named points in an isolated Lean namespace. This lets two
independently compiled programs coexist in one proof, sharing the same heap model.

`algo2lean.embedding.emit_embedding` accepts a component and a larger program.
It requires every component function and class layout to remain unchanged,
ignoring comments and labels. It emits a separate Lean certificate with:

1. translations for function-local frames and returned values;
2. a proof that every component transition is an actual application transition,
   under any suspended caller stack;
3. `summary_<function>` theorems that transfer existing component summaries.

The reusable theorem in `Algo2LeanLib.Embedding` lifts the checked transition
simulation to transcripts, reachability, and function summaries. It preserves
the entire heap, so shared references, mutations, and every clock effect remain
identical. The result decoder explicitly rejects return constructors that exist
only in the larger program. The Lean kernel checks the certificate against the
actual generated files; the Python structural comparison is an early diagnostic,
not the only justification for proof reuse.

For example, `DijkstraFibonacciAnalysis.Queue.cut_summary` applies
`FibonacciQueueEmbedding.summary_FibonacciHeap_cut` to the already checked
`FibonacciHeapAnalysis.cut_summary`. The caller does not replay the cut proof.
The same applies to initialization, ring removal, root insertion, and linking.
The final Dijkstra client also transfers the complete public update and pop
summaries from `QueueRep.update` and `QueueRep.pop_minimum`; it never replays
cascading-cut or consolidation transitions.

## Checking and caching

`import Algo2LeanExamples.FibonacciHeap` makes the existing standalone example
proof available as a cached library. The checker builds its definitions, points,
and analysis as separate modules. Source/proof contents and transitive shared
dependencies participate in the cache key. Neither an old proof nor an old
generated file is reused after its relevant source changes.

Application-specific certificates live in `examples/analysis/support/`.
Only imported support modules are loaded, and they are checked after the current
request's generated definitions and points, in the same temporary workspace.
They are not accepted against a cached application with potentially different
source. A changed algorithm that invalidates a certificate fails Lean checking.

The editor and `python3 -m algo2lean analyze` use this path automatically.
The Fibonacci certificate is `FibonacciHeapIntoDijkstra.lean`; a regression test
requires it to match the emitter's current output. To regenerate it, call
`emit_embedding` with the standalone Fibonacci source, the Dijkstra Fibonacci
source, source module `Algo2LeanExamples.FibonacciHeapGenerated`, source namespace
`FibonacciHeapLibrary`, target module `DijkstraFibonacciGenerated`, and certificate
namespace `FibonacciQueueEmbedding`.

The certificate is generated translation evidence in a separate file. It does not
enlarge either algorithm's default definitions or named-line interface, and
contains no copied heap analysis. Component proofs are cached; caller-facing
transfer statements remain ordinary heap/input/output summaries.

## Current limits

- This transfers an unchanged, closed component into a larger compilation unit.
  Replacing its algorithm with a different implementation requires a new proof
  of the same logical contract, as with the binary and Fibonacci queues.
- This embedding path expects the component definitions to be included in the
  target compilation. For separate source files, use Python-style `.algo` imports
  and project compilation instead; see the
  [Dijkstra project](../examples/dijkstra/README.md).
- The repository supplies example libraries and local project builds. A package
  registry and dependency-version resolver are not provided.
- Cost theorems measure declared ticks. A separate instruction/machine cost model
  would need its own coverage and arithmetic-cost justification.
