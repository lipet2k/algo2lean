# Prim with a Fibonacci heap

This project implements Prim's minimum spanning tree algorithm from CLRS,
fourth edition, Chapter 21, §21.2. The correctness argument uses the safe-edge
principle of Theorem 21.1 in §21.1. The source keeps the extraction and adjacency
loops explicit and imports the existing Fibonacci heap used by Dijkstra.

Open **Examples → Project folders → Prim** in the
[Algo2Lean editor](https://www.algo2lean.com/). The entry file is
`prim/prim_fibonacci.algo`. When opening the project from disk, select the parent
`examples` directory so that the shared heap and priority-queue imports are
available. The compiler remains version **0.1.4**; this project adds an example
and its analysis without changing the language or compiler.

| Source | Purpose | Analysis |
| --- | --- | --- |
| [prim_fibonacci.algo](prim_fibonacci.algo) | Allocate working sequences and a Fibonacci heap, then run Prim. | [Correctness and running time](../analysis/prim/prim_fibonacci.lean) |
| [prim.algo](prim.algo) | Prim's algorithm using the existing three-operation queue interface. | [Generic call proof](../analysis/prim/prim.lean) |
| [graph.algo](graph.algo) | Undirected adjacency lists with signed integer weights. | [Graph representation](../analysis/prim/graph.lean) |
| [fibonacci_heap.algo](../fibonacci_heap.algo) | Shared Fibonacci heap with stable integer vertex handles. | [Independent queue contract](../analysis/dijkstra/support/fibonacci_queue.lean) |

## Input and output

```python
parent = prim_fibonacci(graph, root)
```

The main theorem assumes a nonempty connected undirected graph and an in-range
root. Vertices are the integers `0, …, V−1`. Edge weights are arbitrary integers;
negative weights, ties, parallel edges, and self-loops are allowed.
`Graph.add_edge(u, v, w)` adds both directed adjacency occurrences and rejects
out-of-range endpoints.

The returned sequence describes a minimum spanning tree: `parent[root] = -1`,
and every other vertex's parent names the adjacent predecessor toward the root.
The selected edges are acyclic, span all declared vertices, and have minimum
total weight among **every** spanning forest of the input. Parallel occurrences
have distinct mathematical identities even when their endpoints and weights
coincide. The parent sequence need not distinguish equally suitable occurrences.

An invalid root returns a fresh sequence filled with `-1`, without constructing
a queue or adding ticks. On a disconnected graph the algorithm explores the
root's component; the whole-graph MST theorem requires connectedness.

The textbook initializes all queue keys to infinity. This implementation queues
the root first and inserts other vertices when an edge first reaches them.
An undiscovered vertex has parent `-1`, so no artificial infinity is needed.
Once discovered, a vertex's key is the lightest known incident edge from the
selected tree. Relaxation compares an edge's own weight, rather than adding a
path distance. This permits negative edge weights.

## Correctness and running time

The main result is
`FibonacciPrimAnalysis.correctness_and_running_time`. Its uniform constant is
existentially quantified, so alternative proofs may establish different
constants for the same statement. With `E` directed adjacency occurrences and
`V` vertices, its runtime scale is

\[
E + V(\lfloor\log_2 V\rfloor + 1).
\]

If the undirected input has `m` edge occurrences, including loops and parallel
edges, the graph constructor stores exactly `E = 2m` adjacency occurrences.
Thus the bound is conventionally **O(m + V log V)**. The additional logarithmic
unit handles a graph containing only the root.

`FibonacciPrimAnalysis.runtimeBound` retains the explicit reusable bound

\[
23(E+1) + \bigl(12(2\lfloor\log_2 V\rfloor+2)+3\bigr)V.
\]

Runtime counts each of the seven Fibonacci-heap event clocks and six Prim
bookkeeping clocks once. These are actual clock increments from the caller's
initial heap. They describe the explicit tick model, not measured wall-clock
time. Graph construction is outside the call being analyzed; allocating a
constant mathematical sequence adds no ticks.

The generic proof bounds insert/decrease operations by `E+1`, extractions by
`V`, emptiness checks by `V+1`, adjacency visits and improvements by `E`, and
settlements by `V`. The independent Fibonacci-heap amortized contract supplies
the data-structure work bound. Prim reuses that contract and its potential;
it does not repeat the heap's structural or amortized analysis.

## Reusing the result

Use `FibonacciPrimAnalysis.summary` when a later algorithm calls Prim. It
exposes a generated `prim_fibonacci.Call`, the minimum spanning tree encoded
by the returned parents, a runtime bound, and preservation of preexisting
storage. The returned sequence is freshly allocated. Callers supply the graph
representation, symmetry, connectedness, and root bounds, without supplying
Fibonacci-heap internals or a successful-execution assumption.

The mathematical proof is separate from the generated transitions:

- [math.lean](../analysis/prim/math.lean) proves the light-edge exchange theorem,
  the frontier-key invariant, and the effect of scanning an adjacency list.
- [invariant.lean](../analysis/prim/invariant.lean) connects those facts to
  `SpanningParents`, which states the complete output property.
- [prim.lean](../analysis/prim/prim.lean) links the actual compiled calls to that
  invariant and counts queue operations.
- [prim_fibonacci.lean](../analysis/prim/prim_fibonacci.lean) instantiates the
  existing Fibonacci-heap contract and provides the public results.

The graph and minimum-spanning-tree definitions are shared with Kruskal's
analysis. Additional graph algorithms can reuse these definitions, the cut
theorem, and the published Fibonacci-heap contract independently.

Online proof checking is unavailable. Check the supplied proofs with the
repository's Lean 4.33.1 toolchain, or use the local editor's proof-check action:

```sh
python3 -m algo2lean analyze examples/prim/prim_fibonacci.algo \
  examples/analysis/prim/prim_fibonacci.lean --project examples

python3 -m unittest tests.test_prim
```

The regression suite also executes the fixed example sources and compares
small signed multigraphs against exhaustive spanning-tree enumeration. Those
finite execution tests complement the general Lean proof.
