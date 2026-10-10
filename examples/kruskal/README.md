# Kruskal

This project computes a minimum spanning forest of a finite undirected weighted
graph. Its four source files show how a graph algorithm reuses independently
verified sorting and disjoint-set operations.

In the local editor, choose **Examples → Project folders → Kruskal**. The
project opens [kruskal.algo](kruskal.algo); use **Project file** to inspect the
imported modules and their companion proofs. To open it from disk, select
**Open project → examples/kruskal**. This folder is the source import root.

The complete [analysis](analysis/kruskal.lean) proves termination, minimum
spanning forest correctness, and a total operation bound for the compiled
`kruskal` entry point. It composes the checked sorting, union-find, and graph
proofs without assumptions about unverified data-structure operations.

## Read the source

| Source | Role | Proof |
| --- | --- | --- |
| [kruskal.algo](kruskal.algo) | Sort edge identifiers, construct disjoint sets, and select edges that join distinct components. | [Correctness and running time](analysis/kruskal.lean) |
| [union_find.algo](union_find.algo) | A reusable class with union by rank and full path compression. | [Method contracts](analysis/union_find.lean), [constructor](analysis/union_find_init.lean) |
| [sort_indices.algo](sort_indices.algo) | Return a permutation of identifiers ordered by their integer keys. | [Correctness and running time](analysis/sort_indices.lean) |
| [indexed_heap.algo](indexed_heap.algo) | The binary min-heap used by the sorter. | [Heap contracts](analysis/indexed_heap.lean) |

Start with `kruskal.algo` to see the composition, then read `union_find.algo`.
Its `find` method recursively reaches a root and redirects every visited parent
pointer to that root on return. Its `union` method compares the two root ranks,
attaches the lower-ranked root, and increments the winner's rank only on a tie.
The data structure has no dependency on graphs, weights, or Kruskal.

The entry point is:

```python
kruskal(size, sources, targets, weights, count)
```

Vertices are `0, ..., size - 1`; edge identifiers are `0, ..., count - 1`.
The sequences give each edge's two endpoints and weight. Sizes and counts must
be nonnegative, and every endpoint in the input prefix must be in range.
Weights are arbitrary integers. Parallel edges keep distinct identifiers,
self-loops are skipped, and negative weights are allowed. Disconnected inputs
produce a forest spanning each component; nonempty connected inputs produce a tree.

The result is a fresh sequence of flags: `chosen[edge]` is `1` for a selected
edge and `0` otherwise. Entries outside the input edge prefix are `0`.
The input arrays are read without mutation. Equal-weight edges can be chosen
in any order; the sorter does not promise stable tie order.

For example, a triangle with edges `(0, 1, 4)`, `(1, 2, -2)`, and `(0, 2, 1)`
selects the last two edge identifiers and has total weight `-1`. An isolated
vertex contributes no edge. The empty graph returns an all-zero sequence.

## Follow the proofs

The proof layers retain their own contracts, so a caller can reuse a verified
operation without reopening its transitions.

1. [Union-find mathematics](../../Algo2LeanLib/UnionFind.lean) describes parent
   forests, representatives, ranks, and component masses. It proves that rank
   linking joins precisely two components, path compression preserves the
   partition, and a find follows at most `log₂ size` parent links. The separate
   [amortized library](../../Algo2LeanLib/UnionFindAmortized.lean) defines the
   Ackermann-level potential and proves inverse-Ackermann bounds for arbitrary
   mixed sequences of finds and unions. It has no dependency on graph algorithms.
2. [Compiled union-find contracts](analysis/union_find.lean) connect that model
   to the actual mutable arrays and recursive source execution.
   `UnionFindAnalysis.find_amortized` preserves the partition and ranks while
   compressing the visited path. `UnionFindAnalysis.union_amortized` specifies
   exactly which formerly separate components become connected, its Boolean
   result, the storage it preserves, and its amortized cost from actual initial
   counters. Both the postcondition and the potential refer to the same returned
   model and heap. The [constructor theorem](analysis/union_find_init.lean),
   `UnionFindAnalysis.constructor_contract`, establishes singleton components
   with two fresh arrays and a fresh object.
3. [The sorter](analysis/sort_indices.lean) reuses the indexed heap contracts.
   `SortIndicesAnalysis.call` supplies a terminating call, an exact permutation,
   nondecreasing keys, preserved caller storage, and a cost budget.
   `SortIndicesAnalysis.correct` and `SortIndicesAnalysis.running_time` are its
   main results for every completed execution.
4. [The graph proof](../../Algo2LeanLib/KruskalMath.lean) establishes
   `Algo2Lean.Kruskal.Scan.minimum_spanning_forest` by an exchange argument.
   It compares the selected forest's total weight with every spanning forest,
   including for negative weights.
   The input adapter's [KruskalInput.SortedEdges.minimum](analysis/kruskal_input.lean)
   transfers that conclusion to the original edge arrays.
5. [KruskalAnalysis.scan_contract](analysis/kruskal_scan.lean) proves termination
   and the exact acceptance rule for the compiled recursive edge scan. It
   reuses `UnionFindAnalysis.union_summary_amortized` and preserves storage outside
   the private parent, rank, and chosen arrays. It sums the imported potential
   inequalities over the actual calls; it does not inspect union-find transitions
   or reprove the data structure's amortized argument.

The [final analysis](analysis/kruskal.lean) combines these layers. Its public
results require only nonnegative vertex and edge counts and in-range endpoints:

| Theorem in `KruskalAnalysis` | Guarantee |
| --- | --- |
| [`terminates`](analysis/kruskal.lean) | Every well-formed input has a completed execution and a cost record. |
| [`correct`](analysis/kruskal.lean) | Every returned flag sequence selects a minimum spanning forest of the original input graph. |
| [`running_time`](analysis/kruskal.lean) | Every completed execution satisfies the total bound below. |
| [`connected_correct`](analysis/kruskal.lean) | If the graph is also nonempty and connected, the selection is a minimum spanning tree. |

`call_contract` is the primary reusable result. It gives a generated
`kruskal.Call`, minimum-spanning-forest correctness, output flags, a fresh valid
result reference, preservation of every old caller location, exact clock
increments, and the runtime bound on those increments. It permits arbitrary
starting counters and aliasing among the three input arrays. `verified` and the
ordinary output results are derived views of the same call proof. The mathematical libraries use Lean and Std and
import no generated algorithm definitions.

## Count the work

`KruskalAnalysis.runtime` adds all eight explicit clocks with unit weight:
`sort_steps`, `heap_comparisons`, `heap_swaps`, `uf_init`, `uf_find`,
`uf_compress`, `uf_union`, and `kruskal`. This includes imported method calls.
The model treats integer arithmetic and sequence access as unit-cost operations;
it does not measure elapsed time or integer bit complexity. Let `n` be the
vertex count and `m` the edge count.

| Checked component | Bound |
| --- | --- |
| Union-find construction | Exactly `n + 1` on `uf_init`; initial potential is zero. |
| One find | Actual work + `2Φ(after)` ≤ `2Φ(before) + 2α(n) + 3`. |
| One union | Actual work + `2Φ(after)` ≤ `2Φ(before) + 6α(n) + 7`. |
| Sort `m` edge identifiers | At most `2m(3 log₂(m + 1) + 2)` across `sort_steps`, `heap_comparisons`, and `heap_swaps`. |
| Scan `m` edges | Actual work + `2Φ(after)` ≤ `2Φ(before) + m(6α(n) + 8)`. |

The complete algorithm has the explicit bound

```text
2m(3 log₂(m + 1) + 2) + n + 2 + m(6α(n) + 8).
```

This is `KruskalAnalysis.runtimeBound n m`, giving
**O(n + m log(m + 1) + m α(n))** total recorded work. The sorting term is
unchanged; the disjoint-set part improves from **O(m log n)** to
**O(m α(n))**. The additive `n + 2` includes initialization and the entry tick.
Individual operations may still take logarithmic time. The earlier per-operation
worst-case theorems and `scan_verified` remain available; the new guarantee
bounds their accumulated cost using the same evolving data structure.

The exact convention for `α` is in
[Ackermann.lean](../../Algo2LeanLib/Ackermann.lean):

```text
A₀(r) = r + 1
Aₖ₊₁(r) = Aₖ iterated (r + 1) times, starting at r
α(n) = the least positive k for which Aₖ(1) > n.
```

For example, `A₁(1) = 3`, `A₂(1) = 7`, and `A₃(1) = 2047`.
The inverse is used in theorem statements, not evaluated by the compiled
algorithm. The pure library's `Operations.from_initial` also bounds arbitrary
mixed find/union sequences, independently of Kruskal. The compiled method
contracts connect these mathematical results to actual source ticks.

The potential assigns credits according to each vertex's rank and its parent's
Ackermann level. Compression releases credits for repeated levels along a path;
at most `α(n)` distinct levels remain unpaid. A rank link adds at most `α(n)`
credits. Scaling credits by two covers both the find test and compression tick.
Kruskal only adds one scan tick per edge and cancels successive potentials.

## Check locally

Run these commands from the repository root with the pinned Lean 4 toolchain
from [lean-toolchain](../../lean-toolchain):

```sh
python3 -m algo2lean compile examples/kruskal/kruskal.algo \
  --project examples/kruskal --check --output-dir /tmp/algo2lean-kruskal

python3 -m algo2lean analyze examples/kruskal/kruskal.algo \
  examples/kruskal/analysis/kruskal.lean --project examples/kruskal
```

The final analysis imports and checks its companion proofs automatically.
The local editor's **Check analysis** does the same; **Main results** links to
the correctness and running-time statements.

The [behavioral regressions](../../tests/test_kruskal_algorithms.py) test sorting
with duplicates and negative keys, then compare Kruskal's output with exhaustive
minimum-spanning-forest enumeration on small graphs. Their oracle uses adjacency
traversal and subset enumeration independently of the implementation. These
checks supplement the Lean proofs.

```sh
python3 -m unittest tests.test_kruskal tests.test_kruskal_algorithms
```

Compilation generates Lean propositions describing execution; it does not run
the algorithm. Lean checks the stated theorems against those generated
propositions. The compiler itself has no formal semantics-preservation proof.
