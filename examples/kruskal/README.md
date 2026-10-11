# Kruskal

Compute a minimum spanning forest of a finite undirected weighted graph, with
separate running-time results for the complete algorithm and the work after
sorting. Both entry points use the same union-find implementation with union by
rank and full path compression.

Choose **Examples → Project folders → Kruskal** in the editor. The project opens
[kruskal.algo](kruskal.algo); **Project file** opens its imported modules and their
companion proofs. The complete analysis highlights **Correctness**,
**Running time (total)**, and **Running time (after sorting)**. To open the project
from disk, choose **Open project → examples/kruskal**.

The examples and proofs compile with Algo2Lean **v0.1.4**. The compiler version
and semantics are unchanged.

## Two entry points

```python
kruskal(size, sources, targets, weights, count)
kruskal_sorted(size, sources, targets, weights, count, order)
```

`kruskal` sorts the edge identifiers by weight, then calls `kruskal_sorted`.
`kruskal_sorted` accepts an already-sorted permutation of those identifiers,
creates singleton vertex sets, and scans the edges. Its implementation contains
no call to the sorter; even if sorting clocks already contain work from another
call, it leaves those clocks unchanged. Its cost includes union-find
initialization and the edge scan.

Vertices are `0, ..., size - 1`; edge identifiers are `0, ..., count - 1`.
`sources`, `targets`, and `weights` hold each edge's endpoints and weight.
Both counts must be nonnegative and every endpoint in the input prefix must be
in range. The sorted entry additionally requires that `order[0:count]` contain
each edge identifier exactly once, in nondecreasing order of `weights`.
Equal-weight identifiers may occur in any order. These are theorem preconditions;
the implementation does not spend time validating the sorted permutation.

Weights are arbitrary mathematical integers. Negative weights, parallel edges,
self-loops, disconnected graphs, and the empty graph are supported. The result
is a fresh flag sequence: `chosen[edge]` is `1` for a selected edge and `0`
otherwise, including outside the input prefix. Inputs are read without mutation.
The chosen edges form a minimum spanning forest of the original graph; for a
nonempty connected graph they form a minimum spanning tree.

For example, edges `(0, 1, 4)`, `(1, 2, -2)`, and `(0, 2, 1)` have sorted order
`[1, 2, 0]`. Either entry point selects identifiers `1` and `2`, of total weight
`-1`. Different valid tie orders can select different forests of the same
minimum weight.

## Read the source

| Source | Role | Proof |
| --- | --- | --- |
| [kruskal.algo](kruskal.algo) | Sort edge identifiers and call the verified sorted-input algorithm. | [Complete algorithm](analysis/kruskal.lean) |
| [kruskal_sorted.algo](kruskal_sorted.algo) | Initialize singleton components and execute the textbook edge loop. | [After sorting](analysis/kruskal_sorted.lean) |
| [union_find.algo](union_find.algo) | Union by rank and full path compression. | [Method contracts](analysis/union_find.lean), [constructor](analysis/union_find_init.lean) |
| [sort_indices.algo](sort_indices.algo) | Return a permutation of identifiers sorted by their integer keys. | [Sorting contract](analysis/sort_indices.lean) |
| [indexed_heap.algo](indexed_heap.algo) | Binary min-heap used by the sorter. | [Heap contracts](analysis/indexed_heap.lean) |

The algorithm follows CLRS fourth edition, Chapter 21, Section 21.2. The sorted
entry keeps the main edge loop explicit: compare representatives, mark an
accepted edge, and call `union`. The two lookups inside `union` remain, matching
the textbook call structure. The constructor batches the MAKE-SET loop, a flag
sequence represents the selected edge set, and an integer-indexed sequence
represents the sorted edge order. Sorting is factored into the complete entry
point so callers with a sorted order can skip it.

`UnionFind.find` recursively reaches a root and redirects every visited parent
pointer to that root on return. `UnionFind.union` attaches the lower-ranked root
to the higher-ranked root, increasing rank only on a tie. This data structure
has no dependency on graphs, weights, or Kruskal.

## The two running-time results

Let `n` be the vertex count and `m` the edge count. The primary theorems use a
universal positive constant, independent of the graph and initial heap:

| Entry point | Running time |
| --- | --- |
| `kruskal` | **O(n + m log(m + 1))**, including sorting and union-find construction. |
| `kruskal_sorted` | **O(n + m α(n))**, including union-find construction and all work after sorting. |

The finite bounds include an additive constant to cover the empty graph.
The simplified total bound absorbs the inverse-Ackermann term into the sorting
and vertex terms; it does not assume that the graph is connected or simple.
The sorted bound excludes the caller's earlier sorting work and counts the
actual clock increments of the sorted call.

The explicit helper bounds remain available for quantitative reuse:

```text
KruskalAnalysis.runtimeBound n m
  = 2m(3 log₂(m + 1) + 2) + n + 2 + m(10α(n) + 14)

KruskalSortedAnalysis.runtimeBound n m
  = n + 2 + m(10α(n) + 14).
```

Both runtime functions sum the same eight clocks with unit weight:
`sort_steps`, `heap_comparisons`, `heap_swaps`, `uf_init`, `uf_find`,
`uf_compress`, `uf_union`, and `kruskal`. A sorted call has zero increments on
the first three clocks. This makes its bound directly composable with a prior
sort or other caller work without resetting any counters.

These clocks count explicitly instrumented source events. They do not measure
wall-clock time, integer bit complexity, or every arithmetic operation, memory
access, and allocation.

The inverse-Ackermann convention is defined in
[Ackermann.lean](../../Algo2LeanLib/Ackermann.lean):

```text
A₀(r) = r + 1
Aₖ₊₁(r) = Aₖ iterated (r + 1) times, starting at r
α(n) = the least positive k for which Aₖ(1) > n.
```

For example, `A₁(1) = 3`, `A₂(1) = 7`, and `A₃(1) = 2047`.
This function occurs in theorem statements; the algorithm does not evaluate it.

## Reuse the proofs

The complete and sorted analyses expose the same style of source-facing
contract. `KruskalAnalysis.call_contract` and
`KruskalSortedAnalysis.call_contract` give a terminating generated `Call`,
minimum-spanning-forest correctness, output flags, fresh valid result storage,
preservation of every old caller location, exact counter increments, and the
explicit runtime bound. Arbitrary initial counters and aliasing among the
read-only input arrays are permitted. The sorted contract additionally requires
the sorted-permutation property and preserves the sorting clocks.

`correctness_and_running_time` is each analysis's principal reusable result
with an unspecified uniform constant. `correct`, `running_time`, and the
ordinary `Returns` and `ReturnsWithCost` views are consequences of the call
contract. A client can invoke these results without inspecting the algorithm's
transitions or rebuilding its data-structure proofs.

The proof layers are:

1. [Union-find mathematics](../../Algo2LeanLib/UnionFind.lean) establishes rank
   linking, representatives, and path compression. The independent
   [amortized analysis](../../Algo2LeanLib/UnionFindAmortized.lean) proves bounds
   for arbitrary mixed sequences of finds and unions.
2. [Union-find method contracts](analysis/union_find.lean) connect those models
   to the mutable `.algo` implementation. `find_amortized` and
   `union_amortized` carry the same object's potential before and after each
   call, including its actual cost increments. The
   [constructor contract](analysis/union_find_init.lean) establishes singleton
   components and zero potential.
3. [Sorting](analysis/sort_indices.lean) reuses the binary heap contracts.
   `SortIndicesAnalysis.call` supplies a sorted permutation, preserved caller
   storage, and a cost budget.
4. [The graph proof](../../Algo2LeanLib/KruskalMath.lean) uses an exchange
   argument to compare Kruskal's selection with every spanning forest, including
   for signed weights. [The input adapter](analysis/kruskal_input.lean) connects
   that mathematical argument to the original endpoint and weight arrays.
5. [The scan proof](analysis/kruskal_scan.lean) composes the union-find contracts
   over the explicit edge loop. It sums their potential inequalities without
   reopening the data structure's transitions or redoing its amortized proof.
6. [The sorted contract](analysis/kruskal_sorted.lean) combines initialization
   and scanning. [The complete contract](analysis/kruskal.lean) reuses the sorted
   contract and the sorting contract.

The independently proved component budgets are:

| Component | Bound |
| --- | --- |
| Union-find construction | Exactly `n + 1` on `uf_init`; initial potential is zero. |
| One find | Actual work + `2Φ(after)` ≤ `2Φ(before) + 2α(n) + 3`. |
| One union | Actual work + `2Φ(after)` ≤ `2Φ(before) + 6α(n) + 7`. |
| Sorting | At most `2m(3 log₂(m + 1) + 2)` on the three sorting clocks. |
| Scanning | Actual work + `2Φ(after)` ≤ `2Φ(before) + m(10α(n) + 14)`. |

Successive potentials cancel over the same evolving data structure. This is an
aggregate guarantee: an individual find or union may still take logarithmic
time. The per-operation worst-case theorems remain available.

## Check locally

From the repository root, using the pinned toolchain in
[lean-toolchain](../../lean-toolchain):

```sh
python3 -m algo2lean analyze examples/kruskal/kruskal.algo \
  examples/kruskal/analysis/kruskal.lean --project examples/kruskal

python3 -m algo2lean analyze examples/kruskal/kruskal_sorted.algo \
  examples/kruskal/analysis/kruskal_sorted.lean --project examples/kruskal

python3 -m unittest tests.test_kruskal tests.test_kruskal_algorithms
```

The analyses import their companion proofs automatically. The hosted editor
provides generated Lean and proof downloads; proof checking can be performed
with a local Lean installation.

[Behavioral regressions](../../tests/test_kruskal_algorithms.py) compare both
entry points with exhaustive minimum-spanning-forest enumeration on small
multigraphs. They cover signed weights, arbitrary tie orders, disconnected and
empty inputs, storage preservation, nonzero starting counters, and zero sorting
increments for the sorted entry. These tests supplement the Lean proofs.

Compilation generates propositions describing execution. Lean checks the
proofs against those definitions; the compiler itself has no formal
semantics-preservation proof.
