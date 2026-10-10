# Verified Dijkstra analysis

This implementation uses **adjacency lists and an indexed binary min-heap**
with decrease-key. The heap holds at most one entry per unsettled vertex; an
inverse position map locates that entry without a linear search. Graph weights
are nonnegative mathematical integers. A distance of `-1` denotes unreachable.

The general analysis proves termination, shortest-path correctness, and
runtime bounds for the actual compiled algorithm. It applies to arbitrary finite
represented graphs, including directed cycles, self-loops, parallel edges, zero
weights, and unreachable vertices. Correctness uses a valid source; termination
also covers invalid sources. All completed executions have the same output and
clock increments.

The mathematical proof is shared in `Algo2LeanLib/Dijkstra.lean`, which imports
only `Std`. It contains paths, greedy safety, relaxation invariants, the ordinary
`ShortestDistances` specification, and a queue-independent `SearchRun` relation.
A `SearchRun` records minimum selection, an actual adjacency-list relaxation
scan, and exhaustion. Its checked theorems establish correctness and finite
vertex/edge operation bounds. The compiled binary-heap loop constructs this
relation and applies its correctness theorem; it does not repeat the graph proof.

Shared analysis modules are imported on demand and cached with their transitive
dependencies. Ordinary algorithm checks still prepare only `Algo2Lean.lean`.
Changes to an analysis library do not invalidate that smaller runtime cache.

## Checked building blocks

| Example | What its Lean analysis proves |
| --- | --- |
| `weighted_ticks.algo` | Exact triangular work and iteration counts, termination for all integer inputs, and aggregate cost summaries. |
| `relax_edge.algo` | The exact effect and cost of one edge relaxation, preservation of other entries, nonincreasing known distances, and preservation of abstract path-cost witnesses. |
| `select_min.algo` | A first minimum among eligible vertices, or `-1` exactly when none exists, with exactly `n.toNat` scans and unchanged data. |
| `heap_height.algo` | Following binary-heap parents terminates with exactly `log₂(index.toNat + 1)` parent steps; exact output and clock costs hold for every integer input. |
| `indexed_heap.algo` | General compiled sift-up/down, insertion, decrease-key, and minimum-extraction contracts: termination, heap order, exact membership/key effects, client-storage preservation, and logarithmic comparison/swap bounds. |
| `dijkstra.algo` | General compiled termination, output iff shortest distances, and logarithmic indexed-heap runtime bounds for every completed output; verified graph construction and exact edgeless/one-edge examples. |

The linear scan is an educational baseline, **not Dijkstra's priority queue**.
Its proof separates a prefix-minimum invariant, a local iteration, termination,
and the final output/cost specification. This provides a small example of the
minimum contract supplied more efficiently by the verified heap.

The relaxation proof is organized into three cases: unusable source/weight,
unchanged distance, and strict improvement. Its `relax_summary` applies under
an arbitrary caller and describes the final heap exactly. `path_costs_preserved`
lets a graph proof reuse the update without inspecting its transition rules.
It also handles a self-edge and preserves the conventional `-1` sentinel when
the initial distances use it.

## Data structures and representation

The implemented heap uses four fields:

- `vertices[position]` identifies the vertex at a heap position.
- `positions[vertex]` identifies its position, with `-1` for absence.
- `keys[vertex]` stores its current priority.
- `size` bounds the finite active prefix of the mathematical sequences.

Each graph vertex has a linked adjacency list of `Edge` objects, containing a
target, weight, and nullable next reference. This uses the object-sequence
support without requiring sets, dictionaries, or finite-list syntax.

Valid graph inputs require finite acyclic adjacency **chains**, targets in
`[0, size)`, and nonnegative weights. Directed cycles in the graph itself are
allowed. `Graph.add_edge` checks endpoints and weights when building the graph,
but subsequent mutation of public fields can invalidate these conditions.
`GraphRep` expresses these representation requirements explicitly: each
head decodes a finite list of target/weight pairs through `AdjacencyChain`.
`graph_constructor_verified` proves that an actual `Graph(size)` call supplies
this representation, with normalized size `max 0 size`, empty adjacency lists,
zero clock costs, and all previous caller storage preserved. Class membership alone does not validate a graph. The checked
`add_edge_preserves_representation` theorem composes the real edge constructor
and list update, preserves all existing edge fields, and prepends exactly one
mathematical edge. Invalid insertions leave the entire heap unchanged. Both
cases leave all clocks unchanged. `GraphRep.nonnegative_edges` and
`GraphRep.edge_endpoints` connect this representation to the path lemmas.
`GraphFrame` describes the graph observations that must remain unchanged when
queue arrays, distances, or clocks change; `GraphRep.preserved` transports the
representation through such updates. The adjacency helpers expose one edge and
a strictly shorter tail, ready for an edge-loop induction.

`indexed_heap.algo` implements insertion, decrease-key, minimum extraction,
sift-up, and sift-down. The `Indexed` predicate in its analysis states both
directions of the active-prefix/position-map correspondence, including absent
vertices. `swap_indexed_summary` packages its preservation with the exact swap
effect, so later operation proofs can reuse it without re-proving four writes.

The order proof separates two mathematical ideas from the storage layout.
`Ordered priority size` says that each active non-root position has priority at
least its parent's priority. `Ordered.root_minimum` turns those local comparisons
into the global minimum property. `root_minimum_vertex` combines this with the
inverse-position map, so a caller can compare the root's key with any present
vertex without mentioning its array position.

`UpInvariant` describes the intermediate situation during sift-up: only the
moving position's incoming edge may be out of order, and its parent remains
below its children. The second condition matters: just allowing one unordered
edge is too weak to justify a parent/child exchange. `Ordered.decrease` and
`Ordered.append` establish the invariant after lowering a key or appending a
leaf. `UpInvariant.exchange_parent` moves the exception one level up, and
`UpInvariant.finish` yields full heap order when the comparison succeeds or the
root is reached. `swap_priorities` relates this mathematical exchange to the
actual heap mutation. These helper statements keep the proof's outline separate
from transition-constructor details.

`heap_height.algo` isolates the parent traversal before proving its use inside
the data structure. Its `depth_interval` theorem also bounds the index between
successive powers of two. This proves the logarithmic arithmetic fact reused by the complete queue
operation and whole-Dijkstra runtime contracts.

`sift_up_summary` connects parent traversal to the compiled method: for any
valid active position, a completed execution preserves `Layout.Valid`, `Indexed`,
and exactly the same present vertices. It charges each of `"heap_comparisons"`
and `"heap_swaps"` at most `depth index`. Given `UpInvariant`, it also establishes
full heap order. Keys, client-owned arrays, and unrelated clocks are unchanged.
The bound includes early termination at an already ordered parent.

`QueueRep heap queue layout` packages storage validity, nonnegative size, the
inverse-position map, and heap order. `new_heap_rep` proves that construction
supplies it. The three contracts for `push_or_decrease` then describe the
source's cases independently:

| Contract | Resulting queue | Comparisons | Swaps |
| --- | --- | --- | --- |
| `insert_correct` | Adds exactly the absent vertex with its proposed key; size increases by one. | At most `depth oldSize` | At most `depth oldSize` |
| `decrease_correct` | Lowers exactly the selected present vertex's key; size and membership stay fixed. | At most `1 + depth oldPosition` | At most `depth oldPosition` |
| `unchanged_correct` | An equal or larger proposed key preserves all queue data. | Exactly 1 | Exactly 0 |

All three establish a valid ordered queue after the actual compiled call.
Other keys and client arrays stay unchanged; insertion and decrease-key also
explicitly preserve every clock except the two heap counters. Here
`depth i = floor(log2(i + 1))` for a nonnegative position. Their proofs reuse
`append_summary` and `decrease_summary`: those helpers expose the few surrounding
writes and accept the sift-up contract as a premise. They do not re-inspect
sift-up's internal transitions. These are constructive terminating-run contracts. In the Dijkstra compilation
unit, `execution_unique` and `output_with_cost_unique` lift the composed result
to every completed Dijkstra execution.
`QueueRep` itself permits arbitrary integer vertex identifiers; Dijkstra's graph
invariant restricts them to its nonnegative vertex range.

Sift-down has the analogous `DownInvariant`: only edges leaving the moving
position may be unordered. Choosing a minimum child, comparing it with the
moving key, and possibly swapping are separate local proof steps. For an active
position `i` in a heap of size `n`, `sift_down_summary` bounds swaps by
`depth (n - 1) - depth i` and comparisons by twice that amount. It repairs heap
order under `DownInvariant` and preserves membership, keys, and client data.

`pop_correct` composes root/last exchange, size reduction, removal from the
position map, and the proved sift-down call. Its `Extracted` postcondition says
that the returned vertex was present and minimum, exactly that vertex becomes
absent, all other keys remain unchanged, and the shorter queue is ordered.
For an original nonempty size `n`, comparisons are at most `2 * depth (n - 2)`
and swaps at most `depth (n - 2) + 1`. The extra swap is the source's initial
root/last exchange. A singleton incurs its self-swap, zero comparisons, and
returns an empty represented queue. Empty extraction returns `-1` with the
entire heap unchanged and zero cost. `pop_minimum_output` exposes minimum and
cost facts through the ordinary output interface, without a final heap argument.

`OtherStoragePreserved` records that neither sift changes object fields, typed
collections, or allocation counters. Insertion and extraction preserve those
stores except for their stated queue-size update; decrease-key preserves them
entirely. Together with the array frame conditions, these facts let callers keep
graph and distance invariants across queue calls.

The general `scan_adjacency` and `extraction_loop_correct` proofs lift the
path/relaxation invariants through the actual Dijkstra loops and compose these
heap bounds. The standalone example exposes the embedded MinHeap contracts under
`DijkstraAnalysis.Queue`: `Queue.insert_correct`, `Queue.decrease_correct`, and
`Queue.pop_correct`. For an algorithm that imports its queue implementation from
a separate file, use the [Dijkstra project](../examples/dijkstra/README.md).
It provides one generic client proof and independently proved queue backends.
The public output theorems below expose the composed result for every completed
run. Runtime is bounded by `O((V + E) log(V + 1))` in the explicitly instrumented
operation model. The queue-size bound is proved; a separate whole-program memory
complexity theorem is not claimed.

## General-loop invariants

The general proof establishes initialization for any represented graph heap,
with separate distance/settled arrays and a fresh source-only queue. `Initialized`
packages the executed constructor/insertion summaries, exact initial values,
array separation, graph preservation, and unchanged clocks.

`StorageInvariant` keeps allocation and aliasing obligations separate from the
path argument. `QueueMatches` says that the queue contains exactly finite,
unsettled distances and that their keys agree. Its extraction and improvement
lemmas connect the actual queue contracts to those mathematical observations.

`SearchInvariant` states path witnesses, settled optimality, canonical unknown
values, and the frontier bounds. `RelaxationInvariant` distinguishes previously
settled vertices from the selected vertex whose outgoing list is being scanned.
Its helper lemmas cover successful and unsuccessful relaxation, already-settled
targets, and restoration of the complete frontier. `LoopInvariant` and
`ScanInvariant` combine these mathematical and storage facts; initialization,
greedy settlement, completed-scan restoration, and empty-queue correctness are
checked. `scan_adjacency` composes the actual edge branches and returns a
mathematical relaxation summary plus operation bounds. `extraction_loop_correct`
then proves termination, correct distances, and finite clock budgets for the
entire remaining outer loop by induction on the remaining-vertex count.

A duplicate-free list of remaining vertices supplies the termination measure.
`queue_size_bound` derives the queue bound from its inverse position map.
`edgeBudget` sums adjacency-list lengths, counting parallel entries and shared
suffix occurrences separately. Erasing a selected vertex releases exactly its
vertex and adjacency budgets. Clock bounds compose through actual heap-call
summaries, including arbitrary initial counter values.

## Public correctness and runtime interface

The main public statements are near the end of `examples/analysis/dijkstra.lean`:

- `dijkstra_correct_output_exists` constructs a completed output and its clock
  map, proving shortest distances, runtime bounds, and `-1` outside the vertex
  range. Its premises are `GraphRep` and `0 ≤ source < size`.
- `dijkstra_output_with_cost_correct` gives the same guarantees for **any**
  supplied `dijkstra.ReturnsWithCost` proof. It does not require the caller to
  construct a particular transcript.
- `dijkstra_output_iff` states that `dijkstra.Returns` is equivalent to
  `ShortestDistances` for the represented graph and valid source.
- `dijkstra_terminates` proves existence of a completed output for every integer
  source. An invalid source produces all `-1` entries and zero clock increments.
- `output_unique` and `output_with_cost_unique` identify the result independently
  of the transcript used to justify it.

`ShortestDistances edge source output` says that `output v = -1` exactly when
`v` is unreachable, and otherwise `output v` is the attained weight of a shortest
path. It uses only ordinary sequence values. Its `shortest` helper accepts a
path-existence proof, and `source_zero` proves the source entry is zero.
Storage layouts, program counters, and caller stacks are absent from this
mathematical interface. The initial heap and `GraphRep` remain necessary to
connect the graph's shared objects to its mathematical adjacency lists.

`DijkstraRuntimeBound costs V E` exposes these checked bounds, with
`H = floor(log₂(V + 1))`:

| Counter | Upper bound |
| --- | --- |
| `settlements` | `V` |
| `edges` | `E` |
| `improvements` | `E` |
| `heap_comparisons` | `2HV + (H + 1)E` |
| `heap_swaps` | `(H + 1)V + HE` |
| Every other clock | `0` |

Here `E = edgeBudget adjacency (vertexRange size)` counts adjacency entries,
including parallel edges. For `V > 0`, `DijkstraRuntimeBound.total_logarithmic`
proves that the sum of all five counters is at most `5H(V + E)`. These are counts
of the source's explicit ticks; they do not model arbitrary-precision machine
arithmetic, elapsed time, or memory allocation cost. Graph construction is
outside the measured call, and initial clock values may be nonzero.

## Using the Dijkstra example

`dijkstra.algo` includes `MinHeap`, `Edge`, `Graph`, and `dijkstra`. For example,
this function can be added below their definitions:

```python
def example() -> Seq:
    graph = Graph(5)
    graph.add_edge(0, 1, 10)
    graph.add_edge(0, 2, 1)
    graph.add_edge(2, 1, 1)
    graph.add_edge(1, 3, 0)
    return dijkstra(graph, 0)
```

The five distances are `0, 2, 1, 2, -1`; vertex 4 is unreachable. Invalid source
indices return the all-`-1` sequence. All positions outside the vertex interval
also retain `-1`. Zero-weight and parallel edges are allowed.

The source counts five kinds of work: `"settlements"`, adjacency `"edges"`
visited, distance `"improvements"`, `"heap_comparisons"`, and `"heap_swaps"`.
An improvement includes the first discovery of a vertex. Extracting a singleton
performs the source's root/last self-swap and counts one swap. Graph construction
is outside the call being measured. These counters describe the chosen
instrumentation, not every operation of a machine implementation.

`edgeless_correct` is the first complete graph-family proof through the actual
program. For any `0 ≤ source < size`, it constructs a completed execution with
distance zero at the source and `-1` elsewhere, one settlement, one heap swap,
and no other charged work. It also proves the corresponding shortest-path and
unreachability facts. The argument composes constructor, insertion, extraction,
initialization, and loop-exit summaries. This constructive family theorem complements the general
every-output theorem and output/cost uniqueness below.

`single_edge_correct` extends the complete-run proof to a valid graph with one
edge from `source` to a distinct `target`, any nonnegative integer weight, and
any graph size containing both endpoints. The distances are zero at the source,
the edge weight at the target, and `-1` everywhere else. The same execution has
exactly two settlements, two heap swaps, one edge visit, one improvement, zero
heap comparisons, and no other charges. The graph representation is connected
to the mathematical edge relation, so shortestness and unreachability describe
the actual supplied graph. The proof reuses extraction-to-edge-loop,
improvement, and empty-edge-loop continuation lemmas. It covers a successful
relaxation and reinsertion, while the queue holds at most one vertex at a time.
The general loop proof handles queues of arbitrary represented size.

`execution_clocks_monotone` applies to every completed Dijkstra execution,
including arbitrary initial counters. `consecutive_execution_costs` uses this
to justify exact addition of two consecutive calls' cost maps, avoiding
truncation issues from natural-number subtraction. These cost facts are independent of the shortest-path theorem.

The tests compare the actual source algorithm against an independent
Bellman–Ford implementation on random graphs and edge cases. They also check
heap order and inverse positions after mixed queue operations, graph
nonmutation, and finite-instance cost bounds. These execution tests complement the general Lean proofs.

The heap class currently appears identically in the standalone heap and Dijkstra
examples. A test checks their syntax trees for equality. Each `.algo` file is an
independent compilation unit; cross-file Algo2Lean imports remain future work.

## Checking and reading the proofs

Each example has a matching file in `examples/analysis`. For example:

```sh
python3 -m algo2lean analyze examples/relax_edge.algo examples/analysis/relax_edge.lean
python3 -m algo2lean analyze examples/select_min.algo examples/analysis/select_min.lean
```

Theorems and helper statements use mathematical invariants, named locations,
typed observations, and public output/summary relations. Transition constructor
details stay in local proof bodies. Line labels can change independently of the
general algorithm module and its main theorem statements.
