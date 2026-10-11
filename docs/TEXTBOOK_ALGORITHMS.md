# Reading the CLRS examples

The examples use the control flow and operations of *Introduction to
Algorithms*, fourth edition, in Algo2Lean's Python-like syntax. Explicit
`tick` statements measure selected operations, and standalone `# @name`
comments mark locations for proofs. Neither replaces an algorithmic operation.
Proof helpers belong in the companion Lean analysis; source code should remain
recognizable without reading that analysis.

The reference is the [fourth-edition book and its author-supplied resources](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/).
These programs are implementations of the algorithms, with the following
explicit representation choices.

## Dijkstra: Chapter 22, §22.3

The [shared routine](../examples/dijkstra/dijkstra.algo) initializes the source
distance, repeatedly extracts a minimum-distance vertex, and relaxes its
outgoing edges. The adjacency scan is a separate helper. The [Fibonacci heap
entry](../examples/dijkstra/dijkstra_fibonacci.algo) creates the mutable
storage and supplies the independently verified queue.

| Textbook concept | Source representation |
| --- | --- |
| Distance estimate | `distance[vertex]`; `-1` represents infinity for nonnegative-weight graphs. |
| Settled set | `settled[vertex]` is `1` after extraction. |
| Adjacency list | Linked `Edge` objects starting at `graph.heads[vertex]`. |
| Extract a minimum | `queue.pop_min()`. |
| Insert or decrease a key | `queue.push_or_decrease(vertex, distance)`. |

Only discovered vertices enter the queue. The textbook's initial queue contains
every vertex, including vertices with infinite estimates; here unreachable
vertices remain absent and retain distance `-1`. The source skips edges whose
target is already settled. It returns distances only, without a predecessor
tree. These choices preserve shortest-distance correctness for the stated
nonnegative-weight inputs, but this is not a literal transcription of the
textbook program.

The indexed Fibonacci heap implements the textbook's root lists, consolidation,
ranked trees, cuts and marking discipline with integer handles and parallel
mutable sequences. Its `push_or_decrease` operation combines insertion and
decrease-key behind the common queue interface. Meld and arbitrary deletion
are outside this example's interface.

## Prim: Chapter 21, §21.2

The [shared Prim routine](../examples/prim/prim.algo) repeatedly extracts the
minimum-key vertex and scans its outgoing adjacency list. For an unselected
neighbor, a lighter incident edge replaces its key and parent. The
[Fibonacci heap entry](../examples/prim/prim_fibonacci.algo) allocates the
parent, key and selected sequences and supplies the same verified queue used
by Dijkstra.

`parent[vertex]` records the chosen tree predecessor; the root retains `-1`.
`key[vertex]` stores an incident edge weight rather than a distance from the
root. Only discovered vertices enter the queue, so no integer infinity sentinel
is needed and negative weights are supported. The textbook initializes every
vertex in the queue, including vertices with infinite keys. On the connected
inputs of the main theorem, both formulations select every vertex.

The [graph builder](../examples/prim/graph.algo) inserts both orientations of
each undirected edge. Parallel edges and self-loops are allowed. The runtime
parameter E counts adjacency entries, so an undirected edge inserted by the
builder contributes two. The proof returns a minimum spanning parent tree and
bounds the sum of the source's named operation counters by O(E + V log V).
It reuses the existing heap's amortized contracts without changing its source
or redoing its analysis. See the [Prim guide](../examples/prim/README.md) for
the exact statement and explicit bound.

## Kruskal: Chapter 21, §21.2

The [entry routine](../examples/kruskal/kruskal.algo) creates empty output and
singleton components, sorts edges by weight, and scans the sorted edges. For
each edge it compares endpoint representatives, selects the edge when they
differ, and joins the components.

| Textbook concept | Source representation |
| --- | --- |
| Edge set and weights | Edge identifiers index the `sources`, `targets` and `weights` sequences. |
| Chosen edge set | `chosen[edge]` is `1` for a selected edge and `0` otherwise. |
| Make one singleton per vertex | `UnionFind(size)` performs the initialization loop. |
| Find a representative | `sets.find(vertex)`, with full path compression. |
| Union components | `sets.union(u, v)`, with union by rank. |
| Sort by edge weight | `sort_indices(weights, count)` returns ordered edge identifiers. |

The union-find implementation follows Chapter 19, §19.3. Equal-rank ties select
one root consistently; the choice of which root wins does not change the
component partition. The sorting operation uses an independently verified
indexed priority queue. It is not the in-place heapsort routine of §6.4.

The result is a minimum spanning forest, so the specification also covers
disconnected and empty graphs. Negative weights, parallel edges and self-loops
are allowed. The proof retains the sorting cost as well as the
inverse-Ackermann disjoint-set cost.

## Checking the correspondence

Each companion analysis proves a generated `Call` contract for the actual
source. The algorithm proofs reuse the data-structure contracts, including
their mutation and amortized-cost guarantees. The runtime counts the named
ticks; it does not count every primitive operation or measure machine time.

Changing a loop, method call or initialization order requires regenerating the
definitions and rechecking the affected proof. A textbook-like appearance and
a matching generated file are useful review evidence, but neither is itself
a formal proof of the compiler's semantics preservation.
