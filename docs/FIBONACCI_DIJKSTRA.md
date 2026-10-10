# Fibonacci-heap Dijkstra and proof reuse

The indexed Fibonacci heap has complete compiled constructor, update, and
minimum-extraction proofs. Each public operation terminates, preserves the finite
heap representation and client storage, has the exact intended entry effect,
and satisfies its amortized bound on the actual source clocks.

The Dijkstra client reuses those operation contracts, the shared graph proof,
and the same shortest-path theory and finite execution driver as binary-heap
Dijkstra. The checked cross-module reuse mechanism is documented in
[MODULAR_PROOFS.md](MODULAR_PROOFS.md). Heap transition proofs are imported;
they are not copied into the caller.

## Source and representation

`examples/fibonacci_heap.algo` implements an indexed Fibonacci heap. Vertex
identifiers are stable nonnegative handles. Eight shared integer sequences store
keys, parent/child handles, circular sibling links, degrees, marks, and presence.
Insertion adds an unmarked singleton root. Decrease-key cuts an out-of-order
node and performs cascading cuts. Minimum extraction promotes children and
consolidates roots of equal degree using a ninth, reusable degree table.
It scans only the encountered degree range and clears visited buckets while
rebuilding the roots. Queue operations allocate no additional sequences.

The finite logical forest records heap order, unique handles, marks, and the
rank history needed after child losses. Circular-ring and storage invariants
connect that forest to the exact compiled sequence reads and writes. Child
lists retain newest-first link order. Unused sequence cells have no arbitrary
parent-rank requirement; all termination arguments concern the active forest.

`examples/dijkstra_fibonacci.algo` uses the same heap class. Its `Graph`, `Edge`,
and Dijkstra body agree with the binary-heap example except for the queue
constructor. Regression tests enforce both agreements. Vertices with equal keys
may be selected in any order consistent with the actual queue; shortest-path
correctness does not require a special tie policy.

## Public heap interface

Start in `examples/analysis/fibonacci_heap.lean`:

- `new_heap_representation` establishes a represented empty queue.
- `QueueRep.update` runs insertion or strict decrease, changes exactly the
  requested vertex's binding, and preserves all other bindings.
- `QueueRep.pop_minimum` runs extraction on a nonempty queue, returns a least-key
  vertex, and removes exactly that binding.

These statements use a heap, queue reference, storage layout, and finite logical
forest. They do not expose program counters, rings, table loops, or execution
transcripts. Method summaries work under arbitrary callers. `Heap.Modifies`
identifies the nine queue sequences and queue object as the mutation footprint;
other sequences, objects, collections, and allocation counters stay unchanged.
`PreservesOtherClocks` keeps caller counters unchanged.

The update charge is at most 20; the extraction charge is at most
`12 * (2 * N.log2 + 2)`, where `N` is the queue's size before extraction.
Both are amortized statements:

```text
actual heap events + final potential ≤ initial potential + charge
potential = 4 * (number of roots + 2 * number of marked nodes)
```

Roots are unmarked in the representation, so marked nodes are nonroots.
A particular extraction or decrease can do more work than its amortized charge;
the decrease in stored potential pays for it.

## Dijkstra interface

In `examples/analysis/dijkstra_fibonacci.lean`, begin with
`dijkstra_output_iff`: for a represented finite graph and valid source, an
ordinary output is exactly a sequence of shortest distances.
`dijkstra_output_exists` establishes a terminating output for a valid source.
`dijkstra_terminates` covers every integer source, including invalid sources,
which return the all-`-1` sequence without ticking.
`dijkstra_output_with_cost_correct` bounds the sum of all ten clocks for every
completed output. `dijkstra_correct` gives a call summary and final graph
preservation for reuse by a caller.

`verifiedQueueContracts` constructs the three local method contracts from the
standalone heap theorems. These final Dijkstra results have no queue-contract
premise. The `_of_queue_contracts` helper theorems are useful when
explaining how the graph proof depends on its queue interface. See the
[contract guide](DIJKSTRA_FIBONACCI_CONTRACTS.md) for their exact boundary.

## Proof composition

The shared proof files have distinct responsibilities:

- `Algo2LeanLib/Dijkstra.lean` supplies paths, relaxation, and `SearchRun`
  correctness. `DijkstraExecution.lean` supplies finite execution and accounting
  composition. Both queue implementations reuse them.
- `Fibonacci.lean` supplies Fibonacci subtree-size and logarithmic degree bounds,
  plus potential accounting. `FibonacciForest.lean` proves the finite forest
  transformations and their rank-history invariants.
- `FibonacciRings.lean` and `FibonacciStorage.lean` connect exact pointer and
  sequence effects to the forest. `FibonacciStoredContext.lean` lifts local
  subtree changes through ancestors.
- `FibonacciCascade.lean`, `FibonacciMutableCascade.lean`,
  `FibonacciDecrease.lean`, and `FibonacciKeyUpdate.lean` justify the finite
  cascading-cut execution and its complete entry replacement.
- `FibonacciRootInsertion.lean`, `FibonacciConsolidation.lean`,
  `FibonacciRebuild.lean`, and `FibonacciDeleteMin.lean` justify promotion,
  finite bucket collisions, root reconstruction, and exact minimum removal.
- `examples/analysis/fibonacci_heap.lean` realizes those finite operations as
  the actual compiled method summaries, including their measured clocks.
- `examples/analysis/dijkstra_fibonacci.lean` uses only the public queue contracts
  for graph correctness and runtime. A checked embedding transfers the standalone
  summaries into the larger compiled program. A separate determinism certificate
  establishes uniqueness of the final output, heap, and clocks.

The original mathematical accounting follows
[Fredman and Tarjan's paper](https://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/fibonacci%20heaps.pdf).
The constants above are for this implementation's instrumented events.

## Cost model and limits

The seven heap clocks count operations, key comparisons, links, cuts, child
promotions, root visits, and degree-table visits. Dijkstra additionally counts
settlements, edge visits, and successful improvements. `clockWork` adds all ten
with unit weight. The complete client bound is

```text
clockWork ≤ 22 * (E + 1) + (12 * (2 * V.log2 + 2) + 1) * V
```

This is O(E + V log V) for a represented finite graph with nonnegative edge
weights and a valid source. Parallel adjacency entries each count toward `E`;
unreachable vertices have distance `-1`.

The theorem concerns explicitly instrumented events, not elapsed machine time.
Integers and infinite integer sequences are mathematical objects; sequence
allocation and integer arithmetic use the language's abstract model. A bit-cost
or machine-cost theorem would require additional modeling. The compiler itself
is not formally verified. Lean checks the emitted definitions, the concrete
execution proofs, and each component embedding against the current compiled
source.

Source-level imports are not implemented: the two `.algo` files contain the
same heap class, and tests enforce that they agree. Compiled definitions can use
separate namespaces, and component proofs are imported and cached. The graph
client still has source-specific continuation lemmas for its own loop; replacing
a queue does not require repeating its ring or tree proofs.

## Checking

```sh
python3 -m algo2lean analyze examples/fibonacci_heap.algo examples/analysis/fibonacci_heap.lean
python3 -m algo2lean analyze examples/dijkstra_fibonacci.algo examples/analysis/dijkstra_fibonacci.lean
python3 -m unittest tests.test_fibonacci_heap
```

The seven execution regressions include randomized queue invariants, adversarial
cascading cuts, reusable degree-table storage, and randomized Dijkstra results
compared with Bellman-Ford. The general Lean proofs use no placeholder proofs,
extra axioms, or increased resource limits.

The public update, pop, correctness, output-equivalence, and termination theorems
use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
There are no admitted proof obligations or project-specific axioms. Generated
embedding and determinism certificates are checked against the current source;
reusable component proofs are cached with their dependencies.
