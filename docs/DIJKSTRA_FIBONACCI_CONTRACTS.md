# Fibonacci Dijkstra: the verified queue interface

`examples/analysis/dijkstra_fibonacci.lean` proves the complete compiled Dijkstra
algorithm using the verified Fibonacci heap. The `verifiedQueueContracts`
instance supplies all local queue contracts from independently checked heap
method proofs. The public results have no queue-contract premise.

The main correctness/runtime theorem is `dijkstra_output_with_cost_correct`.
Given a represented finite graph and a valid source vertex, every
`dijkstra.ReturnsWithCost` result satisfies:

- `ShortestDistances (representedEdges size adjacency) source output`;
- `clockWork costs ≤ 22 * (E + 1) + (12 * (2 * V.log2 + 2) + 1) * V`,
  where `V = size.toNat` and `E` is the number of represented adjacency entries.

Parallel edges each count as an edge. Unreachable vertices retain `-1`, as
specified by `ShortestDistances`. The existing invalid-source theorem covers
sources outside the graph separately. The cost is the sum of actual source tick
increments, rather than elapsed time: the three Dijkstra clocks and seven
Fibonacci heap clocks each receive unit weight. The bound is O(E + V log V).

`dijkstra_correct` additionally exposes the final graph representation and a
call summary reusable under arbitrary callers. `dijkstra_output_exists`
constructs a terminating output with its correctness and runtime bound.
`dijkstra_output_correct` uses the ordinary output proposition without clocks;
`dijkstra_output_iff` identifies that proposition with the mathematical
shortest-distance specification. `dijkstra_terminates` covers every integer
source, including the invalid-source branch.
`support/DijkstraFibonacciDeterminism.lean` checks a next-configuration
projection against every compiled transition. This establishes uniqueness of
the final heap, output, and clocks, so the guarantees hold for every output.

## The local contracts

The constructor must have an actual `FibonacciHeap.Call` execution,
produce a represented empty forest, preserve existing graph/client storage,
and leave clocks unchanged. This field is discharged by the unconditional
`queue_constructor_verified` theorem.

An insertion or strict decrease must have an actual
`FibonacciHeap.push_or_decrease.Call` execution, preserve representation
and graph/client storage, replace exactly the requested vertex's entry, and
satisfy:

```
heapEventWork before after + scaledPotential afterForest.counts
  ≤ scaledPotential beforeForest.counts + 20
```

Minimum extraction must have an actual `FibonacciHeap.pop_min.Call`
execution, remove precisely a least-key entry, preserve representation and
client storage, and satisfy:

```
heapEventWork before after + scaledPotential afterForest.counts
  ≤ scaledPotential beforeForest.counts + 12 * (2 * V.log2 + 2)
```

The extraction contract receives a finite queue whose handles lie within the
vertex range. The contracts preserve the three caller clocks; heap work is
measured from the other seven actual clocks. The shared potential is
`scaledPotential counts = 4 * (roots + 2 * marks)`.

Every contract is about one public queue operation. None mentions shortest
paths, a Dijkstra search trace, or execution of the full algorithm. Existing
standalone heap proofs fill these fields through the checked cross-module
adapter. `queue_update_verified` reuses `FibonacciHeapAnalysis.QueueRep.update`,
and `queue_extract_verified` reuses `FibonacciHeapAnalysis.QueueRep.pop_minimum`.
Neither adapter inspects the internal heap algorithm.

## What is shared, and what remains specific

The Graph example supplies the adjacency representation and storage lemmas.
`Algo2LeanLib.Dijkstra` supplies `RelaxScan`, `SearchRun`, and all shortest-path
reasoning. `Algo2LeanLib.DijkstraExecution` supplies finite outer-loop recursion
and accounting composition. Both binary and Fibonacci Dijkstra instantiate the
same driver.

The Fibonacci client invariant matches logical forest entries to finite,
unsettled tentative distances. It does not inspect heap rings, linking,
cascading cuts, or array indices. Its transition proofs concern only the
Dijkstra source: initialization, selecting a vertex, and the three edge
branches. Helper lemmas expose these as local continuation contracts.

`Storage.of_modifies` and `Storage.clients_unchanged` connect a method's declared
mutation footprint to graph and client preservation. The constructor, update,
and extraction contracts are all proved. The `_of_queue_contracts` theorems
remain available to separate the client proof from its local implementation
contracts, making changes to queue proofs independent of the graph argument.

The checked public queue and Dijkstra theorems use no admitted proof obligations
or project-specific axioms. The algorithm's event counters and mathematical
potential are explicit in the contracts, so callers can reuse their guarantees
without inspecting the heap's internal transitions.
