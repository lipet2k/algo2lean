# Dijkstra with an independently verified priority queue

`dijkstra.algo` imports the existing `graph.algo` and the three-method
`PriorityQueue` interface. It contains no heap implementation. The project root
is `examples`, so imported source and companion proofs keep their own modules.

In the editor, choose **Examples → Dijkstra — binary heap (imports)** or
**Dijkstra — Fibonacci heap (imports)**. Each opens the complete project with
its imported sources and unchanged companion proofs. **Check analysis** checks
the selected proof and its imports. To open the files from disk instead, choose
**Open project → examples**, then select a `composable_dijkstra` module;
opening only this subfolder leaves out the graph and heap modules.

The entry point is:

```python
dijkstra(graph, source, queue, distance, settled)
```

The caller supplies a represented graph with nonnegative edge weights, an
in-range source, an empty queue, a distance sequence filled with `-1`, and a
separate settled sequence filled with `0`. Queue storage must be separate from
these sequences and preserve the graph. Construction belongs in a small
concrete wrapper. The returned reference is the supplied distance sequence.

The proof at `../analysis/composable_dijkstra/dijkstra.lean` establishes:

- A terminating summary of the actual compiled source and shortest distances.
- At most `E + 1` insert/decrease calls and `V` extractions.
- At most `V + 1` emptiness checks, `E` edge visits and improvements, and `V`
  settlements.
- Backend work at most `initialPotential + updateBudget * (E + 1) + popBudget * V`.

Here `V` is the graph's number of vertices and `E` counts all represented
adjacency-list entries, including parallel edges. Counts are changes in the six
explicit source clocks, so initial heaps and counters may be arbitrary.
Backend work is a finite weighted metric of separate implementation clocks.
The correctness and cost bounds use the same queue-call witnesses.

`PriorityQueueAnalysis.Contracts` specifies terminating method summaries,
abstract contents and minimum selection, protected client storage, and the
amortized charge of each operation. A backend chooses its own representation
and potential. `is_empty` preserves the heap; its call is counted by the client.
The queue's bounded, unique vertex identifiers imply its size is at most the
chosen capacity. The generic proof assumes capacity covers all graph vertices.

`ComposableDijkstraAnalysis.dijkstra_correct` is the reusable summary theorem.
`dijkstra_output_exists` provides ordinary sequence values and costs.
`every_execution`, supplied with the generated dependency facts, establishes
the same guarantees for every completed execution. The shortest-path and finite
termination arguments reuse `Algo2LeanLib.Dijkstra` and `DijkstraExecution`.

From the repository root:

```sh
python3 -m algo2lean compile examples/composable_dijkstra/dijkstra.algo \
  --project examples --check --output-dir /tmp/algo2lean-generic-dijkstra

python3 -m algo2lean analyze examples/composable_dijkstra/dijkstra.algo \
  examples/analysis/composable_dijkstra/dijkstra.lean --project examples

python3 -m unittest tests.test_composable_dijkstra
```

## Concrete queues

`dijkstra_fibonacci.algo` and `dijkstra_binary.algo` are small construction
wrappers. Each imports its original queue source and calls the same generic
Dijkstra module. Their companion proofs instantiate the independent queue
contract through generated method-summary transfers. The heap proofs, queue
adapters, and generic Dijkstra proof are reused without caller-specific
transition adapters or copied algorithm bodies.

Both wrappers accept only `graph` and `source`. For any represented graph they
terminate; out-of-range sources return a fresh all-`-1` sequence with zero clock
cost. For an in-range source, every completed execution returns shortest
distances and satisfies the six operation bounds above.

Their total runtime metric adds each backend clock and each client clock once:

| Queue | Backend clocks | Total bound |
| --- | --- | --- |
| Fibonacci heap | Seven event clocks | `23*(E+1) + (12*(2*log₂ V+2)+3)*V` |
| Indexed binary heap | Comparisons and swaps | `(2*depth(V)+4)*(E+1) + (3*depth(V)+4)*V` |

`depth` is the independently proved binary heap depth function. The bounds are
respectively O(E + V log V) and O((E + V) log V), under the explicit tick model.
Constructors add no ticks. The public `summary`, `output_exists`,
`every_execution`, `output_with_cost_correct`, and `terminates` theorems require
no queue representation or abstract-contract assumption from callers.
Use `summary` when composing another call: it supplies the compiled call summary,
preserved graph representation, shortest distances, operation counts, total
clock bound, and proof that the returned sequence is allocated. Thus the result
can immediately satisfy another sequence function's input-validity condition.
Its mutable-state guarantee covers the represented graph and returned distance
sequence; it does not claim preservation of every unrelated caller location.

```sh
python3 -m algo2lean analyze examples/composable_dijkstra/dijkstra_fibonacci.algo \
  examples/analysis/composable_dijkstra/dijkstra_fibonacci.lean --project examples

python3 -m algo2lean analyze examples/composable_dijkstra/dijkstra_binary.algo \
  examples/analysis/composable_dijkstra/dijkstra_binary.lean --project examples
```
