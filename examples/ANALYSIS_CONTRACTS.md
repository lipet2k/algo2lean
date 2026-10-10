# Reusing the example analyses

Use a theorem about `f.Call before input after result` when verifying another
algorithm that calls `f`. A call includes input validity and applies under every
suspended caller stack. `f.CallFrom` is the corresponding interface for a named
intermediate location. The output relations `f.Returns` and `f.ReturnsWithCost`
are views of these execution semantics, intended for ordinary-value statements.

A contract can specify the final heap exactly, such as `heap`,
`heap.tick "work" count`, or `heap.write ref index value`. This specifies storage,
allocation, and **every** clock, without additional preservation assumptions.
For larger algorithms, contracts instead expose a mathematical result,
representation or preservation predicates, valid references, and cost facts.
Preservation predicates have the scope stated in their definitions: preserving
a graph representation or every old sequence is not automatically a theorem
that every heap field is unchanged.

Clock guarantees concern the source's explicit `tick` operations. An unchanged
heap implies no recorded charge; it does not mean the algorithm performs no
computation. Binary lower bound, for example, is uninstrumented. Composition
with it retains the sorting phase's cost bound, rather than asserting a measured
bound for the whole sort-and-search computation.

## Contract inventory

Paths below are relative to `examples`. Groups include companion analyses that
share the same contract pattern; they are not additional assumptions.

| Analysis | Reusable entry point and guarantees |
| --- | --- |
| `analysis/factorial.lean` | `FactorialAnalysis.summary`: every signed input, factorial of `n.toNat`, entire heap unchanged. |
| `analysis/sum_loop.lean` | `SumLoopAnalysis.summary`: every signed input, finite sum, entire heap unchanged. |
| `analysis/range_sum.lean` | `RangeSumAnalysis.summary`, `stepped_summary`, `empty_range_summary`: exact sums and unchanged heaps; `zero_step_no_call` excludes invalid zero steps. The stepped contract covers intervals expressed by a start, nonzero step, and natural count. |
| `analysis/gcd.lean` | `GcdAnalysis.summary`: signed integer GCD, termination, unchanged heap. Local helpers use `gcd.CallFrom`. |
| `analysis/mutual_recursion.lean` | `MutualRecursionAnalysis.summaries`: both parity functions on signed inputs, unchanged heaps. |
| `analysis/sequences.lean` | `replace_summary`, `negative_index_summary`, `distant_value_summary`: exact mutation, read-only access, or fresh allocation effects for arbitrary heaps. |
| `analysis/mutable_sequences.lean` | `overwrite_summary`, `parameter_mutation_summary`: exact writes, including input aliasing. |
| `analysis/classes.lean` | Counter read/write contracts and `chain_sum_summary`: exact object effects or unchanged heaps. The linked-list sum assumes a represented finite nonempty chain. |
| `analysis/object_sequences.lean` | `read_value_summary`, `set_value_summary`, `shallow_copy_summary`: exact effects on shared object references and typed sequence copies. |
| `analysis/clocks.lean`, `analysis/weighted_ticks.lean`, `analysis/heap_height.lean` | `counted_summary`/`summary`: mathematical results and exact clock changes on arbitrary heaps. Other storage and clocks are unchanged. |
| `analysis/lower_bound.lean` | `terminating_summary`, `sorted_summary`: finite search termination, optional sorted-input partition guarantee, entire heap unchanged. |
| `analysis/select_min.lean` | `selection_summary`: first minimum among eligible vertices, exact scan count, all other heap state unchanged. |
| `analysis/relax_edge.lean` | `relax_summary` and `exact_costs`: exact conditional mutation and clock increments, with projections for unaffected indices and sequences. |
| `analysis/merge_sort.lean` | `MergeSortAnalysis.summary`: one call gives sorted permutation, preservation outside the interval and of all old sequences, valid result reference, exact sorting cost, and unchanged other clocks. A base case may return the input reference. |
| `analysis/matrix_multiply.lean` | `MatrixMultiplyAnalysis.call`: product for every natural dimension, one fresh result sequence, preservation of old sequences, exact cubic charge. `summary` also gives the complete final heap. |
| `analysis/matrix_recursive.lean` | `MatrixRecursiveAnalysis.call`: product for a power-of-two dimension, fresh result, old-sequence preservation, exact recursive-call and multiplication charges. `recursive_summary` gives the complete final heap. |
| `analysis/matrix_strassen.lean` | `MatrixStrassenVerified.call`: power-of-two product, fresh valid reference, old-sequence preservation, exact increments of every clock. Helper contracts use generated Calls; the raw semantics clock bridge is private. |
| `analysis/graph.lean` | Constructor and edge-insertion Calls provide exact heap effects; `graph_constructor_verified` and `add_edge_preserves_representation` expose the graph model. |
| `analysis/indexed_heap.lean` | `insert_correct`, `decrease_correct`, `unchanged_correct`, `pop_correct`: represented queue behavior, operation bounds, unchanged other clocks, and storage frame facts. Constructors and local operations have exact-heap Calls. |
| `analysis/fibonacci_heap.lean` | `QueueRep.update`, `QueueRep.pop_minimum`, and their contract records: represented queue behavior, storage frame, unchanged other clocks, and amortized costs. This is a data-structure API, not one ordinary-value result. |
| `analysis/dijkstra.lean` | `dijkstra_call_contract`: generated Call, preserved graph representation, fresh valid distance sequence, shortest paths, outside-range sentinel, actual clock increments and binary-heap bounds, plus `heap.Footprint after [] [] []` preserving every pre-existing caller location. Ordinary output results derive from the same Call. |
| `analysis/dijkstra_fibonacci.lean` | `dijkstra_call_contract`: generated Call, graph preservation, shortest paths, fresh valid distance sequence, total Fibonacci-heap cost bound, and `heap.Footprint after [] [] []` preserving every pre-existing caller location. Queue contracts are discharged by the concrete backend; ordinary outputs are derived views. |
| `analysis/dijkstra/dijkstra.lean` | `dijkstra_complete`: abstract priority-queue Calls compose correctness, graph preservation, operation counts, backend cost, valid result allocation, and preservation of the caller snapshot. |
| `analysis/dijkstra/dijkstra_binary.lean`, `dijkstra_fibonacci.lean` | `summary`: concrete backend Call, shortest paths, counts, combined runtime, valid fresh distance identity, and `heap.Footprint after [] [] []` preserving every pre-existing caller sequence, object, and typed collection. |
| `analysis/dijkstra/priority_queue.lean` | Abstract `Contracts` state represented updates/extractions, protected storage, preserved caller snapshots, and amortized clock laws. They are behavioral premises, instantiated by the two verified backend adapters. |
| `analysis/dijkstra/support/*.lean` | Independently reusable heap method contracts and the binary/Fibonacci queue adapters. Adapter proofs preserve the original generated backend Calls. |
| `modules/analysis/increment.lean`, `twice.lean`, `pipeline.lean` | `summary`: layered imported Calls with exact final heaps and charges, reused unchanged by the next caller. |
| `modules/analysis/compare_exchange.lean`, `sort_three.lean`, `lower_bound_three.lean`, `sorted_search_three.lean` | `summary`: exact mutation/clock effects and sortedness or insertion-position facts for the small three-element example. |
| `modules/analysis/general_merge_sort.lean` | `GeneralMergeSortAnalysis.summary`: combined sorting correctness, old-sequence preservation, result validity, exact charge, and unchanged other clocks. |
| `modules/analysis/general_lower_bound.lean`, `general_binary_lower_bound.lean` | General search Calls; linear search includes comparison counts, binary search preserves the entire heap. Sorted-input premises are explicit. |
| `modules/analysis/general_sort_then_search.lean`, `general_linear_sort_then_search.lean`, `general_consumer.lean`, `general_linear_consumer.lean` | `summary`: imported Calls and a result specification carrying the reusable sorting/search/preservation/cost facts through further layers. |
| `modules/analysis/callable_direct.lean`, `callable_staged.lean`, `callable_bindings.lean` | Concrete generated Calls, their exact effects, and verified bindings to the abstract callable example. |
| `interfaces/analysis/direct.lean`, `negated.lean` | `read_summary`/`write_summary` specify exact backend heap effects; `read`/`write` expose represented values, exact increments, and storage preservation outside the receiver. |
| `interfaces/analysis/counter.lean` | `CounterContract` is an abstract behavior contract, not a concrete execution theorem. It promises the represented counter value, clock increments, unchanged allocation, and preservation of all storage outside the receiver object. The concrete backend contracts specify their full heap effects. |
| `interfaces/analysis/increment.lean`, `consumer/advance_twice.lean`, `use_direct.lean`, `use_negated.lean` | `summary`: generated interface Calls, representation postconditions, composed clock increments, and preservation of unrelated storage through every reuse layer; behavioral assumptions are discharged by concrete bindings. |
| `mutual_recursion/analysis/parity.lean`, `client.lean` | `calls`/`call`: reusable contracts across a recursive import group and its external caller, exact heap effects and costs for natural inputs. No termination claim is made for negative arguments. |
| `kruskal/analysis/kruskal.lean` | `KruskalAnalysis.call_contract`: generated Call, minimum spanning forest, exact selection flags, fresh valid result, `heap.Footprint final [] [] []` preserving all pre-existing caller storage, actual clock increments, and the improved total runtime bound. Ordinary graph theorems are derived views. |
| `kruskal/analysis/union_find.lean` | `find_amortized` and `union_amortized`: generated method Calls, representation and connectivity postconditions, storage preservation, actual clock increments, and inverse-Ackermann amortized bounds with explicit potential. The contracts remain reusable by algorithms other than Kruskal. |
| `kruskal/analysis/kruskal_scan.lean` | `scan_contract`: generated scan Call, selection correctness, a storage footprint, unchanged unrelated clocks, and a potential inequality that telescopes across the repeated union operations. |
| `kruskal/analysis/sort_indices.lean`, `union_find_init.lean`, `indexed_heap.lean` | Reusable sorting, initialization, and queue contracts supply the independent components of the full Kruskal proof. `kruskal_input.lean` translates finite graph representations; it does not define another executable algorithm. |

## Special cases

- `analysis/divergence.lean` proves `endless_loop_has_no_call` and
  `endless_recursion_has_no_call`. Valid finite prefixes remain available. There
  is no terminating output, final-heap guarantee, or finite whole-call cost.
- `analysis/transcripts.lean` retains its local transition and transcript lemmas;
  these deliberately do not assume a completed call. `assignment_summary` and
  `caller_summary` additionally support ordinary composition of the two complete
  source functions.
- `modules/analysis/callable_client.lean` is a manually defined, parameterized
  executable semantics example. Its local `call.Call` and `twice.Call` wrappers
  use the same caller-independent summary semantics. There is no generated
  source function for these two definitions; concrete generated bindings are
  proved in `callable_bindings.lean`.
- `analysis/support/*.lean` contains checked transition embeddings and a
  determinism certificate for the older standalone Dijkstra examples. These are
  proof infrastructure; they transport Calls rather than exporting a new
  algorithm or asserting another runtime bound.

Contracts cover their stated input domains and representations. This inventory
does not turn conditional method contracts, local transcript facts, or an
uninstrumented algorithm into an unconditional termination or runtime claim.
