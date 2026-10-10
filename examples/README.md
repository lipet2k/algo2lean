# Algo2Lean examples

Choose a single file or a project folder from the editor's **Examples** menu.
Single files compile on their own. Projects load related source files, imports,
and companion proofs together; use **Project file** to switch between them.

| Project folder | What it demonstrates |
| --- | --- |
| [modules/](modules/README.md) | Reusable calls, sorting and searching, and passing algorithms as arguments. |
| [interfaces/](interfaces/README.md) | One abstract interface with interchangeable implementations and reusable proofs. |
| [mutual_recursion/](mutual_recursion/README.md) | Recursive imports, shared execution, and a caller that reuses the parity proof. |
| [kruskal/](kruskal/README.md) | Minimum spanning forests, reusable union-find with rank and path compression, and heap-based edge sorting. |
| [dijkstra/](dijkstra/README.md) | One Dijkstra algorithm with binary-heap and Fibonacci-heap implementations and analyses. |

**New file** creates a standalone file or adds one to the open project. Use
**Open project** for a folder from your computer and **Download project** to
keep all source and proof edits together.

```sh
python3 -m algo2lean serve --open
python3 -m algo2lean compile examples/merge_sort.algo -o MergeSort.lean --check
```

Run these commands from the repository root. Compilation produces Lean propositions; it does not execute the algorithm. `--check` asks Lean to check the generated definitions.

Each example also has a separate [Lean analysis](analysis/README.md). Choosing an
example in the editor loads that file into the **Lean analysis** pane. **Check
analysis** checks its theorems against the current source. From the command line:

```sh
python3 -m algo2lean analyze examples/factorial.algo examples/analysis/factorial.lean
```

The analyses cover general properties of the simpler algorithms and complete
functional specifications for GCD, binary search, and merge sort. The analysis
guide lists the hypotheses and final theorem names.

Compilation writes the algorithm file and a companion `Points.lean` file with
the named-line interface. The algorithm file imports the reusable `Algo2Lean`
library. The checker prepares that library automatically; `--standalone` embeds
it in the algorithm file instead. The companion always imports the algorithm.

| Example | What it demonstrates |
| --- | --- |
| [factorial.algo](factorial.algo) | Recursive function calls and arbitrary integer arithmetic. |
| [mutual_recursion.algo](mutual_recursion.algo) | Two functions calling each other; parity on nonnegative inputs. |
| [sum_loop.algo](sum_loop.algo) | Local variables and a terminating `while` loop. |
| [sequences.algo](sequences.algo) | Sequence updates, very large indices, and negative indices. |
| [gcd.algo](gcd.algo) | Euclid's algorithm, remainder, and signed-input normalization. |
| [lower_bound.algo](lower_bound.algo) | Binary search within a sorted finite interval. |
| [merge_sort.algo](merge_sort.algo) | Recursive merge sort with correctness and O(n log n) operation-count proofs. |
| [matrix_multiply.algo](matrix_multiply.algo) | Ordinary square matrix multiplication, full correctness, and exactly cubic scalar work. |
| [matrix_recursive.algo](matrix_recursive.algo) | Eight-way recursive multiplication with full correctness and cubic runtime for power-of-two sizes. |
| [matrix_strassen.algo](matrix_strassen.algo) | Seven-way Strassen multiplication with full correctness, exact counters, and subcubic bounds. |
| [mutable_sequences.algo](mutable_sequences.algo) | Shared objects, rebinding, copying, and mutation through function calls. |
| [classes.algo](classes.algo) | Typed mutable classes, constructors, method calls through aliases, and nullable linked nodes. |
| [object_sequences.algo](object_sequences.algo) | Object sequences, mutation through an indexed reference, and shallow copying. |
| [clocks.algo](clocks.algo) | Independent explicit cost counters shared across a loop and its function calls. |
| [weighted_ticks.algo](weighted_ticks.algo) | Exact triangular work and independent iteration counts, with aggregate cost summaries. |
| [relax_edge.algo](relax_edge.algo) | One edge relaxation with exact mutation and runtime costs. |
| [select_min.algo](select_min.algo) | A fully analyzed linear minimum baseline with stable ties and exact scan cost. |
| [heap_height.algo](heap_height.algo) | Exact logarithmic cost of following binary-heap parents. |
| [indexed_heap.algo](indexed_heap.algo) | Indexed binary min-heap with checked insertion, decrease-key, minimum extraction, and logarithmic operation costs. |
| [graph.algo](graph.algo) | Shared adjacency-list objects and independently checked graph-storage contracts, reused by both Dijkstra examples. |
| [dijkstra.algo](dijkstra.algo) | Adjacency-list Dijkstra with an indexed binary heap; general termination, shortest-distance output equivalence, and logarithmic runtime bounds. |
| [fibonacci_heap.algo](fibonacci_heap.algo) | Indexed Fibonacci heap with complete compiled insertion/decrease and minimum-extraction proofs, exact contents, client isolation, and amortized constant/logarithmic event bounds. |
| [dijkstra_fibonacci.algo](dijkstra_fibonacci.algo) | The same adjacency-list Dijkstra with a verified Fibonacci queue; shared shortest-path proof, termination, and O(E + V log V) bounds on all ten instrumented clocks. |
| [range_sum.algo](range_sum.algo) | Integer ranges, signed steps, and empty-loop variable bindings. |
| [transcripts.algo](transcripts.algo) | Named statement locations, local facts, and a caller that can reuse a function summary. |
| [divergence.algo](divergence.algo) | Infinite iteration and recursion, both having no output. |

## Merge sort

```python
merge_sort(a, lo, hi)
```

This sorts the finite interval **`[lo, hi)`** into ascending order. Indices may be negative. The sequence is infinite, so the bounds explicitly select which elements to sort. Every position outside the interval retains its input value. Intervals with `hi <= lo + 1`, including empty or reversed intervals, return the input unchanged.

`merge_sort` splits the interval recursively and calls `merge` on two sorted halves. The helper first calls `copy(a)`, then reads its input while writing into a separate object. Its `<=` comparison takes an equal element from the left half first, giving the usual stable merge behavior. The helper assumes `lo <= mid <= hi` and that both halves are sorted.

The `"merge_sort"` clock charges one unit at each sorting call and each merged
output write. For `n = max(hi - lo, 0)`, the checked [analysis](analysis/merge_sort.lean)
proves the exact recurrence `T(0) = T(1) = 1` and
`T(n) = 1 + T(⌊n/2⌋) + T(⌈n/2⌉) + n` for `n > 1`, then bounds every run by
`2 * n * (Nat.log2 n + 1) + 1`. Empty and reversed intervals cost one call.
This is an abstract operation count: sequence copies are constant-time mathematical
snapshots, and integer bit complexity is excluded. The reusable heap-level cost
contract also applies with nonzero starting clocks and preserves unrelated counters.

`demo_merge_sort()` constructs the interval `[3, 1, 4, 1]` at indices 0 through 3 and sorts it into `[1, 1, 3, 4]`. Its markers at indices -1 and 4 stay unchanged. Bracket notation here is only explanatory; Algo2Lean constructs the input using `const` and element assignments.

The main generated proposition is:

```lean
merge_sort.Returns
    (my_input : Algo2LeanGenerated.Seq × Int × Int)
    (my_output : Algo2LeanGenerated.Seq) : Prop
```

For example, `merge_sort.Returns (a, -3, 5) b` states that sorting the input interval from -3 through 4 returns the sequence `b`.

`merge_sort.Returns` presents sequence contents as mathematical functions. For object identity, input aliasing, and final heap effects, use `merge_sort.Run` with explicit sequence references and initial and final heaps.

## Mutable sequences and ranges

`b = a` shares a sequence object; updates through either variable affect both. Rebinding a variable to a fresh `const` object leaves its old aliases unchanged. `copy(a)` creates a separate object containing the current values of `a`; `update(a, i, value)` mutates `a` and returns the same reference. Negative indices are ordinary integer indices, not offsets from an end.

`range(stop)`, `range(start, stop)`, and `range(start, stop, step)` evaluate their integer arguments once, from left to right. The stop bound is excluded, and a negative step iterates downwards. A zero step has no output. An empty loop preserves an existing loop-variable binding; a newly introduced variable is not available after the loop unless initialized beforehand.

## GCD and binary search

`gcd(a, b)` returns a nonnegative greatest common divisor for signed integers. The example defines `gcd(0, 0)` as 0. For instance, `gcd(-48, 18)` returns 6.

`lower_bound(a, lo, hi, target)` assumes `lo <= hi` and an ascending sequence on that interval. It returns the first index whose value is at least `target`, or `hi` if no such index exists. Returning the upper bound avoids using -1 as a failure marker, since -1 is a valid sequence index. An empty interval returns `lo`, which equals `hi`. `demo_lower_bound()` returns 1.

## Classes and linked structures

`classes.algo` defines a mutable `Counter` and a `Node` with a nullable next
link. `counter_alias(start, delta)` updates the counter through an alias and
returns `start + delta`. `linked_sum(a, b)` builds two nodes and traverses them
through the recursive `sum` method. The source accepts shared and cyclic
object graphs; a recursive traversal need not terminate on a cycle.

The generated interface exposes class membership, typed field observations,
field updates, and helpers for constructing input heaps. Object arguments take
an explicit heap so sharing is expressible. Read the [class guide](../docs/CLASSES.md)
for source syntax and the Lean interface.

## Object sequences

`object_sequences.algo` stores `Node` references in `Seq[Node]`. `read_value`
observes an indexed node's field; `set_value` changes that shared node.
`shallow_copy` creates a distinct sequence while preserving its element
references. The analysis proves summaries for these operations and explains
how two positions that hold the same node observe the same field update.
All integer indices remain valid, including negative ones. See the
[collection guide](../docs/COLLECTIONS.md) for nullable and nested sequences,
input-heap construction, and the planned extension path for `Set` and `Dict`.

## Explicit costs

`clocks.algo` uses `"calls"` for function entries and `"work"` for counted
operations inside a callee. `counted_loop(n)` returns `max(n, 0)`, with one
entry tick and `n.toNat` work ticks; all other counters have zero cost.
The analysis proves this exact output-and-cost characterization for every
integer input and every completed execution, reusing a summary for `advance`.
`tick("name", amount)` also supports weighted nonnegative increments. These
are abstract costs chosen by the source author, not elapsed time; see the
[cost guide](../docs/COSTS.md).

## Named locations and transcripts

The [Dijkstra guide](../docs/DIJKSTRA.md) explains how the runtime, relaxation,
and minimum examples compose into the verified adjacency-list algorithm with an
indexed binary heap. The linear scan is a simpler baseline, not its final queue.

Labels occupy their own comment line immediately above a statement, at the
same indentation, with no blank or comment line between them. Inline labels
are not supported. In `transcripts.algo`, `# @set` directly above `a = 1`
exposes `assignment.At.set`, a predicate identifying the state before the
assignment starts. A location predicate alone does not assert that an execution
reaches it. `assignment.Local.a` returns a value only at named locations where
`a` is initialized. It returns `none` at `@initialize` and at internal
instruction points. Name the next statement to observe a value after an
assignment.

`assignment.ValidTranscript` describes an explicit valid sequence of configurations, including both endpoints. A transcript may stop before the function finishes. Outputs use completed valid transcripts. The checked [proof fixture](../tests/proofs/transcripts.lean) proves the assignment's local effect, lifts it to arbitrary valid transcripts, and uses its intermediate value to prove a function summary and then the caller's output.

## Validation

The test suite compiles every example and, when Lean is installed, checks its
generated definitions and separate analysis in Lean 4. Algorithm tests also
compare finite intervals against independent expected results, including
duplicates, negative indices, and outside values. The separate analyses provide
general proofs: GCD's exact mathematical result, binary search's sorted partition
boundary, and merge sort's termination, sortedness, permutation, and outside
preservation. They also describe heap effects and output uniqueness. Lean checks
skip if the `lean` executable is absent. The compiler itself is not formally
verified. GCD and binary search have no runtime bounds here; merge sort proves
a logarithmic runtime bound but no tagged-key stability theorem. The runtime examples prove explicit
operation counts; Dijkstra additionally proves general shortest-path correctness
and bounds all instrumented clocks: five in the binary-heap example and ten in
the Fibonacci-heap example. See the [Fibonacci Dijkstra guide](../docs/FIBONACCI_DIJKSTRA.md)
for the queue contracts, proof reuse, and abstract cost model.

```sh
python3 -m unittest discover -v
```

## CLRS Chapter 4 (§4.1–4.4)

The [Chapter 4 guide](../docs/CLRS_CHAPTER_4.md) covers the three matrix examples,
their row-major representation, power-of-two assumptions for recursion, and
proved unit-cost runtime bounds. The [recurrence guide](../docs/RECURRENCES.md)
describes reusable substitution and recursion-tree proofs. These examples and
frameworks use Lean/Std alone; the master theorem is outside the current scope.
