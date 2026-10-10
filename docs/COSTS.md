# Explicit cost counters

Use `tick("name")` to count an abstract operation at a chosen source location:

```python
def advance(value: Int) -> Int:
    tick("work")
    return value + 1
```

With one argument, each execution increments that named counter by one. Use
`tick("work", amount)` to add a nonnegative integer amount instead, for example:

```python
def charge_copy(length: Int) -> None:
    tick("array_reads", length)
```

The amount is an ordinary `Int` expression evaluated normally, including any
function calls or side effects in that expression. Zero is allowed. A negative
amount has no increment step and no completed output on that path; the prefix
before it, including effects of evaluating the amount, can still be described
by a transcript.

Names must be literal strings with ASCII identifier syntax, such as `"work"`,
`"comparisons"`, or `"array_reads"`. A tick is a standalone statement, not an
expression with a return value. Its counter is a mathematical natural number;
there is no overflow.

The quoted name distinguishes a clock from an algorithm variable without an
extra declaration. Lean uses the same string name, so `tick("work", amount)`
corresponds directly to observations such as `costs "work"`. The counter map is
the small shared type `Clocks := String → Nat`; ordinary Algo2Lean expressions
still do not support string values or operations.

Counters are shared throughout an execution, including function calls, methods,
constructors, and recursion. Distinct names are independent. A function's
argument named `work` has no connection to the `"work"` counter. Source code
cannot read or reset counters to control its own behavior.

The meaning of one tick is chosen by the algorithm author. It can represent one
comparison, one array access, or one iteration. Other operations do not incur
cost automatically. These counts are not elapsed time, machine instructions,
or the number of compiler transitions. Put ticks on every executed path where
the intended operation occurs; an implicit final loop test is not counted by
a tick placed only in the loop body.

## Output and cost of the same run

Programs containing ticks additionally generate:

```lean
f.ReturnsWithCost input output costs
```

Here `costs : String → Nat`, and `costs "work"` gives the increment of that
counter during the completed run. The relation connects the output and all
costs to **one execution**. It does not combine a value from one execution
with a cost from another. The ordinary `f.Returns` interface remains
available when cost is irrelevant.

Ordinary inputs begin with zero counters. An explicit input heap may already
contain counter values; the cost interface records the difference between the
final and initial counters. A diverging execution has no completed output with
cost. Its finite prefixes can still be studied through transcripts and local
clock observations.

The generated algorithm module adds the cost relations and bridge theorems
only when the source uses ticks. Programs without ticks need no generated cost interface.
Adding or removing a tick changes the execution semantics. Renaming a line
label changes only the separate `Points` module, as before.

## Local observations and reusable call summaries

The shared heap carries the counters:

| Interface | Meaning |
| --- | --- |
| `heap.clocks "work"` | Current counter value. |
| `heap.tick "work" amount` | Same sequence and object contents, with this counter increased by the natural `amount`; the amount defaults to one. |
| `Heap.cost before after "work"` | Final minus initial counter value. |
| `clock state "work"` | Counter observed in one supplied configuration. |

`clock` requires no transcript or reachability premise. For example, a theorem
about a named tick can relate the counters in its before and after
configurations. A transcript can then reuse that local fact. As with other
named statements, place `# @name` on its own line immediately above `tick(...)`
at the same indentation; it observes the state before the increment.

The existing heap-aware `f.Call` already describes a call's counter
effects through its final heap. A summary for the source above can state:

```lean
advance.Call heap value (heap.tick "work") (value + 1)
```

For a whole segment with several counters, use `heap.charge costs` in a summary.
This shared proof helper adds a cost map to the existing counters and preserves
program data. It is not an additional source-language instruction.
`Clocks.single "work" amount` describes one counter and `Clocks.add first second`
combines segment costs pointwise. `Heap.tick_charge` and `Heap.charge_add` connect
individual ticks to aggregate summaries, while `Heap.cost_charge` extracts the
exact increment even when the caller's counters were nonzero.

A caller applies that theorem under its own suspended stack. No additional
cost-specific calling semantics or transcript reconstruction is needed. Heap
updates and allocations preserve counters; ticks preserve sequence and class
object contents.

`Heap.cost` uses natural-number subtraction. For unrelated arbitrary heaps it
therefore truncates at zero. Valid execution steps never decrease counters;
prove the appropriate execution or monotonicity facts when composing costs
between intermediate states.

The generated theorem `f.ReturnsWithCost.returns` forgets the cost from an
output-with-cost fact. Conversely, `f.Returns.withCost` gives some cost map
for an ordinary output. These bridges retain the shared execution semantics.
For example, `triangular_work.ReturnsWithCost.returns measured` retains the
output from a measured run. Older analyses must migrate their cost relations
and bridge lemmas to these scoped names.

## Checked example

[clocks.algo](../examples/clocks.algo) maintains two independent counters.
`counted_loop(n)` increments `"calls"` once and invokes `advance` until its
value reaches `n`, starting at zero. Each invocation increments `"work"`.
The [separate analysis](../examples/analysis/clocks.lean) proves a completed
run with result `max(n, 0)`, one call tick, and `n.toNat` work ticks for every
integer input. Negative inputs perform no iterations but still count the
entry tick.

The proof is organized around a local tick fact, a small summary for `advance`,
a remaining-iterations lemma at the named loop, and an output-with-cost theorem.
It then proves determinism and `output_with_cost_iff`: every completed execution
has exactly that output and cost map, and the specified execution exists for
every integer input. The heap-aware `execution_correct` theorem also applies
to arbitrary initial heaps with nonzero counters. This establishes exact costs
for the chosen instrumentation; it does not assert a relationship with elapsed
machine time.

## Weighted work and a nonlinear bound

[weighted_ticks.algo](../examples/weighted_ticks.algo) charges `i` work units
in iteration `i`, separately counting iterations. Its
[analysis](../examples/analysis/weighted_ticks.lean) proves exact costs for all
integer inputs: with `m = n.toNat`, there are `m` iterations and
`0 + 1 + … + (m - 1)` work units. The theorem `triangular_formula` proves that
twice this work equals `m * (m - 1)`. Negative inputs do no work.

The proof separates the mathematical cost recurrence from local transitions.
Its reusable summary has final heap `heap.charge (costs n)`, so callers need not
reconstruct the order of individual clock updates. `output_with_cost_iff`
characterizes every completed execution, including all untouched counters.
Its statements use `triangular_work.Call`, `triangular_work.Run`, and
`triangular_work.ReturnsWithCost`; local helpers refer to
`triangular_work.At.charge` and `triangular_work.Local.i`.

[heap_height.algo](../examples/heap_height.algo) is a logarithmic example. It
follows the parent formula `(index - 1) // 2` to the root and counts each move.
The analysis characterizes both the returned number and the exact `"levels"`
cost as `Nat.log2 (index.toNat + 1)`, including negative indices, and gives an
upper bound of `Nat.log2 size` for a nonnegative index below `size`.

The [Dijkstra guide](DIJKSTRA.md) explains the progression from exact relaxation
and scan costs to an indexed binary heap and the full graph algorithm. It documents the checked whole-algorithm runtime theorem and the smaller
examples used to build it.


## Costs of actual priority-queue operations

The [indexed-heap analysis](../examples/analysis/indexed_heap.lean) connects
logarithmic depth to compiled queue operations, not only to the isolated parent
walk. `sift_up_summary` bounds comparisons and swaps separately by `depth i`.
An insertion starts at the old queue size and pays at most that many parent
levels. A successful decrease starts at the vertex's old position and pays one
extra comparison to test whether its key improves. A non-improving proposal
pays exactly one comparison and no swaps. These bounds include early exits.

The contracts establish termination, queue representation, membership, and key
behavior for the same execution whose clocks are bounded. They preserve client
arrays and unrelated counters, so a caller can compose them with other work.
Minimum extraction also has a checked bound: from a nonempty queue of size `n`,
it charges at most `2 * depth (n - 2)` comparisons and `depth (n - 2) + 1` swaps.
Sift-down descends at most the height of the shortened heap; the extra swap is
the initial root/last exchange, including singleton self-swaps. Empty extraction
charges nothing. These actual call bounds are composed in the whole-Dijkstra
runtime theorem.


The complete one-edge Dijkstra family has an exact cost map tied to its
shortest-distance result: two settlements, two heap swaps, one edge visit, one
improvement, and zero on every other clock. The endpoints and nonnegative
weight are arbitrary within the graph's vertex range. Separate general lemmas
prove that every completed Dijkstra execution has nondecreasing counters and
that consecutive completed calls have additive costs, even from nonzero initial
counters.

For arbitrary represented finite graphs with nonnegative weights and a valid
source, `dijkstra_output_with_cost_correct` proves runtime bounds for every
compiled output. With `V` vertices, `E` adjacency entries, and
`H = floor(log₂(V + 1))`, settlements are at most `V`, edge visits and improvements
at most `E`, comparisons at most `2HV + (H + 1)E`, and swaps at most
`(H + 1)V + HE`. All other clock increments are zero.
`DijkstraRuntimeBound.total_logarithmic` bounds the sum by `5H(V + E)` when
`V > 0`. The same theorem also proves shortest-path correctness; termination
is established constructively through the actual compiled loops. Parallel edges
and shared adjacency suffixes count by their source-list occurrences.
