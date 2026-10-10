# Algorithm analyses

Each `.lean` file imports the corresponding compiled algorithm and proves
properties through its public interface. Theorem and helper-lemma statements
use mathematical values, heaps, configurations, named locations, and execution
predicates. Proof bodies may inspect the generated transition rules and internal
fields. Generated definitions remain in a separate, unedited file.

Start with the small examples:

| Analysis | Proved properties |
| --- | --- |
| [factorial.lean](factorial.lean) | Existence of the mathematical factorial output for every integer input, including the nonpositive base case. |
| [mutual_recursion.lean](mutual_recursion.lean) | Simultaneous recursive summaries and complementary even/odd outputs for every integer input. |
| [sum_loop.lean](sum_loop.lean) | Sum output for every integer input, reusing a local theorem about the remaining iterations at a named loop test. |
| [sequences.lean](sequences.lean) | General update behavior, preservation at every other integer index, negative-index reads, and huge-index writes. |
| [matrix_multiply.lean](matrix_multiply.lean) | All-size matrix-product correctness, termination, input preservation, and exactly n³ multiply-adds. |
| [matrix_recursive.lean](matrix_recursive.lean) | Power-of-two matrix products, all-output/cost characterization, and cubic multiplication/call bounds. |
| [matrix_strassen.lean](matrix_strassen.lean) | Power-of-two Strassen products, all-output/cost characterization, preservation, and Θ(7^k) total charged work. |
| [mutable_sequences.lean](mutable_sequences.lean) | General mutation summaries and the effects of shared versus distinct argument references. |
| [classes.lean](classes.lean) | Reusable counter method summaries, mutation through aliases, and termination with the correct sum for every finite linked chain; the traversal preserves the entire heap. |
| [object_sequences.lean](object_sequences.lean) | General object-sequence read and field-update summaries, alias observations, and shallow-copy behavior. |
| [clocks.lean](clocks.lean) | Exact output and independent entry/work costs for every integer input and every completed execution; local tick reasoning and a reusable callee summary. |
| [weighted_ticks.lean](weighted_ticks.lean) | Exact triangular work, iteration count, and output for every integer input; a proved quadratic formula and aggregate caller-heap summaries. |
| [relax_edge.lean](relax_edge.lean) | Exact relaxation behavior and cost, local assignment effect, preserved entries and path witnesses, self-edges, and complete output/cost characterization. |
| [select_min.lean](select_min.lean) | Terminating linear scan with first-minimum correctness, absent-result equivalence, unchanged data, and exact scan cost for every execution. |
| [heap_height.lean](heap_height.lean) | Exact `log₂(index.toNat + 1)` output and step cost for binary-parent traversal, plus bounds between powers of two. |
| [indexed_heap.lean](indexed_heap.lean) | General sift-up/down, insertion, decrease-key, and minimum-extraction contracts with heap order, exact membership/key effects, client-storage preservation, and logarithmic costs. |
| [dijkstra.lean](dijkstra.lean) | General compiled termination; ordinary output iff shortest distances; every-output correctness, outside-range preservation, and runtime bounds with total charged work ≤ 5⌊log₂(V+1)⌋(V+E). Includes verified graph construction, indexed-heap contracts, and exact edgeless/one-edge cases. |
| [graph.lean](graph.lean) | Independently checked adjacency storage and graph construction, shared by both Dijkstra implementations. |
| [fibonacci_heap.lean](fibonacci_heap.lean) | Complete compiled queue contracts: finite execution, exact insertion/decrease/deletion effects, isolated client storage, and amortized constant update/logarithmic minimum extraction. Start with `QueueRep.update` and `QueueRep.pop_minimum`. |
| [dijkstra_fibonacci.lean](dijkstra_fibonacci.lean) | Shared shortest-path and execution reasoning with the verified Fibonacci queue; termination, every-output correctness, and O(E + V log V) bounds on the sum of all ten source clocks. Start with `dijkstra_output_iff` and `dijkstra_output_with_cost_correct`. |
| [transcripts.lean](transcripts.lean) | Local assignment facts, composition, and reuse on arbitrary valid transcripts. |
| [range_sum.lean](range_sum.lean) | `range(n)` for every integer; positive/negative stepped ranges with aligned endpoints; zero-step impossibility; empty-loop binding preservation. |
| [divergence.lean](divergence.lean) | Neither infinite iteration nor infinite recursion has an output; both admit nontrivial finite prefixes. |

The following analyses provide general functional correctness proofs:

| Analysis | Proved properties | Start reading at |
| --- | --- | --- |
| [gcd.lean](gcd.lean) | Exact output characterization by `Int.gcd` for every signed pair, general termination, and heap preservation. | `summary`, `output_iff` |
| [lower_bound.lean](lower_bound.lean) | Termination for any contents and integer bounds; on sorted intervals, exact characterization of the partition boundary; unique outputs and whole-heap preservation. | `loop_induction`, `sorted_summary`, `output_iff_partition` |
| [merge_sort.lean](merge_sort.lean) | Termination on all integer intervals; every output is sorted, permutes the input interval including duplicates, and preserves all outside positions; preservation of existing heap objects; an exact operation count and an O(n log n) bound. | `every_output_correct` (Correctness), `running_time` (Running time) |

An existence theorem constructs a valid output; it does not by itself prove
that every possible output equals that value. Each file states its scope.

For binary search, sortedness and `lo ≤ hi` are hypotheses of the partition
specification, not of termination. Empty/reversed intervals have a separate
exact output theorem. Merge sort needs no input-sortedness hypothesis and handles
reversed intervals as empty. The sort proof permits allocating fresh objects;
it proves that existing objects retain their contents. The binary-search analysis
has no complexity theorem. Neither sorting analysis proves stability for
distinguishable records with equal keys; the algorithm sorts integer values.

Merge sort's `runtime n` is its exact charge to the `merge_sort` clock, counting
one unit per sort call and per merged output write. `execution_cost` proves that
charge for every completed heap-level execution, even with nonzero initial
clocks. The highlighted `running_time` theorem bounds the ordinary output's
charge by `2 * n * (Nat.log2 n + 1) + 1`, where `n = (hi - lo).toNat`.
This model treats sequence copies as constant-time snapshots and excludes integer
bit complexity. The [modular merge-sort analysis](../modules/analysis/general_merge_sort.lean)
provides the corresponding correctness and runtime interface for imported calls.

## Reusing local analysis

The class analysis defines `Chain heap node values` using class membership and
typed field getters. `last_node_summary` handles the null link;
`linked_node_summary` reuses a summary of the tail's recursive method call.
`chain_sum_summary` then follows by induction over the chain and works under
any suspended caller. Its output corollary establishes existence of the list
sum, without claiming a separate all-output uniqueness theorem. Counter
summaries describe the exact final heap; an alias corollary observes the same
updated object through another reference.

The named-loop helper in `sum_loop.lean` takes only a configuration, its source
variable values, and a mathematical count. Its conclusion uses
`sum_to.CallFrom`, which says how this function completes from that state
under any caller stack. It needs no transcript or reachability hypothesis.
The entry-point theorem reuses it to prove `sum_to.Returns`.

Use small phase lemmas to separate transition details from the mathematical
proof outline. Their statements describe source-level phases; only their bodies
inspect generated transitions. The GCD analysis is a complete example: sign
normalization, one iteration, decreasing-remainder induction, then an exact
output theorem.

The range examples need an additional public reachability premise: `range`
captures its bounds and step before iteration, so those values cannot in general
be recovered from source-variable getters alone. Their proof bodies establish
the corresponding invariant over the generated transitions. This does not add
reachability to `At` or the getters themselves.

Statements stay source-facing; proof bodies still depend on generated transition
names and may need updating after compiler changes. Independent component compilations can use distinct namespaces. A separately
checked embedding transfers their summaries into a larger compilation unit,
preserving exact heaps and clocks. The Fibonacci Dijkstra example reuses the
standalone queue proof this way; see [modular proofs](../../docs/MODULAR_PROOFS.md).

The [Fibonacci Dijkstra guide](../../docs/FIBONACCI_DIJKSTRA.md) explains the
complete heap interface, proof layers, amortized potential, and event-cost
model. Its public queue theorems expose contents and a storage footprint, while
local helper lemmas contain the ring and transition details.

## Navigate an analysis

The editor's **Main results** section offers **Correctness** and **Running time**
buttons for the guarantees proved in an analysis. Selecting a result displays its exact theorem statement from the
Lean source and its documentation comment, when present. **Go to proof** jumps
to that declaration in the analysis editor. Use **All theorems** to browse the
file's theorems and helper lemmas, including declarations without a result
button.

To mark a result in your own analysis, add a line comment immediately before
its `theorem` or `lemma` declaration, or immediately before the declaration's
`/-- ... -/` documentation comment:

```lean
-- Main result: Correctness
```

Use `Running time` for a cost theorem. If one theorem proves both guarantees,
use `Correctness and running time`: the editor shows two short buttons that open
the same statement. Each category appears once, using its first marked theorem;
alternate results remain available in **All theorems**. Custom analyses can use
other descriptive labels. The declaration name remains visible in the preview.
The [factorial analysis](factorial.lean) demonstrates placing the marker before
a theorem's documentation comment.

When a saved proof matches a bundled example except for comments and formatting,
the editor uses the current example's selected categories. This removes outdated
helper highlights and updates old labels without changing any saved proof text.
Marker comments on otherwise unchanged bundled code therefore do not override
the curated selection. Older or edited proofs can also recover the label of an
individual theorem when its namespace, name, and complete statement match a
bundled result. Changes to proof bodies or surrounding helper lemmas do not hide
that result. The actual statement is displayed unchanged. Different or ambiguous
statements retain their explicit markers instead of receiving an inferred label.
An older proof without a runtime theorem shows only its correctness result.

These ordinary Lean comments affect editor navigation only. The preview reads
the current source and does not imply that Lean has accepted it; use **Check
analysis** to check the proof against the current algorithm.

## Check an analysis

From the repository root, with Lean 4.26 installed:

```sh
python3 -m algo2lean analyze examples/factorial.algo examples/analysis/factorial.lean
python3 -m algo2lean analyze examples/sequences.algo examples/analysis/sequences.lean
```

The command compiles the algorithm and its named-line interface into two
temporary modules, builds their `.olean` files, and checks the analysis as a
separate importing module. It does not concatenate
the source files or modify either input. Diagnostics use the analysis's own line
numbers. Reported `sorry` warnings make the check unsuccessful. Like ordinary
Lean checking, this respects declared assumptions and options. It does not audit
proof completeness: suppressed warnings and explicitly introduced axioms are
not independently rejected. The included analyses use neither placeholder
proofs nor extra axioms.

The module name is the source filename in Pascal case with `Generated` appended:
`factorial.algo` becomes `FactorialGenerated`, and its analysis begins with
`import FactorialGenerated`. Analyses that use named locations or getters import
the companion instead, such as `import GcdGeneratedPoints`; this imports the
algorithm as well. To work in your own Lean project, export the algorithm to
`FactorialGenerated.lean`. The compiler also writes `FactorialGeneratedPoints.lean`.
Add these and `Algo2Lean.lean` to the project and build the imported modules
before checking the analysis. For a fixed theorem statement with editable
proof labels, see [the module separation guide](../../docs/NAMED_POINTS.md).

```sh
python3 -m algo2lean compile examples/factorial.algo -o FactorialGenerated.lean
python3 -m algo2lean library -o /path/to/project/Algo2Lean.lean
```

In the local editor, choosing an example also loads its analysis. Use **Check
analysis** in the separate pane to check the current pair, and **Save analysis**
to keep the proof file. Source and analysis drafts are recovered together. The
pane provides whole-file checking and clickable diagnostics; it does not yet
provide live Lean goals or completion.

The automated suite checks every analysis in this folder against the current
compiler. No extra axioms, placeholder proofs, or test-specific proof tactics
are used in these files.

## CLRS Chapter 4 (§4.1–4.4)

See the [Chapter 4 guide](../../docs/CLRS_CHAPTER_4.md) for the main theorem
names, exact specifications, and runtime model. The Strassen analysis bundles
maintained proof modules so it works directly in the editor.

The [§4.3–4.4 recurrence library](../../docs/RECURRENCES.md) is checked as
separate reusable modules. Its source-linked Strassen application sharpens the
total work upper bound to `13*7^k`; the editor analysis retains its valid
`33*7^k` theorem.

The matrix analyses and recurrence modules use Lean/Std alone. Their public
execution results use scoped relations such as `strassen.ReturnsWithCost`.
The master theorem is outside the current Chapter 4 scope.
