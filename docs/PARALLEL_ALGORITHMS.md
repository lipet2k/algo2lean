# Structured fork–join algorithms

Algo2Lean supports deterministic, structured fork–join calls within a source
file and across concrete module imports. A fork starts two function calls and joins them before
returning their pair of results. The generated Lean interface records the
returned value, final heap, work, span, and memory accesses in the same completed
evaluation.

## Source syntax

```python
def sum(a: Seq, lo: Int, n: Int) -> Int:
    if n <= 0:
        return 0
    if n == 1:
        return a[lo]
    half: Int = n // 2
    left, right = fork_join(sum(a, lo, half), sum(a, lo + half, n - half))
    return left + right
```

`fork_join` takes exactly two calls to named source functions and returns a
heterogeneous tuple of their return types. Recursive calls are allowed. The
arguments to the left call are evaluated first, then the arguments to the right
call, before either child begins. After both children return, the parent resumes.
Ordinary calls remain sequential.

This implementation supports `Int`, `Bool`, ordinary integer-valued `Seq`,
arrays of integer rows (`Seq[Seq]`), `None`, and tuples of these types. It rejects
random choices within parallel callees, classes, other typed sequences (including deeper
nesting), finite collections, real values, and abstract interface bindings for
fork–join programs. These restrictions
are diagnosed explicitly; unsupported parallel code is not silently compiled as
sequential-only code.

Concrete module imports and mutually recursive source modules are supported.
An imported child can appear directly in `fork_join`; the compiler supplies its
small forwarding boundary. That boundary contains a call and return, adding two
instructions to that child's work and span. The original callee's cost and
access record are retained without copying its instructions. All fork arguments
are captured before either child runs.

In project mode, import `Algo.<module>.Parallel` to use the parallel contracts.
The ordinary `Generated` module remains independent of the parallel library.
Single-file compilation includes the contracts when its source contains a fork.
The editor exposes project contracts in the **Parallel contracts** view.

## Reuse across deterministic, parallel, and randomized analyses

The common functional interface is `f.Call before input after output`.
`f.ParallelCall` adds work/span and access evidence for that same heap and result.
Its `call` theorem produces the ordinary contract. For certified deterministic
functions, `f.Call.hasLaw` and `f.Call.expectedReturn` then reuse that contract in
the optional probability layer. No new correctness proof is needed.

Determinism follows reachable function calls, including imported calls. A pure
function beside an unrelated random function retains these adapters; recursive
pure groups do too. Random draws within a parallel child remain unsupported.
The functional probability adapter describes the sequential serialization,
not a distribution over schedules or processor elapsed times.

The [imported-contract fixture](../tests/fixtures/parallel_imports) proves a
mutating helper once with Std, reuses it twice on disjoint cells of one shared
array, and exports a parallel call with work 22, span 16, and two counter
increments. A randomized caller reuses that proof to obtain its joint
heap/output law. Its exported Lake project rebuilds all three layers from
source.

## Execution and safety

For a source function `f`, `f.ParallelCall` relates the initial heap and arguments
to the final heap, returned value, `Algo2LeanParallel.Cost`, and
`Algo2LeanParallel.Access`. The parallel declarations live in the stable generated
algorithm file. Changing named labels does not change them.

The structured evaluation records a canonical left-to-right serialization of
the two children. Its fork rule additionally requires that their recorded
memory accesses are compatible before assigning parallel span:

- Multiple children may read the same cell.
- Neither child may write a cell that the other reads or writes.
- A cell is identified by its actual sequence reference and integer index.
  Renaming an alias does not establish independence. For `a[i][j]`, the access
  record includes the outer row-reference slot `a[i]` and the actual inner cell.
  Changing a row reference can therefore conflict with another child reading it.
  `const(row)` shares that same row at every index; it does not create distinct rows.
- Neither child may allocate, including allocations in nested calls. Allocate
  scratch/output sequences before entering the fork.

Access records combine accesses throughout the execution. A write followed by a
restoring write still counts as a write. Pure conditional and short-circuit
expressions may conservatively record reads in branches that are not selected;
this can require stronger independence assumptions, but does not permit an
unrecorded conflicting access.

Compilation alone does not prove a program race-free. The ordinary `f.Call`
interface describes sequential serialization; a proof of `f.ParallelCall` must
also discharge the fork compatibility obligations. The implementation does not
model unrestricted threads, locks, atomic operations, an arbitrary interleaving
scheduler, or operating-system execution.

## Work and span

Work counts the total modeled operations. Span counts the longest dependency
chain. Costs are derived from lowered instructions, rather than supplied as
independent annotations:

| Instruction/composition | Work | Span |
| --- | --- | --- |
| Primitive step, call entry, or return | 1 | 1 |
| Sequential segments A then B | `A.work + B.work` | `A.span + B.span` |
| Fork A and B, including their join | `A.work + B.work + 2` | `max A.span B.span + 2` |

The fork's continuation is composed sequentially after that join. Argument
preparation is included in the parent-side instructions. A source statement may
lower to several instructions; these costs are therefore distinct from source
line counts. Existing named `tick` clocks retain their operation-count meaning
and are not the work/span fields. Tick clocks are additive ghost counters:
increments from both children accumulate; they do not serialize the children
or determine span.

This is an abstract unit-cost model for mathematical values and storage. In
particular, integer arithmetic and the model's constant-sequence allocation are
unit-cost operations. It is not a bit-complexity or physical-memory model. No
processor-count scheduling theorem or elapsed-time guarantee is asserted here.

## Examples and checked contracts

[`examples/parallel/parallel.algo`](../examples/parallel/parallel.algo) contains:

- `parallel_sum`: the sum over an arbitrary integer-indexed interval.
- `upsweep`: writes balanced subtree totals into a preallocated scratch sequence.
- `downsweep`: propagates preceding totals to disjoint output intervals.
- `prefix_sum`: allocates scratch and output storage, runs the two phases, and
  returns a fresh sequence of **exclusive** prefixes.

For `[2, -1, 4]`, the exclusive prefix result is `[0, 2, 1]`. A nonpositive length
denotes an empty interval. Non-power-of-two lengths split into floor and ceiling
halves. The original input remains unchanged.

The checked analyses establish source-connected contracts for `parallel_sum`,
`upsweep`, `downsweep`, and the complete `prefix_sum` wrapper. Correctness,
independence, heap effects, and costs describe the same completed generated
execution. Their main runtime theorems quantify a positive uniform constant;
concrete bounds are also available:

| Algorithm | Work | Span | Length contract |
| --- | --- | --- | --- |
| `parallel_sum` | `≤ 36 * (n.toNat + 1)` | `≤ 36 * (Nat.log2 n.toNat + 1)` | Any integer `n` |
| `prefix_sum` | `≤ 128 * (n + 1)` | `≤ 128 * (Nat.log2 n + 1)` | Natural `n`, or integer `n ≥ 0` |

Here `Nat.log2 0 = 0`, so these bounds include the empty input. Both algorithms
have O(n) work and O(log(n + 1)) span. The prefix implementation also treats
negative lengths as empty, as checked by executable regressions, but its general
Lean contract requires a nonnegative length.

`parallel_sum` leaves the complete heap unchanged. `prefix_sum` allocates two
sequences (scratch and output), returns the fresh output reference, preserves all
caller-owned sequences, objects, collections, and clocks, and leaves output cells
outside the requested interval equal to zero. Neither theorem requires a
power-of-two length.

The mathematical balanced-tree lemmas in `Algo2LeanLib/ParallelBounds.lean` are
connected to the source by the traversal proofs; they are not standalone
surrogates for an algorithm runtime proof. The
[example instructions](../examples/parallel/README.md) explain how to check and
export the complete analysis. The principal theorem audit uses only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms, with no unfinished
proofs or additional axioms.

Regression tests execute the canonical serialization on exhaustive small signed
arrays, negative/zero lengths, shifted intervals, and large mathematical integers.
Lean checks and isolated exported builds validate generated definitions and proof
sources separately from those executable regressions.

## CLRS parallel merge and merge sort

[`examples/parallel_merge/parallel_merge.algo`](../examples/parallel_merge/parallel_merge.algo)
implements CLRS fourth-edition Section 26.3 using median selection, binary search,
and two disjoint recursive merges. Merge sort alternates two preallocated buffers
and reuses the verified merge contract at each recursion level.

| Algorithm | Work | Span |
| --- | --- | --- |
| Parallel merge, total input size n | O(n) | O(log²(n + 1)) |
| Parallel merge sort | O(n log(n + 1)) | O(log³(n + 1)) |

The generated-source contracts prove termination, sortedness, exact multiplicity
preservation, and these costs for the same execution. They cover nonnegative
lengths, arbitrary integer values and starting indices, duplicate keys, and
non-power-of-two sizes. The allocating entry points preserve all caller-owned
storage and counters, return fresh output, and leave that output zero outside
the result interval. Main runtime theorems quantify a uniform positive constant;
explicit bounds are retained for reuse.

The [example guide](../examples/parallel_merge/README.md) documents the
preallocated-buffer adaptation, median convention, alias preconditions, proof
modules, and standalone export checks. The unit-cost and scheduler limitations
above apply to these algorithms as well.

## Parallel matrix multiplication with nested arrays

[`examples/parallel_matrix/parallel_matrix.algo`](../examples/parallel_matrix/parallel_matrix.algo)
uses `Seq[Seq]` matrices and balanced fork–join trees across rows, columns, and
dot-product terms. The input matrices and their rows may share references.
Writable output rows must be distinct and disjoint from input rows.

| Entry point | Work | Span |
| --- | --- | --- |
| Preallocated `parallel_matrix_multiply_into` | O(n³) | O(log(n + 1)) |
| Fresh-output `parallel_matrix_multiply` | O(n³) | O(n + log(n + 1)) |

Both contracts cover every nonnegative dimension, including zero and uneven
sizes, with mathematical integer entries. They connect termination, the finite
row-by-column product, storage preservation, and costs to the same generated
execution. The allocating wrapper creates a fresh outer array, n independent
output rows, and one zero default row. Caller-owned storage and counters are
preserved, and output values outside the result rectangle remain zero.

Row allocation is sequential because fork children may not allocate. Its span
is included in the fresh-output bound; reusing an already allocated matrix
permits the logarithmic computation span. The [example guide](../examples/parallel_matrix/README.md)
explains representation assumptions, reusable proof modules, and export checks.
