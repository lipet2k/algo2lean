# CLRS parallel merge and merge sort

`parallel_merge.algo` implements the divide-and-conquer merge and merge sort from
CLRS, fourth edition, **Section 26.3**, within the development compiler's
structured fork–join model. [CLRS table of contents](https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/4e_toc.pdf)

## Algorithms and contracts

- `binary_search` returns a relative lower-bound position: entries before it are
  strictly smaller than the key, and entries after it are at least the key.
- `p_merge` merges two sorted input intervals into a caller-provided output
  interval. It selects the median of the longer input, binary-searches that key
  in the other input, writes the pivot at its final position, and forks the two
  disjoint remaining merges.
- `sort_into` recursively sorts disjoint halves and invokes `p_merge`, alternating
  two caller-provided output/scratch buffers between recursion levels.
- `parallel_merge` allocates and returns a fresh merged sequence, starting at zero.
- `parallel_merge_sort` allocates two fresh buffers and returns the sorted interval
  at the same indices as the original input.

Input lengths in the formal contracts are nonnegative. Values and starting
indices are arbitrary integers; lengths need not be powers of two. Equal values
are supported, and the permutation specifications retain every multiplicity.
No stability result for distinguishable equal keys is claimed.

The input intervals to merge may overlap: both are read-only, and the result
contains the multiset of both intervals. The preallocated output must be distinct
from the input. For `sort_into`, source, output, and scratch must be three distinct
allocated references. Writes remain within the specified output/buffer interval;
all other sequence contents, object/collection storage, and caller counters are
preserved. The allocating wrappers return fresh output and retain zero outside
their requested output interval.

The proof modules separate the binary search, merge, sorting recursion, and
allocating wrapper contracts. Each source-connected contract relates correctness,
storage effects, termination, access compatibility, work, and span to the same
completed `ParallelCall`. The generated `ParallelCall.call` bridge also exposes
its ordinary sequential serialization.

The public entry-point results are `ParallelMergePublic.correctness` and
`ParallelMergePublic.running_time` for merge, and
`ParallelMergeSortPublic.correctness` and `ParallelMergeSortPublic.running_time`
for merge sort. Each namespace also exposes `call_contract` for reuse and
`running_time_explicit` for concrete work/span bounds. In the editor, choose the
qualified theorem in the theorem selector to inspect either algorithm: the
overview shows one result per category, while the selector retains both.

The proved asymptotic bounds are:

| Operation | Work | Span |
| --- | --- | --- |
| Binary search | O(log(n + 1)) | O(log(n + 1)) |
| Parallel merge, total input size n | O(n) | O(log²(n + 1)) |
| Parallel merge sort | O(n log(n + 1)) | O(log³(n + 1)) |

The concrete inequalities include additive constants for empty inputs. Costs count
lowered instructions, calls, returns, and fork/join operations. Arithmetic on
mathematical integers and constant-sequence allocation use the compiler's unit
cost. These are work/span bounds, with no processor scheduler or elapsed-time
claim. See [the fork–join guide](../../docs/PARALLEL_ALGORITHMS.md).

## Differences from the textbook representation

The source retains CLRS's median/binary-search partition and parallel recursive
merge structure. Intervals use a start and a length rather than inclusive
endpoints. For an even-sized longer interval, `lo + n // 2` selects its upper
median; CLRS's inclusive-endpoint formula selects the lower median. Both
partitions retain the required balance and asymptotic bounds. `fork_join`
expresses a pair of spawned calls followed by their join.

The textbook's recursive merge sort allocates temporary storage during recursion.
This version allocates two buffers before entering a fork and alternates their
roles. Recursive calls still sort the two halves before parallel merging. This
storage arrangement satisfies the current fork model's prohibition on allocation
inside a child while avoiding a sequential copying pass at every level.

## Check and export

From the repository root, with the pinned Lean toolchain installed:

```sh
python3 scripts/check_parallel_merge_examples.py
python3 scripts/check_parallel_merge_examples.py --write-analysis /tmp/ParallelMergeAnalysis.lean --export /tmp/parallel-merge-analysis.zip
python3 -m unittest tests.test_parallel_merge -v
```

The script compiles the current source, combines the exact proof bodies into one
editor analysis, checks the result, and audits its principal theorem axioms.
Local imports become their proof bodies; shared libraries remain imported. The
combined analysis can be pasted into the editor alongside `parallel_merge.algo`.
The exported ZIP includes the generated program, analysis, and shared libraries;
`lake --no-cache build` checks it in an isolated directory without this checkout.

Executable regressions cover all ternary arrays through length seven, every pair
of sorted ternary arrays through length five, shifted intervals, overlapping input
slices, duplicate keys, empty inputs, large integer values, and prepopulated
buffer boundaries. These finite checks complement the general Lean proofs.
