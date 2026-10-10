# General finite-interval library composition

The main example combines the repository's existing merge sort and binary
lower-bound search over arbitrary finite intervals of an infinite integer
sequence. It covers negative indices, duplicate values, and empty or reversed
bounds, then exposes the verified composition to a further external caller.

| Module | Independently proved behavior |
| --- | --- |
| `general_merge_sort` | Termination, sorted permutation, preservation outside the interval and of pre-existing sequence references, and exact sorting work with an O(n log n) bound |
| `general_binary_lower_bound` | Termination, the unique lower-bound partition on sorted input, and preservation of the whole heap |
| `general_sort_then_search` | Actual imported sorting and binary-search calls satisfy both specifications together and retain the sorting-work bound |
| `general_consumer` | An external caller imports the verified composition and returns its insertion offset |

`general_merge_sort.algo` and `general_binary_lower_bound.algo` are byte-identical
copies of the existing `examples/merge_sort.algo` and `examples/lower_bound.algo`
sources. Their analyses migrate the existing complete proofs into independent
module namespaces. Generated
Facts supply determinism without comparing every pair of transition rules.

`Algo2LeanLib.SequenceModel` contains the common finite-interval model. Its
`sorted_indices` lemma turns sorting's list-based sortedness into the index-wise
order expected by the existing binary-search proof. A short wrapper reuses that
proof and normalizes empty or reversed intervals to length zero; it does not
repeat the binary-search invariant or termination argument.

`GeneralSortThenSearchAnalysis.summary` imports the sort and search summaries.
It records a valid sorted result reference, the sorted permutation, the
lower-bound partition, preservation of all pre-existing sequences, exact sorting
work, and preservation of every clock other than `"merge_sort"`.
`GeneralConsumerAnalysis.summary` imports that complete composition
unchanged. Both analyses prove their specifications for every completed execution
through `eq_of_summary`, as well as constructing terminating executions.

Merge sort increments `"merge_sort"` once per sort call and once per merged
output write. For normalized interval length `n = (hi - lo).toNat`, its exact
count is `GeneralMergeSortAnalysis.runtime n`, bounded by
`2 * n * (Nat.log2 n + 1) + 1`. The recurrence and its bound are proved once in
`Algo2LeanLib.MergeSortCost`; the caller reuses the algorithm's checked clock
contract. These are abstract operation counts: `Seq` values are mathematical
infinite sequences, and `copy(a)` creates a heap snapshot rather than modeling
an eager copy of infinitely many cells.

Binary search has no ticks. `GeneralSortThenSearchAnalysis.running_time`
therefore bounds only the sorting phase, and appears in **All theorems** rather
than as a **Running time** result button. This composition does not yet claim a
total sort-plus-binary-search runtime bound.

A separate linear-search composition includes costs for both phases:

| Module | Role |
| --- | --- |
| `general_lower_bound` | Linear search with at most `(hi - lo).toNat` recorded comparisons |
| `general_linear_sort_then_search` | Reuses the sorting-work and search-comparison contracts and bounds their sum |
| `general_linear_consumer` | Reuses the complete linear composition, including both clock guarantees |

Both counters measure increments from arbitrary initial clock values. Sorting
preserves `"search_comparisons"`, searching preserves `"merge_sort"`, and the
composition preserves every other clock. The **Running time** theorem in
`GeneralLinearSortThenSearchAnalysis` bounds their sum on the same execution by
`2 * n * (Nat.log2 n + 1) + n + 1`. Empty or reversed intervals charge one sort
call and no search comparisons. A bounded three-entry example is also
available separately.

From the repository root:

```sh
python3 -m algo2lean analyze examples/modules/general_consumer.algo \
  examples/modules/analysis/general_consumer.lean --project examples/modules
python3 -m algo2lean analyze examples/modules/general_linear_consumer.algo \
  examples/modules/analysis/general_linear_consumer.lean --project examples/modules
python3 -m unittest tests.test_general_module_composition -v
```

The checker imports and checks the actual component analyses. Each component
can also be checked independently with its matching source and analysis file.
