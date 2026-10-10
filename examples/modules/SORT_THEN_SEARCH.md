# A bounded sort-then-search composition

This acceptance example sorts **exactly three adjacent entries** of an infinite
integer sequence, then finds the first entry at least a supplied key. The first
index can be any integer, including a negative index. Duplicate values and keys
outside the three-value range are covered.

The modules and their companion Lean analyses are independent:

| Source | Reused proof | New conclusion |
| --- | --- | --- |
| `compare_exchange.algo` | — | One comparison, optional exchange, preserved surrounding data |
| `sort_three.algo` | `CompareExchangeAnalysis.summary`, three times | Sorted values, permutation, exactly three comparisons |
| `lower_bound_three.algo` | — | Lower-bound partition, one to three comparisons, preserved data |
| `sorted_search_three.algo` | Both sorting and searching summaries | Termination, sorting, lower bound, mutation preservation and combined cost |

`SortedSearchThreeAnalysis.correct` describes every completed execution.
Its `Correct` specification includes sortedness, permutation of the original
three values, the lower-bound partition, exactly three sorting comparisons,
at most three searching comparisons, and preservation of all entries outside
the three-element interval and in other sequence objects. Existing clock values
are arbitrary, and `other_clocks` preserves unrelated counters.
`comparisons_le_six` gives the combined bound of at most six comparisons.

The final caller never opens a comparison or search branch. Its analysis imports
the existing component summaries; `sort_three` is itself a verified composition
reused by that caller. Generated definitions and optional analysis imports remain
separate.

This is an intermediate composability milestone. It does not claim a general
insertion-sort or merge-sort correctness/runtime theorem. General finite-interval
sorting and search remain later acceptance examples.

From the repository root:

```sh
python3 -m algo2lean analyze examples/modules/sorted_search_three.algo \
  examples/modules/analysis/sorted_search_three.lean --project examples/modules
```

Each component can also be checked on its own by substituting its source and
analysis filename in that command.
