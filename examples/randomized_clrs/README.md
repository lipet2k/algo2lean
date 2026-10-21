# Randomized algorithms from CLRS

These sources follow *Introduction to Algorithms*, fourth edition, using the
experimental Algo2Lean development compiler. They exercise mutable sequences,
separately imported algorithms, recursion, finite sets, and random stopping
times. The section references follow the publisher's
[table of contents](https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/4e_toc.pdf).

`randint(a, b)` draws uniformly from the integers `a <= value < b`. Array intervals
are likewise half-open. An infinite mathematical `Seq` supplies all integer
indices; a length argument specifies the finite interval relevant to an
algorithm. Mutation is shared with the caller.

| File | Algorithm | CLRS section |
| --- | --- | --- |
| `shuffle.algo` | RANDOMIZE-IN-PLACE, also called Fisher-Yates shuffle | 5.3 |
| `hiring.algo` | HIRE-ASSISTANT and RANDOMIZED-HIRE-ASSISTANT | 5.1-5.3 |
| `partition.algo` | PARTITION and RANDOMIZED-PARTITION | 7.1, 7.3 |
| `selection.algo` | RANDOMIZED-SELECT | 9.2 |
| `quicksort.algo` | RANDOMIZED-QUICKSORT | 7.3-7.4 |
| `coupon_collector.algo` | Repeated draws until every coupon type has appeared | 5.4 |

`hiring.algo` imports the shuffle. Selection and quicksort both import the same
randomized partition. Their analyses should reuse the imported contracts,
including mutation and cost, instead of inspecting the callee's transitions.

## Source conventions

The shuffle acts on `[0, n)`. Its explicit `i = 0; while i < n; i += 1`
spells out the textbook loop counter so local Lean invariants can observe all
loop state through `Local.i`. A `for` loop also has an internal iteration cursor,
which a source-variable getter does not expose. No compiler-specific state is
needed in the shuffle helper statements. Hiring and partition use the same
explicit-loop convention for their local invariants.

As in RANDOMIZE-IN-PLACE, its last iteration draws
from a singleton interval and swaps that position with itself. Thus, for `n >= 0`,
it performs exactly `n` random-draw operations and `n` swaps.

Hiring counts strict improvements in candidate score. It hires the first
candidate directly, avoiding a fictitious sentinel of score minus infinity.
For `n <= 0` it returns zero. Randomized hiring permutes the supplied candidates
in place before scanning them. Distinct scores are the precondition for the
usual exact harmonic-number expectation.

Partition uses the final element of `[lo, hi)` as the pivot and requires
`lo < hi`. Randomized partition first moves a uniformly selected element into
that position. Selection accepts a **zero-based rank relative to the interval**;
its precondition is `0 <= rank < hi - lo`. Sorting and selection allow equal
values, but the usual quicksort comparison expectation and the initial linear
selection analysis use distinct values. The textbook two-way partition can be
quadratic when all keys are equal.

Coupon collection returns both the mutable set of collected coupon types and
the number of draws. For `n <= 0` it immediately returns an empty set and zero.
For `n > 0`, an individual infinite sequence of draws may omit a coupon forever;
almost-sure termination is a probabilistic theorem, not a deterministic bound
on every possible execution.

## Explicit costs

The clocks record operations named by the source:

| Clock | One unit represents |
| --- | --- |
| `random_draws` | One completed call to `randint`, including a singleton draw |
| `swaps` | One sequence exchange, including an exchange of a cell with itself |
| `comparisons` | One element-to-pivot comparison in PARTITION |
| `interviews` | One candidate inspected by HIRE-ASSISTANT |
| `hires` | One strict new record, counting the first candidate |
| `selection_calls` | One invocation of RANDOMIZED-SELECT |
| `quicksort_calls` | One invocation of RANDOMIZED-QUICKSORT, including a base case |

Counters begin at the caller's actual initial values. A contract bounds their
increments, and callers can assign nonnegative weights to the operations.
Counting a set operation or random draw does not establish the machine cost of
an underlying set implementation or random-number generator. Integer bit
complexity is outside this unit-operation model.

## Checked results

All six source programs have Lean-checked analyses connected to the generated
execution semantics. Write `H_n = sum_{i=1}^n 1/i`, with `H_0 = 0`.

| Analysis | Correctness | Running time in the explicit cost model |
| --- | --- | --- |
| [Shuffle](analysis/shuffle.lean) | Uniform positional permutation; each permutation has probability `1/n!` for distinct values | Exactly `n` draws and `n` swaps |
| [Hiring](analysis/hiring.lean) | Returns the number of strict score records after shuffling | Expected hires `H_n` for distinct scores; interviews, draws, and swaps each number `n` |
| [Partition](analysis/partition.lean) | Correct partition and preserved multiset; uniform pivot rank for distinct keys | Exactly `n-1` comparisons, one random draw, and at most `n+1` swaps |
| [Selection](analysis/selection.lean) | Returns the requested order statistic for distinct keys | Expected comparisons at most `4n`; comparisons, swaps, draws, and calls together at most `12n` |
| [Quicksort](analysis/quicksort.lean) | Sorted permutation, including repeated keys | For distinct keys, expected comparisons `C_n = 2(n+1)H_n-4n`; all four charged operations together at most `2C_n+5n+1` |
| [Coupon collector](analysis/coupon_collector.lean) | For `n>0`, returns exactly the set of types `[0,n)` with probability one | Expected draws `n H_n`; `Pr(draws > t) <= n(1-1/n)^t` for natural `t` |

These runtime expectations concern complete execution paths. They retain work
on unsuccessful and nonterminating paths; they do not condition on return.
All contracts measure increments from the supplied heap's actual counters.
Quicksort's logarithmic comparison bound and selection's weighted-operation
bound are also available in their analysis helpers. The displayed correctness
and running-time results have simple markers for navigation in the editor.

The reusable `shuffle_law`, `randomized_hiring_law`, `randomized_partition_law`, `selection_law`, and
`quicksort_law` contracts specify joint final-heap/output distributions through
`HasLaw`. Selection and quicksort reuse partition's contract, preserving
correlations between the pivot, rearranged sequence, and operation counts.
Their source-law and termination proofs allow repeated values, while the initial
selection correctness theorem and both recursive runtime analyses assume
distinct keys. The coupon collector instead uses finite-prefix probabilities
and stopped expectations to handle its unbounded stopping time. Its
`total_clock_reward` helper supports arbitrary measurable nonnegative functions
of the total draw cost.

Sequence analyses establish interval permutation and preservation of outside
storage in their model contracts. The coupon result identifies the fresh set
reference and its exact contents. The current guarantees do not claim a machine
implementation cost for mathematical integers or finite sets.

Proof files keep the short main results separate from model counting,
recurrences, and local source-transition reasoning. For example, the coupon
collector's main file imports `coupon_contract.lean`; the latter connects the
generated loop to `coupon_model.lean` and `coupon_expectation.lean`. The shared
`CallRewards` tail-sum theorem derives its mean from source draw-count tails.

## Proof organization

1. Prove a source-facing shuffle-step contract for a chosen position, including
   heap framing and exact counter increments. Lift it to the uniform finite
   permutation law by induction on the remaining interval.
2. Analyze the deterministic hiring scan as a record-count function. Reuse the
   imported shuffle law and sum the record indicators to derive `H_n`.
3. Prove deterministic partition once. Randomized partition composes a uniform
   draw, a swap, and that contract. Selection and quicksort then use only the
   completed partition contract and their mathematical recurrences.
4. For coupon collection, connect the loop to finite uniform-draw experiments.
   Prove almost-sure completion from their tails, then use the tail-sum identity
   to obtain the exact expectation. This validates unbounded execution and
   runtime observables.
5. Expose correctness and running-time results as concise named corollaries.
   Keep transition inspection in local helper proof bodies; statements should
   use public call, location, heap, and probability interfaces.

Compile a project from the repository root, for example:

```sh
python3 -m algo2lean compile examples/randomized_clrs/hiring.algo \
  --project examples/randomized_clrs --output-dir /tmp/clrs-hiring --check
```

`--check` checks the generated algorithm definitions and named observations.
Probability companions additionally require the pinned optional Mathlib setup
in `probability/`; see the [probability guide](../../probability/README.md).
