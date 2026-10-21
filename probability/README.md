# Probability analysis

This optional Lean package gives probabilistic meaning to the finite choices
generated for randomized algorithms. Deterministic algorithm definitions and
their ordinary proofs do not import Mathlib.

The package pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. From this directory, run:

```sh
lake update
lake exe cache get
lake build
```

The cache command downloads precompiled dependencies. After setup, checking an
Algo2Lean probability analysis reuses those dependencies.

## Execution semantics

`Choice.uniform a b resume` chooses uniformly from the integers satisfying
`a ≤ value < b`. Bounds may depend on the current configuration. Each invocation
uses a fresh draw conditional on the current configuration. An empty interval
(`b ≤ a`) is an error.

`execution next initial` is a probability measure on infinite runs. Successful
termination repeats its final configuration; error enters the absorbing `none`
state. This padding adds no source instructions or clock increments. An infinite
nonterminating execution remains represented instead of being discarded or
conditioned away. `choiceLaw_support` relates the probability distribution to
the allowed source transitions, with an explicit exception for terminal padding.

The mathematical heap and call continuations need not be countable.
`SampleState` supplies a discrete measurable structure, and Mathlib's
Ionescu–Tulcea construction builds the path law. The full path space has its
product measurable structure; arbitrary predicates on an infinite run are not
automatically measurable.

## Analysis interface

- `Event.atTime n P`, `Event.ever P`, `Event.always P`, and `Event.within n P`
  turn arbitrary predicates of one configuration into measurable path events.
- `Event.returnsWhere observe post` expresses successful return satisfying a
  joint heap/output postcondition. `probability law event` is unconditional:
  nontermination and failure do not cause success probabilities to be rescaled.
- `Observable.atTime n value` observes one configuration.
  `Observable.total counter` takes the supremum of the counter over finite
  prefixes, including execution prefixes before an error. For monotone tick
  counters this is total cost.
- `expected law observation` is nonnegative expectation and may be infinite.
  `expectedReal law value integrable` requires a proof of integrability before
  returning a signed real expectation.
- Custom `Event` and `Observable` values can be built by supplying their
  measurability proofs. The underlying Mathlib measure remains available for
  more advanced analyses.

Import `Algo2LeanProbability.Observations` for products, joint rewards, and
moments of observations. `Event.exceeds observation threshold` describes a
runtime tail or any other nonnegative reward exceeding a threshold.
`probability_exceeds_le` gives Markov's bound, and
`costProbability_le_moment` uses a higher moment. The underlying cost observation
takes the supremum over finite prefixes: work before a failure is preserved,
and endlessly increasing charged work has infinite cost. Finite expected cost
implies almost-sure finite charged cost; it does not imply termination when a
loop can run without ticking.

Import `Algo2LeanProbability.Call` for stopped-call reasoning. `callExpected`
accepts an observer of the completed output and any nonnegative reward. It is
the increasing limit of first-return rewards within finite transition bounds.
`HasLaw` specifies all such rewards using one joint output PMF; taking reward
one yields probability-one successful return. Partial functions can instead
be specified directly through their unconditional `callExpected` values.
`Stopped.expected_first_return` decomposes an arbitrary-length computation at
an earlier boundary, while `Stopped.expected_map` transports a contract through
a probability-preserving embedding. The latter checks transitions only before
the boundary, allowing the caller to continue after the callee returns.

For actual generated call sites, import `Algo2LeanProbability.CallContext`.
`callExpected_with_stack` handles calls within a module and recursive calls;
`callExpected_import` handles separately compiled modules. They preserve the
actual heap, counters, and suspended caller frames. Supply the returned-value
continuation and the generated delegation/context equation. The shared theorem
handles stopping boundaries and rejected return tags. `pmfExpected_congr_support`
lets that continuation use the callee's guarantees only on possible results.

`Algo2LeanProbability.StoppedRules` provides `expected_le_on` and
`expected_unique_on` for local equations on a preserved invariant. Malformed or
unreachable states outside the invariant need no extra proof cases. Uniqueness
requires a finite bound and almost-sure stopping; a recurrence alone cannot
justify an expectation for an unbounded loop.

`Algo2LeanProbability.CallRewards` provides addition and countable-sum rules
for completed-call rewards. In particular, `callExpected_nat_tail_sum` proves
that the expectation of a natural-valued returned quantity is the sum of its
strict tail probabilities. These rules allow infinite expectations and require
no termination assumption: an unsuccessful call contributes zero to both sides.
For a total-runtime claim, first justify agreement with the completed reward
using `CallObservations`. The coupon-collector analysis uses this route to derive
its expected draw count from source-level tail probabilities.
The same optional module supplies `pmfExpected_const`, `pmfExpected_add`,
`pmfExpected_mul`, and `pmfExpected_mono_support` for routine reward arithmetic.
`HasLaw.probability_one` turns a property of all supported outcomes into a
probability-one completed-call guarantee. These helpers let an analysis reuse
the joint law without repeating sum manipulations for each correctness result.

`execution_marginal` and `probability_atTime` reduce full-path statements at time
`n` to the recursively defined `finiteLaw`. `finiteLaw_one` and `finiteLaw_succ`
expose local probability calculations. `finiteLaw_eq_toMeasure` also converts
these finite laws to `finitePMF`, whose recursion uses ordinary `PMF.bind`. `uniformInt_mass` gives probability
`1 / (b-a)` for each allowed integer; `uniformInt_expected` reduces a draw's
nonnegative expectation to a finite sum. `probability_ever` expresses eventual
events as increasing limits of their bounded-time probabilities.
`probability_ever_of_preserved` reduces locally preserved events, such as a
successful return, to the supremum of their finite-state probabilities. For an
algorithm known to stop by time `n`, `probability_ever_of_stopped` gives its
eventual return probability directly from `finiteLaw` at time `n`; no analysis
of arbitrary infinite traces is required. `finiteLaw_stable` justifies the
finite bound by preserving the state law after absorption.

`choiceLaw_map` proves exact preservation of a local choice distribution under
a caller embedding. This is stronger than preserving possible transitions.
Completed-call composition is provided separately by the stopped-expectation
module. Its local transition premise must be established for the actual caller
embedding; support equality alone is insufficient to preserve probabilities.

## Connecting return rewards and total runtime

`Algo2LeanProbability.CallObservations` supplies
`expected_total_eq_callExpected` and `costProbability_eq_callProbability`.
Under almost-sure successful return and counter monotonicity along supported
transitions, a function of total path cost equals the same function of the
final clock increment. The reward can be nonlinear, such as the second moment,
or an indicator of exceeding a threshold. These theorems do not condition the
execution law or assume a fixed bound on the number of instructions.

The generated charged-draw regression samples uniformly from `{0,1,2,3}` and
charges that value to its work clock. Its joint return law yields total expected
work `3/2`, second moment `7/2`, and exact tail probability `Pr(work > 2) = 1/4`.
A separate imported-call regression proves a sampler once, reuses its `HasLaw`
at two actual call sites, and exports the caller's joint law. A third module
imports that caller, reuses the law unchanged, and proves the correlated result
and cumulative clocks. An isolated export test builds that full package from its
downloaded sources and external Mathlib dependencies. Initial heaps and clock
counters are arbitrary in these regressions.

The partial-import regression makes the distinction concrete. Its callee charges
one work tick, returns on one fair-coin outcome, and loops forever on the other.
The caller reuses its arbitrary-reward equation without asserting a normalized
`HasLaw`. Successful return has probability `1/2`, and the completed-return work
reward has expectation `1/2`. Total-path expected work is at least `1`, because
the diverging branch also performed that tick. A finite amount of charged work
therefore does not imply termination, and a partial return contract must not be
used as a total-cost formula.
