# Randomized algorithms

Development began on `feature/randomized-algorithms` and continues on
`feature/additional-types`. This work does not publish a release or change the
public repository.

Deterministic and parallel callees share the ordinary `f.Call` contract.
The optional `f.Call.hasLaw` and `f.Call.expectedReturn` adapters reuse a proved
deterministic call as its joint final-heap/output law, including mutations and
counter increments. Certification follows reachable calls rather than whole
files, so unrelated random functions do not remove these adapters. This works
in single-file companions, concrete imports, and recursive source modules.
For a parallel proof, first apply `f.ParallelCall.call`; the same probability
adapter then applies. See the [composition guide](FOUNDATION_COMPOSITION.md)
for checked examples and the limits of this shared interface.

## Design

The operational core describes one instruction at a time. Deterministic
instructions choose one successor; `randint(lower, upper)` chooses a fresh,
conditionally uniform integer from the half-open interval `[lower, upper)`. Bounds are evaluated
once, from left to right. A valid interval requires `lower < upper`; equal or
reversed bounds fail rather than selecting a default
value. Integers and sequence indices retain their mathematical interpretation.

Configurations, mutable heaps, named locations, and clock increments retain
their existing meaning. A lightweight `Choice` description records a successor,
a uniform integer choice, successful stopping, or failure. Its possible
successors agree with the generated `Step` relation. Local proofs therefore
remain independent of whole executions.

A separate mathlib-backed library interprets these descriptions as probability
laws. A run is an infinite sequence, with completed configurations and errors
absorbing. General events must be measurable. Nonnegative expectations take
values in the extended nonnegative reals; signed expectations require
integrability. The library, rather than each generated algorithm, supplies
these constructions and their reusable lemmas.

Return probabilities are unconditional probabilities of eventual successful
return. Their total mass can be below one. Failure and divergence remain
distinct, and conditioning on return is an explicit operation. Clock costs
include work on executions that fail or diverge; a finite expected tick count
does not alone imply termination if an infinite loop need not tick.

The reusable call law must retain the joint final heap and returned value. Imported
calls must preserve probability weights, not merely possible transitions.
Contract composition stops the callee at its first return and then continues the caller.
Existing existential `Call` statements retain their meaning; they are not
silently reinterpreted as probabilistic correctness claims.

## Dependencies

Integer-only generated definitions and possible-execution proofs use Lean/Std.
Probability analysis uses the separately pinned Mathlib package in
`probability/`. Its [setup guide](../probability/README.md) explains how to
install the optional dependencies. Compilation does not download them.

## Current interface

A randomized single file produces `NameGenerated.lean`, its usual named-line
companion, and `NameGeneratedProbability.lean`. Projects use
`Algo.module.Generated`, `Algo.module.Points`, and `Algo.module.Probability`.
The general algorithm file remains independent of Mathlib. Adding or moving
labels changes neither the general definitions nor the probability companion.

For a source function `f`, import its probability companion to use:

| Interface | Meaning |
| --- | --- |
| `f.outcome state` | Final heap and returned value, when this call has returned. |
| `f.HasLaw heap input distribution` | Reusable joint final-heap/output distribution, including almost-sure successful termination. |
| `f.expectedReturn heap input reward` | Unconditional expected nonnegative reward of the final heap and output; unsuccessful calls contribute zero. |
| `f.expectedFrom state reward` | The same kind of return reward from a local state of this function, independently of its caller stack. |
| `f.law heap input` | Probability measure on the whole infinite execution. |
| `f.returnProbability heap input post` | Probability of eventually returning with a heap and value satisfying `post`. |
| `f.outputProbability input output` | Probability of returning this ordinary mathematical output, using the same input loading as `f.Returns`. |
| `f.terminationProbability heap input` | Probability of successful termination. |
| `f.expectedCost heap input "clock"` | Expected increment of this clock over the entire execution, possibly infinite. |
| `f.cost heap "clock"` | An observation of the total clock increment on each execution; use it for moments or joint cost functions. |
| `f.costProbability heap input "clock" threshold` | Unconditional probability that the total clock increment exceeds the threshold. |

For example, the statement `die.outputProbability () 6 = (6 : ENNReal)⁻¹`
says that a call to `die` eventually returns six with probability one sixth.
`die.returnProbability heap () (fun final value => final = heap ∧ value ≤ 6)`
also describes storage preservation. Both are unconditional probabilities;
failed and nonterminating paths are not discarded from the denominator.

General events use `Algo2LeanProbability.probability (f.law heap input) event`.
Build `event` with `Event.atTime`, `Event.within`, `Event.ever`, `Event.always`,
Boolean combinations, or a custom predicate with a measurability proof.
`expected` accepts a measurable nonnegative `Observable`; `expectedReal`
requires integrability. See [the shared library guide](../probability/README.md).

`HasLaw` takes a `PMF (Heap × Output)`. A single theorem about this distribution
specifies correlations between the result, mutation, and every final clock.
Its definition compares expectations for **every** nonnegative reward, rather
than asserting a separate probability fact for each output. It therefore
supports rewards such as the square of a returned value, a weighted clock sum,
or an indicator that both the output and its cost satisfy a condition.

For example, these expressions use the generated interface (with `f` replaced
by the source function name):

```lean
-- Expected squared runtime, including nonterminating executions.
Algo2LeanProbability.expected (f.law heap input)
  ((f.cost heap "work").pow 2)

-- Probability that the total runtime exceeds a threshold.
f.costProbability heap input "work" threshold

-- A joint reward on successful return; here f returns an Int.
f.expectedReturn heap input (fun final result =>
  (result.toNat : ENNReal) ^ 2 + (Heap.cost heap final "work" : ENNReal))
```

An `expectedReturn` theorem is also useful when the function can diverge: its
reward is zero on paths with no successful return. In contrast, `expectedCost`
and `costProbability` retain all charged work. Do not use a return-only reward
as a total-runtime statement without justifying their agreement.

`expectedFrom` is the probabilistic counterpart of `CallFrom` for local loop
analysis. It accepts a configuration at any source location, discards the
suspended caller stack, and analyzes the remaining computation of that function.
It assumes neither reachability nor valid inputs. A configuration belonging to
another active function, or a completed configuration, gives zero. Local helper
lemmas should state the required `At` and `Local` facts explicitly.

Time indexes count generated instructions, including argument evaluation and
call bookkeeping. They are not source line numbers or runtime costs. Source
locations remain available through `f.At.label`; runtime uses explicit clocks.
Named-location observations are still local predicates and can appear inside
an `Event.ever` predicate without requiring a transcript in their statements.

## Implementation and boundaries

The compiler emits `nextChoice` and a checked theorem `choice_step` equating its
allowed successors with `Step`. The shared library interprets each choice as a
probability distribution and builds the infinite path measure with Mathlib's
trajectory construction. Successful termination repeats the final state; an
invalid instruction enters an absorbing error state. These padding transitions
do not execute more source instructions or charge more ticks.

Concrete imports and mutually recursive source groups carry probability
companions. Imported instructions use the original module's choices, and
`choiceLaw_map` proves that a caller embedding preserves their entire
distribution. Functions that can reach random choices do not receive deterministic uniqueness
theorems. Other functions in a mixed module can retain scoped certificates;
see [composition](FOUNDATION_COMPOSITION.md).

Each probability companion also proves `nextChoice_context`: appending suspended
callers preserves the current instruction's choice distribution and only changes
where its eventual return resumes. This certificate supports reuse between
functions in the same source file, including recursive calls. Imported modules
keep their separately checked probability companions. Shared call transport
stops at every callee exit, so unrelated result tags can be rejected by the
caller without requiring a new proof of the callee's law.

The shared stopped-expectation core provides first-return decomposition and probability-preserving
embedding rules. An imported sampler's `HasLaw` is reused at two call sites, and
the caller exports its own joint law, which a third module reuses unchanged.
The optional `CallContext` module supplies shared rules for same-file and imported
calls, so analyses provide the continuation reward rather than rebuilding path
embeddings. The CLRS shuffle analysis proves a uniform permutation, preservation,
termination, and exact costs. Hiring reuses it to prove `H_n` expected hires and
`n` interviews, including total-path runtime tails. Randomized partition proves
correctness, exact `n-1` comparisons, and uniform returned pivot rank for distinct
keys. Selection reuses that joint law for its recursive call and proves expected
comparison cost at most `4n` and combined operation cost at most `12n` for distinct
keys. Quicksort reuses it for both recursive calls, proves sorting even with
duplicates, and establishes exact expected comparisons `2(n+1)H_n-4n` for
distinct keys. The coupon source analysis proves almost-sure completion, the
exact collected set, mean total draws `n H_n`, and tail bound
`Pr(draws > t) <= n(1-1/n)^t` for positive `n`. These statements concern the
actual generated source. See the [CLRS example guide](../examples/randomized_clrs/README.md)
for assumptions, operation clocks, and main-result files.
Existing `f.Call` contracts retain their pathwise meaning and
carry no probability weights. They do retain runtime information: for
`f.Call before input after output`, `Heap.cost before after clock` measures the
specified counter's increase, including nested calls. Both interfaces use the
same explicit source ticks and preserve the caller's initial counters.

A deterministic module's optional probability companion now supplies
`f.Call.hasLaw` and `f.Call.expectedReturn`. Given an existing proof
`call : f.Call before input after output`, use:

```lean
have law : f.HasLaw before input (PMF.pure (after, output)) :=
  f.Call.hasLaw call
have continuation := f.Call.expectedReturn call reward
```

The original deterministic analysis needs no changes and no Mathlib import.
The bridge proves the joint final-heap/output law, so storage effects and costs
remain available to a randomized caller. The checked example in
`tests/fixtures/deterministic_probability` reuses one mutation proof twice, then
exports the resulting randomized contract to a further caller.

This automatic bridge currently requires a deterministic **execution unit**,
including its executed dependencies. An unrelated random function in the same
unit prevents its global determinism certificate; separating the deterministic
helper into an imported source module enables reuse. An existential `Call` for
a randomized function is not enough to derive a complete law. Recursive-module
facades expose the full probability interface, including `HasLaw`,
`expectedReturn`, and `expectedFrom`, just like ordinary modules.

Abstract implementation slots still need probability contracts; the compiler
reports this limitation rather than assigning an unjustified law. Kth-visit and
conditioning convenience interfaces remain future extensions.

The local analysis checker uses Mathlib only when an analysis imports a
probability companion or Mathlib explicitly. It requires preinstalled pinned
dependencies and gives setup instructions when they are missing. Downloads
include the probability library source and pinned Lake dependency declaration;
Mathlib itself is installed by Lake. Browser compilation works without Lean,
but probability proof checking needs a local Lean environment.
