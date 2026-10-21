# Composing algorithm analyses

Use `f.Call` for the reusable functional contract of a completed call. It carries
the actual input heap, output heap, returned value, and caller counters. Existing
correctness, mutation, freshness, and runtime proofs can then be reused by
further callers without changing the callee's analysis.

| Caller and callee | Interface to reuse |
| --- | --- |
| Deterministic calls | The existing `f.Call` theorem |
| Randomized caller, deterministic callee | `f.Call.hasLaw` or `f.Call.expectedReturn` |
| Randomized caller, randomized callee | `f.HasLaw` or an unconditional `f.expectedReturn` contract |
| Parallel caller, deterministic imported callee | The callee's parallel contract, including work, span, and accesses |
| Randomized caller, completed deterministic parallel call | `f.ParallelCall.call`, then the deterministic probability adapter |

## Deterministic proofs in randomized callers

A completed deterministic call induces a point-mass return law. The optional
`Algo2LeanProbability.Deterministic` module proves this once; generated
companions supply `f.Call.hasLaw` and `f.Call.expectedReturn`. These adapters
retain the heap and actual clock values. They do not require a second
correctness proof or a randomized copy of the original function.

Determinism is certified over each function's reachable call graph. Unrelated
random functions can share its source file. Concrete imports and mutually
recursive modules retain this interface. Lean checks closure and step uniqueness
for the generated region; the compiler's classification alone is not trusted
as a proof. Mixed abstract-interface implementations are outside this scoped
certificate's current support.

A random function's possible completed trace cannot be converted into a
point-mass law. `HasLaw` includes probability-one successful return. For partial
or diverging calls, use an unconditional expected-return contract, and establish
any total-path cost claim separately.

The [deterministic-to-randomized fixture](../tests/fixtures/deterministic_probability/analysis/helper.lean)
proves a mutating helper without Mathlib. Its caller uses the helper twice and
reuses the resulting joint law through a third imported source module. Counter
increments start from the caller's supplied values.

## Imported parallel contracts

A `ParallelCall` includes the value, heap effects, work, span, and accesses of
one completed evaluation. Sibling independence is an explicit proof condition.
The functional projection `.call` reuses the same ordinary `Call` interface.
An ordinary correctness theorem alone does not provide a parallel cost or
memory-access bound.

Concrete imported calls preserve the original callee's evaluation, costs, and
access record. An imported fork child uses a call-and-return forwarding boundary,
adding two instructions to that child's work and span. Its arguments are captured
before the children start. The implementation and its proof remain separately
compiled and reusable.

The [parallel composition fixture](../tests/fixtures/parallel_imports/analysis/client.lean)
reuses one mutating helper contract for two disjoint writes to a shared array.
A further randomized caller reuses that parallel contract and its accumulated
counters. The exported project rebuilds the entire composition from source.

Random choices inside parallel children and abstract-interface dependencies in
parallel calls are unsupported. The [parallel guide](PARALLEL_ALGORITHMS.md)
specifies the supported storage types and the work/span model.

## Dependency boundaries

Ordinary integer algorithms use the existing Std execution core. Scoped
determinism and parallel semantics are optional Std modules. Probability adapters
live in the optional Mathlib package; real arithmetic uses its separate real
library. A deterministic integer proof need not import either library merely
because a later caller uses probabilities or real values.

Public theorem and helper statements use source-facing contracts and named
observations. Proof bodies may inspect the generated transition rules. This
keeps reusable results readable without hiding the semantics needed to prove
them.
