# Algo2Lean 0.2.0

Version 0.2.0 extends the language and makes existing call proofs reusable
across deterministic, randomized, and structured parallel algorithms.

| Addition | What it enables |
| --- | --- |
| Richer values | Heterogeneous tuples, typed and nested sequences, finite mutable sets and dictionaries, and exact `Real` arithmetic |
| Randomized algorithms | Fresh uniform integer draws, joint return laws, expected costs, almost-sure return, and runtime tails |
| Structured parallel algorithms | Deterministic fork–join calls with correctness, heap effects, access independence, work, and span in one contract |
| Reusable call proofs | Deterministic `Call` proofs reused by randomized callers; imported parallel contracts reused without duplicating the callee's proof |
| Natural matrix programs | Nested row arrays, ordinary `a[i][j]` indexing, and contracts preserving aliases, old storage, fresh outputs, and counters |
| More checked examples | Randomized CLRS algorithms, dictionaries and sets, real-valued centroids, parallel sum, prefix sum, merge sort, and matrix multiplication |

## One common functional contract

`f.Call` remains the common interface for a completed call. For a certified
deterministic function, `f.Call.hasLaw` and `f.Call.expectedReturn` reuse that
proof in the optional probability interface. `f.ParallelCall.call` recovers the
ordinary functional contract from a parallel proof. Determinism is certified
per function's reachable call graph, so an unrelated random function does not
prevent reuse. See [composition](FOUNDATION_COMPOSITION.md).

Integer-only definitions and structured parallel proofs use Lean/Std. Mathlib
is required only for probability analysis and exact real arithmetic. The
optional package pins its dependency and does not change the ordinary checking
path. Python remains the only compiler dependency; no Python packages are
required.

## Upgrading from 0.1.4

Keep existing proofs paired with their original compiler release. Regenerate
all modules in a project together when upgrading: generated Lean and its
shared libraries are versioned together, and should not be mixed across
releases. Existing source-level `Call`, `Run`, and `Returns` contracts remain
the preferred interfaces; generated state layouts are not compatibility APIs.

Matrix examples now use `Seq[Seq[Int]]` and heap-aware contracts rather than
flattened integer arrays. Clients of those examples need to adopt the nested
representation and the new matrix contracts. Imported module facades also expose
the optional probability and parallel companion interfaces.

Lean remains pinned to **4.33.1**. To check probability or real-valued proofs,
follow [the optional package setup](../probability/README.md). Downloaded proof
projects include the required shared sources and pinned dependency configuration;
they do not bundle Mathlib binaries. Browser compilation works offline once
the release's assets are loaded; Lean proof checking runs locally.

## Scope

- Parallel children must be deterministic. Random draws inside fork children,
  abstract-interface dependencies in parallel calls, classes, finite collections,
  and real-valued parallel storage are not supported. The [parallel guide](PARALLEL_ALGORITHMS.md)
  lists the exact supported types and access conditions.
- A possible randomized return does not imply a probability or termination
  guarantee. A completed-return reward can differ from total runtime for a
  diverging program. The [randomized guide](RANDOMIZED_ALGORITHMS.md) explains
  these distinctions.
- Real numbers are mathematical reals, not floating-point values. Set and
  dictionary semantics do not promise constant-time hashing. Explicit clocks
  and parallel instruction counts are mathematical cost models.
- Recursive matrix contracts require power-of-two sizes. The master theorem
  is not included.
- Generation verification checks exact compiler output. Lean checks the
  resulting definitions and proofs; the compiler itself is not formally proved
  to preserve the intended source semantics.

Earlier numbered releases and their compiler archives remain unchanged.
