# Randomized algorithms

These examples use the experimental `0.2.0-dev` compiler. `randint(a, b)` draws
uniformly from the integers in `[a, b)`. In particular, `randint(1, 7)` has six
possible results, and `randint(0, 2)` has two. This upper-bound convention agrees
with `range(a, b)`; it differs from Python's inclusive `random.randint`.

| File | Purpose |
| --- | --- |
| `sampling.algo` | A variable interval, a six-sided die, and a Boolean coin. |
| `client.algo` | Two fresh draws through an imported die function. |
| `retry.algo` | Repeated coin flips until a head, with a `flips` cost counter. |

The checked [die analysis](analysis/sampling.lean) exposes three results:

- `SamplingAnalysis.die_output_probability`: the eventual return probability is
  `1/6` for each integer in `[1, 7)`, and zero otherwise.
- `SamplingAnalysis.die_terminates_almost_surely`: termination probability is one
  for every initial heap.
- `SamplingAnalysis.die_return_probability`: any joint final-heap/output
  postcondition has exactly its probability under a uniform draw; the final heap
  equals the supplied initial heap.

Choose **Randomized algorithms** in the editor's project examples. The ordinary
generated file describes possible executions. The separate **Probability
interface** defines the execution measure and probabilities. Compiler output
alone does not prove a distribution, a runtime bound, or almost-sure termination.
The two-dice and retry sources currently demonstrate language support; their
distribution and expected-runtime analyses remain future examples.

Probability analyses use the optional pinned Mathlib project. Set it up once
from the repository root:

```sh
cd probability
lake update
lake exe cache get
lake build
cd ..
python3 -m algo2lean analyze examples/randomized/sampling.algo examples/randomized/analysis/sampling.lean --project examples/randomized
```

The [probability guide](../../probability/README.md) describes general events,
expectations, failure, and nontermination. The
[design document](../../docs/RANDOMIZED_ALGORITHMS.md) distinguishes implemented
interfaces from the remaining work on reusable probabilistic call contracts.
