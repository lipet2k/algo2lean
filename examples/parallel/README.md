# Parallel sum and exclusive prefix sum

`parallel.algo` is a single deterministic source file using structured
`fork_join` calls. It supports arbitrary signed integer entries, shifted integer
indices, and lengths that need not be powers of two. Nonpositive lengths denote
empty intervals. `prefix_sum` returns exclusive prefixes in a fresh sequence.
Its general Lean correctness/runtime contract requires `n ≥ 0`; the reduction
contract also covers negative lengths. Both prove linear work and logarithmic
span in the abstract instruction-cost model.

In the website's Examples menu, choose **Parallel sum and prefix sum** to load
the source and complete Lean analysis. **Save analysis** downloads a checkable
Lean project with the shared libraries.

The source-connected proofs live in `analysis/`. They use the generated
`ParallelCall` API to prove values, heap effects, sibling independence, work, and
span together. The reusable mathematical lemmas are in
`Algo2LeanLib/ParallelBounds.lean` and `Algo2LeanLib/ParallelSeq.lean`.

From the repository root, with the pinned Lean toolchain installed:

```sh
python3 scripts/check_parallel_examples.py
python3 scripts/check_parallel_examples.py --write-analysis /tmp/ParallelAnalysis.lean --export /tmp/parallel-analysis.zip
python3 -m unittest tests.test_parallel -v
```

The checker compiles the current `.algo` source, combines the exact proof bodies
into one analysis, checks that analysis, and audits the principal theorems'
axioms. Local proof imports become their source bodies; shared runtime imports
remain imports. This avoids maintaining a second generated proof copy.

The combined `ParallelAnalysis.lean` can be used in the editor's analysis pane
with `parallel.algo`. The optional ZIP contains the generated definitions,
combined analysis, and all required shared library sources. After extracting it,
`lake --no-cache build` checks the package independently of this checkout.

See [the parallel guide](../../docs/PARALLEL_ALGORITHMS.md) for the supported
language subset, cost model, memory-access restrictions, and scope of the
runtime claims.
