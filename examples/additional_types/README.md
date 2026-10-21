# Values and collections

Choose **Values and collections** in the local editor's project examples. The
project opens `main.algo`; use **Project file** to inspect each small algorithm.

| File | Algorithm and features |
| --- | --- |
| `histogram.algo` | Count a sequence prefix with `Dict[Int, Int]`, optional lookup, and insertion. |
| `visited.algo` | Count distinct values using `Set[Int]`, membership, insertion, and size. |
| `centroid.algo` | Average planar points stored in `Seq[Tuple[Real, Real]]`, using tuple unpacking and exact division. |
| `main.algo` | Import the three helpers and combine their results in a heterogeneous tuple. |

`Seq` has every integer index; `n` selects the finite prefix `[0, n)`. The first
two algorithms return an empty histogram or zero distinct values for `n ≤ 0`.
The centroid's intended domain is `n > 0`; division by zero has no successful
execution. Callers also supply valid sequence references and typed elements.

The histogram and visited-set modules use the Std-only runtime. The centroid
and its importing caller additionally use the optional exact-real library and
pinned Mathlib. Generated propositions describe executions; compilation alone
does not establish an algorithm's correctness or running time.

**Download project** includes all `.algo` files, generated Lean modules, required
shared library sources, and the pinned dependency configuration. For the real
examples, install the declared Mathlib dependencies before checking the download:

```sh
lake update
lake exe cache get
lake build
```

The [tuple guide](../../docs/TUPLES.md),
[finite collection guide](../../docs/FINITE_COLLECTIONS.md), and
[exact-real guide](../../docs/REALS.md) describe the source and Lean interfaces.
