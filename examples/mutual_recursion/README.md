# Mutual recursion across source files

`even.algo` and `odd.algo` import and call each other. The compiler generates
their execution rules together, preserving the public namespaces
`Algo.even.is_even` and `Algo.odd.is_odd`. `client.algo` imports only `is_even`
under the alias `parity`; it uses the recursive group's existing implementation.

For nonnegative input `n`, either parity function makes `n + 1` invocations.
Every invocation charges `tick("work", 2)`, so the exact recorded cost is
`2 * (n + 1)`. Nonpositive inputs use the base case and cost two units. These
ticks describe the explicit cost model, rather than machine execution time.

Compile and check all generated definitions, including the external client:

```sh
python3 -m algo2lean compile examples/mutual_recursion/client.algo \
  --project examples/mutual_recursion --check \
  --output-dir /tmp/algo2lean-mutual-recursion
```

The exported `Algo/even/Generated.lean` and `Algo/odd/Generated.lean` files
provide the ordinary function interfaces. Both refer to the same generated
recursive implementation. The named `base_case` point belongs only to
`even.is_even.At.base_case`; changing that label leaves all general definitions
unchanged.

## Correctness and cost proofs

[`analysis/parity.lean`](analysis/parity.lean) proves both recursive functions
together. Its local helpers describe the zero case and each recursive-call
case through `Call`; one simultaneous induction then establishes their outputs
and exact heap effects for all natural-number inputs. The theorem applies to
an arbitrary starting heap, so callers may already hold objects or have nonzero
clock values. `correct` characterizes every completed evenness run, and
`output_cost` supplies the exact weighted cost of a terminating execution.

[`analysis/client.lean`](analysis/client.lean) imports that analysis and reuses
its call theorem. The client proof inspects only the client's own transitions;
it does not repeat the parity induction or inspect either callee's transitions.
Its correctness and running-time statements use `classify.Run` and
`classify.ReturnsWithCost`.

```sh
python3 -m algo2lean analyze examples/mutual_recursion/client.algo \
  examples/mutual_recursion/analysis/client.lean \
  --project examples/mutual_recursion
```

The two source modules have cyclic imports, but their proof imports are
acyclic: the joint parity proof depends on both generated modules, and the
client proof depends on the joint proof. This prevents a proof from assuming
its own conclusion through an import cycle.
