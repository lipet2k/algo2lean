# Prove one client, choose an implementation

`increment.algo` reads a counter and stores its successor through the small
`Counter` interface. It knows nothing about the storage layout.

- `direct.algo` stores the integer directly. Its two operations cost one tick each.
- `negated.algo` stores the integer's negation. Its operations cost two ticks each.
- `use_direct.algo` and `use_negated.algo` import the same client. The compiler
  checks the method signatures and supplies each concrete implementation.
- `both.algo` calls that same compiled client with both implementations in one
  program. The two bindings share the client body, while retaining distinct code.
- `consumer/advance_twice.algo` imports an already linked wrapper and calls it
  twice on the same object. Its analysis reuses the wrapper's postcondition and
  cost theorem, without reopening either underlying implementation or proof.

The analysis under `analysis/increment.lean` proves termination, the new value,
and the sum of the two operation costs **once**. The linking analyses apply that
unchanged theorem and the independently checked backend analyses. Their
`correct` theorems cover every completed execution and retain the post-state
representation for the next caller. Initial heaps and clock values are arbitrary.

```sh
python3 -m algo2lean analyze examples/interfaces/use_direct.algo \
  examples/interfaces/analysis/use_direct.lean --project examples/interfaces
python3 -m algo2lean analyze examples/interfaces/use_negated.algo \
  examples/interfaces/analysis/use_negated.lean --project examples/interfaces
```

## The public interface

An `.algo` interface declares method signatures. `Counter.Code` is the executable
implementation; `CounterContract` is an ordinary Lean record of the mathematical
laws this particular client needs. Matching source signatures supplies code,
**not** a proof of those laws.

A generic theorem takes `dependencies : Algo.increment.Dependencies`, containing
`dependencies.Counter`. Its public call relation is
`Algo.increment.increment.Call dependencies before counter after result`.
Concrete wrappers hide that parameter in their generated binding. The compiler
also supplies a summary-transfer lemma for each bound method, so the linking
proof applies the backend's original theorem without inspecting its transitions.

Optional `Facts` imports provide determinism. Given a constructed summary,
`execution.eq_of_summary summary` identifies the final heap and result of every
completed execution. Generic clients take the corresponding `DependencyFacts`;
concrete bindings supply these from checked backend facts.

This first version uses one implementation per interface type within a module
instance. A caller may use multiple instances of a generic module, including
instances with different implementations. Interface objects are passed as
parameters; interface fields, sequences of interfaces, returning interfaces from
instantiated calls, and binding a backend that still has abstract dependencies
are diagnosed as unsupported. Concrete sequences/classes, ordinary imports, and
recursive generic calls keep their existing semantics.

Bindings are currently module-wide: all exports of a generic module share its
`Dependencies`, even a helper that does not itself call an interface method.
Put independently reusable helpers in a separate module if they should need no
implementation argument. A module may bind some dependencies and forward the
others to a later caller.

See [Using a proved algorithm](../../docs/REUSING_ANALYSES.md) for a guided example
of the public theorem interface.
