# Static functions use the same execution interface

This is a bounded architecture acceptance example. The two backends are ordinary
`.algo` functions; the generic callable client is currently written in Lean.
Source-level `Callable` annotations and function arguments are not implemented.

`callable_direct.algo` and `callable_staged.algo` independently implement integer
successor. They charge one and two `callable_work` operations respectively. Each
has an ordinary `successor.Call` theorem that knows nothing about the
client or its adapter. Their generated code is unchanged when imported together.

The proof-only `analysis/callable_client.lean` module defines a small local
`CallableClient.Code` record: executable `InterfaceCode Heap Int` plus a typed
`entry : Int → Frame`. It has no receiver, reference-validity predicate, or
dummy object. This record is specific to the example rather than a new public
compiler API.

The client calls its parameter twice. Its single generic proof assumes a local
successor summary for that executable parameter, then constructs both real calls
using `ModuleCall.summary`. The law does not replace a call's transitions.
`lift_prefix` also transfers arbitrary finite prefixes without requiring a
completed call or a behavioral law.

`analysis/callable_bindings.lean` uses the existing `InterfaceAdapter` once per
backend to decode its result. It transfers each original backend proof unchanged
and instantiates the same client proof. For every initial integer and heap:

- Both clients terminate and return the integer plus two.
- The direct implementation adds exactly two to `callable_work`; the staged
  implementation adds exactly four.
- Every completed execution has that result and the exact corresponding heap,
  preserving all sequence/object storage, identities, and other clocks.
- A concrete first source tick remains observable inside the nested call before
  the first function has returned.

`callable_bindings.algo` only collects the two ordinary source imports. It does
not pretend to express the generic client in unsupported syntax.

Check the acceptance example with:

```sh
python3 -m algo2lean analyze examples/modules/callable_bindings.algo \
  examples/modules/analysis/callable_bindings.lean --project examples/modules
python3 -m unittest tests.test_callable_modules -v
```

The tests also check both backend analyses independently, preservation of their
generated code, arbitrary pre-existing clocks and aliased storage, and rejection
when a backend's proved result or charge changes.
