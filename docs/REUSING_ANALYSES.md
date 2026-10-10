# Using an algorithm that has already been proved

Import the `.algo` operation in your source, then import its companion
`Analysis` module in your proof. The imported code and proof keep their original
identity. You prove the new caller's logic; you can apply the imported
correctness, termination, mutation, and cost theorems unchanged.

## Choose the theorem for your question

| Question | Typical public theorem |
| --- | --- |
| Can I call this operation and reuse its result in another algorithm? | `call_contract`, `summary`, or `call`, over the generated `f.Call` relation |
| What does every completed run guarantee? | `correct`, `verified`, or `every_execution`, derived from the call contract |
| Does some ordinary output exist? | `output_exists` or `terminates` |
| What is the measured work of an output? | `running_time`, derived from the same call contract |

These names belong to the component's handwritten analysis. The compiler
provides the underlying `f.Returns`, `f.Run`, and `f.Call`
relations, grouped under the source function's name; it does not infer what an
algorithm is supposed to compute. A method uses `Counter.add.Call`, for example,
and a constructor uses `Counter.Call`. Use the same compiler version for the
imported algorithm, its analysis, and the calling project.

Use a theorem over `f.Call` as the primary reusable result. It works from the
supplied heap under any suspended caller stack. Its postcondition describes the
new heap and becomes the next call's precondition. You never need to supply a
transcript or a caller stack when applying that theorem. Some analyses name
this handwritten theorem `summary`; that is a theorem over `Call`, not a need
to use the lower-level `Summary` relation directly.

`f.Returns` is a convenient ordinary-value view for readers interested in the
final answer. `f.ReturnsWithCost` also exposes recorded costs. These relations
hide references and intermediate heaps, so they do not replace the call
contract when a subsequent operation needs the mutated object or newly
allocated output. Keep both views, and prove the mathematical argument once.

`f.Call.run call` gives an ordinary `f.Run` from a reusable call fact. With the
project's optional Facts module imported, `f.Run.eq_of_call execution call`
identifies the final heap and result of any completed run with those of the
proved call. This is the usual last step in an all-executions correctness proof.

## What a reusable contract provides

Under the operation's preconditions, its primary theorem supplies:

- An actual `f.Call before input after result`, establishing termination.
- The mathematical result and any representation predicate needed for later calls.
- Preservation of unrelated storage and freshness of newly allocated outputs.
- A bound on `Heap.cost before after`, or exact `before.Increments after costs`.

An exact final-heap description can already imply preservation and allocation;
it need not be accompanied by a redundant second statement. A read-only scalar
operation can simply return the same heap. A partial operation states the
domain on which it terminates; divergence examples retain their nontermination
theorems instead of claiming a total call contract.

For amortized analysis, the contract states

```text
actual cost + potential(after) ≤ budget + potential(before).
```

The representation and both potentials belong to the same object in the same
actual call. Successive inequalities cancel the middle potentials. Constructor
contracts establish the initial potential, and nonnegativity permits dropping
the final potential. This proves bounds for repeated calls without assuming
that each individual call has a small worst-case cost.

The [example contract inventory](../examples/ANALYSIS_CONTRACTS.md) identifies
the reusable theorem for each family. The
[Kruskal project](../examples/kruskal/README.md) shows a graph algorithm consuming
an independently proved amortized data-structure contract.

## A complete small example

The counter library has an abstract increment algorithm, two implementations,
and concrete wrappers. A further client just imports an already linked wrapper:

```python
from direct import Direct
from use_direct import advance

def advance_twice(counter: Direct) -> Int:
    advance(counter)
    return advance(counter)
```

Its proof imports `Algo.use_direct.Analysis`. The essential reasoning is two
applications of the same public theorem:

```lean
obtain ⟨middle, first, advanced, firstCost⟩ :=
  DirectClientAnalysis.summary represented
obtain ⟨after, second, advancedAgain, secondCost⟩ :=
  DirectClientAnalysis.summary advanced
```

`represented` says the supplied object contains the initial value. `advanced`
says the same object now contains its successor, so the second application can
use it directly. `first` and `second` describe the actual calls. The two clock
increments add using `firstCost.trans secondCost`; neither call resets clocks.

The resulting theorem statement contains just the application's inputs and
postcondition:

```lean
theorem correct {before after : Heap} {counter : ObjectRef} {value output : Int}
    (represented : DirectAnalysis.Represents before counter value)
    (execution : advance_twice.Run before counter after output) :
    output = value + 2 ∧ DirectAnalysis.Represents after counter (value + 2) ∧
      before.Increments after (Clocks.single "counter_work" 4)
```

The checked source and proof are in
[`examples/interfaces/consumer`](../examples/interfaces/consumer/advance_twice.algo)
and its
[`companion analysis`](../examples/interfaces/analysis/consumer/advance_twice.lean).
The proof's small `calls` helper inspects only this caller's two call boundaries.
It never unfolds the generic increment algorithm or the counter implementation.
All earlier component proofs remain unchanged.

Check it from the repository root:

```sh
python3 -m algo2lean analyze examples/interfaces/consumer/advance_twice.algo \
  examples/interfaces/analysis/consumer/advance_twice.lean --project examples/interfaces
```

## Why the heap appears

A heap records shared sequences, objects, and clocks. Passing it makes mutation
and aliases explicit. A caller normally uses its current heap and obtains the
next heap from a component's theorem; it does not rebuild memory by hand.
Constructor theorems establish fresh references and their representations.

Representation predicates describe the mathematical meaning of stored data.
For example, `Represents heap counter value` states which integer the counter
represents. The concrete Dijkstra theorems require a represented input graph;
they construct and validate their own queue and working sequences. Users of
those theorems supply no heap implementation invariant or abstract queue law.

Preservation guarantees matter: a theorem about a mutated counter does not by
itself promise that a different array was preserved. Use the component's
published framing guarantees when the next call depends on other storage.
Likewise, an amortized bound carries the potential of the same represented
object across calls; an alias does not create another copy of that potential.

## What remains local to a new proof

You still prove the new caller's preconditions, local steps, and composition.
If it loops, it needs a loop invariant. If it allocates, it must connect the
constructor's guarantees to later calls. Proof bodies may inspect those local
transition rules; the statements of their helper lemmas can use ordinary
summaries and source-facing predicates.

A new backend for an abstract algorithm proves the interface's behavioral and
cost laws once. Signature compatibility only selects its executable methods.
The compiler supplies method-summary transfers; the linking proof applies the
backend's existing theorems. Ordinary callers of that linked result use the
same public relations as any other module.

Start with the [counter interface](../examples/interfaces/README.md), then see
[sort followed by search](../examples/modules/GENERAL_SORT_THEN_SEARCH.md) and
[Dijkstra with two queues](../examples/dijkstra/README.md).
[Module setup](MODULES.md) covers file naming, editor use, and current syntax
limits. Project checking caches generated modules and proofs until their contents
or dependencies change. Cost theorems describe declared ticks;
an algorithm without runtime instrumentation does not acquire a runtime bound
merely by being imported.
