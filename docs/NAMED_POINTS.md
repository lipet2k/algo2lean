# Fixed algorithm definitions, editable proof locations

The compiler produces two Lean modules. For `gcd.algo`, the editor uses:

| File | Contents | Changes when line names change? |
| --- | --- | --- |
| `GcdGenerated.lean` | States, transitions, initialization, outputs, transcripts, executions, and function summaries | No |
| `GcdGeneratedPoints.lean` | Named locations, variable getters, and sequence-element getters | Yes |

The second file imports the first. Both use the existing shared `Algo2Lean.lean`
library; there is only one transition relation and one definition of an output.
The editor shows the two generated files in separate boxes with their own copy
and export controls.

Adding, removing, renaming, or moving valid `# @name` labels leaves the general
algorithm file **byte-for-byte identical**. Adding comment lines or blank lines
also preserves it. Source-line coordinates occur only in the named-line file and
editor metadata. Label-only changes do not change internal instruction numbers.
Changing executable code or compiler versions can change the algorithm file.

## Naming the state before a statement

Put `# @name` on its own line directly above the statement, at the same
indentation:

```python
def assignment() -> Int:
    # @set
    a = 1
    # @ready
    return a
```

There must be no blank or comment line between the label and its statement.
Inline labels are not supported. `assignment.At.set` describes the state
**before** `a = 1` starts; `assignment.At.ready` describes the state before
`return a` starts. To observe a value after an assignment, name the next
statement. A label does not assert that an execution reaches that state.

## Keep the mathematical goal independent of proof labels

A theorem statement can use only the algorithm definitions:

```lean
import GcdGenerated

def GcdCorrect : Prop :=
  ∀ a b result, gcd.Returns (a, b) result ↔ result = (Int.gcd a b : Int)
```

Save that as `Specification.lean`. A separate proof file can import
`Specification` and `GcdGeneratedPoints`. Its final theorem has the fixed type
`GcdCorrect`; its helper lemmas can use `gcd.At.loop`, `gcd.Local.a`, and
`gcd.Local.b`. Renaming `@loop` requires updating those helpers, while the
specification and the algorithm module remain unchanged.

The repository's `gcd.lean` analysis proves this exact output characterization.
The automated regression also builds a small algorithm and a specification
module once, replaces only the named-line module, and checks proofs with both
sets of labels against the original compiled specification.

The ordinary `analyze` command and editor currently manage the two generated
files plus one analysis file. A project with an additional `Specification.lean`
module should build those files in its Lean project. No extra specification
module is required when keeping the statement and proof in one analysis file.

## What belongs in each module

The general module always includes `f.CallFrom`: completing a function
from a supplied configuration does not intrinsically depend on a label.
`f.Returns`, `f.Run`, `f.ValidTranscript`, `f.ValidHeapTranscript`,
`f.Call`, input loaders, and validity predicates belong to this stable module.

The companion contains `f.At.label`, `f.Local.variable`, and
`f.Element.sequence`. Getters depend on the selected labels: they return a value
only at named locations where the variable is definitely initialized. Adding a
label can therefore extend where a getter is defined. These are local views of
a configuration; they do not assert reachability or change execution semantics.
With no labels, the companion imports the algorithm but defines no observations.

## Compile and export

```sh
python3 -m algo2lean compile examples/gcd.algo -o GcdGenerated.lean --check
python3 -m algo2lean analyze examples/gcd.algo examples/analysis/gcd.lean
```

The first command writes `GcdGenerated.lean` and `GcdGeneratedPoints.lean` in the
same directory. It checks both before writing either and does not rewrite files
whose contents are already identical. This preserves the general file's
modification time when only labels change, allowing Lean project builds to reuse
that module. Output-only consumers import `GcdGenerated`; proofs using labels
import `GcdGeneratedPoints`, which also brings in the algorithm definitions.

Without `-o`, standard output contains only the general algorithm definitions.
`--points-output GcdGeneratedPoints.lean` saves the companion separately. When
using `-o Custom.lean`, the module names are `Custom` and `CustomPoints`.
`--standalone` embeds the shared library in the general file; the named-line
file still imports that file. It never embeds a second copy of the algorithm.

## Scope of the guarantee

This separation fixes the mathematical object being proved while labels evolve;
it does not make a lemma about a moved label remain true. The named-line module
and any proof using it must be checked again. Algorithm and specification files
can remain untouched. The local checker currently rebuilds generated modules in
a temporary directory on each check; it does not yet cache algorithm modules
between editor requests.

When measuring checking time or generated size, account for the algorithm and
named-line modules separately. A measurement of the algorithm module alone
does not include the cost of checking its observations or handwritten proofs.

Default standalone outputs share the `Algo2LeanGenerated` namespace. To combine
algorithms from different files, use [project compilation](MODULES.md), which
gives each source module its own namespace while preserving the separation of
algorithm definitions and named observations.
