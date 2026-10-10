# Chapter 4 proof modules

This library covers CLRS fourth edition §4.1–4.4 and uses Lean/Std alone.
The master theorem is outside this scope.

The Strassen proof is maintained in modules and bundled into
[`examples/analysis/matrix_strassen.lean`](../../examples/analysis/matrix_strassen.lean)
for the editor and CLI's single-file analysis interface.

| Module | Responsibility |
| --- | --- |
| `MatrixMath.lean` | Finite dot products, block multiplication, seven-product identity, exact recurrences and bounds. |
| `StrassenValue.lean` | Pure flat-matrix model; ordinary product entries and zero outside the finite result. |
| `StrassenLinear.lean` | Source linear-combination and scalar-leaf summaries; sequence preservation and counter helpers. |
| `StrassenHelpers.lean` | Source quadrant-copy and join summaries, complete contents, and exact costs. |
| `StrassenComposition.lean` | Composition of the 34 real recursive-branch calls, in source evaluation order. |
| `StrassenExecution.lean` | Induction connecting those calls to the value model and exact costs. |
| `StrassenDeterminism.lean` | Uniqueness of completed source executions, outputs, and counters. |
| `StrassenTheorems.lean` | Public termination, correctness, preservation, and runtime theorems. |

Edit these sources, then run from the repository root:

```sh
python3 scripts/build_chapter4_analysis.py
python3 -m algo2lean analyze examples/matrix_strassen.algo examples/analysis/matrix_strassen.lean
python3 -m unittest tests.test_chapter4
```

The bundler combines sources, removes their internal imports, and scopes each
module’s local options and open namespaces. It does not change theorem
statements, insert assumptions, or bypass Lean checking.
The ordinary analysis test checks the entire result with fresh generated
algorithm/Points modules. The chapter regression also rejects a stale bundle.
No generated algorithm files or cached `.olean` files belong in this directory.

See the [Chapter 4 guide](../../docs/CLRS_CHAPTER_4.md) for assumptions and exact
proof scope. The iterative and eight-way recursive analyses are maintained
directly in their individual example analysis files.

## General recurrence framework (§4.3–4.4)

These modules are checked independently and are not added to the editor bundle:

| Module | Responsibility |
| --- | --- |
| `Substitution.lean` | General upper/lower comparison, exact-solution uniqueness, and natural-valued eventual asymptotic bounds. |
| `RecursionTree.lean` | Arbitrary finite tree accounting, unequal depths, finite-tree existence, recurrence connection, and balanced unrolling. |
| `SubstitutionExamples.lean` | A total floor/ceiling recurrence and bounds at every natural size. |
| `RecurrenceApplications.lean` | Balanced linear-work example and application of both methods to compiled Strassen counters. |

```sh
python3 scripts/check_chapter4_proofs.py
```

This compiles each module against freshly generated Strassen semantics and
audits the main theorem assumptions. `tests.test_chapter4` includes this check.
See [the recurrence guide](../../docs/RECURRENCES.md) for hypotheses, examples,
source-program connections, and the remaining scope.
