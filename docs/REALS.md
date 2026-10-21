# Exact real arithmetic

`Real` denotes an exact mathematical real number, represented by Mathlib's
`Real` in Lean. It is suitable for stating and proving mathematical algorithms;
it does not model floating-point rounding, overflow, or machine precision.

```python
def interpolate(left: Real, right: Real, weight: Real) -> Real:
    return (1 - weight) * left + weight * right
```

Real values work in parameters, results, local variables, class fields, tuples,
`Seq[Real]`, sets, and dictionary keys or values. Imported algorithms and abstract
interface signatures retain these source types.

## Literals and arithmetic

| Source | Exact meaning |
| --- | --- |
| `0.1` | `1 / 10` |
| `.5`, `5e-1` | `1 / 2` |
| `1.25e2` | `125` |
| `1 / 2` | Real division, yielding exactly one half |
| `Real(n)` | Convert an `Int` to the same mathematical value; an existing Real stays unchanged |

The compiler reads decimal and scientific literals from their original source
tokens. It never uses Python's rounded floating-point value. Underscores between
digits are allowed. For example, `1e309` remains a finite exact number and
`1e-1000` remains nonzero.

Each real literal has at most 1,024 source characters, exponent magnitude at most
1,024, and at most 2,048 decimal digits in its expanded numerator or denominator.
Literals beyond these resource limits receive a source diagnostic. Positive and
negative signs use the ordinary unary operators.

Addition, subtraction, multiplication, equality, and order support Real values.
An integer promotes to Real when the other operand or the expected type is Real.
`/` always returns a Real, including when both inputs are integers. Division by
zero has no successful execution; Lean's totalized division cannot produce a
spurious source result. `//` and `%` remain integer-only.

`+=`, `-=`, and `*=` preserve an Int or Real variable's or field's declared type.
`/=` requires a Real destination. There is no implicit conversion from Real to
Int, and Boolean values are not numbers. Sequence indices, range bounds, clock
increments, and both `randint` bounds remain Int. A range loop can assign each
integer index to a previously declared Real variable by exact conversion.

## Tuples and shared containers

```python
def initial_values() -> Tuple[Seq[Real], Dict[Int, Real], Set[Real]]:
    coordinates: Seq[Real] = const(0)
    weights: Dict[Int, Real] = {0: 1, 1: 0.5}
    selected: Set[Real] = {0.1, 1 / 10}
    return coordinates, weights, selected
```

Fresh constructors and literals use their expected element types, so `const(0)`
above allocates a real-valued sequence. Immutable tuple components can also
promote from Int to Real. Existing mutable aliases cannot change their element
types: a `Seq` cannot become `Seq[Real]`, and a `Dict[Int, Int]` cannot become
`Dict[Int, Real]` through assignment or `copy`.

Real set elements and dictionary keys use exact mathematical equality. The two
entries in `selected` above denote the same value, so the set has size one.
Equality can be noncomputable; the container model makes no hashing or
constant-time lookup claim. Integer-key lookup does not compare a dictionary's
real-valued entries. Explicit ticks remain the algorithm's cost model.

## Lean analysis and dependencies

Generated Real modules import `Algo2LeanReal`, which uses the pinned Mathlib
checkout also used for probability analysis. Deterministic Real algorithms do
not import `Algo2LeanProbability`. Integer-only modules retain the Std-only path.

Set up the optional dependencies once from the repository root:

```sh
cd probability
lake update
lake exe cache get
lake build Algo2LeanReal
```

Then return to the repository root to use the usual compiler or editor checks.
Checks use already installed dependencies; they do not silently download
Mathlib or a Lean toolchain. Generated-code and analysis downloads include their
required Algo2Lean shared sources and pinned Mathlib configuration. In an
extracted package, run `lake update`, `lake exe cache get`, and `lake build`.

Real-valued inputs and outputs appear as ordinary `Real` values in the Lean
interface. Reusable `Call` statements use the same shared heap as integer
algorithms. For example, an interpolation contract can state
`interpolate.Call heap (left, right, weight) heap ((1 - weight) * left + weight * right)`.
Class fields and typed containers retain their public getters, updates, and
validity predicates; local storage facts do not require constructing a complete
transcript.

Exact Real comparisons and storage decoding may require `noncomputable`
definitions and classical reasoning in Lean. The generated code selects that
support when needed. Mathematical theorem statements remain about Real values,
not floating-point encodings or runtime casts. Integer and real algorithms
share the same heap, so imported calls preserve aliases across these types.

Real arithmetic can be combined with integer random draws and the optional
probability interface. `randint(a, b)` still samples uniformly from integers in
the half-open interval `[a, b)`; Real support does not add continuous sampling.
The checked [random-Real analysis](../tests/proofs/reals_probability.lean)
proves that `randint(0, 2) / 2` returns each of `0` and `1/2` with probability
one-half, preserves the input heap, and terminates with probability one.

The local editor's [Values and collections project](../examples/additional_types/README.md)
includes a planar centroid over tuple-valued real coordinates, alongside small
set and dictionary algorithms.
