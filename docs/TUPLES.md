# Heterogeneous tuples

Tuples are immutable, fixed-length values. Their entries can have different
types, including references to mutable sequences and objects.

```python
def adjacent(value: Int) -> Tuple[Int, Int]:
    return value, value + 1

def gap(value: Int) -> Int:
    first, second = adjacent(value)
    return second - first
```

Tuple expressions evaluate entries once, from left to right. Unpacking evaluates
its entire right-hand side once before assigning names. Thus `a, b = b, a`
swaps the two values. Nested name patterns such as `a, (b, c) = result` work
when their arities match the value's type.

## Shape and indexing

| Source value | Source type | Lean value type |
| --- | --- | --- |
| `()` | `Tuple[()]` | `Unit` |
| `(3,)` | `Tuple[Int]` | `Tuple1 Int` |
| `(3, True)` | `Tuple[Int, Bool]` | `Int × Bool` |
| `(3, True, 4)` | `Tuple[Int, Bool, Int]` | `Int × Bool × Int` |
| `(3, (True, 4))` | `Tuple[Int, Tuple[Bool, Int]]` | `Int × (Bool × Int)` |

The last two Lean types are definitionally equal, but their source types and
stored encodings remain distinct. A tuple stored in a class field or typed
sequence retains its exact source arity and nesting.

Use a literal integer to select an entry: `pair[0]` is the first entry and
`pair[-1]` is the last. Invalid indices are compile errors. This finite indexing
rule does not change `Seq`, whose negative indices remain independent positions
in an infinite sequence. `(x)` is grouping, not a tuple; use `(x,)` for one entry.

The initial implementation rejects dynamic indices, slices, starred unpacking,
tuple mutation, and unpacking into fields or sequence positions. Equality and
inequality compare components when every component supports equality. Tuples
containing sequences cannot be compared, and tuple ordering and `is` are not
supported. Compatible nullable object entries can widen without copying objects.
Immutable Int entries can also promote to Real when the expected tuple type or
an equality comparison requires it; mutable references inside a tuple keep their
exact container types.

## Shared references

```python
def alias(a: Seq) -> Tuple[Seq, Seq]:
    pair = (a, a)
    pair[0][0] = 7
    return pair
```

The two entries refer to the same sequence. The tuple does not allocate or copy
that sequence, and reading `pair[1][0]` observes the update. Copying an outer
sequence containing tuples is likewise shallow: references inside the tuple
entries retain their identity.

Tuple types work in parameters, returns, fields, typed sequences, imported
signatures, and recursive module groups. Abstract interface references inside
composite values remain outside the current interface-binding support; use
concrete object classes there.

## Lean analysis

Pure tuple arguments and results use ordinary Lean products in `Returns`.
For example, `adjacent.Returns value (value, value + 1)` states the example's
output. The primary reusable contract retains the existing heap interface:

```lean
adjacent.Call heap value heap (value, value + 1)
```

A tuple containing mutable references uses explicit heap and reference values in
its output/input view, preserving aliases. The generated local observations and
`At` predicates work as before. Elementary tuple projection and codec facts do
not require an execution transcript.

`Algo2LeanLib.Tuple` supplies the singleton wrapper and shared typed codecs.
Product proofs use ordinary Lean projections; only singleton values need
`Tuple1.mk` and `.value`. The compiler generates a descriptor for each used
tuple-valued sequence, with a readable quoted name such as
`«seq[Tuple[Int, Bool]]»`. Local field read-after-write and sequence codec laws
reuse the shared round-trip theorem instead of generating a proof for every
tuple shape.

The semantic tests include an independently compiled tuple-returning helper and
a caller whose `Call` proof reuses the helper theorem unchanged. They also check
stored aliases, evaluation order, exact tick counts, malformed tuple encodings,
and an exported analysis package that builds with its own shared library.
Probability companions use the same execution-law interface. A checked two-draw
tuple example proves that every binary pair has probability one quarter and that
returning with the original heap has probability one. The proof calculates the
actual joint distribution, so it also checks that identical draw expressions
produce independent fresh choices.
