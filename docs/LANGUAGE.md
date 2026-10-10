# Algo2Lean language reference

Algo2Lean uses a deliberately small subset of Python syntax. It describes mathematical algorithms for formal verification, not machine execution. The compiler parses source as syntax and never evaluates it as Python.

## Types and signatures

Every function parameter and return value has an explicit type:

| Type | Meaning |
| --- | --- |
| `Int` | Arbitrary mathematical integers, represented by Lean `Int`. |
| `Bool` | `True` or `False`. There is no integer truthiness. |
| `Seq`, `Seq[Int]` | A mutable shared object with mathematical contents `Int → Int` and an element at every integer index. |
| `Seq[T]` | A mutable sequence of values of type `T`, including class references, nullable references, booleans, and nested sequences. |
| A class name, such as `Node` | A reference to an instance of that declared class. |
| `Node \| None` | A nullable class reference; useful for linked structures. |
| `None` | The sole value `None`; represented by Lean `Unit`. |

```python
def select(a: Seq, index: Int) -> Int:
    return a[index]
```

Functions may call later functions, themselves, or each other recursively. Calls are positional and must match their signatures. There are no default parameters, keyword arguments, variadic parameters, nested functions, or higher-order function values.

Local variables may be inferred or annotated. A variable keeps its type:

```python
count: Int = 0
answer = count + 1
```

Names must be initialized on every path reaching their use. A variable introduced only inside a loop is not available afterward, because the loop might run zero times. A variable assigned in both branches of an `if` is available after the branches, provided the continuing paths initialize it consistently.

## Expressions

- Integer literals, including arbitrarily large values; `True`, `False`, and `None`.
- Names and parentheses.
- Integer addition, subtraction, multiplication, unary `+` and `-`.
- Integer floor division `//` and remainder `%`.
- Equality `==` and `!=` between two integers or two booleans; integer ordering `<`, `<=`, `>`, `>=`.
- Boolean `and`, `or`, and `not`.
- Conditional expressions: `value_if_true if condition else value_if_false`.
- Positional function calls.
- Constructors, object field access, and method calls. Class-reference `==` and
  `!=` compare identity; `is` and `is not` support references and `None`.
- Sequence indexing, `const(value)`, `copy(sequence)`, and `update(sequence, index, value)`.

Boolean operations short-circuit from left to right. Therefore `False and diverge()` returns `False` even when `diverge()` never returns. Conditional expressions evaluate only the selected branch. Arithmetic operands and call arguments are evaluated strictly. Chained comparisons preserve short-circuit behavior and evaluate each reached operand once.

`//` rounds toward negative infinity, as in Python: `-7 // 3` is `-3`, and `7 // -3` is `-3`. A remainder has the divisor's sign and satisfies `a == (a // b) * b + a % b` when `b != 0`. Division or remainder by zero has no output. A no-output relation can therefore express a stuck computation as well as divergence; it does not classify why an execution failed to return.

`/` and floating-point numbers are not supported. Booleans are distinct from integers: `True + 1`, `if 1:`, and returning an integer from a `Bool` function are errors. Equality between entire sequences is not a supported condition; compare their individual elements instead.

## Explicit cost counters

`tick("steps")` is a standalone statement that increments the named natural
counter by one. `tick("steps", amount)` adds a nonnegative `Int` amount instead;
zero is allowed, and a negative amount has no next increment step. The amount
expression is evaluated normally, including any function calls. The name must
be a literal string with ASCII identifier syntax.
Counters are shared across calls, methods, and recursion; distinct names are
independent. No source expression reads or resets them, and operations without
ticks do not automatically contribute cost. The author chooses what one tick
represents.

Programs containing ticks additionally expose
`f.ReturnsWithCost input output costs`, where `costs : String → Nat` records
the increments from the same completed execution that produced `output`.
See [the cost guide](COSTS.md) for local observations and call-summary reuse.

## Infinite sequences

`Seq` has contents on **all integer indices**, including negative integers. There is no length, last element, or out-of-bounds index. In particular, `a[-1]` is the value at index `-1`, not indexing relative to an end.

```python
def example(a: Seq) -> Int:
    original = a
    a[-1] = 42
    return original[-1]
```

Assignment shares an object reference, so this example returns 42. Element updates are visible through aliases and function arguments. Rebinding a variable changes only that variable. Use `original = copy(a)` to preserve an independent snapshot of the contents.

```python
def zeros_with_one(index: Int) -> Seq:
    a = const(0)
    return update(a, index, 1)
```

`const(k)` allocates a new object with value `k` at every index. `copy(a)` allocates an independent object with the current contents of `a`. `update(a, i, v)` mutates the existing object and returns the same reference. Any Lean function `Int → Int` can be an input to a generated relation, even when Algo2Lean has no finite expression that constructs that particular sequence.

For object elements, write `Seq[Node]` or `Seq[Node | None]`. `const(node)`
shares that single node at every index. `copy` is shallow: it copies element
references, so changing a referenced object's field remains visible through
both sequences. Replacing one sequence entry does not replace the entry in its
copy. Boolean and nested sequence elements work in the same way.

The element type of an existing mutable sequence cannot be widened. In
particular, `Seq[Node]` cannot be used as `Seq[Node | None]`. An annotation
can guide a fresh allocation, such as
`slots: Seq[Node | None] = const(None)`. Plain `Seq` and `Seq[Int]` are the
same type. See [typed sequences](COLLECTIONS.md) for examples and the Lean
interface. `Set` and `Dict` are not source types yet.

Finite list literals and slices are not sequences in this version. There are no operations that enumerate an entire infinite sequence.

## Statements and control flow

Supported statements are local assignment, annotated assignment, object field assignment, sequence element assignment, `if` / `elif` / `else`, `while`, `for ... in range(...)`, `pass`, and `return`. Integer variables and fields support `+=`, `-=`, `*=`, `//=`, and `%=`. A function, constructor, or method call can also be a statement whose return value is discarded; the call must still terminate before execution continues.

```python
def sum_to(n: Int) -> Int:
    total = 0
    while n > 0:
        total = total + n
        n = n - 1
    return total
```

Conditions must be `Bool`. `return` exits the current function even when it appears inside a loop or nested branch. Functions annotated `-> None` may use a bare return or fall through, returning `None`. Other functions must return a value on every continuing path. An unconditional `while True` may end the function without a following return. This static check recognizes the literal infinite loop; it does not attempt to decide termination in general.

```python
def forever(x: Int) -> Int:
    while True:
        x = x + 1
```

The above is valid. `forever.Returns x y` is false for every `x` and `y` because no finite derivation reaches a return.

`range(stop)`, `range(start, stop)`, and `range(start, stop, step)` use integer bounds and an exclusive stop. Arguments are evaluated once, left to right. Negative steps work; a zero step has no output. Assigning to the loop variable does not change the iterator. An existing loop variable survives an empty range unchanged; a new one is not definitely initialized after the loop.

Top-level Python-style module imports, named imports, and aliases are supported
in algorithm projects. Imports resolve statically within the project root;
relative, wildcard, conditional, function-local, and dynamic imports are not
supported, and source-module import cycles are rejected. See the
[module guide](MODULES.md) for file naming, reexports, and proof reuse.
There are no exceptions, I/O, `break`, `continue`, loop `else` clauses, or
comprehensions. Comments beginning with `#` and blank lines are allowed.

## Classes

Classes have fixed, explicitly typed instance fields and positional methods.
Declare fields in the class body or with `self.field: Type = value` inside
`__init__`. An initializer is annotated `-> None`; calling `ClassName(...)`
allocates an object, runs that initializer, then returns the object reference.
Method parameters begin with `self`, whose class type is implicit.

Field declarations do not initialize values. Reading an uninitialized field or
dereferencing `None` is undefined and has no execution step. Nullable links must
be explicitly assigned `None` when that is the intended value. Object aliases,
shared sequence fields, and cycles are supported. Inheritance, dynamically added
attributes, class attributes, properties, and custom special methods other than
`__init__` are not supported.

Evaluation follows Python's ordering: constructor arguments precede allocation;
method receiver lookup precedes arguments; field assignment evaluates its RHS
before its target; augmented field assignment captures the receiver and old
field value before its RHS. See [the classes guide](CLASSES.md) for examples and
heap-aware specifications.

## Generated propositions

For data structures, terminology, and a practical Lean API guide, see
[Using the generated Lean interface](LEAN_INTERFACE.md).

Every source function `f` gets a public proposition `f.Returns` with exactly two arguments: its input and output. These are named `my_input` and `my_output`.

The following table describes signatures using primitive values and integer
sequences. If any input is a class reference or non-integer typed sequence,
`my_input` is `(initialHeap, rawArguments)`, preserving the object graph and
aliases. If the output has one of those types, `my_output` is
`(finalHeap, reference)`. Nullable class references follow the same convention.

| Source arguments | Type of `my_input` | Example |
| --- | --- | --- |
| None | `Unit` | `f.Returns () result` |
| One `x: Int` | `Int` | `f.Returns 3 result` |
| Two `x: Int, a: Seq` | `Int × Seq` | `f.Returns (3, a) result` |
| Three `x: Int, y: Int, z: Int` | `Int × Int × Int` | `f.Returns (1, 2, 3) result` |

Internal state records and one inductive `Step` relation encode program control flow and call results, threading the shared heap through calls. The shared `Algo2LeanCore.Valid` relation checks finite lists of configurations. Only transcripts ending in a completed root return can construct an output proof. No execution occurs during compilation, and compilation does not require a termination argument.

Lean accepts these finite-derivation definitions through its ordinary [inductive type rules](https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=inductive-datatypes-parameters-and-indices). This avoids using Lean's `partial` functions as the logical meaning of a potentially nonterminating algorithm; see Lean's [recursive definitions reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/).

In the table above, source `Seq` means the Lean contents type
`Algo2LeanGenerated.Seq`. The output convenience view loads each integer
sequence argument into a separate object. For aliases and mutations, use
`f.Run initialHeap input finalHeap output`, where integer sequence inputs and outputs are `SeqRef`
references and typed non-integer sequences use `CollectionRef`.

Project compilation gives each source module its own Lean namespace and
Generated, Points, and optional Facts modules. Imported declarations retain the
identity of their defining module, and callers can reuse its companion Lean
analysis unchanged. Use the project workflow in [the module guide](MODULES.md)
to combine algorithms. Standalone compilation remains available, but pasting
several default standalone outputs into one namespace can cause name collisions.

Identifiers use ASCII letters, digits, and underscores. Type names and `const`, `copy`, `update`, `range`, and `tick` are reserved. Variables cannot shadow function names. The compiler checks unreachable code as well, so unsupported syntax is still rejected after a return. Source is limited to 200,000 characters and 12,000 syntax nodes to keep the local editor responsive; these are compilation resource limits and do not bound integers, sequence indices, or the length of a mathematical execution.

The compiler is not a theorem prover for arbitrary source programs. **Check both files** verifies the generated Lean definitions, while proving a desired algorithm property remains a Lean proof task. The semantic proof tests provide examples of this distinction.

## Finite transcripts and named locations

The general algorithm file imports `Algo2Lean`; use `--standalone` to embed the same library.
The separate `Points.lean` companion imports the algorithm file and contains only
named locations and getters. Editing line names leaves the general file unchanged.
The library is reusable across algorithms and contains no algorithm-specific
interpreter. The compiler emits direct constructors for each lowered instruction
in one `Step` relation.

A configuration is either an active function frame (program counter and local
variables), heap, and suspended caller stack, or a completed result and heap.
`Transcript` is `List Configuration`. `Algo2LeanCore.Valid Step initial trace final`
requires a nonempty list including both endpoints and a valid transition between
each adjacent pair. It may stop before a return, even inside a diverging call.

`f.ValidTranscript input trace` accepts ordinary mathematical inputs and uses the
same automatic input loader as `f.Returns`. Both allocate a separate object for
each sequence argument, even when two arguments have equal contents.
`f.ValidHeapTranscript heap input trace` is the advanced form with explicit
references and input validity. `f.Run` describes a completed run with an
explicit initial and final heap. All views refer to the same `Step` and `Valid`;
there is no separate output evaluator.

Put each label on its own comment line immediately above the statement, at
the same indentation. Do not leave a blank or comment line between them.
Inline labels are not supported. For example:

```python
def assign() -> Int:
    # @set_a
    a = 1
    # @ready
    return a
```

`assign.At.set_a cfg` means the active frame is immediately before the assignment.
`assign.At.ready cfg` means it is before the return. Locations alone do not assert
reachability; membership in a valid transcript supplies that fact.
`assign.Local.a cfg : Option Int` is `some value` at named locations where `a` is
definitely initialized, and `none` elsewhere. In this example it is available at
`ready`, not `set_a`. Unlabeled programs generate no local accessors. For a named
sequence variable, `f.Element.a cfg index : Option Int` directly reads an element
from that configuration's heap. The lower-level `f.Local.a` retains its object
reference for identity and aliasing proofs.

A named `while` marks the start of each condition evaluation, including the final
false check. A named `for` marks the start of range-bound initialization once per
entry to that loop statement. Name a statement inside the body to observe each
iteration. Labels do not add transitions; `pass` always has a no-op transition.
Only source statements can be labeled, and labels are unique within a function.
Read-only expressions are emitted directly as Lean expressions with definedness
conditions for sequence access, division, and remainder. A variable assignment
using such an expression is one transition. Calls, allocation, and mutation
retain sequential evaluation. Expressions with effects can therefore span
multiple steps; transcript positions and internal PC numbers are not source-line
numbers or stable costs.

For local reasoning, prove `Step before after → P before → Q after`. The shared
`Valid.lift`, `Valid.invariant`, and `Valid.all_states` lemmas reuse local facts on
arbitrary histories, without constructing one. `Valid.append` and `Reaches.trans`
compose segments. `Valid.final_mem` places the final configuration in the same
transcript, so a theorem about every member also applies there. `f.Call` describes a completed call under any caller stack;
use it for reusable callee proofs, and `Summary.root` to specialize to a root call.
An arbitrary `f.Returns` theorem is not automatically converted into such a
contextual summary; prove `f.Call` when a contract must be reused by callers.

Visit counters, a dedicated “before the k-th visit” predicate, infinite transcript
data, and automatic invariant generation are not implemented. Finite prefixes
already support observations during nontermination. See the
[transcript analysis](../examples/analysis/transcripts.lean) and
[divergence analysis](../examples/analysis/divergence.lean) for checked examples.
