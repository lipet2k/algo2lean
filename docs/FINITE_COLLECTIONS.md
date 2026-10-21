# Finite sets and dictionaries

`Set[T]` and `Dict[K, V]` are finite mutable containers. Assignment, argument
passing, and returning a container preserve its identity; `copy` creates a new
outer container. References inside its contents remain shared.

```python
def count(values: Seq, n: Int) -> Dict[Int, Int]:
    counts: Dict[Int, Int] = {}
    for i in range(n):
        value = values[i]
        counts[value] = counts.get(value, 0) + 1
    return counts
```

The input `Seq` still has every integer index. Only the dictionary is finite.
An empty dictionary needs an expected type, supplied by a variable annotation,
parameter, result type, field, or enclosing literal. Empty sets use `set()` and
likewise require an expected `Set[T]`. Nonempty literals can infer their types.

## Operations

| Source | Meaning |
| --- | --- |
| `{a, b}` | New set; duplicate elements occur once |
| `{key: value}` | New dictionary; later duplicate keys replace earlier values |
| `x in values`, `x not in values` | Set membership or dictionary key membership |
| `len(values)` | Number of distinct elements or keys, as `Int` |
| `values.add(x)` | Insert into a set; already present is a no-op |
| `values.discard(x)` | Remove from a set; absent is a no-op |
| `values[key]` | Read a dictionary entry; missing keys fail |
| `values[key] = value` | Insert or replace a dictionary entry |
| `values.get(key, default)` | Read, or use the explicit default when absent |
| `del values[key]` | Delete a dictionary entry; missing keys fail |
| `copy(values)` | Allocate a fresh shallow copy |
| `for key in values` | Iterate a captured list of keys in insertion order |

Literal entries and method arguments evaluate once, left to right. Dictionary
assignment evaluates its right-hand value, then its target container, then its
key. `get` evaluates the default even when the key exists. Duplicate dictionary
literal entries still evaluate all their keys and values, including side effects
and random draws. Container operations do not add implicit ticks.

Values can include tuples, objects, sequences, and nested finite containers.
Keys and set elements support `Int`, `Real`, `Bool`, `None`, concrete object identities,
nullable object identities, and tuples of supported keys. Mutating an object's
fields does not change its identity as a key. Mutable containers cannot be keys.
Real keys use exact mathematical equality through the optional
[Real library](REALS.md), without assuming a hash implementation.

Mutable container types are invariant: an existing `Dict[Int, Node]` cannot
be widened to `Dict[Int, Node | None]`. Fresh literals can use their expected
type, for example `{1: node}` when returning `Dict[Int, Node | None]`.
Boolean and integer key types remain distinct. A missing key is different from
a present key whose stored value is `None`.

Container equality, dictionary views, comprehensions, `set(iterable)`, and
membership comparison chains are outside this initial interface. Use separate
Boolean conditions when combining membership tests.

## Iteration and mutation

Each loop captures the keys once, after evaluating its iterable once. The
snapshot is an internal immutable list, without allocating another source
container. Updating the original container cannot change that snapshot.

```python
def captured_keys() -> Int:
    values = {2: 0, 1: 0, 3: 0}
    result = 0
    for key in values:
        result = 10 * result + key
        if key == 2:
            del values[1]
            values[4] = 0
    return result  # 213: the original keys, in their original order
```

Replacing a dictionary value retains that key's position. Removing and then
reinserting a key moves it to the end of the next snapshot. Sets follow the same
insertion-order convention. This is an explicit `.algo` choice: Python does not
guarantee set insertion order and has different mutation-during-iteration rules.
Only simple variable loop targets are supported initially.

## Lean interface

A container is represented by `CollectionRef` in the shared `Heap`. It uses the
same allocation arena as typed sequences, with a header distinguishing its
kind and source types. Public `Call` statements retain before/after heaps, so
contracts describe aliases, shared mutation, allocation, and clock increments.
`Returns` for a returned container supplies its final heap and reference.

The compiler emits a short typed descriptor, such as `«dict[Int, Int]»` or
`«set[Tuple[Int, Bool]]»`, backed by `Algo2LeanLib.FiniteCollections`:

| Observation/operation | Lean interface |
| --- | --- |
| Validity | `descriptor.valid heap ref : Prop` |
| Membership | `descriptor.contains heap ref key : Bool` |
| Dictionary lookup | `descriptor.get heap ref key : Option Value` |
| Size | `descriptor.size heap ref : Nat` |
| Ordered snapshot | `descriptor.keys heap ref : List Key` |
| Input construction | `descriptor.create heap entries : Heap × CollectionRef` |
| Dictionary update | `descriptor.set heap ref key value : Heap` |
| Set insertion | `descriptor.insert heap ref value : Heap` |
| Removal | `descriptor.erase heap ref key : Heap` |
| Shallow copy | `descriptor.copy heap ref : Heap × CollectionRef` |

Validity checks allocation, the header, every finite key/value decoder, and key
uniqueness. A matching header alone cannot validate malformed or duplicate stored
entries. The check is shallow: it does not recursively inspect referenced object
graphs or infinite sequences. Using those references applies their own normal
validity checks.

The low-level observations are total and use default values for invalid heaps;
generated source instructions require validity, and partial reads/deletions
also require presence. Defaults therefore cannot produce source executions from
invalid input or a missing key.

Use local laws such as `DictType.valid_set`, `DictType.get_set_same`, and
`DictType.get_set_other` to analyze updates without a transcript. Set laws describe
membership and size. Clock-preservation lemmas keep cost proofs separate from
container contents. `Heap.Footprint` preserves every existing collection header
and storage outside the declared footprint. Its allocation and replacement lemmas
support container framing.

The regression proofs include a dictionary-writing helper whose independent
`Call` theorem is reused unchanged by an importing caller. Main statements use
the source-facing `Call`/`ValidInput` and typed descriptors; the caller inspects
only its own transitions. Downloaded analysis packages include the finite
collection and tuple libraries. Containers without Real components need no
Mathlib; Real components additionally include the optional Real library and its
pinned Mathlib dependency.

## Cost model

These are abstract finite containers, represented simply for verification.
An explicit tick can count a lookup or update, but it does not prove constant-time
hashing or another machine implementation. Such bounds require a concrete data
structure and its separately reusable analysis.
