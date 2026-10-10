# Typed sequences and shared elements

Use `Seq[T]` for an infinite mutable sequence whose elements have type `T`.
`Seq[Node]` stores references to `Node` objects; `Seq[Node | None]` also permits
null entries. `Seq[Bool]` and nested types such as `Seq[Seq[Node]]` use the same
operations. Plain `Seq` is shorthand for `Seq[Int]` and keeps its existing Lean
interface.

Every integer is an index, including negative integers. There is no length,
last element, or operation that enumerates the entire sequence. A finite array
algorithm supplies the interval that it intends to use.

## Creating, sharing, and copying

```python
class Node:
    value: Int

    def __init__(self, value: Int) -> None:
        self.value = value

def shared_node(start: Int, changed: Int) -> Int:
    node = Node(start)
    nodes = const(node)
    snapshot = copy(nodes)
    nodes[-1].value = changed
    return snapshot[5].value
```

This returns `changed`. `const(node)` puts the **same object reference** at
every index; it does not create infinitely many independent nodes. `copy(nodes)`
allocates a new sequence with the same element references. Changing a node's
field is consequently visible through either sequence. Replacing `nodes[-1]`
with a different node would change only that position in `nodes`, leaving
`snapshot`'s entries unchanged. The copy is shallow, including when elements
are themselves sequences.

`alias = nodes` shares the sequence itself. `update(nodes, index, node)` changes
that sequence's entry and returns the same sequence reference. Ordinary element
assignment evaluates the right-hand side before its target and index, as with
integer sequences.

An annotation can supply the element type when creating a fresh constant
sequence:

```python
slots: Seq[Node | None] = const(None)
slots[0] = Node(7)
item = slots[0]
if item is not None:
    item.value = 8
```

Mutable sequences are invariant in their element type. An existing
`Seq[Node]` cannot be assigned or passed as `Seq[Node | None]`: that would let
one alias store `None` while another still promises that every element is a
`Node`. The contextual annotation above is safe because `const` creates a
fresh sequence. Each class field, argument, return value, and local variable
keeps its declared sequence type.

## Lean interface

The generated algorithm module includes a small sequence descriptor for each
non-integer sequence type used by the program:

| Source type | Generated descriptor | Lean element type |
| --- | --- | --- |
| `Seq[Node]` | `seq_Node` | `Ref_Node` |
| `Seq[Node \| None]` | `seq_Node_optional` | `Option Ref_Node` |
| `Seq[Bool]` | `seq_Bool` | `Bool` |
| `Seq[Seq[Node]]` | `seq_Seq_Node` | `CollectionRef` |

Each descriptor has type `SequenceType α`, where `α` is the element type. The
operations and their laws live once in the shared library:

| Interface | Meaning |
| --- | --- |
| `seq_Node.valid heap nodes` | The reference identifies an allocated sequence with the expected element type. |
| `seq_Node.get heap nodes index` | `some node` for a readable entry; `none` if the sequence or stored value is incompatible. |
| `seq_Node.set heap nodes index node` | The heap with that entry replaced. |
| `seq_Node.create heap values` | A fresh sequence and updated heap from `values : Int → Ref_Node`. |
| `seq_Node.const heap node` | A fresh sequence containing that reference at every integer index. |
| `seq_Node.copy heap nodes` | A fresh sequence containing the same element references as `nodes`. |

For nullable elements, the getter returns `Option (Option Ref_Node)`:
`some none` is a stored null value, while `none` means the read is unavailable.
These observations use only a supplied heap. They do not require a transcript
or proof that an algorithm reached that heap.

Constructing an input uses the same explicit heap as its element objects:

```lean
let (heap₁, first) := create_Node ({} : Heap) 10
let (heap₂, second) := create_Node heap₁ 20
let (heap₃, nodes) := seq_Node.create heap₂
  (fun index => if index = 0 then first else second)
read_value.Returns (heap₃, (nodes, 0)) 10
```

`create_Node` and `seq_Node.create` describe mathematical inputs; they do not
execute the source constructor. Functions with typed sequence inputs take
`(initialHeap, arguments)` in `f.Returns` and `f.ValidTranscript`. A typed sequence
output is `(finalHeap, sequenceReference)`. The heap is essential for object
elements: the reference alone does not contain their fields or nested
collections. As before, `f.Run` and `f.Call` expose both heaps and
raw references for mutation and reusable call specifications.

Integer sequences retain their compact interface: ordinary `Seq` inputs and
outputs are mathematical functions `Int → Int`, loaded automatically when no
argument requires an explicit heap. In a mixed signature with a class or typed
sequence argument, supply one heap and raw references for all reference
arguments, including integer sequences.

Named-line files also generate `f.Element.nodes configuration index`. Its
return type is `Option α`, so object-sequence analyses can refer directly to
entries without inspecting local-state fields. The accessor is available where
the variable is initialized at a named location. Like other observations it is
local to the supplied configuration, and the named-line module stays separate
from the stable algorithm module.

Validity is deliberately shallow. A sequence descriptor checks the sequence's
allocation and element-type tag; reading an entry checks its value encoding.
Neither recursively traverses object fields or nested sequences. For a read
node's fields, use `is_Node heap node` and `field_Node_value heap node`, just as
when the reference came directly from a function argument. This permits shared
and cyclic structures, and avoids checking infinitely many elements as an input
condition. Well-formed graph, tree, or array invariants belong in the analysis.

See [the source example](../examples/object_sequences.algo) and its
[separate Lean analysis](../examples/analysis/object_sequences.lean) for general
read/update summaries and observations through shared object references.

## Room for Set and Dict

Typed sequences use a common collection reference space and a tagged element
encoding. The element encoding already represents integers, booleans, object
references, nullable values, and other collection references. The sequence
descriptor uses a shared `ValueCodec` containing the encoder, decoder, and their
round-trip law; it is not a
separate heap arena or a new family of runtime operations for every class.

Future `Set[T]` and `Dict[K, V]` can add collection kinds and reuse these element
descriptors, identities, heap threading, and generated input conventions.
Their membership/key operations will need their own semantics and proof laws.
Object keys should be distinguished from equality of mutable object contents;
the current object comparison is reference identity. This change does not add
sets, dictionaries, finite enumeration, or hash-table costs yet.
