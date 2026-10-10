# Classes and shared data structures

Algo2Lean supports typed mutable objects, constructors, methods, and nullable
object references. This is a first building block for linked lists, trees, and
other textbook data structures. Objects use the same execution and transcript
semantics as functions and mutable sequences.

See [classes.algo](../examples/classes.algo) for a counter and a linked chain.

## Source syntax

```python
class Node:
    value: Int
    next: Node | None

    def __init__(self, value: Int, next: Node | None) -> None:
        self.value = value
        self.next = next

    def sum(self) -> Int:
        tail = self.next
        if tail is None:
            return self.value
        else:
            return self.value + tail.sum()

def two_nodes(a: Int, b: Int) -> Int:
    tail = Node(b, None)
    head = Node(a, tail)
    return head.sum()
```

Declare fields on the class, or use annotated assignments such as
`self.value: Int = value` in `__init__`. These declare instance fields, not
Python-style shared class attributes. Parameters and return types are explicit;
the method receiver is written as the unannotated first parameter `self`.
Methods returning `None` can omit their final return. Initializers (`__init__`)
return `None` and initialize the new object through `self`; the constructor call
`Node(...)` returns the new object.

Fields may contain `Int`, `Bool`, `Seq`, typed sequences such as `Seq[Node]`,
class references, or nullable class references such as `Node | None`.
Nullable fields must be explicitly initialized;
an uninitialized field is different from a field containing `None`.

Assignments share identity: `alias = node` makes both names refer to the same
object. Field assignment through either name affects both. A `Seq` stored in a
field similarly shares the sequence object rather than copying its contents.
Class references may form shared or cyclic structures. Recursion is unrestricted:
the `sum` method above has no output on a cycle that it follows forever.

Use `is None` or `is not None` to test a nullable reference. Accessing a field or
calling a method on `None`, or reading an uninitialized field, has no next
execution step. This is a semantic definedness condition, not a static
requirement that the source contain a null check. A proof of termination must
establish that these accesses are defined, just as it must establish that a
divisor is nonzero. A transcript can still describe the prefix before a failed
access.

The initial implementation does not include inheritance, dynamic attributes,
class attributes, default arguments, properties, or method overriding. Use
`Seq[Node]` for a sequence of object references and `Seq[Node | None]` for
nullable entries. A shallow sequence copy preserves its element references;
see [typed sequences and their Lean interface](COLLECTIONS.md).

## Describing an object in Lean

The generated algorithm module provides source-facing helpers for every class:

| Helper | Meaning |
| --- | --- |
| `Ref_Node` | An object reference used for a `Node`. |
| `is_Node heap node` | The reference is allocated and its class is `Node`. |
| `field_Node_value heap node` | `some value` when the field can be read with its declared type; otherwise `none`. |
| `field_Node_next heap node` | `some none` for a stored null link, `some (some tail)` for a stored reference, and `none` for an unavailable field. |
| `set_Node_value heap node value` | The heap after replacing this object's field. |
| `create_Node heap value next` | A new heap and reference with all declared fields initialized directly. |

`create_Node` is a convenience for describing a mathematical input heap. It
does **not** execute the source constructor or assert that it has that effect.
The constructor's execution is described by the ordinary generated relations.
This distinction matters when a constructor computes values or calls methods.

For example, construct a two-node input with shared heap helpers:

```lean
let (heap₁, tail) := create_Node ({} : Heap) b none
let (heap₂, head) := create_Node heap₁ a (some tail)
-- Use heap₂ and head together in a specification of Node.sum.
```

The reference alone does not contain its fields; the heap records their current
values. Keeping the heap explicit allows statements about aliases, updates,
shared children, and cycles. `is_Node` checks identity and class, not global
list validity or acyclicity. Such data-structure invariants belong in the
analysis and can be reused across functions.

Reference types such as `Ref_Node` are readable aliases of the raw reference
type, not proof-carrying handles. A successful `next` getter says that a
reference was stored; it does not recursively establish the target's class or
fields. Use `is_Node heap tail` when a proof needs to dereference that target.
Field-update helpers describe heaps directly; execution rules separately check
that their receiver is allocated with the expected class. This shallow
representation permits cycles without recursive input-validity checks.

## Function and method specifications

Method relation names include their class: `Node.sum` becomes
`Node.sum.Returns`, `Node.sum.Run`, and `Node.sum.Call`.
The implicit receiver is the first input reference.

If a function takes an object, nullable object, or typed non-integer sequence argument, its output and
transcript interfaces take an explicit input heap and raw argument references.
For example:

```lean
Node.sum.Returns (heap, node) total
read_counter.Returns (heap, counter) value
```

The heap supplies the whole reachable structure and any intended sharing.
Signatures containing only integers, Booleans, and integer sequences keep the existing
ordinary-value interface. Consequently, `counter_alias start delta` in the
example still exposes:

```lean
counter_alias.Returns (start, delta) result
```

An object-valued output includes its final heap with its reference, so it is
meaningful even when the function allocated the object:

```lean
make_node.Returns value (finalHeap, node)
```

Use `f.Run initialHeap arguments finalHeap result` when analyzing a
call's heap effects. Use `f.Call` for a completed execution valid under
any suspended caller stack, so a caller can reuse the method theorem without
inspecting its implementation. A theorem about `Counter.add`, for example,
can specify that the counter's value is increased by `delta` and then be
reused to analyze a call through an alias.

Fields are observations of a supplied heap. These helpers never require a
whole transcript. Named-line observations remain in the companion `Points`
module; class definitions, field helpers, and output predicates stay in the
stable algorithm module. Changing only line names leaves that module unchanged.

## Current proof scope

The [class analysis](../examples/analysis/classes.lean) proves general
`Counter.read` and `Counter.add` summaries, observes an update through an alias,
and reuses a method summary from an ordinary caller.

For nodes, `Chain heap node values` describes a finite nonempty chain through
the public field interface. `last_node_summary` handles a null next link;
`linked_node_summary` composes a proved tail summary with the current value.
Induction gives `chain_sum_summary`: the method terminates with `values.sum`
and preserves the entire heap under any caller stack. The output corollary is
an existence theorem; it does not separately prove output uniqueness. Unrelated
objects and aliases elsewhere in the heap are permitted. No general linked-list
library, cyclic-traversal theorem, or complexity bound is claimed.
