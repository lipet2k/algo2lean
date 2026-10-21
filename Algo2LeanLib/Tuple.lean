import Algo2Lean

/-!
Immutable heterogeneous tuples use ordinary Lean products. The singleton wrapper
preserves the distinction between a single value and a tuple with one entry.
Stored tuples retain their exact arity and nesting; object and collection entries
encode their existing references without allocating or copying their contents.
-/

namespace Algo2LeanGenerated

/-- A one-entry tuple, distinct from its entry's type and from an empty tuple. -/
structure Tuple1 (α : Type u) where
  value : α
  deriving Inhabited, DecidableEq

namespace ValueCodec

def int : ValueCodec Int where
  encode := .intValue
  decode := ObjectValue.asInt
  decode_encode := fun _ => rfl

def bool : ValueCodec Bool where
  encode := .boolValue
  decode := ObjectValue.asBool
  decode_encode := fun _ => rfl

def seq : ValueCodec SeqRef where
  encode := .seqValue
  decode := ObjectValue.asSeq
  decode_encode := fun _ => rfl

def collection : ValueCodec CollectionRef where
  encode := .collectionValue
  decode := ObjectValue.asCollection
  decode_encode := fun _ => rfl

def object : ValueCodec ObjectRef where
  encode := .objectValue
  decode := ObjectValue.asObject
  decode_encode := fun _ => rfl

def unit : ValueCodec Unit where
  encode := fun _ => .noneValue
  decode := ObjectValue.asNone
  decode_encode := by intro value; cases value; rfl

def nullableObject : ValueCodec (Option ObjectRef) where
  encode := fun value => match value with
    | some ref => .objectValue ref
    | none => .noneValue
  decode := ObjectValue.asNullableObject
  decode_encode := by intro value; cases value <;> rfl

/-- Optional mathematical scalars use a checked dependent box. Primitive codecs
    keep their direct computable decoders and do not invoke this type comparison. -/
noncomputable def scalar (α : Type) : ValueCodec α where
  encode value := .scalarValue ⟨α, value⟩
  decode value := match value with
    | .scalarValue stored => stored.get α
    | _ => none
  decode_encode := ScalarValue.get_mk α

@[simp] theorem scalar_decode_mk_of_type_ne (α β : Type) (value : β)
    (different : β ≠ α) :
    (scalar α).decode (.scalarValue ⟨β, value⟩) = none :=
  ScalarValue.get_of_type_ne α ⟨β, value⟩ different

end ValueCodec

/-- A fixed tuple shape encoded as a list of tagged entries. A successful decode
    consumes the complete list, so extra entries never disappear silently. -/
structure TupleFields (α : Type) where
  encode : α → List ObjectValue
  decode : List ObjectValue → Option α
  decode_encode : ∀ value, decode (encode value) = some value

namespace TupleFields

/-- The empty tuple has no entries and is represented by `Unit`. -/
def empty : TupleFields Unit where
  encode := fun _ => []
  decode := fun values => match values with
    | [] => some ()
    | _ => none
  decode_encode := by intro value; cases value; rfl

/-- The final entry of a product spine; decoding requires exactly one entry. -/
def last (entry : ValueCodec α) : TupleFields α where
  encode := fun value => [entry.encode value]
  decode := fun values => match values with
    | [value] => entry.decode value
    | _ => none
  decode_encode := entry.decode_encode

/-- A singleton preserves its source tuple shape in the Lean-facing type. -/
def singleton (entry : ValueCodec α) : TupleFields (Tuple1 α) where
  encode := fun value => [entry.encode value.value]
  decode := fun values => match values with
    | [value] => (entry.decode value).map Tuple1.mk
    | _ => none
  decode_encode := by
    intro value
    cases value
    simp [entry.decode_encode]

/-- Prepend one entry to the remaining fields of a heterogeneous tuple. -/
def cons (entry : ValueCodec α) (rest : TupleFields β) : TupleFields (α × β) where
  encode := fun value => entry.encode value.1 :: rest.encode value.2
  decode := fun values => match values with
    | head :: tail => do
      let first ← entry.decode head
      let remaining ← rest.decode tail
      return (first, remaining)
    | [] => none
  decode_encode := by
    intro value
    simp [entry.decode_encode, rest.decode_encode]

end TupleFields

/-- Store a complete tuple as one value. Nested tuple codecs introduce another
    wrapper, distinguishing `(a, (b, c))` from `(a, b, c)` in the heap. -/
def ValueCodec.tuple (fields : TupleFields α) : ValueCodec α where
  encode := fun value => .tupleValue (fields.encode value)
  decode := fun value => match value with
    | .tupleValue values => fields.decode values
    | _ => none
  decode_encode := fields.decode_encode

end Algo2LeanGenerated
