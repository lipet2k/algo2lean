import Algo2LeanReal
import Algo2LeanLib.FiniteCollections

open Algo2LeanGenerated

namespace ScalarStorage
noncomputable section

private theorem unit_ne_real : Unit ≠ ℝ := by
  intro same
  haveI : Subsingleton ℝ := same ▸ (inferInstance : Subsingleton Unit)
  exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)

example : ValueCodec.real.decode (.scalarValue ⟨Unit, ()⟩) = none :=
  ValueCodec.scalar_decode_mk_of_type_ne ℝ Unit () unit_ne_real

example (value : ℝ) : ValueCodec.real.decode (ValueCodec.real.encode value) = some value :=
  ValueCodec.real.decode_encode value

def pairs : ValueCodec (ℝ × Int) :=
  ValueCodec.tuple (TupleFields.cons ValueCodec.real (TupleFields.last ValueCodec.int))

example (value : ℝ × Int) : pairs.decode (pairs.encode value) = some value :=
  pairs.decode_encode value

def sequence : SequenceType ℝ where
  name := "Real"
  toValueCodec := ValueCodec.real

example (heap : Heap) (values : Int → ℝ) (index : Int) :
    sequence.get (sequence.create heap values).1 (sequence.create heap values).2 index =
      some (values index) := sequence.get_create heap values index

example (heap : Heap) (ref : CollectionRef) (index : Int) (value : ℝ)
    (valid : sequence.valid heap ref) :
    sequence.get (sequence.set heap ref index value) ref index = some value :=
  sequence.get_set_same heap ref index value valid

-- Dictionary values need a codec, but no equality operation on their type.
def scalarValues (α : Type) : DictType Int α where
  keyName := "Int"
  valueName := "Scalar"
  key := ValueCodec.int
  value := ValueCodec.scalar α
  keyEq := inferInstance

theorem lookup_updated_scalar (α : Type) (heap : Heap) (ref : CollectionRef)
    (key : Int) (value : α) (valid : (scalarValues α).valid heap ref) :
    (scalarValues α).get ((scalarValues α).set heap ref key value) ref key = some value :=
  (scalarValues α).get_set_same heap ref key value valid

example (heap : Heap) (ref : CollectionRef) (key : Int) (value : ℝ)
    (valid : (scalarValues ℝ).valid heap ref) :
    (scalarValues ℝ).get ((scalarValues ℝ).set heap ref key value) ref key = some value :=
  lookup_updated_scalar ℝ heap ref key value valid

def realKeys : DictType ℝ Int where
  keyName := "Real"
  valueName := "Int"
  key := ValueCodec.real
  value := ValueCodec.int
  keyEq := Classical.decEq ℝ

example (heap : Heap) (ref : CollectionRef) (key : ℝ) (value : Int)
    (valid : realKeys.valid heap ref) :
    realKeys.get (realKeys.set heap ref key value) ref key = some value :=
  realKeys.get_set_same heap ref key value valid

def realSet : SetType ℝ where
  name := "Real"
  toValueCodec := ValueCodec.real
  keyEq := Classical.decEq ℝ

example (heap : Heap) (ref : CollectionRef) (value : ℝ)
    (valid : realSet.valid heap ref) :
    realSet.contains (realSet.insert heap ref value) ref value = true :=
  realSet.contains_insert_same heap ref value valid

example (heap : Heap) (value : ℝ) :
    (((heap.allocateObject "Box").writeField heap.nextObject "value"
      (ValueCodec.real.encode value)).readField heap.nextObject "value").bind
        ValueCodec.real.decode = some value := by
  rw [Heap.readField_writeField_same _ _ _ _ "Box" (Heap.objectClass_allocateObject_new heap "Box")]
  exact ValueCodec.real.decode_encode value

end
end ScalarStorage
