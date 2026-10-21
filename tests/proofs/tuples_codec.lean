import Algo2LeanLib.Tuple
open Algo2LeanGenerated

def pairCodec : ValueCodec (Int × Bool) :=
  .tuple (.cons .int (.last .bool))

def tripleCodec : ValueCodec (Int × Bool × Option ObjectRef) :=
  .tuple (.cons .int (.cons .bool (.last .nullableObject)))

def nestedCodec : ValueCodec (Int × (Bool × Option ObjectRef)) :=
  .tuple (.cons .int (.last (.tuple (.cons .bool (.last .nullableObject)))))

example (value : Int × Bool × Option ObjectRef) :
    tripleCodec.decode (tripleCodec.encode value) = some value :=
  tripleCodec.decode_encode value

example (value : Int × (Bool × Option ObjectRef)) :
    nestedCodec.decode (nestedCodec.encode value) = some value :=
  nestedCodec.decode_encode value

example : pairCodec.decode (.tupleValue [.intValue 4]) = none := rfl
example : pairCodec.decode (.tupleValue [.intValue 4, .boolValue true, .noneValue]) = none := rfl
example : pairCodec.decode (.tupleValue [.boolValue false, .boolValue true]) = none := rfl
example : nestedCodec.decode (tripleCodec.encode (3, true, none)) = none := rfl
example : tripleCodec.decode (nestedCodec.encode (3, true, none)) = none := rfl
example : (ValueCodec.tuple TupleFields.empty).decode .noneValue = none := rfl
example : (ValueCodec.tuple TupleFields.empty).decode (.tupleValue []) = some () := rfl
example : (ValueCodec.tuple (.singleton .int)).decode (.tupleValue [.intValue 9]) =
    some (Tuple1.mk 9) := rfl
example : (ValueCodec.tuple (.singleton .int)).decode (.intValue 9) = none := rfl
example : (ValueCodec.tuple (.singleton .int)).decode (.tupleValue []) = none := rfl
example : (ValueCodec.tuple (.singleton .int)).decode (.tupleValue [.intValue 9, .intValue 10]) = none := rfl
example (value : Tuple1 (Option ObjectRef)) :
    (ValueCodec.tuple (.singleton .nullableObject)).decode
      ((ValueCodec.tuple (.singleton .nullableObject)).encode value) = some value :=
  (ValueCodec.tuple (.singleton .nullableObject)).decode_encode value
example : DecidableEq (Tuple1 Int) := inferInstance
example : Inhabited (Tuple1 Int) := inferInstance

def pairSequence : SequenceType (Int × Bool) where
  toValueCodec := pairCodec
  name := "Tuple[Int,Bool]"

example (heap : Heap) (value : Int × Bool) (index : Int) :
    pairSequence.get (pairSequence.const heap value).1
      (pairSequence.const heap value).2 index = some value :=
  pairSequence.get_const heap value index
