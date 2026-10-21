import Algo2LeanLib.Tuple

open Algo2LeanGenerated

/-! Primitive computation and safe generic scalar storage require no Mathlib. -/

example : ObjectValue.asInt (.intValue 3) = some 3 := by decide
example : ObjectValue.asBool (.boolValue true) = some true := by decide
example : (({} : Heap).allocate (fun index => index + 4)).read 0 (-2) = 2 := by decide
example : ObjectValue.asInt (.scalarValue ⟨Int, 3⟩) = none := by decide

example (α : Type) (value : α) :
    (ValueCodec.scalar α).decode ((ValueCodec.scalar α).encode value) = some value :=
  (ValueCodec.scalar α).decode_encode value

private theorem unit_ne_empty : Unit ≠ Empty := by
  intro same
  have impossible : Empty := same ▸ ()
  cases impossible

-- A scalar payload cannot masquerade as a different Lean type.
example : (ValueCodec.scalar Empty).decode (.scalarValue ⟨Unit, ()⟩) = none :=
  ValueCodec.scalar_decode_mk_of_type_ne Empty Unit () unit_ne_empty
