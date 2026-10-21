open Algo2LeanCore Algo2LeanGenerated

/-- Exact division has a reusable heap-preserving contract when defined. -/
theorem divide_call (heap : Heap) (numerator denominator : Real)
    (nonzero : denominator ≠ 0) :
    divide.Call heap (numerator, denominator) heap (numerator / denominator) := by
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.divide_pc2 heap
    { v0 := numerator, v1 := denominator } caller nonzero)
  exact Reaches.single (Step.divide_pc1 _ _ caller)

/-- Source division by zero cannot return a value, even though Lean's division is total. -/
theorem divide_zero (heap after : Heap) (numerator output : Real) :
    ¬ divide.Call heap (numerator, 0) after output := by
  intro call
  obtain ⟨_, trace, execution⟩ := divide.Call.run call
  unfold divide.initial start at execution
  cases execution with
  | cons transition tail => cases transition <;> simp_all

/-- Decimal literals denote exact rationals, so the familiar decimal sum is exact. -/
theorem decimal_sum_call (heap : Heap) : decimal_sum.Call heap () heap true := by
  refine ⟨trivial, ?_⟩
  intro caller
  apply Reaches.prepend (Step.decimal_sum_pc2 heap {} caller)
  convert Reaches.single (Step.decimal_sum_pc1 heap _ caller) using 1
  norm_num

/-- An unreached division contributes no definedness obligation. -/
theorem short_circuit_call (heap : Heap) : short_circuit.Call heap () heap false := by
  refine ⟨trivial, ?_⟩
  intro caller
  apply Reaches.prepend (Step.short_circuit_pc2 heap {} caller (by simp))
  exact Reaches.single (Step.short_circuit_pc1 _ _ caller)

/-- A failed earlier comparison skips the later comparison and its zero division. -/
theorem short_chain_call (heap : Heap) : short_chain.Call heap () heap false := by
  refine ⟨trivial, ?_⟩
  intro caller
  apply Reaches.prepend (Step.short_chain_pc2 heap {} caller (by norm_num))
  convert Reaches.single (Step.short_chain_pc1 heap _ caller) using 1
  norm_num

/-- One marker appends its argument to the decimal accumulator and charges one tick. -/
def markHeap (heap : Heap) (values : SeqRef) (value : Int) : Heap :=
  (heap.write values 0 (10 * heap.read values 0 + value)).tick "arguments"

theorem mark_call (heap : Heap) (values : SeqRef) (value : Int)
    (allocated : values < heap.nextRef) :
    mark.Call heap (values, value) (markHeap heap values value) value := by
  refine ⟨allocated, ?_⟩
  intro caller
  apply Reaches.prepend (Step.mark_pc4 heap { v0 := values, v1 := value } caller ⟨allocated, allocated⟩)
  apply Reaches.prepend (Step.mark_pc3 _ _ caller)
  apply Reaches.prepend (Step.mark_pc2 _ _ caller)
  exact Reaches.single (Step.mark_pc1 _ _ caller)

@[simp] theorem markHeap_nextRef (heap : Heap) (values : SeqRef) (value : Int) :
    (markHeap heap values value).nextRef = heap.nextRef := rfl

@[simp] theorem markHeap_read (heap : Heap) (values : SeqRef) (value : Int) :
    (markHeap heap values value).read values 0 = 10 * heap.read values 0 + value := by
  simp [markHeap]

@[simp] theorem markHeap_arguments (heap : Heap) (values : SeqRef) (value : Int) :
    (markHeap heap values value).clocks "arguments" = heap.clocks "arguments" + 1 := by
  simp [markHeap]

/-- The three calls are evaluated from left to right, and their Int results are
    promoted only where required by the surrounding real arithmetic. -/
theorem effect_order_call (heap : Heap) (values : SeqRef)
    (allocated : values < heap.nextRef) :
    effect_order.Call heap values
      (markHeap (markHeap (markHeap heap values 1) values 2) values 3) (-1 + 2 / 3) := by
  refine ⟨allocated, ?_⟩
  intro caller
  apply Reaches.prepend (Step.effect_order_pc13 heap { v0 := values } caller)
  apply Reaches.prepend (Step.effect_order_pc12 _ _ caller)
  apply Reaches.prepend (Step.effect_order_pc11 _ _ caller)
  apply ((mark_call heap values 1 allocated).2 _).trans
  apply Reaches.prepend (Step.effect_order_pc10 _ _ caller)
  apply Reaches.prepend (Step.effect_order_pc9 _ _ caller)
  apply Reaches.prepend (Step.effect_order_pc8 _ _ caller)
  apply Reaches.prepend (Step.effect_order_pc7 _ _ caller)
  apply ((mark_call (markHeap heap values 1) values 2 (by simpa using allocated)).2 _).trans
  apply Reaches.prepend (Step.effect_order_pc6 _ _ caller)
  apply Reaches.prepend (Step.effect_order_pc5 _ _ caller)
  apply Reaches.prepend (Step.effect_order_pc4 _ _ caller)
  apply ((mark_call (markHeap (markHeap heap values 1) values 2) values 3
    (by simpa using allocated)).2 _).trans
  apply Reaches.prepend (Step.effect_order_pc3 _ _ caller (by norm_num))
  apply Reaches.prepend (Step.effect_order_pc2 _ _ caller)
  convert Reaches.single (Step.effect_order_pc1 _ _ caller) using 1
  norm_num

/-- The reusable marker contract also discharges a unary Int-to-Real coercion. -/
theorem unary_cast_call (heap : Heap) (values : SeqRef)
    (allocated : values < heap.nextRef) :
    unary_cast.Call heap values (markHeap heap values 4) (-4) := by
  refine ⟨allocated, ?_⟩
  intro caller
  apply Reaches.prepend (Step.unary_cast_pc5 heap { v0 := values } caller)
  apply Reaches.prepend (Step.unary_cast_pc4 _ _ caller)
  apply Reaches.prepend (Step.unary_cast_pc3 _ _ caller)
  apply ((mark_call heap values 4 allocated).2 _).trans
  apply Reaches.prepend (Step.unary_cast_pc2 _ _ caller)
  convert Reaches.single (Step.unary_cast_pc1 _ _ caller) using 1
  norm_num

/-- An existing Real loop variable receives the exact embedding of each integer index. -/
theorem range_cast_call (heap : Heap) : range_cast.Call heap () heap 3 := by
  refine ⟨trivial, ?_⟩
  intro caller
  apply Reaches.prepend (Step.range_cast_pc12 heap {} caller)
  apply Reaches.prepend (Step.range_cast_pc11 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc10 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc9 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc8 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc7 _ _ caller (by decide))
  -- The fixed range visits exactly 0, 1, and 2.
  apply Reaches.prepend (Step.range_cast_pc3_true _ _ caller (by decide))
  apply Reaches.prepend (Step.range_cast_pc6 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc5 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc4 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc3_true _ _ caller (by decide))
  apply Reaches.prepend (Step.range_cast_pc6 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc5 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc4 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc3_true _ _ caller (by decide))
  apply Reaches.prepend (Step.range_cast_pc6 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc5 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc4 _ _ caller)
  apply Reaches.prepend (Step.range_cast_pc3_false _ _ caller (by decide))
  apply Reaches.prepend (Step.range_cast_pc2 _ _ caller)
  convert Reaches.single (Step.range_cast_pc1 _ _ caller) using 1
  norm_num

/-- The final observation distinguishes order, repeated evaluation, and missing ticks. -/
theorem effect_order_observation (heap : Heap) (values : SeqRef)
    (allocated : values < heap.nextRef) (initial : heap.read values 0 = 0) :
    ∃ after, effect_order.Call heap values after (-1 + 2 / 3) ∧
      after.read values 0 = 123 ∧ after.clocks "arguments" = heap.clocks "arguments" + 3 := by
  refine ⟨_, effect_order_call heap values allocated, ?_, ?_⟩
  · simp [initial]
  · simp [Nat.add_assoc]
