-- Negative arithmetic must stay in Int even when used inside a Bool expression.
example : literal_chain.Returns () true := by algo_steps
example : negative_arithmetic.Returns () (-5) := by algo_steps
example : negative_chain.Returns (-7) true := by algo_steps
example : negative_chain.Returns (-1000000000000000000000000000000) true := by algo_steps

-- Every RHS observes the previous binding until the single assignment commits.
example : boolean_self_and.Returns true false := by algo_steps
example : boolean_self_and.Returns false false := by algo_steps
example : boolean_self_or.Returns true true := by algo_steps
example : boolean_self_or.Returns false false := by algo_steps
example : arithmetic_self.Returns (-3) 6 := by algo_steps
example : pure_update.Returns 4 11 := by algo_steps
example : pure_update.Returns (-3) (-10) := by algo_steps
example : augmented_sequence.Returns 4 (-6) := by algo_steps
example : augmented_sequence.Returns (-3) (-6) := by algo_steps

-- Short-circuit operators and conditionals skip unselected division and remainder
-- expressions, so a zero divisor in an unselected branch cannot block an output.
example : skipped_division.Returns () false := by algo_steps
example : skipped_modulo.Returns () true := by algo_steps
example : selected_branch.Returns (-3) (-4) := by algo_steps

-- Read-only partial expressions preserve short-circuiting and signed Python
-- division; a write observes its old heap until the assignment commits.
example : chained_skip.Returns () false := by algo_steps
example : nested_division.Returns (-9, 2, 7) 1 := by algo_steps
example : nested_division.Returns (9, -2, 7) (-1) := by algo_steps
example : conditional_division.Returns (true, -9) (-5) := by algo_steps
example : conditional_division.Returns (false, -9) 0 := by algo_steps
example : read_before_write.Returns (-7) (-5) := by algo_steps
example : guarded_read.Returns (false, fun _ => 9) false := by algo_steps
example : guarded_read.Returns (true, fun _ => 9) true := by algo_steps
example : nested_short_circuit.Returns () true := by algo_steps

-- Augmented division and remainder use signed Python semantics and a computed
-- divisor; their guards must apply before committing the updated local.
example : augmented_quotient.Returns (-9, 3) (-5) := by algo_steps
example : augmented_quotient.Returns (9, -1) (-5) := by algo_steps
example : augmented_quotient.Returns (-9, -1) 4 := by algo_steps
example : augmented_remainder.Returns (-9, 3) 1 := by algo_steps
example : augmented_remainder.Returns (9, -1) (-1) := by algo_steps
example : augmented_remainder.Returns (-9, -1) (-1) := by algo_steps

-- Boolean operators and chained comparisons produce outputs when their
-- short-circuit conditions skip the expression with a zero divisor.
example : required_and.Returns false false := by algo_steps
example : required_or.Returns true true := by algo_steps
example : required_chain.Returns 0 false := by algo_steps

-- Every possible output is excluded when the zero divisor is actually needed.
-- These proofs inspect the first guarded transition, without global proof search.
theorem augmented_quotient_zero_divisor (input output : Int) :
    ¬ augmented_quotient.Returns (input, 1) output := by
  rintro ⟨_, _, _, execution⟩
  cases execution with
  | cons first _ => cases first <;> simp_all [augmented_quotient.load]

theorem augmented_remainder_zero_divisor (input output : Int) :
    ¬ augmented_remainder.Returns (input, 1) output := by
  rintro ⟨_, _, _, execution⟩
  cases execution with
  | cons first _ => cases first <;> simp_all [augmented_remainder.load]

theorem selected_branch_is_undefined (input output : Int) (selected : 0 ≤ input) :
    ¬ selected_branch.Returns input output := by
  rintro ⟨_, _, _, execution⟩
  cases execution with
  | cons first _ =>
    cases first <;> simp_all [selected_branch.load]
    have negative : input < 0 := of_decide_eq_true ‹decide (input < 0) = true›
    omega

theorem required_and_is_undefined (output : Bool) :
    ¬ required_and.Returns true output := by
  rintro ⟨_, _, _, execution⟩
  cases execution with
  | cons first _ => cases first <;> simp_all [required_and.load]

theorem required_or_is_undefined (output : Bool) :
    ¬ required_or.Returns false output := by
  rintro ⟨_, _, _, execution⟩
  cases execution with
  | cons first _ => cases first <;> simp_all [required_or.load]

theorem required_chain_is_undefined (input : Int) (positive : 0 < input) (output : Bool) :
    ¬ required_chain.Returns input output := by
  rintro ⟨_, _, _, execution⟩
  cases execution with
  | cons first _ => cases first <;> simp_all [required_chain.load]

-- A chained comparison always evaluates its middle operand. A zero divisor in
-- that operand blocks every output, regardless of the first operand's value.
theorem required_middle_is_undefined (input : Int) (output : Bool) :
    ¬ required_middle.Returns input output := by
  rintro ⟨_, _, _, execution⟩
  cases execution with
  | cons first _ => cases first <;> simp_all [required_middle.load]
