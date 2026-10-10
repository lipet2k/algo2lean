open Algo2LeanCore

def oneClock (name : String) (amount : Nat) : Clocks :=
  fun other => if other = name then amount else 0

-- A transition at count_once's named tick adds exactly 1 to the steps clock;
-- the local fact requires no reachability hypothesis.
theorem tick_local {before after : Configuration}
    (transition : Step before after) (location : count_once.At.before before) :
    count_once.At.after after ∧ clock after "steps" = clock before "steps" + 1 := by
  cases transition <;>
    simp_all [count_once.At.before, count_once.At.after, clock, Config.heap]

theorem count_once_summary (heap : Heap) (x : Int) :
    count_once.Call heap x (heap.tick "steps") (x + 1) := by
  refine ⟨True.intro, ?_⟩
  intro stack
  algo_steps

theorem count_once_cost (x : Int) :
    count_once.ReturnsWithCost x (x + 1) (oneClock "steps" 1) := by
  refine ⟨({} : Heap).tick "steps", ?_, ?_⟩
  · exact ⟨True.intro, (count_once_summary {} x).2.root⟩
  · funext name
    by_cases same : name = "steps" <;> simp [Heap.cost, Heap.tick, oneClock, same, count_once.load]

-- The ordinary output statement follows from the same witnessed execution.
example (x : Int) : count_once.Returns x (x + 1) := (count_once_cost x).returns

def pairCosts : Clocks := fun name =>
  if name = "steps" then 2 else if name = "calls" then 1 else 0

theorem nested_calls_share_counters : pair_calls.ReturnsWithCost 40 42 pairCosts := by
  refine ⟨((({} : Heap).tick "calls").tick "steps").tick "steps", ?_, ?_⟩
  · algo_steps
  · funext name
    by_cases steps : name = "steps" <;> by_cases calls : name = "calls" <;>
      simp_all [Heap.cost, Heap.tick, pairCosts, pair_calls.load]

theorem recursion_shares_counters :
    recursive_count.ReturnsWithCost 3 3 (oneClock "steps" 3) := by
  refine ⟨((({} : Heap).tick "steps").tick "steps").tick "steps", ?_, ?_⟩
  · algo_steps
  · funext name
    by_cases same : name = "steps" <;> simp [Heap.cost, Heap.tick, oneClock, same, recursive_count.load]

-- Input clocks can be nonzero. Cost measures increments, not final readings.
def nonzeroInput : Heap × Ref_Box :=
  create_Box ({ clocks := fun _ => 17 } : Heap) 8

theorem nonzero_initial_counts_are_subtracted :
    count_box.ReturnsWithCost nonzeroInput 8 (oneClock "steps" 1) := by
  refine ⟨nonzeroInput.1.tick "steps", ?_, ?_⟩
  · algo_steps
  · funext name
    by_cases same : name = "steps" <;> simp [Heap.cost, Heap.tick, oneClock, same, count_box.load]

def mutationHeap : Heap :=
  let first := (({} : Heap).tick "steps").allocate (fun _ => 0)
  let written := first.write 0 (-1) 7
  let copied := written.allocate (written.store 0)
  let initialized := set_Box_value ((copied.allocateObject "Box").tick "allocations") 0 3
  let bumped := set_Box_value (initialized.tick "steps") 0 4
  bumped.tick "writes"

def mutationCosts : Clocks := fun name =>
  if name = "steps" then 2 else
  if name = "allocations" then 1 else
  if name = "writes" then 1 else 0

theorem heap_operations_and_methods_preserve_counters :
    mutate_and_count.ReturnsWithCost () 11 mutationCosts := by
  refine ⟨mutationHeap, ?_, ?_⟩
  · algo_steps
  · funext name
    by_cases steps : name = "steps" <;>
      by_cases allocations : name = "allocations" <;>
      by_cases writes : name = "writes" <;>
      simp_all [Heap.cost, mutationHeap, Heap.tick, mutationCosts,
        set_Box_value, mutate_and_count.load]

-- A dynamic mathematical weight is charged exactly when it is nonnegative.
theorem weighted_cost (amount : Int) (nonnegative : 0 ≤ amount) :
    weighted.ReturnsWithCost amount amount (oneClock "weighted" amount.toNat) := by
  refine ⟨({} : Heap).tick "weighted" amount.toNat, ?_, ?_⟩
  · algo_steps
  · funext name
    by_cases same : name = "weighted" <;>
      simp [Heap.cost, Heap.tick, oneClock, same, weighted.load]

example : weighted.ReturnsWithCost 0 0 (fun _ => 0) := by
  have zero : oneClock "weighted" 0 = (fun _ => 0) := by
    funext name
    simp [oneClock]
  simpa only [Int.toNat_zero, zero] using weighted_cost 0 (by decide)

theorem negative_weight_has_no_output (amount : Int) (negative : amount < 0) (output : Int) :
    ¬ weighted.Returns amount output := by
  have terminal : Terminal Step (weighted.initial {} amount) := by
    intro next transition
    unfold weighted.initial start at transition
    cases transition
    rename_i defined
    change 0 ≤ amount at defined
    omega
  rintro ⟨heap, _, trace, run⟩
  cases run with
  | cons transition _ => exact terminal _ transition

theorem effectful_weight_cost :
    weighted_call.ReturnsWithCost 4 0
      (fun name => if name = "weighted" then 4 else if name = "effects" then 1 else 0) := by
  refine ⟨(({} : Heap).tick "effects").tick "weighted" 4, ?_, ?_⟩
  · algo_steps
  · funext name
    by_cases weighted : name = "weighted" <;> by_cases effects : name = "effects" <;>
      simp_all [Heap.cost, Heap.tick, weighted_call.load]

theorem unit_cost : return_unit.ReturnsWithCost () () (oneClock "returned" 1) := by
  refine ⟨({} : Heap).tick "returned", ?_, ?_⟩
  · algo_steps
  · funext name
    by_cases same : name = "returned" <;>
      simp [Heap.cost, Heap.tick, oneClock, same, return_unit.load]

theorem sequence_cost :
    return_sequence.ReturnsWithCost () (fun _ => 3) (oneClock "returned" 1) := by
  refine ⟨(({} : Heap).tick "returned").allocate (fun _ => 3), 0, ?_, rfl, ?_⟩
  · algo_steps
  · funext name
    by_cases same : name = "returned" <;>
      simp [Heap.cost, Heap.tick, oneClock, same, return_sequence.load]

def returnedObject : Heap × Ref_Box :=
  create_Box ((({} : Heap).tick "returned").tick "allocations") 2

theorem object_cost :
    return_object.ReturnsWithCost () returnedObject
      (fun name => if name = "returned" then 1 else if name = "allocations" then 1 else 0) := by
  refine ⟨?_, ?_⟩
  · algo_steps
  · funext name
    by_cases returned : name = "returned" <;> by_cases allocations : name = "allocations" <;>
      simp_all [Heap.cost, Heap.tick, return_object.load, returnedObject,
        create_Box, set_Box_value]

theorem nullable_cost :
    return_nullable.ReturnsWithCost () (({} : Heap).tick "returned", none)
      (oneClock "returned" 1) := by
  refine ⟨?_, ?_⟩
  · algo_steps
  · funext name
    by_cases same : name = "returned" <;>
      simp [Heap.cost, Heap.tick, oneClock, same, return_nullable.load]

-- Cost forgetting and recovering use the same output semantics for every result kind.
example : return_unit.Returns () () := unit_cost.returns
example : return_sequence.Returns () (fun _ => 3) := sequence_cost.returns
example : return_object.Returns () returnedObject := object_cost.returns
example : return_nullable.Returns () (({} : Heap).tick "returned", none) := nullable_cost.returns
example : ∃ costs, return_unit.ReturnsWithCost () () costs := unit_cost.returns.withCost
example : ∃ costs, return_sequence.ReturnsWithCost () (fun _ => 3) costs := sequence_cost.returns.withCost
example : ∃ costs, return_object.ReturnsWithCost () returnedObject costs := object_cost.returns.withCost
example : ∃ costs, return_nullable.ReturnsWithCost () (({} : Heap).tick "returned", none) costs :=
  nullable_cost.returns.withCost

def spinHeap (heap : Heap) : Nat → Heap
  | 0 => heap
  | n + 1 => (spinHeap heap n).tick "spin"

def spinBefore (heap : Heap) (n : Nat) : Configuration :=
  .active (spinHeap heap n) (.fn_spin 3 { t0 := true }) []

theorem spin_reaches_each_count (heap : Heap) (n : Nat) :
    Reaches Step (spin.initial heap ()) (spinBefore heap n) := by
  induction n with
  | zero => algo_steps
  | succ n previous =>
    apply previous.trans
    algo_steps

theorem spin_count (heap : Heap) (n : Nat) :
    clock (spinBefore heap n) "spin" = heap.clocks "spin" + n := by
  change (spinHeap heap n).clocks "spin" = _
  induction n with
  | zero => rfl
  | succ n previous => simpa [spinHeap, previous, Nat.add_assoc]

-- A diverging algorithm has finite valid transcripts reaching every tick count.
theorem divergent_finite_prefixes (heap : Heap) (n : Nat) :
    ∃ trace, spin.ValidHeapTranscript heap () trace ∧
      ∃ state ∈ trace, spin.At.again state ∧ clock state "spin" = heap.clocks "spin" + n := by
  obtain ⟨trace, valid⟩ := spin_reaches_each_count heap n
  exact ⟨trace, ⟨True.intro, _, valid⟩, _, valid.final_mem, True.intro, spin_count heap n⟩

private def spinRegion : Configuration → Prop
  | .active _ (.fn_spin pc _) _ => pc = 0 ∨ pc = 1 ∨ pc = 2 ∨ pc = 3
  | _ => False

theorem spin_has_no_output : ¬ spin.Returns () () := by
  rintro ⟨heap, _, trace, valid⟩
  have impossible := valid.invariant spinRegion (by simp [spinRegion, spin.load, spin.initial, start])
    (by intro before after transition inside; cases transition <;> simp_all [spinRegion])
  exact impossible

-- Evaluating a weight can have effects, even when the subsequent negative tick
-- is undefined. The prefix records those effects without fabricating a charge.
def rejectedWeight : Configuration :=
  .active (({} : Heap).tick "effects") (.fn_weighted_call 3 { v0 := -1, t2 := -1, t3 := -1 }) []

theorem negative_effectful_weight_prefix :
    ∃ trace, weighted_call.ValidHeapTranscript {} (-1) trace ∧
      rejectedWeight ∈ trace ∧ clock rejectedWeight "effects" = 1 ∧
      clock rejectedWeight "weighted" = 0 ∧ Terminal Step rejectedWeight := by
  have reaches : Reaches Step (weighted_call.initial {} (-1)) rejectedWeight := by
    algo_steps
  obtain ⟨trace, valid⟩ := reaches
  refine ⟨trace, ⟨True.intro, _, valid⟩, valid.final_mem, rfl, rfl, ?_⟩
  intro after transition
  unfold rejectedWeight at transition
  cases transition
  rename_i negative
  contradiction
