import Algo.composable_dijkstra.support.fibonacci_heap.Analysis
import Algo.composable_dijkstra.priority_queue.Analysis

/-! The Fibonacci implementation supplies the abstract queue contract once.
    The bridge is instantiated by generated interface-binding theorems; neither
    this module nor the heap proof imports a graph algorithm. -/

namespace FibonacciQueueAnalysis

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap
open Algo.fibonacci_heap.Algo2LeanGenerated
open Algo.composable_dijkstra.priority_queue
open FibonacciModuleAnalysis PriorityQueueAnalysis

/-- A generated binding transfers public heap summaries to interface summaries. -/
structure Bridge (code : PriorityQueue.Code) : Prop where
  valid : ∀ heap queue, code.valid heap queue = true ↔ is_FibonacciHeap heap queue
  is_empty : ∀ {before after queue result},
    FibonacciHeap.is_empty.Call before queue after result →
    PriorityQueue.is_empty.Call code before queue after result
  update : ∀ {before after queue vertex key},
    FibonacciHeap.push_or_decrease.Call before (queue, vertex, key) after () →
    PriorityQueue.push_or_decrease.Call code before (queue, vertex, key) after ()
  extract : ∀ {before after queue vertex},
    FibonacciHeap.pop_min.Call before queue after vertex →
    PriorityQueue.pop_min.Call code before queue after vertex

structure State where
  layout : Layout
  forest : Algo2Lean.Fibonacci.Forest

/-- Protected client sequences are separate from the queue's private storage. -/
structure Rep (queue : ObjectRef) (protection : Protected) (capacity : Int)
    (heap : Heap) (state : State) : Prop where
  represented : QueueRep heap queue state.layout state.forest
  separate : ∀ ref ∈ protection.sequences, ref ∉ state.layout.refs
  bounded : ∀ vertex key, (vertex, key) ∈ state.forest.entries → 0 ≤ vertex ∧ vertex < capacity

theorem Rep.tick {queue protection capacity heap state}
    (rep : Rep queue protection capacity heap state) (clock : String) (amount : Nat) :
    Rep queue protection capacity (heap.tick clock amount) state := by
  refine ⟨⟨Layout.Valid.tick _ _ _ rep.represented.layoutValid _ _, ?_⟩, rep.separate, rep.bounded⟩
  simpa only [snapshot_tick] using rep.represented.represented

theorem Rep.write {queue protection capacity heap state}
    (rep : Rep queue protection capacity heap state) (ref : SeqRef) (guarded : ref ∈ protection.sequences)
    (index value : Int) : Rep queue protection capacity (heap.write ref index value) state := by
  have outside := rep.separate ref guarded
  have read (target : SeqRef) (member : target ∈ state.layout.refs) :
      (heap.write ref index value).read target = heap.read target := by
    funext position
    apply Heap.read_write_other_ref
    intro same
    exact outside (same ▸ member)
  have unchanged : snapshot (heap.write ref index value) state.layout = snapshot heap state.layout := by
    unfold snapshot
    congr 1 <;> apply read <;> simp [Layout.refs]
  refine ⟨⟨Layout.Valid.write _ _ _ rep.represented.layoutValid _ _ _, ?_⟩, rep.separate, rep.bounded⟩
  rw [unchanged]
  exact rep.represented.represented

/-- The seven instrumented heap event categories, each with unit weight. -/
def metric : List (String × Nat) := heapClocks.map fun name => (name, 1)

theorem measured_work (before after : Heap) :
    Clocks.weighted metric (Heap.cost before after) = heapEventWork before after := by
  simp [metric, heapClocks, Clocks.weighted, heapEventWork, Nat.add_assoc]

def model (code : PriorityQueue.Code) (bridge : Bridge code) (queue : ObjectRef)
    (protection : Protected) (capacity : Int) : Model code queue protection where
  State := State
  entries := fun state => state.forest.entries
  Rep := Rep queue protection capacity
  capacity := capacity
  unique := fun rep => rep.represented.represented.valid.1
  bounded := fun rep => rep.bounded
  metric := metric
  potential := fun state => Algo2Lean.Fibonacci.scaledPotential state.forest.counts
  updateBudget := 20
  popBudget := 12 * (2 * capacity.toNat.log2 + 2)
  valid := fun rep => (bridge.valid _ _).mpr rep.represented.layoutValid.object
  tick := Rep.tick
  write := Rep.write

/-- Local heap footprints preserve every storage class protected by the caller. -/
theorem protected_frame {before after : Heap} {queue : ObjectRef} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} {protection : Protected}
    (rep : QueueRep before queue layout forest)
    (separate : ∀ ref ∈ protection.sequences, ref ∉ layout.refs)
    (classOutside : "fibonacci_heap.FibonacciHeap" ∉ protection.objectClasses)
    (changed : before.Modifies after layout.refs [queue]) :
    PriorityQueueAnalysis.Frame protection before after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [changed.nextRef, Nat.le_refl]
  · simp only [changed.nextObject, Nat.le_refl]
  · simp only [changed.nextCollection, Nat.le_refl]
  · intro ref allocated
    exact congrFun changed.classes ref
  · intro ref allocated
    simp only [Heap.sequenceType, changed.collections]
  · intro ref guarded allocated
    exact changed.read ref (separate ref guarded)
  · intro ref className allocated tagged guarded
    apply changed.otherObjects
    simp only [List.mem_singleton]
    intro same
    subst ref
    have classNameEq : className = "fibonacci_heap.FibonacciHeap" :=
      Option.some.inj (tagged.symm.trans rep.layoutValid.object.2)
    exact classOutside (classNameEq ▸ guarded)
  · intro ref guarded allocated
    exact congrFun changed.collections ref

private theorem removed_entries {before after : Algo2Lean.Fibonacci.Forest} {vertex key : Int}
    (unique : before.Unique)
    (contents : ((vertex, key) :: after.entries).Perm before.entries) (v k : Int) :
    (v, k) ∈ after.entries ↔ v ≠ vertex ∧ (v, k) ∈ before.entries := by
  have distinct := (contents.map Prod.fst).nodup_iff.mpr unique
  have absent := (List.nodup_cons.mp distinct).1
  constructor
  · intro member
    refine ⟨?_, contents.mem_iff.mp (List.mem_cons_of_mem _ member)⟩
    intro same
    exact absent (List.mem_map.mpr ⟨(v, k), member, same⟩)
  · rintro ⟨different, member⟩
    rcases List.mem_cons.mp (contents.mem_iff.mpr member) with same | present
    · exact False.elim (different (congrArg Prod.fst same))
    · exact present

/-- All queue operations satisfy the shared interface, with the actual measured
    work and potential attached to the same execution witness. -/
theorem contracts (code : PriorityQueue.Code) (bridge : Bridge code) (queue : ObjectRef)
    (protection : Protected) (capacity : Int) (reserved : List String)
    (classOutside : "fibonacci_heap.FibonacciHeap" ∉ protection.objectClasses)
    (clockOutside : ∀ name ∈ reserved, name ∉ heapClocks) :
    Contracts (model code bridge queue protection capacity) reserved := by
  constructor
  · intro name named item included
    obtain ⟨clock, member, rfl⟩ := List.mem_map.mp included
    intro same
    exact clockOutside name named (same ▸ member)
  · intro heap state rep
    exact bridge.is_empty rep.represented.is_empty
  · intro heap state vertex key rep lower upper improvement
    obtain ⟨after, layout, forest, execution, represented, contents, changed, refs, clocks, amortized⟩ :=
      rep.represented.update vertex key lower improvement
    refine ⟨after, ⟨layout, forest⟩, bridge.update execution, ?_, contents,
      protected_frame rep.represented rep.separate classOutside changed, ?_, ?_⟩
    · refine ⟨represented, ?_, ?_⟩
      · simpa only [refs] using rep.separate
      · intro v k member
        rcases (contents v k).mp member with ⟨rfl, rfl⟩ | ⟨_, old⟩
        · exact ⟨lower, upper⟩
        · exact rep.bounded v k old
    · intro name named
      exact clocks name (clockOutside name named)
    · simpa only [model, measured_work] using amortized
  · intro heap state rep nonempty
    have forestNonempty : state.forest ≠ [] := by
      intro empty
      exact nonempty (by simp [model, empty, Algo2Lean.Fibonacci.Forest.entries])
    obtain ⟨after, layout, forest, contract⟩ := rep.represented.pop_minimum forestNonempty
    have contents := removed_entries rep.represented.represented.valid.1 contract.contents
    refine ⟨after, ⟨layout, forest⟩, state.layout.minimum,
      heap.read state.layout.keys state.layout.minimum, bridge.extract contract.execution, ?_,
      contract.contents.mem_iff.mp (by simp), ?_, contents,
      protected_frame rep.represented rep.separate classOutside contract.frame, ?_, ?_⟩
    · refine ⟨contract.represented, ?_, ?_⟩
      · simpa only [contract.refs] using rep.separate
      · intro v k member
        exact rep.bounded v k ((contents v k).mp member).2
    · intro v k member
      have stored := rep.represented.represented.entry member
      have present : heap.read state.layout.present v = 1 := stored.2
      have least := (rep.represented.minimum forestNonempty).2.2 v (by rw [present]; decide)
      have value : heap.read state.layout.keys v = k := stored.1
      simpa only [value] using least
    · intro name named
      exact contract.otherClocks name (clockOutside name named)
    · have cardinality := (model code bridge queue protection capacity).cardinality_bound rep
      have logarithm := Algo2Lean.Fibonacci.log2_mono cardinality
      have amortized := contract.amortized
      simp only [model, measured_work] at *
      omega


/-- The constructor gives an empty abstract state with fresh private sequences. -/
def initialState (heap : Heap) : State := ⟨emptyLayout heap, []⟩

theorem constructor_rep (heap : Heap) (protection : Protected) (capacity : Int)
    (allocated : ∀ ref ∈ protection.sequences, ref < heap.nextRef) :
    Rep heap.nextObject protection capacity (newHeap heap) (initialState heap) := by
  refine ⟨new_heap_representation heap, ?_, ?_⟩
  · intro ref member
    have old := allocated ref member
    have different (offset : Nat) : ref ≠ heap.nextRef + offset :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _))
    simp [initialState, emptyLayout, Layout.refs, different, Nat.ne_of_lt old]
  · intro vertex key member
    simp [initialState, Algo2Lean.Fibonacci.Forest.entries] at member

private theorem constructor_old_object (heap : Heap) (ref : ObjectRef)
    (old : ref < heap.nextObject) : (newHeap heap).objects ref = heap.objects ref := by
  have different : ref ≠ heap.nextObject := Nat.ne_of_lt old
  simp [newHeap, initializedHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
    Heap.writeField, Heap.allocateObject, different]

private theorem constructor_old_sequence (heap : Heap) (ref : SeqRef)
    (old : ref < heap.nextRef) : (newHeap heap).read ref = heap.read ref := by
  have different (offset : Nat) : ref ≠ heap.nextRef + offset :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _))
  have notBase : ref ≠ heap.nextRef := Nat.ne_of_lt old
  funext index
  simp [newHeap, initializedHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
    Heap.read, Heap.allocate, Nat.add_assoc, different, notBase]

/-- Fresh construction preserves all previously allocated client storage. -/
theorem constructor_frame (heap : Heap) (protection : Protected) :
    Frame protection heap (newHeap heap) := by
  refine ⟨?_, ?_, Nat.le_refl _, ?_, fun _ _ => rfl, ?_, ?_, fun _ _ _ => rfl⟩
  · change heap.nextRef ≤ heap.nextRef + 9
    omega
  · change heap.nextObject ≤ heap.nextObject + 1
    omega
  · intro ref old
    simp only [Heap.objectClass, constructor_old_object heap ref old]
  · intro ref _ old
    exact constructor_old_sequence heap ref old
  · intro ref _ old _ _
    exact constructor_old_object heap ref old

theorem constructor_clocks (heap : Heap) : (newHeap heap).clocks = heap.clocks := rfl

end FibonacciQueueAnalysis
