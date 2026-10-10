import Algo.composable_dijkstra.priority_queue.Generated
import Algo2LeanLib.CallCost
import Algo2LeanLib.Footprint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The priority-queue contract mentions only public operations, abstract contents,
and protected client storage. A backend chooses its own ghost state and
representation. No queue layout, balancing invariant, or implementation clock
is part of this interface.
-/

namespace PriorityQueueAnalysis

open Algo2LeanGenerated
open Algo.composable_dijkstra.priority_queue

/-- Queue calls preserve the listed client locations. The caller snapshot marks
    all storage that existed before the private queue and work arrays were
    allocated; its contents remain an invariant of the represented queue. -/
structure Protected where
  sequences : List SeqRef
  objectClasses : List String
  collections : List CollectionRef
  caller : Heap := {}

/-- Allocation is allowed; every previously allocated protected value survives. -/
structure Frame (protection : Protected) (before after : Heap) : Prop where
  nextRef : before.nextRef ≤ after.nextRef
  nextObject : before.nextObject ≤ after.nextObject
  nextCollection : before.nextCollection ≤ after.nextCollection
  classes : ∀ ref, ref < before.nextObject → after.objectClass ref = before.objectClass ref
  types : ∀ ref, ref < before.nextCollection → after.sequenceType ref = before.sequenceType ref
  sequences : ∀ ref ∈ protection.sequences, ref < before.nextRef → after.read ref = before.read ref
  objects : ∀ ref className, ref < before.nextObject → before.objectClass ref = some className →
    className ∈ protection.objectClasses →
    after.objects ref = before.objects ref
  collections : ∀ ref ∈ protection.collections, ref < before.nextCollection →
    after.collections ref = before.collections ref

/-- One interface instance and its abstract contents. The protected sequence
    writes belong to the caller, so they cannot invalidate the queue. -/
structure Model (code : PriorityQueue.Code) (queue : ObjectRef) (protection : Protected) where
  State : Type
  entries : State → List (Int × Int)
  Rep : Heap → State → Prop
  capacity : Int
  /-- Representation invariants retain every location from the caller snapshot. -/
  callerPreserved : ∀ {heap state}, Rep heap state → protection.caller.Footprint heap [] [] []
  unique : ∀ {heap state}, Rep heap state → (entries state |>.map Prod.fst).Nodup
  bounded : ∀ {heap state}, Rep heap state → ∀ vertex key, (vertex,key) ∈ entries state →
    0 ≤ vertex ∧ vertex < capacity
  metric : List (String × Nat) := []
  potential : State → Nat := fun _ => 0
  updateBudget : Nat := 0
  popBudget : Nat := 0
  valid : ∀ {heap state}, Rep heap state → code.valid heap queue = true
  tick : ∀ {heap state}, Rep heap state → ∀ clock amount, Rep (heap.tick clock amount) state
  write : ∀ {heap state}, Rep heap state → ∀ ref ∈ protection.sequences,
    ∀ index value, Rep (heap.write ref index value) state

/-- Each call preserves the caller's reserved clocks. Queue implementation
    clocks are deliberately unrestricted and may be analyzed independently. -/
def PreservesClocks (reserved : List String) (before after : Heap) : Prop :=
  ∀ name ∈ reserved, after.clocks name = before.clocks name

structure Updated {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) (reserved : List String)
    (before after : Heap) (state next : model.State) (vertex key : Int) : Prop where
  execution : PriorityQueue.push_or_decrease.Call code before (queue, vertex, key) after ()
  represented : model.Rep after next
  contents : ∀ v k, (v,k) ∈ model.entries next ↔
    (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v,k) ∈ model.entries state)
  frame : Frame protection before after
  clocks : PreservesClocks reserved before after
  amortized : Clocks.weighted model.metric (Heap.cost before after) + model.potential next ≤
    model.potential state + model.updateBudget

structure Extracted {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) (reserved : List String)
    (before after : Heap) (state next : model.State) (vertex key : Int) : Prop where
  execution : PriorityQueue.pop_min.Call code before queue after vertex
  represented : model.Rep after next
  selected : (vertex,key) ∈ model.entries state
  least : ∀ v k, (v,k) ∈ model.entries state → key ≤ k
  contents : ∀ v k, (v,k) ∈ model.entries next ↔ v ≠ vertex ∧ (v,k) ∈ model.entries state
  frame : Frame protection before after
  clocks : PreservesClocks reserved before after
  amortized : Clocks.weighted model.metric (Heap.cost before after) + model.potential next ≤
    model.potential state + model.popBudget

/-- Local terminating call contracts. No field assumes a Dijkstra run,
    shortest-path correctness, or a whole-program complexity bound. -/
structure Contracts {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) (reserved : List String) : Prop where
  metricReserved : ∀ name ∈ reserved, ∀ item ∈ model.metric, item.1 ≠ name
  is_empty : ∀ heap state, model.Rep heap state →
    PriorityQueue.is_empty.Call code heap queue heap (model.entries state).isEmpty
  update : ∀ heap state vertex key, model.Rep heap state → 0 ≤ vertex → vertex < model.capacity →
    (∀ old, (vertex,old) ∈ model.entries state → key < old) →
    ∃ after next, Updated model reserved heap after state next vertex key
  extract : ∀ heap state, model.Rep heap state → model.entries state ≠ [] →
    ∃ after next vertex key, Extracted model reserved heap after state next vertex key

/-- A list representation gives the usual backend-independent minimum law. -/
theorem minimum_of_matches {entries : List (Int × Int)} {distance : Int → Int}
    {settled : Int → Prop} {vertex key : Int}
    (matching : ∀ v k, (v,k) ∈ entries ↔ ¬settled v ∧ 0 ≤ distance v ∧ k = distance v)
    (selected : (vertex,key) ∈ entries)
    (least : ∀ v k, (v,k) ∈ entries → key ≤ k) :
    ¬settled vertex ∧ 0 ≤ distance vertex ∧
      ∀ v, ¬settled v → 0 ≤ distance v → distance vertex ≤ distance v := by
  obtain ⟨unsettled, finite, value⟩ := (matching vertex key).mp selected
  refine ⟨unsettled, finite, ?_⟩
  intro v free finite
  simpa [value] using least v (distance v) ((matching v _).mpr ⟨free, finite, rfl⟩)

/-- Unique nonnegative vertex identifiers bounded by capacity give a finite queue-size bound. -/
theorem Model.cardinality_bound {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) {heap : Heap} {state : model.State}
    (rep : model.Rep heap state) : (model.entries state).length ≤ model.capacity.toNat := by
  have subset_length (first second : List Int) (unique : first.Nodup)
      (subset : ∀ vertex ∈ first, vertex ∈ second) : first.length ≤ second.length := by
    induction first generalizing second with
    | nil => simp
    | cons vertex rest ih =>
      obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
      have member := subset vertex (by simp)
      have bound := ih (second.erase vertex) restUnique (by
        intro other inRest
        apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
        exact subset other (by simp [inRest]))
      have positive := List.length_pos_of_mem member
      rw [List.length_erase_of_mem member] at bound
      simp only [List.length_cons]
      omega
  have bound := subset_length ((model.entries state).map Prod.fst)
      ((List.range model.capacity.toNat).map Int.ofNat) (model.unique rep) (by
    intro vertex member
    obtain ⟨⟨v,k⟩,entry,same⟩ := List.mem_map.mp member
    obtain ⟨lower,upper⟩ := model.bounded rep v k entry
    subst vertex
    exact List.mem_map.mpr ⟨v.toNat, List.mem_range.mpr (by omega), Int.toNat_of_nonneg lower⟩)
  simpa only [List.length_map,List.length_range] using bound

end PriorityQueueAnalysis
