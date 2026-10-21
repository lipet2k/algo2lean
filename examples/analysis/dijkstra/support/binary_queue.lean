import Algo.dijkstra.support.binary_heap.Analysis
import Algo.dijkstra.priority_queue.Analysis
import Algo2LeanLib.FiniteIndex
import Algo2LeanLib.FiniteMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `contracts`: Reusable queue correctness and amortized-cost contracts.
- `constructor_rep`: Queue initialization representation.
-/

open Algo2LeanCore Algo2LeanGenerated Algo.indexed_heap Algo.indexed_heap.Algo2LeanGenerated
open Algo.dijkstra.priority_queue

namespace BinaryQueueAnalysis

open BinaryModuleAnalysis PriorityQueueAnalysis

/-- The compiler supplies these small method transfers. The backend package
    does not depend on any particular client or its generated binding. -/
structure Bridge (code : PriorityQueue.Code) : Prop where
  valid : ∀ heap ref, code.valid heap ref = decide (is_MinHeap heap ref)
  is_empty : ∀ {before after ref result},
    MinHeap.is_empty.Call before ref after result →
      PriorityQueue.is_empty.Call code before ref after result
  update : ∀ {before after ref vertex key},
    MinHeap.push_or_decrease.Call before (ref, vertex, key) after () →
      PriorityQueue.push_or_decrease.Call code before (ref, vertex, key) after ()
  extract : ∀ {before after ref vertex},
    MinHeap.pop_min.Call before ref after vertex →
      PriorityQueue.pop_min.Call code before ref after vertex

structure State where
  layout : Layout
  entries : List (Int × Int)

/-- The finite abstract map matches the private indexed arrays. -/
def Contents (heap : Heap) (state : State) : Prop :=
  ∀ vertex key, (vertex, key) ∈ state.entries ↔
    0 ≤ heap.read state.layout.positions vertex ∧ key = heap.read state.layout.keys vertex

structure Rep (queueRef : ObjectRef) (protection : Protected) (capacity : Int)
    (heap : Heap) (state : State) : Prop where
  queue : QueueRep heap queueRef state.layout
  contents : Contents heap state
  unique : (state.entries.map Prod.fst).Nodup
  bounded : ∀ vertex key, (vertex, key) ∈ state.entries → 0 ≤ vertex ∧ vertex < capacity
  separate : ∀ ref ∈ protection.sequences,
    ref ≠ state.layout.vertices ∧ ref ≠ state.layout.positions ∧ ref ≠ state.layout.keys
  callerPreserved : protection.caller.Footprint heap [] [] []
  privateSequences : ∀ ref ∈ [state.layout.vertices, state.layout.positions, state.layout.keys],
    protection.caller.nextRef ≤ ref
  privateObject : protection.caller.nextObject ≤ queueRef
  clientSequences : ∀ ref ∈ protection.sequences, protection.caller.nextRef ≤ ref

private theorem queue_tick {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) (name : String) (amount : Nat) :
    QueueRep (heap.tick name amount) queue layout :=
  ⟨represented.valid.tick name amount, represented.nonnegative, represented.indexed, represented.ordered⟩

private theorem queue_write {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) (ref : SeqRef) (index value : Int)
    (separate : ref ≠ layout.vertices ∧ ref ≠ layout.positions ∧ ref ≠ layout.keys) :
    QueueRep (heap.write ref index value) queue layout := by
  refine ⟨represented.valid.write ref index value, represented.nonnegative, ?_, ?_⟩
  · have vertices : (heap.write ref index value).read layout.vertices = heap.read layout.vertices := by
      funext position
      simp [Heap.read, Heap.write, Ne.symm separate.1]
    have positions : (heap.write ref index value).read layout.positions = heap.read layout.positions := by
      funext position
      simp [Heap.read, Heap.write, Ne.symm separate.2.1]
    rw [vertices, positions]
    exact represented.indexed
  · simpa [Heap.read, Heap.write, Ne.symm separate.1, Ne.symm separate.2.2] using represented.ordered

theorem Rep.tick {queue : ObjectRef} {protection : Protected} {capacity : Int}
    {heap : Heap} {state : State} (represented : Rep queue protection capacity heap state)
    (name : String) (amount : Nat) : Rep queue protection capacity (heap.tick name amount) state :=
  ⟨queue_tick represented.queue name amount, represented.contents, represented.unique,
    represented.bounded, represented.separate, represented.callerPreserved.tick name amount,
    represented.privateSequences, represented.privateObject, represented.clientSequences⟩

theorem Rep.write {queue : ObjectRef} {protection : Protected} {capacity : Int}
    {heap : Heap} {state : State} (represented : Rep queue protection capacity heap state)
    (ref : SeqRef) (member : ref ∈ protection.sequences) (index value : Int) :
    Rep queue protection capacity (heap.write ref index value) state := by
  have separate := represented.separate ref member
  refine ⟨queue_write represented.queue ref index value separate, ?_, represented.unique,
    represented.bounded, represented.separate,
    represented.callerPreserved.write ref index value (Or.inr (represented.clientSequences ref member)),
    represented.privateSequences, represented.privateObject, represented.clientSequences⟩
  simpa [Contents, Heap.read, Heap.write, Ne.symm separate.2.1, Ne.symm separate.2.2] using represented.contents

theorem Rep.size_bound {queue : ObjectRef} {protection : Protected} {capacity : Int}
    {heap : Heap} {state : State} (represented : Rep queue protection capacity heap state) :
    state.layout.size ≤ capacity.toNat := by
  have bound := Algo2Lean.FiniteIndex.active_prefix_bound
    (heap.read state.layout.vertices) (heap.read state.layout.positions) state.layout.size
    represented.queue.nonnegative represented.queue.indexed.forward
    (Algo2Lean.FiniteIndex.range capacity) (by
      intro index nonnegative within
      apply (Algo2Lean.FiniteIndex.range_member _ _).mpr
      apply represented.bounded _ (heap.read state.layout.keys (heap.read state.layout.vertices index))
      apply (represented.contents _ _).mpr
      exact ⟨by rw [represented.queue.indexed.forward index nonnegative within]; exact nonnegative, rfl⟩)
  simpa using bound

/-- Binary heaps use no amortized credit; both operation budgets are logarithmic. -/
def model (code : PriorityQueue.Code) (bridge : Bridge code)
    (queue : ObjectRef) (protection : Protected) (capacity : Int) :
    Model code queue protection where
  State := State
  entries := State.entries
  Rep := Rep queue protection capacity
  capacity := capacity
  callerPreserved := Rep.callerPreserved
  unique := Rep.unique
  bounded := Rep.bounded
  metric := [("heap_comparisons", 1), ("heap_swaps", 1)]
  updateBudget := 2 * depth capacity + 1
  popBudget := 3 * depth capacity + 1
  valid := by
    intro heap state represented
    rw [bridge.valid]
    exact decide_eq_true represented.queue.valid.object
  tick := by intro heap state represented; exact represented.tick
  write := by intro heap state represented; exact represented.write

theorem Rep.depth_bound {queue : ObjectRef} {protection : Protected} {capacity : Int}
    {heap : Heap} {state : State} (represented : Rep queue protection capacity heap state) :
    depth state.layout.size ≤ depth capacity := by
  have bound := represented.size_bound
  by_cases nonnegative : 0 ≤ capacity
  · apply depth_mono
    omega
  · have empty : state.layout.size = 0 := by
      have positive := represented.queue.nonnegative
      have zero : capacity.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      omega
    simp [depth, empty, Int.toNat_eq_zero.mpr (by omega : capacity ≤ 0)]

/-- Updating only the queue object's size preserves every protected object class. -/
theorem frame_of_storage {before after : Heap} {queue : ObjectRef} {size : Int}
    {protection : Protected} (valid : is_MinHeap before queue)
    (privateClass : "indexed_heap.MinHeap" ∉ protection.objectClasses)
    (storage : OtherStoragePreserved (set_MinHeap_size before queue size) after)
    (arrays : ∀ ref ∈ protection.sequences, after.read ref = before.read ref) :
    PriorityQueueAnalysis.Frame protection before after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [storage.nextRef] using! Nat.le_refl before.nextRef
  · simpa only [storage.nextObject] using! Nat.le_refl before.nextObject
  · simpa only [storage.nextCollection] using! Nat.le_refl before.nextCollection
  · intro ref old
    change (after.objects ref).map (fun object => object.className) = _
    rw [storage.objects]
    exact Heap.objectClass_writeField before ref queue "size" (.intValue size)
  · intro ref old
    unfold Heap.sequenceType
    rw [storage.collections]
    rfl
  · intro ref member old
    exact arrays ref member
  · intro ref className old tagged owned
    have different : ref ≠ queue := by
      intro same
      subst ref
      have tag : className = "indexed_heap.MinHeap" := Option.some.inj (tagged.symm.trans valid.2)
      exact privateClass (tag ▸ owned)
    rw [storage.objects]
    simp [set_MinHeap_size, Heap.writeField, different]
  · intro ref member old
    rw [storage.collections]
    rfl


private theorem frame_of_unchanged_storage {before after : Heap} {protection : Protected}
    (storage : OtherStoragePreserved before after)
    (arrays : ∀ ref ∈ protection.sequences, after.read ref = before.read ref) :
    PriorityQueueAnalysis.Frame protection before after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [storage.nextRef, Nat.le_refl]
  · simp only [storage.nextObject, Nat.le_refl]
  · simp only [storage.nextCollection, Nat.le_refl]
  · intro ref old
    simp only [Heap.objectClass, storage.objects]
  · intro ref old
    simp only [Heap.sequenceType, storage.collections]
  · intro ref member old
    exact arrays ref member
  · intro ref className old tagged owned
    exact congrFun storage.objects ref
  · intro ref member old
    exact congrFun storage.collections ref

/-- The indexed-array contracts preserve every storage kind outside their arrays. -/
private theorem storage_footprint {before after : Heap} {layout : Layout}
    (storage : OtherStoragePreserved before after)
    (arrays : ∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
      after.read ref = before.read ref) :
    before.Footprint after [layout.vertices,layout.positions,layout.keys] [] [] := by
  refine ⟨Nat.le_of_eq storage.nextRef.symm, Nat.le_of_eq storage.nextObject.symm,
    Nat.le_of_eq storage.nextCollection.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro ref _
    simp only [Heap.objectClass, storage.objects]
  · intro ref _
    simp only [Heap.collectionType, storage.collections]
  · intro ref _ outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    exact arrays ref outside.1 outside.2.1 outside.2.2
  · intro ref _ _
    exact congrFun storage.objects ref
  · intro ref _ _
    exact congrFun storage.collections ref

private def updatedState (state : State) (size vertex key : Int) : State :=
  ⟨{ state.layout with size := size }, Algo2Lean.FiniteMap.set state.entries vertex key⟩

private theorem update_rep {queue : ObjectRef} {protection : Protected} {capacity : Int}
    {heap after : Heap} {state : State} (rep : Rep queue protection capacity heap state)
    (size vertex key : Int) (lower : 0 ≤ vertex) (upper : vertex < capacity)
    (represented : QueueRep after queue { state.layout with size := size })
    (membership : ∀ v, 0 ≤ after.read state.layout.positions v ↔
      v = vertex ∨ 0 ≤ heap.read state.layout.positions v)
    (keys : ∀ v, after.read state.layout.keys v = if v = vertex then key else heap.read state.layout.keys v)
    (preserved : protection.caller.Footprint after [] [] []) :
    Rep queue protection capacity after (updatedState state size vertex key) := by
  refine ⟨represented, ?_, Algo2Lean.FiniteMap.set_unique rep.unique vertex key, ?_, rep.separate,
    preserved, rep.privateSequences, rep.privateObject, rep.clientSequences⟩
  · intro v k
    change (v, k) ∈ Algo2Lean.FiniteMap.set state.entries vertex key ↔ _
    rw [Algo2Lean.FiniteMap.mem_set]
    change _ ↔ 0 ≤ after.read state.layout.positions v ∧ k = after.read state.layout.keys v
    rw [membership v, keys v]
    by_cases same : v = vertex
    · simp [same]
    · simpa [same] using rep.contents v k
  · intro v k member
    rcases Algo2Lean.FiniteMap.mem_set.mp member with ⟨rfl, rfl⟩ | ⟨_, old⟩
    · exact ⟨lower, upper⟩
    · exact rep.bounded v k old

/-- The public size observation agrees with the finite abstract map. -/
theorem Rep.is_empty {queue : ObjectRef} {protection : Protected} {capacity : Int}
    {heap : Heap} {state : State} (rep : Rep queue protection capacity heap state) :
    MinHeap.is_empty.Call heap queue heap state.entries.isEmpty := by
  have result : decide (state.layout.size ≤ 0) = state.entries.isEmpty := by
    cases entries : state.entries with
    | nil =>
      have empty : state.layout.size ≤ 0 := by
        by_cases empty : state.layout.size ≤ 0
        · exact empty
        · have present : 0 ≤ heap.read state.layout.positions (heap.read state.layout.vertices 0) := by
            rw [rep.queue.indexed.forward 0 (by omega) (by omega)]
            omega
          have member := (rep.contents _ _).mpr ⟨present, rfl⟩
          simp [entries] at member
      simp [empty]
    | cons first rest =>
      have present := ((rep.contents first.1 first.2).mp (by simp [entries])).1
      have bound := (rep.queue.indexed.backward first.1 present).1
      have positive : ¬ state.layout.size ≤ 0 := by omega
      simp [positive]
  simpa only [result] using is_empty_summary heap queue state.layout rep.queue.valid

/-- Independently proved binary heap operations discharge the shared queue
    contract, including bounds on their actual comparison and swap clocks. -/
theorem contracts (code : PriorityQueue.Code) (bridge : Bridge code) (queue : ObjectRef)
    (protection : Protected) (capacity : Int) (reserved : List String)
    (privateClass : "indexed_heap.MinHeap" ∉ protection.objectClasses)
    (clockOutside : ∀ name ∈ reserved, name ≠ "heap_comparisons" ∧ name ≠ "heap_swaps") :
    Contracts (model code bridge queue protection capacity) reserved := by
  constructor
  · intro name named item included
    have outside := clockOutside name named
    simp only [model, List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl
    · exact Ne.symm outside.1
    · exact Ne.symm outside.2
  · intro heap state rep
    exact bridge.is_empty rep.is_empty
  · intro heap state vertex key rep lower upper improvement
    have depthBound := rep.depth_bound
    by_cases present : 0 ≤ heap.read state.layout.positions vertex
    · have better : key < heap.read state.layout.keys vertex :=
        improvement _ ((rep.contents _ _).mpr ⟨present, rfl⟩)
      obtain ⟨after, execution, represented, membership, keys, comparisons, swaps, arrays, clocks, storage⟩ :=
        decrease_correct heap queue state.layout rep.queue vertex key present better
      have fullMembership : ∀ v, 0 ≤ after.read state.layout.positions v ↔
          v = vertex ∨ 0 ≤ heap.read state.layout.positions v := by
        intro v
        rw [membership v]
        by_cases same : v = vertex <;> simp [same, present]
      have nextRep := update_rep rep state.layout.size vertex key lower upper represented fullMembership keys
        (Heap.Footprint.trans_fresh rep.callerPreserved
          (storage_footprint storage (by intro ref a b c; funext i; exact arrays ref a b c i))
          rep.privateSequences (by simp) (by simp))
      refine ⟨after, updatedState state state.layout.size vertex key, bridge.update execution, nextRep, ?_,
        frame_of_unchanged_storage storage ?_, ?_, ?_⟩
      · intro v k
        exact Algo2Lean.FiniteMap.mem_set
      · intro ref member
        have separate := rep.separate ref member
        funext index
        exact arrays ref separate.1 separate.2.1 separate.2.2 index
      · intro name named
        exact clocks name (clockOutside name named).1 (clockOutside name named).2
      · have positionDepth : depth (heap.read state.layout.positions vertex) ≤ depth capacity :=
          Nat.le_trans (depth_mono (Int.le_of_lt (rep.queue.indexed.backward vertex present).1)) depthBound
        simp only [model, Clocks.weighted, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.one_mul, Nat.add_zero]
        omega
    · have absent := rep.queue.indexed.absent vertex (by omega)
      obtain ⟨after, execution, represented, membership, keys, comparisons, swaps, arrays, clocks, storage⟩ :=
        insert_correct heap queue state.layout rep.queue vertex key absent
      have nextRep := update_rep rep (state.layout.size + 1) vertex key lower upper represented membership keys
        (Heap.Footprint.trans_fresh
          (rep.callerPreserved.writeField queue "size" (.intValue (state.layout.size + 1)) (Or.inr rep.privateObject))
          (storage_footprint storage (by intro ref a b c; funext i; exact arrays ref a b c i))
          rep.privateSequences (by simp) (by simp))
      refine ⟨after, updatedState state (state.layout.size + 1) vertex key, bridge.update execution, nextRep, ?_,
        frame_of_storage rep.queue.valid.object privateClass storage ?_, ?_, ?_⟩
      · intro v k
        exact Algo2Lean.FiniteMap.mem_set
      · intro ref member
        have separate := rep.separate ref member
        funext index
        exact arrays ref separate.1 separate.2.1 separate.2.2 index
      · intro name named
        exact clocks name (clockOutside name named).1 (clockOutside name named).2
      · simp only [model, Clocks.weighted, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.one_mul, Nat.add_zero]
        omega
  · intro heap state rep nonempty
    have positive : 0 < state.layout.size := by
      cases entries : state.entries with
      | nil => exact False.elim (nonempty entries)
      | cons first rest =>
        have present := ((rep.contents first.1 first.2).mp (by simp [entries])).1
        have bound := (rep.queue.indexed.backward first.1 present).1
        omega
    obtain ⟨after, execution, effect⟩ := pop_correct heap queue state.layout rep.queue positive
    let vertex := heap.read state.layout.vertices 0
    let next : State := ⟨{ state.layout with size := state.layout.size - 1 },
      Algo2Lean.FiniteMap.erase state.entries vertex⟩
    refine ⟨after, next, vertex, heap.read state.layout.keys vertex, bridge.extract execution, ?_,
      (rep.contents _ _).mpr ⟨effect.wasPresent, rfl⟩, ?_, ?_,
      frame_of_storage rep.queue.valid.object privateClass effect.otherStorage ?_, ?_, ?_⟩
    · refine ⟨effect.representation, ?_, Algo2Lean.FiniteMap.erase_unique rep.unique vertex, ?_, rep.separate,
        Heap.Footprint.trans_fresh
          (rep.callerPreserved.writeField queue "size" (.intValue (state.layout.size - 1)) (Or.inr rep.privateObject))
          (storage_footprint effect.otherStorage (by
            intro ref a b c; funext i; exact effect.otherArrays ref a b i))
          rep.privateSequences (by simp) (by simp),
        rep.privateSequences, rep.privateObject, rep.clientSequences⟩
      · intro v k
        change (v, k) ∈ Algo2Lean.FiniteMap.erase state.entries vertex ↔ _
        rw [Algo2Lean.FiniteMap.mem_erase]
        change _ ↔ 0 ≤ after.read state.layout.positions v ∧ k = after.read state.layout.keys v
        rw [effect.membership v, effect.keys v, rep.contents v k]
        simp only [vertex, and_assoc, and_comm]
      · intro v k member
        exact rep.bounded v k (Algo2Lean.FiniteMap.mem_erase.mp member).2
    · intro v k member
      obtain ⟨present, value⟩ := (rep.contents v k).mp member
      simpa only [← value] using effect.minimum v present
    · intro v k
      exact Algo2Lean.FiniteMap.mem_erase
    · intro ref member
      have separate := rep.separate ref member
      funext index
      exact effect.otherArrays ref separate.1 separate.2.1 index
    · intro name named
      exact effect.otherClocks name (clockOutside name named).1 (clockOutside name named).2
    · have depthBound : depth (state.layout.size - 2) ≤ depth capacity :=
        Nat.le_trans (depth_mono (show state.layout.size - 2 ≤ state.layout.size by omega)) rep.depth_bound
      have comparisons := effect.comparisons
      have swaps := effect.swaps
      simp only [model, Clocks.weighted, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.one_mul, Nat.add_zero]
      omega


/-- The constructor gives an empty abstract state with fresh private sequences. -/
def initialState (heap : Heap) : State := ⟨emptyLayout heap, []⟩

private theorem constructor_old_object (heap : Heap) (ref : ObjectRef)
    (old : ref < heap.nextObject) : (newHeap heap).objects ref = heap.objects ref := by
  have different : ref ≠ heap.nextObject := Nat.ne_of_lt old
  simp [newHeap, initializedHeap, set_MinHeap_vertices, set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size,
    Heap.writeField, Heap.allocateObject, different]

private theorem constructor_old_sequence (heap : Heap) (ref : SeqRef)
    (old : ref < heap.nextRef) : (newHeap heap).read ref = heap.read ref := by
  funext index
  exact new_heap_read_old heap ref index old

/-- Fresh construction preserves all previously allocated client storage. -/
theorem constructor_frame (heap : Heap) (protection : Protected) :
    Frame protection heap (newHeap heap) := by
  refine ⟨?_, ?_, Nat.le_refl _, ?_, fun _ _ => rfl, ?_, ?_, fun _ _ _ => rfl⟩
  · change heap.nextRef ≤ heap.nextRef + 3
    omega
  · change heap.nextObject ≤ heap.nextObject + 1
    omega
  · intro ref old
    simp only [Heap.objectClass, constructor_old_object heap ref old]
  · intro ref _ old
    exact constructor_old_sequence heap ref old
  · intro ref _ old _ _
    exact constructor_old_object heap ref old

/-- Construction changes no previously allocated caller location. -/
theorem constructor_footprint (heap : Heap) : heap.Footprint (newHeap heap) [] [] [] := by
  have frame := constructor_frame heap ⟨[], [], [], {}⟩
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.classes, (fun _ _ => rfl),
    ?_, ?_, ?_⟩
  · intro ref old _
    exact constructor_old_sequence heap ref old
  · intro ref old _
    exact constructor_old_object heap ref old
  · intro ref old _
    rfl

theorem constructor_rep (heap : Heap) (protection : Protected) (capacity : Int)
    (allocated : ∀ ref ∈ protection.sequences, ref < heap.nextRef)
    (preserved : protection.caller.Footprint heap [] [] [])
    (clientFresh : ∀ ref ∈ protection.sequences, protection.caller.nextRef ≤ ref) :
    Rep heap.nextObject protection capacity (newHeap heap) (initialState heap) := by
  refine ⟨new_heap_rep heap, ?_, by simp [initialState], ?_, ?_,
    preserved.trans (constructor_footprint heap), ?_, preserved.nextObject, clientFresh⟩
  · intro vertex key
    change (vertex, key) ∈ ([] : List (Int × Int)) ↔ _
    simp [initialState, new_heap_positions]
  · intro vertex key member
    simp [initialState] at member
  · intro ref member
    have old := allocated ref member
    simp only [initialState, emptyLayout]
    exact ⟨Nat.ne_of_lt old,
      Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _)),
      Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _))⟩

  · intro ref member
    have base := preserved.nextRef
    simp only [initialState, emptyLayout, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> omega

theorem constructor_clocks (heap : Heap) : (newHeap heap).clocks = heap.clocks := rfl

end BinaryQueueAnalysis
