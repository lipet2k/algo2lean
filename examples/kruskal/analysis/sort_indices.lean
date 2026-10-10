import Algo.sort_indices.Points
import Algo.sort_indices.Facts
import Algo.indexed_heap.Analysis
import Algo2LeanLib.FiniteIndex
import Algo2LeanLib.CallCost

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Sorting identifiers keeps weights in their original sequence. The insertion
phase reuses the proved heap insertion contract; the extraction phase reuses
minimum extraction. Neither phase unfolds a heap operation's transitions.
-/

open Algo2LeanCore Algo2LeanGenerated
open Algo.indexed_heap.Algo2LeanGenerated hiding Step Frame Result Configuration Stack Transcript
open Algo.sort_indices Algo.sort_indices.Algo2LeanGenerated
open BinaryModuleAnalysis

namespace SortIndicesAnalysis

/-- The finite output is a permutation of the identifiers, ordered by key. -/
def SortedPermutation (keys : Seq) (count : Int) (output : Seq) : Prop :=
  ∃ values : List Int, values.Perm (Algo2Lean.FiniteIndex.range count) ∧
    values.Pairwise (fun first second => keys first ≤ keys second) ∧
    ∀ index : Nat, index < values.length → output index = values[index]!

/-- Sorting changes no previously allocated client data. -/
structure Preserves (before after : Heap) : Prop where
  sequences : ∀ ref, ref < before.nextRef → after.read ref = before.read ref
  objects : ∀ ref, ref < before.nextObject → after.objects ref = before.objects ref
  collections : after.collections = before.collections
  refs : before.nextRef ≤ after.nextRef
  objectRefs : before.nextObject ≤ after.nextObject
  collectionRefs : after.nextCollection = before.nextCollection
  clocks : ∀ name, name ≠ "sort_steps" → name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name

/-- Cost of the source loop body plus logarithmic heap operations. -/
def rate (count : Int) (clock : String) : Nat :=
  if clock = "sort_steps" then 1
  else if clock = "heap_comparisons" then 2 * depth count
  else if clock = "heap_swaps" then depth count + 1 else 0

def Budget (count : Int) (steps : Nat) (before after : Heap) : Prop :=
  ∀ clock, after.clocks clock ≤ before.clocks clock + steps * rate count clock

private theorem Budget.refl (count : Int) (heap : Heap) : Budget count 0 heap heap := by
  intro clock
  simp

private theorem Budget.trans {count : Int} {first second : Nat} {a b c : Heap}
    (one : Budget count first a b) (two : Budget count second b c) :
    Budget count (first + second) a c := by
  intro clock
  have := one clock
  have := two clock
  simp only [Nat.add_mul]
  omega

/-- Internal heap operations preserve every array except the three private
    heap arrays and the newly allocated output array. -/
private structure Storage (queue : ObjectRef) (privateRefs : List SeqRef)
    (before after : Heap) : Prop where
  arrays : ∀ ref, ref ∉ privateRefs → after.read ref = before.read ref
  objects : ∀ ref, ref ≠ queue → after.objects ref = before.objects ref
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  collections : after.collections = before.collections
  nextCollection : after.nextCollection = before.nextCollection
  clocks : ∀ name, name ≠ "sort_steps" → name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name

private theorem Storage.refl (queue : ObjectRef) (refs : List SeqRef) (heap : Heap) :
    Storage queue refs heap heap := ⟨by intros; rfl, by intros; rfl, rfl, rfl, rfl, rfl, by intros; rfl⟩

private theorem Storage.trans {queue : ObjectRef} {refs : List SeqRef} {a b c : Heap}
    (one : Storage queue refs a b) (two : Storage queue refs b c) : Storage queue refs a c :=
  ⟨fun ref outside => (two.arrays ref outside).trans (one.arrays ref outside),
   fun ref outside => (two.objects ref outside).trans (one.objects ref outside),
   two.nextRef.trans one.nextRef, two.nextObject.trans one.nextObject,
   two.collections.trans one.collections, two.nextCollection.trans one.nextCollection,
   fun name source comparisons swaps =>
     (two.clocks name source comparisons swaps).trans (one.clocks name source comparisons swaps)⟩

private theorem Storage.tick (queue : ObjectRef) (refs : List SeqRef) (heap : Heap) :
    Storage queue refs heap (heap.tick "sort_steps") :=
  ⟨by intros; rfl, by intros; rfl, rfl, rfl, rfl, rfl,
    by intro name source _ _; simp [Heap.tick, source]⟩

private theorem Storage.write (queue : ObjectRef) (refs : List SeqRef) (heap : Heap)
    (result : SeqRef) (member : result ∈ refs) (index value : Int) :
    Storage queue refs heap (heap.write result index value) := by
  refine ⟨?_, by intros; rfl, rfl, rfl, rfl, rfl, by intros; rfl⟩
  intro ref outside
  have different : ref ≠ result := by intro same; subst ref; exact outside member
  funext index
  simp [Heap.read, Heap.write, different]

private theorem Storage.of_heap {before after : Heap} {queue : ObjectRef}
    {layout : Layout} {result : SeqRef} {size : Int}
    (arrays : ∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
      ∀ index, after.read ref index = before.read ref index)
    (storage : OtherStoragePreserved (set_MinHeap_size before queue size) after)
    (clocks : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
      after.clocks name = before.clocks name) :
    Storage queue [layout.vertices, layout.positions, layout.keys, result] before after := by
  refine ⟨?_, ?_, storage.nextRef, storage.nextObject, storage.collections, storage.nextCollection,
    fun name _ comparisons swaps => clocks name comparisons swaps⟩
  · intro ref outside
    simp only [List.mem_cons, not_or] at outside
    funext index
    exact arrays ref outside.1 outside.2.1 outside.2.2.1 index
  · intro ref outside
    rw [storage.objects]
    simp [set_MinHeap_size, Heap.writeField, outside]

private theorem queue_tick {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) :
    QueueRep (heap.tick "sort_steps") queue layout :=
  ⟨represented.valid.tick "sort_steps", represented.nonnegative, represented.indexed, represented.ordered⟩

private theorem queue_write {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) (ref : SeqRef) (index value : Int)
    (separate : ref ≠ layout.vertices ∧ ref ≠ layout.positions ∧ ref ≠ layout.keys) :
    QueueRep (heap.write ref index value) queue layout := by
  refine ⟨represented.valid.write ref index value, represented.nonnegative, ?_, ?_⟩
  · have vertices : (heap.write ref index value).read layout.vertices = heap.read layout.vertices := by
      funext position; simp [Heap.read, Heap.write, Ne.symm separate.1]
    have positions : (heap.write ref index value).read layout.positions = heap.read layout.positions := by
      funext position; simp [Heap.read, Heap.write, Ne.symm separate.2.1]
    rw [vertices, positions]
    exact represented.indexed
  · simpa [Heap.read, Heap.write, Ne.symm separate.1, Ne.symm separate.2.2] using represented.ordered

private theorem operation_budget {before after : Heap} {count size : Int}
    (within : size ≤ count)
    (comparisons : Heap.cost (before.tick "sort_steps") after "heap_comparisons" ≤ 2 * depth size)
    (swaps : Heap.cost (before.tick "sort_steps") after "heap_swaps" ≤ depth size + 1)
    (other : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
      after.clocks name = (before.tick "sort_steps").clocks name) : Budget count 1 before after := by
  have depthBound := depth_mono within
  intro clock
  by_cases comparison : clock = "heap_comparisons"
  · subst clock
    simp only [Heap.cost, Heap.tick, String.reduceEq, ↓reduceIte] at comparisons
    simp only [rate, String.reduceEq, ↓reduceIte, Nat.one_mul]
    omega
  by_cases swap : clock = "heap_swaps"
  · subst clock
    simp only [Heap.cost, Heap.tick, String.reduceEq, ↓reduceIte] at swaps
    simp only [rate, String.reduceEq, ↓reduceIte, Nat.one_mul]
    omega
  rw [other clock comparison swap]
  by_cases source : clock = "sort_steps"
  · subst clock; simp [rate, Heap.tick]
  · simp [rate, Heap.tick, source, comparison, swap]

private def Contents (keys : Seq) (remaining : List Int) (heap : Heap) (layout : Layout) : Prop :=
  (∀ value, 0 ≤ heap.read layout.positions value ↔ value ∈ remaining) ∧
  (∀ value ∈ remaining, heap.read layout.keys value = keys value)

private def afterExtract (state : State_sort_indices) (vertex : Int) : State_sort_indices :=
  { state with v4 := state.v4 + 1, t6 := true, t7 := vertex, t8 := state.v4, t9 := state.v3, t10 := state.v2 }

/-- One source loop iteration uses the existing minimum-extraction theorem. -/
private theorem extract_continue (heap after final : Heap) (state : State_sort_indices)
    (vertex : Int) (running : state.v4 < state.v1)
    (allocated : state.v3 < after.nextRef)
    (call : Algo.indexed_heap.MinHeap.pop_min.Call (heap.tick "sort_steps") state.v2 after vertex)
    (rest : Summary Step (after.write state.v3 state.v4 vertex)
      (.fn_sort_indices 4 (afterExtract state vertex)) final (.fn_sort_indices state.v3)) :
    Summary Step heap (.fn_sort_indices 4 state) final (.fn_sort_indices state.v3) := by
  intro caller
  apply Reaches.prepend (Step.sort_indices_pc4 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc3_true _ _ _ (by simpa using running))
  apply Reaches.prepend (Step.sort_indices_pc12 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc11 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc10 _ _ _ (by exact call.1))
  apply Reaches.prepend (Step.sort_indices_pc9 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller call.2).trans
  apply Reaches.prepend (Step.sort_indices_pc8 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc7 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc6 _ _ _ allocated)
  apply Reaches.prepend (Step.sort_indices_pc5 _ _ _)
  simpa [afterExtract, running] using rest caller

/-- Repeated minimum extraction produces a sorted permutation of precisely the
    remaining identifiers and never rewrites the completed output prefix. -/
private theorem extract_loop (count : Int) (fuel : Nat) (keys : Seq) :
    ∀ (heap : Heap) (state : State_sort_indices) (layout : Layout) (remaining : List Int),
    remaining.length = fuel → remaining.Nodup → state.v1 = count →
    0 ≤ state.v4 → state.v4 + (fuel : Int) = count →
    layout.size = (fuel : Int) → QueueRep heap state.v2 layout →
    Contents keys remaining heap layout → state.v3 < heap.nextRef →
    state.v3 ≠ layout.vertices ∧ state.v3 ≠ layout.positions ∧ state.v3 ≠ layout.keys →
    ∃ (final : Heap) (values : List Int),
      Summary Step heap (.fn_sort_indices 4 state) final (.fn_sort_indices state.v3) ∧
      values.Perm remaining ∧ values.Pairwise (fun a b => keys a ≤ keys b) ∧
      (∀ index : Nat, index < values.length →
        final.read state.v3 (state.v4 + index) = values[index]!) ∧
      (∀ index : Int, index < state.v4 → final.read state.v3 index = heap.read state.v3 index) ∧
      Storage state.v2 [layout.vertices, layout.positions, layout.keys, state.v3] heap final ∧
      Budget count fuel heap final := by
  induction fuel with
  | zero =>
    intro heap state layout remaining length unique total index finish size represented contents allocated separate
    have empty : remaining = [] := List.eq_nil_of_length_eq_zero length
    subst remaining
    refine ⟨heap, [], ?_, List.Perm.refl _, by simp, by simp, by intros; rfl,
      Storage.refl _ _ _, Budget.refl _ _⟩
    intro caller
    apply Reaches.prepend (Step.sort_indices_pc4 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc3_false _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.sort_indices_pc2 _ _ _)
    exact Reaches.single (Step.sort_indices_pc1 _ _ _ allocated)
  | succ fuel ih =>
    intro heap state layout remaining length unique total index finish size represented contents allocated separate
    obtain ⟨after, call, effect⟩ := pop_correct (heap.tick "sort_steps") state.v2 layout
      (queue_tick represented) (by omega)
    let vertex := heap.read layout.vertices 0
    have member : vertex ∈ remaining := (contents.1 vertex).mp effect.wasPresent
    have erasedLength : (remaining.erase vertex).length = fuel := by
      have := Algo2Lean.FiniteIndex.erase_length remaining vertex member
      omega
    let written := after.write state.v3 state.v4 vertex
    let next := afterExtract state vertex
    let shorter := { layout with size := layout.size - 1 }
    have nextContents : Contents keys (remaining.erase vertex) written shorter := by
      constructor
      · intro value
        simp only [written, shorter, Heap.read, Heap.write,
          Ne.symm separate.2.1, false_and, ↓reduceIte]
        change 0 ≤ after.read layout.positions value ↔ _
        rw [effect.membership value]
        change (0 ≤ heap.read layout.positions value ∧ value ≠ vertex) ↔ _
        rw [contents.1 value, unique.mem_erase_iff]
        exact and_comm
      · intro value present
        have oldMember := List.mem_of_mem_erase present
        have keyEq := effect.keys value
        change written.read layout.keys value = keys value
        have all := keyEq.trans (contents.2 value oldMember)
        simpa [written, Heap.read, Heap.write, Ne.symm separate.2.2] using all
    obtain ⟨final, values, rest, permutation, sorted, output, kept, storage, budget⟩ :=
      ih written next shorter (remaining.erase vertex) erasedLength (unique.erase vertex) total
        (by dsimp [next, afterExtract]; omega) (by dsimp [next, afterExtract]; omega)
        (by dsimp [shorter]; omega) (queue_write effect.representation _ _ _ separate)
        nextContents (by dsimp [written]; rw [effect.otherStorage.nextRef]; exact allocated) separate
    have valuesLength : values.length = fuel := permutation.length_eq.trans erasedLength
    have popStorage := Storage.of_heap (result := state.v3)
      (fun ref vertices positions _ position => effect.otherArrays ref vertices positions position)
      effect.otherStorage effect.otherClocks
    have iterationStorage : Storage state.v2
        [layout.vertices, layout.positions, layout.keys, state.v3] heap written :=
      ((Storage.tick _ _ _).trans popStorage).trans (Storage.write _ _ _ _ (by simp) _ _)
    have iterationBudget : Budget count 1 heap written :=
      operation_budget (by omega : layout.size - 2 ≤ count) effect.comparisons effect.swaps effect.otherClocks
    refine ⟨final, vertex :: values,
      extract_continue heap after final state vertex (by omega)
        (by rw [effect.otherStorage.nextRef]; exact allocated) call rest,
      (permutation.cons vertex).trans (List.perm_cons_erase member).symm, ?_, ?_, ?_,
      iterationStorage.trans storage, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, sorted⟩
      intro value present
      have oldMember := List.mem_of_mem_erase (permutation.mem_iff.mp present)
      have minimum := effect.minimum value ((contents.1 value).mpr oldMember)
      change heap.read layout.keys vertex ≤ heap.read layout.keys value at minimum
      simpa only [contents.2 vertex member, contents.2 value oldMember] using minimum
    · intro position within
      cases position with
      | zero =>
        have keep := kept state.v4 (by dsimp [next, afterExtract]; omega)
        simpa [next, afterExtract, written, Heap.read, Heap.write] using keep
      | succ position =>
        have keep := output position (by simp only [List.length_cons] at within; omega)
        simpa [next, afterExtract, Int.natCast_add, Int.add_assoc, Int.add_left_comm,
          Int.add_comm] using keep
    · intro position before
      have keep := kept position (by dsimp [next, afterExtract]; omega)
      have unchanged := effect.otherArrays state.v3 separate.1 separate.2.1 position
      have writtenRead : written.read state.v3 position = heap.read state.v3 position := by
        simpa [written, Heap.read, Heap.write, show position ≠ state.v4 by omega] using unchanged
      exact keep.trans writtenRead
    · have all := iterationBudget.trans budget
      simpa [Nat.add_comm] using all

private def afterInsert (state : State_sort_indices) (key : Int) : State_sort_indices :=
  { state with v4 := state.v4 + 1, t11 := true, t12 := (), t13 := state.v2, t14 := state.v4, t15 := key }

/-- One insertion iteration reads an unchanged input key and applies the
    independently proved heap insertion contract. -/
private theorem insert_continue (heap after final : Heap) (state : State_sort_indices)
    (running : state.v4 < state.v1) (allocated : state.v0 < heap.nextRef)
    (call : Algo.indexed_heap.MinHeap.push_or_decrease.Call (heap.tick "sort_steps")
      (state.v2, state.v4, heap.read state.v0 state.v4) after ())
    (rest : Summary Step after
      (.fn_sort_indices 15 (afterInsert state (heap.read state.v0 state.v4))) final (.fn_sort_indices state.v3)) :
    Summary Step heap (.fn_sort_indices 15 state) final (.fn_sort_indices state.v3) := by
  intro caller
  apply Reaches.prepend (Step.sort_indices_pc15 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc14_true _ _ _ (by simpa using running))
  apply Reaches.prepend (Step.sort_indices_pc22 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc21 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc20 _ _ _ (by exact call.1))
  apply Reaches.prepend (Step.sort_indices_pc19 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc18 _ _ _ (by exact allocated))
  apply Reaches.prepend (Step.sort_indices_pc17 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller call.2).trans
  apply Reaches.prepend (Step.sort_indices_pc16 _ _ _)
  simpa [afterInsert, running] using rest caller

/-- The insertion invariant records exactly the identifiers already inserted;
    all input weights retain their original values. -/
private theorem insert_loop (count : Int) (fuel : Nat) (keys : Seq) :
    ∀ (heap : Heap) (state : State_sort_indices) (layout : Layout),
    state.v1 = count → 0 ≤ state.v4 → state.v4 + (fuel : Int) = count →
    layout.size = state.v4 → QueueRep heap state.v2 layout →
    Contents keys (Algo2Lean.FiniteIndex.range state.v4) heap layout →
    heap.read state.v0 = keys → state.v0 < heap.nextRef → state.v3 < heap.nextRef →
    state.v0 ≠ layout.vertices ∧ state.v0 ≠ layout.positions ∧ state.v0 ≠ layout.keys →
    state.v3 ≠ layout.vertices ∧ state.v3 ≠ layout.positions ∧ state.v3 ≠ layout.keys →
    ∃ (final : Heap),
      Summary Step heap (.fn_sort_indices 15 state) final (.fn_sort_indices state.v3) ∧
      SortedPermutation keys count (final.read state.v3) ∧
      Storage state.v2 [layout.vertices, layout.positions, layout.keys, state.v3] heap final ∧
      Budget count (fuel + count.toNat) heap final := by
  induction fuel with
  | zero =>
    intro heap state layout total index finish size represented contents input keysValid outputValid keysSeparate outputSeparate
    have atEnd : state.v4 = count := by omega
    have countNonnegative : 0 ≤ count := by omega
    let next : State_sort_indices := { state with v4 := 0, t11 := false }
    have allContents : Contents keys (Algo2Lean.FiniteIndex.range count) heap layout := by
      simpa [atEnd] using contents
    obtain ⟨final, values, rest, permutation, sorted, output, kept, storage, budget⟩ :=
      extract_loop count count.toNat keys heap next layout (Algo2Lean.FiniteIndex.range count)
        (Algo2Lean.FiniteIndex.range_length _) (Algo2Lean.FiniteIndex.range_nodup _) total
        (by simp [next]) (by dsimp [next]; omega) (by omega) represented allContents outputValid outputSeparate
    refine ⟨final, ?_, ⟨values, permutation, sorted, ?_⟩, storage, ?_⟩
    · intro caller
      apply Reaches.prepend (Step.sort_indices_pc15 _ _ _)
      apply Reaches.prepend (Step.sort_indices_pc14_false _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.sort_indices_pc13 _ _ _)
      simpa [next, show ¬state.v4 < state.v1 by omega] using rest caller
    · simpa [next] using output
    · simpa using budget
  | succ fuel ih =>
    intro heap state layout total index finish size represented contents input keysValid outputValid keysSeparate outputSeparate
    have absent : heap.read layout.positions state.v4 = -1 :=
      represented.indexed.absent state.v4 (by
        have notPresent : ¬0 ≤ heap.read layout.positions state.v4 := by
          intro present
          have := (Algo2Lean.FiniteIndex.range_member _ _).mp ((contents.1 state.v4).mp present)
          omega
        omega)
    obtain ⟨after, call, representedAfter, membership, keyValues, comparisons, swaps, arrays, clocks, storage⟩ :=
      insert_correct (heap.tick "sort_steps") state.v2 layout (queue_tick represented)
        state.v4 (heap.read state.v0 state.v4) absent
    let next := afterInsert state (heap.read state.v0 state.v4)
    let enlarged := { layout with size := layout.size + 1 }
    have nextContents : Contents keys (Algo2Lean.FiniteIndex.range next.v4) after enlarged := by
      constructor
      · intro value
        rw [Algo2Lean.FiniteIndex.range_member]
        change 0 ≤ after.read layout.positions value ↔ _
        rw [membership value]
        change (value = state.v4 ∨ 0 ≤ heap.read layout.positions value) ↔ _
        rw [contents.1 value, Algo2Lean.FiniteIndex.range_member]
        dsimp [next, afterInsert]
        omega
      · intro value present
        change after.read layout.keys value = keys value
        rw [keyValues value]
        by_cases same : value = state.v4
        · subst value
          simp [input]
        · have oldMember : value ∈ Algo2Lean.FiniteIndex.range state.v4 := by
            have := (Algo2Lean.FiniteIndex.range_member _ _).mp present
            apply (Algo2Lean.FiniteIndex.range_member _ _).mpr
            dsimp [next, afterInsert] at this
            omega
          simp [same, contents.2 value oldMember]
    have inputAfter : after.read state.v0 = keys := by
      funext position
      rw [arrays state.v0 keysSeparate.1 keysSeparate.2.1 keysSeparate.2.2 position]
      exact congrFun input position
    obtain ⟨final, rest, correct, frame, budget⟩ := ih after next enlarged total
      (by dsimp [next, afterInsert]; omega) (by dsimp [next, afterInsert]; omega)
      (by dsimp [enlarged, next, afterInsert]; omega) representedAfter nextContents
      inputAfter (by rw [storage.nextRef]; exact keysValid)
      (by rw [storage.nextRef]; exact outputValid) keysSeparate outputSeparate
    have iterationStorage : Storage state.v2
        [layout.vertices, layout.positions, layout.keys, state.v3] heap after :=
      (Storage.tick _ _ _).trans (Storage.of_heap arrays storage clocks)
    have iterationBudget : Budget count 1 heap after :=
      operation_budget (by omega : layout.size ≤ count)
        (Nat.le_trans comparisons (by omega)) (Nat.le_trans swaps (by omega)) clocks
    refine ⟨final, insert_continue heap after final state (by omega) keysValid call rest,
      correct, iterationStorage.trans frame, ?_⟩
    have all := iterationBudget.trans budget
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

private theorem queue_allocate {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) (contents : Seq) :
    QueueRep (heap.allocate contents) queue layout := by
  have old (ref : SeqRef) (allocated : ref < heap.nextRef) :
      (heap.allocate contents).read ref = heap.read ref := by
    funext index
    simp [Heap.read, Heap.allocate, Nat.ne_of_lt allocated]
  constructor
  · refine ⟨represented.valid.object, represented.valid.readVertices, represented.valid.readPositions,
      represented.valid.readKeys, represented.valid.readSize, ?_, ?_, ?_,
      represented.valid.verticesPositions, represented.valid.verticesKeys, represented.valid.positionsKeys⟩
    all_goals change _ < heap.nextRef + 1
    · exact Nat.lt_succ_of_lt represented.valid.verticesAllocated
    · exact Nat.lt_succ_of_lt represented.valid.positionsAllocated
    · exact Nat.lt_succ_of_lt represented.valid.keysAllocated
  · exact represented.nonnegative
  · rw [old layout.vertices represented.valid.verticesAllocated,
        old layout.positions represented.valid.positionsAllocated]
    exact represented.indexed
  · simpa only [old layout.vertices represented.valid.verticesAllocated,
      old layout.keys represented.valid.keysAllocated] using represented.ordered

private def preparedHeap (heap : Heap) : Heap := (newHeap heap).allocate (fun _ => 0)

private theorem prepared_preserves (heap : Heap) : Preserves heap (preparedHeap heap) := by
  constructor
  · intro ref allocated
    funext index
    have separate : ref ≠ (newHeap heap).nextRef := by
      change ref ≠ heap.nextRef + 3
      omega
    simpa [preparedHeap, Heap.read, Heap.allocate, separate] using new_heap_read_old heap ref index allocated
  · intro ref allocated
    have separate : ref ≠ heap.nextObject := Nat.ne_of_lt allocated
    simp [preparedHeap, newHeap, initializedHeap, set_MinHeap_vertices, set_MinHeap_positions,
      set_MinHeap_keys, set_MinHeap_size, Heap.writeField, Heap.allocateObject, separate]
  · rfl
  · change heap.nextRef ≤ heap.nextRef + 3 + 1; omega
  · change heap.nextObject ≤ heap.nextObject + 1; omega
  · rfl
  · intros; rfl

/-- The complete operational contract: a terminating call returns a fresh array,
    preserves the caller's data, sorts exactly the identifiers, and has a
    logarithmic per-iteration bound on every clock. -/
theorem call (heap : Heap) (keys : SeqRef) (count : Int)
    (allocated : keys < heap.nextRef) (nonnegative : 0 ≤ count) :
    ∃ after result, sort_indices.Call heap (keys, count) after result ∧
      SortedPermutation (heap.read keys) count (after.read result) ∧
      Preserves heap after ∧ heap.nextRef ≤ result ∧ result < after.nextRef ∧
      Budget count (2 * count.toNat) heap after := by
  let prepared := preparedHeap heap
  let result := (newHeap heap).nextRef
  let state : State_sort_indices :=
    { v0 := keys, v1 := count, v2 := heap.nextObject, v3 := result,
      t16 := result, t17 := 0, t18 := heap.nextObject }
  have initial := prepared_preserves heap
  have contents : Contents (heap.read keys) (Algo2Lean.FiniteIndex.range state.v4)
      prepared (emptyLayout heap) := by
    constructor
    · intro value
      have position : prepared.read (emptyLayout heap).positions value = -1 := by
        have separate : (emptyLayout heap).positions ≠ (newHeap heap).nextRef := by
          change heap.nextRef + 1 ≠ heap.nextRef + 3
          omega
        simpa [prepared, preparedHeap, Heap.read, Heap.allocate, separate] using new_heap_positions heap value
      simp [state, position, Algo2Lean.FiniteIndex.range]
    · intro value present
      simp [state, Algo2Lean.FiniteIndex.range] at present
  have keysSeparate : keys ≠ (emptyLayout heap).vertices ∧ keys ≠ (emptyLayout heap).positions ∧
      keys ≠ (emptyLayout heap).keys := by
    exact ⟨Nat.ne_of_lt allocated,
      Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _)),
      Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))⟩
  have outputSeparate : result ≠ (emptyLayout heap).vertices ∧ result ≠ (emptyLayout heap).positions ∧
      result ≠ (emptyLayout heap).keys := by
    change heap.nextRef + 3 ≠ heap.nextRef ∧ heap.nextRef + 3 ≠ heap.nextRef + 1 ∧
      heap.nextRef + 3 ≠ heap.nextRef + 2
    omega
  obtain ⟨after, execution, correct, storage, budget⟩ :=
    insert_loop count count.toNat (heap.read keys) prepared state (emptyLayout heap)
      rfl (by simp [state]) (by dsimp [state]; omega) rfl
      (queue_allocate (new_heap_rep heap) (fun _ => 0)) contents
      (initial.sequences keys allocated) (Nat.lt_of_lt_of_le allocated initial.refs)
      (by change result < result + 1; omega) keysSeparate outputSeparate
  refine ⟨after, result, ⟨allocated, ?_⟩, correct, ?_, ?_, ?_, ?_⟩
  · intro caller
    apply Reaches.prepend (Step.sort_indices_pc28 _ _ _)
    apply (ModuleCall.summary import_0_simulates _ caller (new_heap_summary heap).2).trans
    apply Reaches.prepend (Step.sort_indices_pc27 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc26 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc25 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc24 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc23 _ _ _)
    exact execution caller
  · constructor
    · intro ref old
      have separate : ref ∉ [(emptyLayout heap).vertices, (emptyLayout heap).positions,
          (emptyLayout heap).keys, result] := by
        change ref ∉ [heap.nextRef, heap.nextRef + 1, heap.nextRef + 2, heap.nextRef + 3]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        omega
      exact (storage.arrays ref separate).trans (initial.sequences ref old)
    · intro ref old
      exact (storage.objects ref (Nat.ne_of_lt old)).trans (initial.objects ref old)
    · exact storage.collections.trans initial.collections
    · rw [storage.nextRef]; exact initial.refs
    · rw [storage.nextObject]; exact initial.objectRefs
    · exact storage.nextCollection.trans initial.collectionRefs
    · intro name source comparisons swaps
      exact (storage.clocks name source comparisons swaps).trans (initial.clocks name source comparisons swaps)
  · change heap.nextRef ≤ heap.nextRef + 3; omega
  · rw [storage.nextRef]
    change result < result + 1
    omega
  · simpa only [Budget, state, prepared, preparedHeap, Heap.allocate, new_heap_clocks,
      Nat.two_mul] using budget

/-- The budget can be used with any chosen nonnegative weights for the clocks. -/
theorem Budget.weighted {heap after : Heap} {count : Int} {steps : Nat}
    (budget : Budget count steps heap after) (metric : List (String × Nat)) :
    Heap.weightedCost metric heap after ≤ steps * Clocks.weighted metric (rate count) := by
  have bounded : ∀ clock, Heap.cost heap after clock ≤ steps * rate count clock := by
    intro clock
    have bound := budget clock
    unfold Heap.cost
    omega
  have distribute : Clocks.weighted metric (fun clock => steps * rate count clock) =
      steps * Clocks.weighted metric (rate count) := by
    induction metric with
    | nil => simp [Clocks.weighted]
    | cons head tail ih =>
      rcases head with ⟨clock, weight⟩
      simp only [Clocks.weighted, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp [Nat.mul_add, Nat.mul_left_comm]
  have weighted := Clocks.weighted_le metric bounded
  rw [distribute] at weighted
  exact weighted

/-- Unit weight for loop bodies, heap comparisons, and heap swaps. -/
def runtime (costs : Clocks) : Nat :=
  Clocks.weighted [("sort_steps", 1), ("heap_comparisons", 1), ("heap_swaps", 1)] costs

/-- An explicit O(n log(n + 1)) operation bound. -/
def runtimeBound (count : Nat) : Nat := 2 * count * (3 * (count + 1).log2 + 2)

private theorem budget_runtime {heap after : Heap} {count : Int}
    (budget : Budget count (2 * count.toNat) heap after) :
    runtime (Heap.cost heap after) ≤ runtimeBound count.toNat := by
  have bound := budget.weighted [("sort_steps", 1), ("heap_comparisons", 1), ("heap_swaps", 1)]
  have rates : Clocks.weighted [("sort_steps", 1), ("heap_comparisons", 1), ("heap_swaps", 1)]
      (rate count) = 3 * (count.toNat + 1).log2 + 2 := by
    simp [Clocks.weighted, rate, depth]
    omega
  rw [rates] at bound
  exact bound

-- Main result: Correctness
/-- Every completed execution sorts all identifiers and preserves all previously
    allocated sequences, objects, and typed collections. -/
theorem correct {heap after : Heap} {keys result : SeqRef} {count : Int}
    (execution : sort_indices.Run heap (keys, count) after result) (nonnegative : 0 ≤ count) :
    SortedPermutation (heap.read keys) count (after.read result) ∧ Preserves heap after := by
  obtain ⟨final, output, summary, sorted, preserved, fresh, allocated, budget⟩ :=
    call heap keys count execution.1 nonnegative
  obtain ⟨rfl, rfl⟩ := execution.eq_of_call summary
  exact ⟨sorted, preserved⟩

-- Main result: Running time
/-- Every completed execution has at most 2n(3 log2(n+1)+2) weighted operations. -/
theorem running_time {heap after : Heap} {keys result : SeqRef} {count : Int}
    (execution : sort_indices.Run heap (keys, count) after result) (nonnegative : 0 ≤ count) :
    runtime (Heap.cost heap after) ≤ runtimeBound count.toNat := by
  obtain ⟨final, output, summary, sorted, preserved, fresh, allocated, budget⟩ :=
    call heap keys count execution.1 nonnegative
  obtain ⟨rfl, rfl⟩ := execution.eq_of_call summary
  exact budget_runtime budget

end SortIndicesAnalysis
