import Algo.union_find.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Construction of the reusable rank-and-compression disjoint-set structure.
The constructor allocates one object and two arrays, initializes singleton
components, and charges exactly `n + 1` initialization ticks. -/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated

/-- The exact heap effect of initializing a consecutive interval of parent entries. -/
def initializeEntries (heap : Heap) (parent : SeqRef) (first : Int) : Nat → Heap
  | 0 => heap
  | count + 1 => initializeEntries ((heap.write parent first first).tick "uf_init")
      parent (first + 1) count

@[simp] theorem initializeEntries_objects (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).objects = heap.objects := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih, Heap.write]

@[simp] theorem initializeEntries_nextObject (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).nextObject = heap.nextObject := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]

@[simp] theorem initializeEntries_nextRef (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).nextRef = heap.nextRef := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]

@[simp] theorem initializeEntries_collections (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).collections = heap.collections := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]

@[simp] theorem initializeEntries_nextCollection (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) :
    (initializeEntries heap parent first count).nextCollection = heap.nextCollection := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih => simp [initializeEntries, ih]

/-- The named initialization loop writes every remaining parent pointer and
    returns beneath any caller; its preconditions describe only the local state. -/
theorem initialize_remaining (count : Nat) (state : Configuration)
    (object : Ref_UnionFind) (parent : SeqRef) (first : Int)
    (location : UnionFind.__init__.At.initialize state)
    (readObject : UnionFind.__init__.Local.self state = some object)
    (readFirst : UnionFind.__init__.Local.vertex state = some first)
    (readBound : UnionFind.__init__.Local.size state = some (first + (count : Int)))
    (readParent : field_UnionFind_parent state.heap object = some parent)
    (allocated : parent < state.heap.nextRef) :
    UnionFind.__init__.CallFrom state (initializeEntries state.heap parent first count) () := by
  induction count generalizing state first with
  | zero =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_UnionFind_find => cases location
      | fn_UnionFind_union => cases location
      | fn_UnionFind => cases location
      | fn_UnionFind___init__ pc s =>
        have counter : pc = 4 := by
          unfold UnionFind.__init__.At.initialize at location
          split at location <;> simp_all
        subst pc
        simp only [Config.heap] at readParent allocated
        simp [UnionFind.__init__.Local.self, UnionFind.__init__.Local.vertex,
          UnionFind.__init__.Local.size] at readObject readFirst readBound
        intro caller
        apply Reaches.prepend (Step.UnionFind___init___pc4 _ _ _)
        apply Reaches.prepend (Step.UnionFind___init___pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega))
        apply Reaches.prepend (Step.UnionFind___init___pc2 _ _ _)
        exact Reaches.single (Step.UnionFind___init___pc1 _ _ _)
  | succ count ih =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_UnionFind_find => cases location
      | fn_UnionFind_union => cases location
      | fn_UnionFind => cases location
      | fn_UnionFind___init__ pc s =>
        have counter : pc = 4 := by
          unfold UnionFind.__init__.At.initialize at location
          split at location <;> simp_all
        subst pc
        simp only [Config.heap] at readParent allocated
        simp [UnionFind.__init__.Local.self, UnionFind.__init__.Local.vertex,
          UnionFind.__init__.Local.size] at readObject readFirst readBound
        have next := ih
          (.active ((heap.write parent s.v2 s.v2).tick "uf_init")
            (.fn_UnionFind___init__ 4 { s with t4 := decide (s.v2 < s.v1), v2 := s.v2 + 1 })
            originalStack) (first + 1) True.intro
          (by simpa [UnionFind.__init__.Local.self] using readObject)
          (by simp [UnionFind.__init__.Local.vertex, readFirst])
          (by simp [UnionFind.__init__.Local.size]; omega)
          readParent allocated
        intro caller
        apply Reaches.prepend (Step.UnionFind___init___pc4 _ _ _)
        apply Reaches.prepend (Step.UnionFind___init___pc3_true _ _ _
          (by simp only [decide_eq_true_eq]; omega))
        apply Reaches.prepend (Step.UnionFind___init___pc7 _ _ _
          (by simpa [readObject, readParent] using allocated))
        apply Reaches.prepend (Step.UnionFind___init___pc6 _ _ _)
        apply Reaches.prepend (Step.UnionFind___init___pc5 _ _ _)
        simpa [Config.heap, initializeEntries, readFirst, readObject, readParent] using next caller

/-- Allocate the two zero-filled arrays and install the object's fields. -/
def prepareInitialHeap (heap : Heap) (object : Ref_UnionFind) (size : Int) : Heap :=
  let withParent := set_UnionFind_parent (heap.allocate (fun _ => 0)) object heap.nextRef
  let withRank := set_UnionFind_rank (withParent.allocate (fun _ => 0)) object withParent.nextRef
  set_UnionFind_size withRank object size

/-- The initializer's exact output heap. -/
def initializedHeap (heap : Heap) (object : Ref_UnionFind) (size : Nat) : Heap :=
  initializeEntries ((prepareInitialHeap heap object size).tick "uf_init") heap.nextRef 0 size

/-- The constructor's exact output heap, with all allocation identities explicit. -/
def newHeap (heap : Heap) (size : Nat) : Heap :=
  initializedHeap (heap.allocateObject "union_find.UnionFind") heap.nextObject size

/-- The two newly allocated sequence references and their owning object. -/
def newLayout (heap : Heap) : Layout :=
  ⟨heap.nextObject, heap.nextRef, heap.nextRef + 1⟩

@[simp] theorem prepareInitialHeap_valid (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) : is_UnionFind (prepareInitialHeap heap object size) object := by
  simpa [prepareInitialHeap, is_UnionFind, set_UnionFind_parent, set_UnionFind_rank,
    set_UnionFind_size] using valid

@[simp] theorem prepareInitialHeap_nextRef (heap : Heap) (object : Ref_UnionFind) (size : Int) :
    (prepareInitialHeap heap object size).nextRef = heap.nextRef + 2 := by
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size, Nat.add_assoc]

@[simp] theorem prepareInitialHeap_parent (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) :
    field_UnionFind_parent (prepareInitialHeap heap object size) object = some heap.nextRef := by
  have preparedValid := prepareInitialHeap_valid heap object size valid
  rw [field_UnionFind_parent, if_pos preparedValid]
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
    valid.2, ObjectValue.asSeq]

@[simp] theorem prepareInitialHeap_rank (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) :
    field_UnionFind_rank (prepareInitialHeap heap object size) object = some (heap.nextRef + 1) := by
  have preparedValid := prepareInitialHeap_valid heap object size valid
  rw [field_UnionFind_rank, if_pos preparedValid]
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
    valid.2, ObjectValue.asSeq]

@[simp] theorem prepareInitialHeap_size (heap : Heap) (object : Ref_UnionFind) (size : Int)
    (valid : is_UnionFind heap object) :
    field_UnionFind_size (prepareInitialHeap heap object size) object = some size := by
  have preparedValid := prepareInitialHeap_valid heap object size valid
  rw [field_UnionFind_size, if_pos preparedValid]
  simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
    valid.2, ObjectValue.asInt]

@[simp] theorem initializedHeap_valid (heap : Heap) (object : Ref_UnionFind) (size : Nat)
    (valid : is_UnionFind heap object) : is_UnionFind (initializedHeap heap object size) object := by
  simpa [initializedHeap, is_UnionFind, Heap.objectClass] using
    prepareInitialHeap_valid heap object size valid

/-- Initialization executes the source assignments and the complete named loop. -/
theorem initialization_summary (heap : Heap) (object : Ref_UnionFind) (size : Nat)
    (valid : is_UnionFind heap object) :
    UnionFind.__init__.Call heap (object, (size : Int)) (initializedHeap heap object size) () := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.UnionFind___init___pc18 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc17 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc16 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc15 _ _ _ (by simpa [is_UnionFind] using valid))
  apply Reaches.prepend (Step.UnionFind___init___pc14 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc13 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc12 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc11 _ _ _
    (by simpa [is_UnionFind, set_UnionFind_parent] using valid))
  apply Reaches.prepend (Step.UnionFind___init___pc10 _ _ _
    (by simpa [is_UnionFind, set_UnionFind_parent, set_UnionFind_rank] using valid))
  apply Reaches.prepend (Step.UnionFind___init___pc9 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc8 _ _ _)
  have loop := initialize_remaining size
    (.active ((prepareInitialHeap heap object size).tick "uf_init")
      (.fn_UnionFind___init__ 4 { v0 := object, v1 := size, v2 := 0, t5 := heap.nextRef + 1, t6 := object, t8 := heap.nextRef, t9 := object }) caller)
    object heap.nextRef 0 True.intro rfl rfl (by simp [UnionFind.__init__.Local.size])
    (prepareInitialHeap_parent heap object size valid) (by
      change heap.nextRef < (prepareInitialHeap heap object size).nextRef
      simp)
  simpa [initializedHeap, prepareInitialHeap, set_UnionFind_parent] using! loop caller

/-- The public constructor always terminates on a natural size. -/
theorem constructor_summary (heap : Heap) (size : Nat) :
    UnionFind.Call heap (size : Int) (newHeap heap size) heap.nextObject := by
  have allocated : is_UnionFind (heap.allocateObject "union_find.UnionFind") heap.nextObject := by
    simp [is_UnionFind]
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.UnionFind_pc7 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc6 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc5 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc4 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc3 _ _ _)
  apply Reaches.trans ((initialization_summary _ _ size allocated).2 _)
  apply Reaches.prepend (Step.UnionFind_pc2 _ _ _)
  exact Reaches.single (Step.UnionFind_pc1 _ _ _ (initializedHeap_valid _ _ size allocated))

/-- Initializing parents preserves every other sequence. -/
theorem initializeEntries_other (heap : Heap) (parent other : SeqRef)
    (first : Int) (count : Nat) (different : other ≠ parent) :
    (initializeEntries heap parent first count).read other = heap.read other := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeEntries, ih]
    funext index
    simp [Heap.read, Heap.write, different]

/-- Writes in a later interval preserve all earlier entries. -/
theorem initializeEntries_before (heap : Heap) (parent : SeqRef)
    (first index : Int) (count : Nat) (earlier : index < first) :
    (initializeEntries heap parent first count).read parent index = heap.read parent index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeEntries, ih _ _ (by omega)]
    simp [Heap.read, Heap.write, show index ≠ first by omega]

/-- Every initialized vertex becomes its own parent. -/
theorem initializeEntries_identity (heap : Heap) (parent : SeqRef)
    (first index : Int) (count : Nat) (lower : first ≤ index) (upper : index < first + count) :
    (initializeEntries heap parent first count).read parent index = index := by
  induction count generalizing heap first with
  | zero => omega
  | succ count ih =>
    rw [initializeEntries]
    by_cases same : index = first
    · rw [initializeEntries_before _ _ _ _ _ (by omega)]
      simp [same]
    · exact ih _ _ (by omega) (by omega)

/-- Each initialized entry contributes one tick and changes no other clock. -/
theorem initializeEntries_clocks (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (clock : String) :
    (initializeEntries heap parent first count).clocks clock =
      heap.clocks clock + if clock = "uf_init" then count else 0 := by
  induction count generalizing heap first with
  | zero => simp [initializeEntries]
  | succ count ih =>
    rw [initializeEntries, ih]
    by_cases same : clock = "uf_init" <;> simp [Heap.tick, same, Nat.add_assoc, Nat.add_comm]

@[simp] theorem initializeEntries_objectClass (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (object : Ref_UnionFind) :
    (initializeEntries heap parent first count).objectClass object = heap.objectClass object := by
  simp [Heap.objectClass]

@[simp] theorem initializeEntries_readField (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (object : Ref_UnionFind) (field : String) :
    (initializeEntries heap parent first count).readField object field = heap.readField object field := by
  simp [Heap.readField]

/-- Construction establishes the singleton partition and all rank invariants. -/
theorem constructor_rep (heap : Heap) (size : Nat) :
    Rep (newHeap heap size) (newLayout heap) (Algo2Lean.UnionFind.initial size) := by
  have allocated : is_UnionFind (heap.allocateObject "union_find.UnionFind") heap.nextObject := by
    simp [is_UnionFind]
  refine ⟨Algo2Lean.UnionFind.initial_valid size, initializedHeap_valid _ _ _ allocated,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [newHeap, newLayout, initializedHeap, field_UnionFind_parent, is_UnionFind] using!
      prepareInitialHeap_parent _ _ (size : Int) allocated
  · simpa [newHeap, newLayout, initializedHeap, field_UnionFind_rank, is_UnionFind] using!
      prepareInitialHeap_rank _ _ (size : Int) allocated
  · simpa [newHeap, newLayout, initializedHeap, field_UnionFind_size, is_UnionFind] using!
      prepareInitialHeap_size _ _ (size : Int) allocated
  · simp [newHeap, newLayout, initializedHeap]
  · simp [newHeap, newLayout, initializedHeap]
  · simp [newLayout]
  · intro vertex
    exact initializeEntries_identity _ _ 0 vertex.val size (Int.natCast_nonneg _) (by have := vertex.isLt; omega)
  · intro vertex
    have other := initializeEntries_other
      ((prepareInitialHeap (heap.allocateObject "union_find.UnionFind") heap.nextObject size).tick "uf_init")
      heap.nextRef (heap.nextRef + 1) 0 size (Nat.ne_of_gt (Nat.lt_succ_self _))
    change (initializeEntries _ heap.nextRef 0 size).read (heap.nextRef + 1) vertex.val = 0
    rw [other]
    simp [prepareInitialHeap, set_UnionFind_size, set_UnionFind_rank, set_UnionFind_parent,
      Heap.read, Heap.allocate]

/-- The constructor charges exactly one initial tick plus one per vertex. -/
theorem constructor_clocks (heap : Heap) (size : Nat) (clock : String) :
    (newHeap heap size).clocks clock = heap.clocks clock +
      if clock = "uf_init" then size + 1 else 0 := by
  simp only [newHeap, initializedHeap, initializeEntries_clocks]
  by_cases same : clock = "uf_init" <;>
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.tick, same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Constructor allocation adds exactly two integer sequences and one object,
    and leaves the collection allocation boundary unchanged. -/
theorem constructor_allocations (heap : Heap) (size : Nat) :
    (newHeap heap size).nextRef = heap.nextRef + 2 ∧
    (newHeap heap size).nextObject = heap.nextObject + 1 ∧
    (newHeap heap size).nextCollection = heap.nextCollection := by
  simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
    set_UnionFind_size, Nat.add_assoc]

/-- All old storage survives construction; the new arrays and object are fresh. -/
theorem constructor_frame (heap : Heap) (size : Nat) :
    (∀ ref, ref < heap.nextObject → (newHeap heap size).objects ref = heap.objects ref) ∧
    (∀ ref, ref < heap.nextRef → (newHeap heap size).read ref = heap.read ref) ∧
    (newHeap heap size).collections = heap.collections := by
  refine ⟨?_, ?_, ?_⟩
  · intro ref old
    simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size, Heap.writeField, Heap.allocateObject, Nat.ne_of_lt old]
  · intro ref old
    have different : ref ≠ heap.nextRef := Nat.ne_of_lt old
    simp only [newHeap, initializedHeap, Heap.allocateObject_nextRef,
      initializeEntries_other _ _ _ _ _ different]
    funext index
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.read, Heap.allocate, different, show ref ≠ heap.nextRef + 1 by omega]
  · simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size]

-- Main result: Correctness and running time
/-- Constructing `n` singleton components always terminates, establishes the
    reusable disjoint-set representation, preserves preexisting storage, and
    charges exactly `n + 1` ticks to `uf_init` and zero to every other clock. -/
theorem constructor_verified (heap : Heap) (size : Nat) :
    UnionFind.Call heap (size : Int) (newHeap heap size) heap.nextObject ∧
    Rep (newHeap heap size) (newLayout heap) (Algo2Lean.UnionFind.initial size) ∧
    (∀ clock, Heap.cost heap (newHeap heap size) clock = if clock = "uf_init" then size + 1 else 0) ∧
    (∀ ref, ref < heap.nextObject → (newHeap heap size).objects ref = heap.objects ref) ∧
    (∀ ref, ref < heap.nextRef → (newHeap heap size).read ref = heap.read ref) ∧
    (newHeap heap size).collections = heap.collections ∧
    (newHeap heap size).nextRef = heap.nextRef + 2 ∧
    (newHeap heap size).nextObject = heap.nextObject + 1 ∧
    (newHeap heap size).nextCollection = heap.nextCollection := by
  obtain ⟨objects, sequences, collections⟩ := constructor_frame heap size
  obtain ⟨nextRef, nextObject, nextCollection⟩ := constructor_allocations heap size
  refine ⟨constructor_summary heap size, constructor_rep heap size, ?_, objects, sequences,
    collections, nextRef, nextObject, nextCollection⟩
  intro clock
  simp [Heap.cost, constructor_clocks]


/-- Constructor cost includes setup and one initialized parent per vertex. -/
def constructorCosts (size : Nat) : Clocks := fun clock =>
  if clock = "uf_init" then size + 1 else 0

/-- Initialization has exact increments for arbitrary initial caller counters. -/
theorem constructor_increments (heap : Heap) (size : Nat) :
    heap.Increments (newHeap heap size) (constructorCosts size) :=
  constructor_clocks heap size

/-- All existing storage is framed out of construction. Its object and arrays
    are fresh allocations, so its modification footprint is empty. -/
theorem constructor_footprint (heap : Heap) (size : Nat) :
    heap.Footprint (newHeap heap size) [] [] [] := by
  obtain ⟨objects, sequences, collections⟩ := constructor_frame heap size
  obtain ⟨nextRef, nextObject, nextCollection⟩ := constructor_allocations heap size
  refine ⟨by rw [nextRef]; omega, by rw [nextObject]; omega, by simp only [nextCollection, Nat.le_refl],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro ref old
    simp only [Heap.objectClass, objects ref old]
  · intro ref old
    simp only [Heap.collectionType, collections]
  · intro ref old _
    exact sequences ref old
  · intro ref old _
    exact objects ref old
  · intro ref old _
    rw [collections]

/-- Construction is reusable beneath an arbitrary caller: it establishes the
    initial mathematical partition, preserves all old storage, records exact
    clock increments, and allocates exactly two sequences and one object. -/
theorem constructor_contract (heap : Heap) (size : Nat) :
    UnionFind.Call heap (size : Int) (newHeap heap size) heap.nextObject ∧
    Rep (newHeap heap size) (newLayout heap) (Algo2Lean.UnionFind.initial size) ∧
    heap.Footprint (newHeap heap size) [] [] [] ∧
    heap.Increments (newHeap heap size) (constructorCosts size) ∧
    (newHeap heap size).nextRef = heap.nextRef + 2 ∧
    (newHeap heap size).nextObject = heap.nextObject + 1 ∧
    (newHeap heap size).nextCollection = heap.nextCollection :=
  ⟨constructor_summary heap size, constructor_rep heap size, constructor_footprint heap size,
    constructor_increments heap size, constructor_allocations heap size⟩

@[simp] theorem constructor_work (size : Nat) : work (constructorCosts size) = size + 1 := by
  simp [work, constructorCosts]

end UnionFindAnalysis
