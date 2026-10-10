import Algo.indexed_heap.Points

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `new_heap_rep`: Empty heap representation.
- `insert_correct`: Insertion correctness and cost.
- `decrease_correct`: Decrease-key correctness and cost.
- `pop_correct`: Minimum extraction correctness and cost.
-/

open Algo.indexed_heap Algo.indexed_heap.Algo2LeanGenerated

open Algo2LeanCore Algo2LeanGenerated

namespace BinaryModuleAnalysis

-- A small source-facing description of the object's storage. The three arrays
-- are separate mutable sequences; aliases to the MinHeap object remain valid.
structure Layout where
  vertices : SeqRef
  positions : SeqRef
  keys : SeqRef
  size : Int

structure Layout.Valid (layout : Layout) (heap : Heap) (queue : Ref_MinHeap) : Prop where
  object : is_MinHeap heap queue
  readVertices : field_MinHeap_vertices heap queue = some layout.vertices
  readPositions : field_MinHeap_positions heap queue = some layout.positions
  readKeys : field_MinHeap_keys heap queue = some layout.keys
  readSize : field_MinHeap_size heap queue = some layout.size
  verticesAllocated : layout.vertices < heap.nextRef
  positionsAllocated : layout.positions < heap.nextRef
  keysAllocated : layout.keys < heap.nextRef
  verticesPositions : layout.vertices ≠ layout.positions
  verticesKeys : layout.vertices ≠ layout.keys
  positionsKeys : layout.positions ≠ layout.keys

-- These observations use only the generated field interface. Updating an
-- array does not replace the object's fields or change its identity.
@[simp] theorem vertices_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_vertices (heap.write ref index value) queue =
      field_MinHeap_vertices heap queue := rfl

@[simp] theorem positions_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_positions (heap.write ref index value) queue =
      field_MinHeap_positions heap queue := rfl

-- Exact heap effect of swap, including the cost counter. The original two
-- vertices are read before either array is changed, including when i = j.
def swapHeap (heap : Heap) (layout : Layout) (i j : Int) : Heap :=
  let a := heap.read layout.vertices i
  let b := heap.read layout.vertices j
  ((((heap.write layout.vertices i b).write layout.vertices j a).write
    layout.positions a j).write layout.positions b i).tick "heap_swaps"

theorem swap_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (i j : Int) :
    MinHeap.swap.Call heap (queue, i, j) (swapHeap heap layout i j) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_swap_pc9 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc8 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc7 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc6 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc5 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc4 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc3 _ _ _)
  apply Reaches.prepend (Step.MinHeap_swap_pc2 _ _ _)
  simp only [vertices_write, positions_write, valid.readVertices, valid.readPositions,
    Option.getD_some, swapHeap]
  exact Reaches.single (Step.MinHeap_swap_pc1 _ _ _)

-- A permutation of positions, with all other positions left fixed.
def exchange (values : Seq) (i j index : Int) : Int :=
  if index = j then values i else if index = i then values j else values index

theorem swap_vertices (heap : Heap) (layout : Layout) (i j index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (swapHeap heap layout i j).read layout.vertices index =
      exchange (heap.read layout.vertices) i j index := by
  simp [swapHeap, exchange, Heap.read, Heap.write, separate]

theorem swap_positions (heap : Heap) (layout : Layout) (i j vertex : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (swapHeap heap layout i j).read layout.positions vertex =
      if vertex = heap.read layout.vertices j then i
      else if vertex = heap.read layout.vertices i then j
      else heap.read layout.positions vertex := by
  simp [swapHeap, Heap.read, Heap.write, Ne.symm separate]

theorem swap_keys (heap : Heap) (layout : Layout) (i j vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (swapHeap heap layout i j).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [swapHeap, Heap.read, Heap.write, Ne.symm separateVertices, Ne.symm separatePositions]

theorem swap_cost (heap : Heap) (layout : Layout) (i j : Int) :
    Heap.cost heap (swapHeap heap layout i j) = Clocks.single "heap_swaps" 1 := by
  funext name
  by_cases swaps : name = "heap_swaps"
  · subst name
    simp [swapHeap, Heap.cost, Heap.tick, Heap.write, Clocks.single]
  · simp [swapHeap, Heap.cost, Heap.tick, Heap.write, Clocks.single, swaps]

-- No duplicate active vertices, no stale positive positions, and exactly -1
-- for vertices outside the heap. These are finite-prefix map invariants.
structure Indexed (vertices positions : Seq) (size : Int) : Prop where
  forward : ∀ index, 0 ≤ index → index < size → positions (vertices index) = index
  backward : ∀ vertex, 0 ≤ positions vertex →
    positions vertex < size ∧ vertices (positions vertex) = vertex
  absent : ∀ vertex, positions vertex < 0 → positions vertex = -1

theorem Indexed.distinct {vertices positions : Seq} {size i j : Int}
    (indexed : Indexed vertices positions size)
    (iNonnegative : 0 ≤ i) (iBound : i < size)
    (jNonnegative : 0 ≤ j) (jBound : j < size) :
    vertices i = vertices j → i = j := by
  intro same
  have left := indexed.forward i iNonnegative iBound
  have right := indexed.forward j jNonnegative jBound
  rw [same] at left
  exact left.symm.trans right

@[simp] theorem exchange_left (values : Seq) (i j : Int) :
    exchange values i j i = values j := by
  by_cases same : i = j <;> simp [exchange, same]

@[simp] theorem exchange_right (values : Seq) (i j : Int) :
    exchange values i j j = values i := by simp [exchange]

-- Swapping two valid heap positions preserves the inverse map, including a
-- self-swap. No heap-order assumption or concrete input values are required.
theorem swap_preserves_indexed (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) :
    Indexed ((swapHeap heap layout i j).read layout.vertices)
      ((swapHeap heap layout i j).read layout.positions) layout.size := by
  have left := indexed.forward i iNonnegative iBound
  have right := indexed.forward j jNonnegative jBound
  have equalIndices : heap.read layout.vertices i = heap.read layout.vertices j → i = j :=
    indexed.distinct iNonnegative iBound jNonnegative jBound
  constructor
  · intro index nonnegative bound
    rw [swap_vertices heap layout i j index separate]
    by_cases atRight : index = j
    · subst index
      rw [exchange_right, swap_positions heap layout i j _ separate]
      by_cases same : heap.read layout.vertices i = heap.read layout.vertices j
      · simp [equalIndices same]
      · simp [same]
    · by_cases atLeft : index = i
      · subst index
        rw [exchange_left, swap_positions heap layout i j _ separate]
        simp
      · have notRight : heap.read layout.vertices index ≠ heap.read layout.vertices j := by
          intro same
          exact atRight (indexed.distinct nonnegative bound jNonnegative jBound same)
        have notLeft : heap.read layout.vertices index ≠ heap.read layout.vertices i := by
          intro same
          exact atLeft (indexed.distinct nonnegative bound iNonnegative iBound same)
        simp only [exchange, atRight, atLeft, ite_false]
        rw [swap_positions heap layout i j _ separate]
        simpa [notRight, notLeft] using indexed.forward index nonnegative bound
  · intro vertex nonnegative
    by_cases isRight : vertex = heap.read layout.vertices j
    · subst vertex
      simp only [swap_positions heap layout i j _ separate, ite_true]
      exact ⟨iBound, by rw [swap_vertices heap layout i j i separate, exchange_left]⟩
    · by_cases isLeft : vertex = heap.read layout.vertices i
      · subst vertex
        simp only [swap_positions heap layout i j _ separate, isRight, ite_false, ite_true]
        exact ⟨jBound, by rw [swap_vertices heap layout i j j separate, exchange_right]⟩
      · have unchanged : (swapHeap heap layout i j).read layout.positions vertex =
            heap.read layout.positions vertex := by
          rw [swap_positions heap layout i j _ separate]
          simp [isRight, isLeft]
        rw [unchanged] at nonnegative ⊢
        obtain ⟨bound, identity⟩ := indexed.backward vertex nonnegative
        have notRight : heap.read layout.positions vertex ≠ j := by
          intro same
          rw [same] at identity
          exact isRight identity.symm
        have notLeft : heap.read layout.positions vertex ≠ i := by
          intro same
          rw [same] at identity
          exact isLeft identity.symm
        refine ⟨bound, ?_⟩
        rw [swap_vertices heap layout i j _ separate]
        simpa [exchange, notRight, notLeft] using identity
  · intro vertex negative
    rw [swap_positions heap layout i j _ separate] at negative ⊢
    split at negative <;> simp_all
    · omega
    split at negative <;> simp_all
    · omega
    exact indexed.absent vertex negative

-- Position numbers may change, but exactly the same vertices remain present.
theorem swap_preserves_membership (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) (vertex : Int) :
    0 ≤ (swapHeap heap layout i j).read layout.positions vertex ↔
      0 ≤ heap.read layout.positions vertex := by
  rw [swap_positions heap layout i j vertex separate]
  by_cases atRight : vertex = heap.read layout.vertices j
  · subst vertex
    simp [indexed.forward j jNonnegative jBound, iNonnegative, jNonnegative]
  · by_cases atLeft : vertex = heap.read layout.vertices i
    · subst vertex
      simp [atRight, indexed.forward i iNonnegative iBound, iNonnegative, jNonnegative]
    · simp [atRight, atLeft]

theorem swap_preserves_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (i j : Int) :
    layout.Valid (swapHeap heap layout i j) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem swap_indexed_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (i j : Int) (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) :
    ∃ after, MinHeap.swap.Call heap (queue, i, j) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after = Clocks.single "heap_swaps" 1 := by
  refine ⟨swapHeap heap layout i j, swap_summary heap queue layout valid i j,
    swap_preserves_layout heap queue layout valid i j, ?_, swap_cost heap layout i j⟩
  exact swap_preserves_indexed heap layout i j valid.verticesPositions indexed
    iNonnegative iBound jNonnegative jBound

-- Simple endpoint cases are checked against the compiled methods as well.
theorem pop_empty_summary (heap : Heap) (queue : Ref_MinHeap) (size : Int)
    (valid : is_MinHeap heap queue) (stored : field_MinHeap_size heap queue = some size)
    (empty : size ≤ 0) :
    MinHeap.pop_min.Call heap queue heap (-1) := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [stored]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_true _ _ _ (by simp [stored, empty]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc19 _ _ _)
  exact Reaches.single (Step.MinHeap_pop_min_pc18 _ _ _)

theorem sift_up_root_summary (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    MinHeap.sift_up.Call heap (queue, 0) heap () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_sift_up_pc3_false _ _ _ (by simp))
  apply Reaches.prepend (Step.MinHeap_sift_up_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_sift_up_pc1 _ _ _)

theorem sift_down_leaf_summary (heap : Heap) (queue : Ref_MinHeap) (index size : Int)
    (valid : is_MinHeap heap queue) (stored : field_MinHeap_size heap queue = some size)
    (leaf : size ≤ 2 * index + 1) :
    MinHeap.sift_down.Call heap (queue, index) heap () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [stored]))
  apply Reaches.prepend (Step.MinHeap_sift_down_pc3_false _ _ _ (by simp [stored]; omega))
  apply Reaches.prepend (Step.MinHeap_sift_down_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_sift_down_pc1 _ _ _)

-- The mathematical depth is the prospective logarithmic bound. Each upward
-- move decreases it by exactly one; downward moves increase it by one.
def depth (index : Int) : Nat := (index.toNat + 1).log2

theorem parent_bounds (index : Int) (positive : 0 < index) :
    0 ≤ Int.fdiv (index - 1) 2 ∧ Int.fdiv (index - 1) 2 < index := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem parent_depth (index : Int) (positive : 0 < index) :
    depth (Int.fdiv (index - 1) 2) + 1 = depth index := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have offset : ((index - 1) / 2).toNat + 1 = (index.toNat + 1) / 2 := by omega
  unfold depth
  rw [offset, Nat.log2_def (index.toNat + 1), if_pos (by omega)]

theorem child_depth (index child : Int) (nonnegative : 0 ≤ index)
    (isChild : child = 2 * index + 1 ∨ child = 2 * index + 2) :
    depth child = depth index + 1 := by
  have offset : (child.toNat + 1) / 2 = index.toNat + 1 := by omega
  unfold depth
  rw [Nat.log2_def (child.toNat + 1), if_pos (by omega), offset]

-- Construction keeps its heap effect in source order. Each sequence has a
-- distinct fresh reference, and the empty queue has no present vertices.
def initializedHeap (heap : Heap) (queue : Ref_MinHeap) : Heap :=
  let first := set_MinHeap_vertices (heap.allocate (fun _ => 0)) queue heap.nextRef
  let second := set_MinHeap_positions (first.allocate (fun _ => -1)) queue first.nextRef
  let third := set_MinHeap_keys (second.allocate (fun _ => 0)) queue second.nextRef
  set_MinHeap_size third queue 0

def emptyLayout (heap : Heap) : Layout :=
  ⟨heap.nextRef, heap.nextRef + 1, heap.nextRef + 2, 0⟩

theorem initialized_object (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) : is_MinHeap (initializedHeap heap queue) queue := by
  simpa [initializedHeap, is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions,
    set_MinHeap_keys, set_MinHeap_size] using valid

theorem initialization_summary (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    MinHeap.__init__.Call heap queue (initializedHeap heap queue) () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap___init___pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc14 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc12 _ _ _
    (by simpa [is_MinHeap] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc11 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc9 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc8 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc7 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc5 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc4 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc3 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions,
      set_MinHeap_keys] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc2 _ _ _)
  exact Reaches.single (Step.MinHeap___init___pc1 _ _ _)

def newHeap (heap : Heap) : Heap :=
  initializedHeap (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject

theorem new_heap_summary (heap : Heap) :
    MinHeap.Call heap () (newHeap heap) heap.nextObject := by
  have allocated : is_MinHeap (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject := by
    simp [is_MinHeap]
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc5 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc3 _ _ _)
  apply Reaches.trans ((initialization_summary _ _ allocated).2 _)
  apply Reaches.prepend (Step.MinHeap_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_pc1 _ _ _ (initialized_object _ _ allocated))

theorem initialization_layout (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    (emptyLayout heap).Valid (initializedHeap heap queue) queue := by
  have object := initialized_object heap queue valid
  have present := valid.2
  constructor
  · exact object
  · simp [emptyLayout, initializedHeap, field_MinHeap_vertices, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_positions, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_keys, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_size, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asInt, Nat.add_assoc]
  · change heap.nextRef < heap.nextRef + 3
    omega
  · change heap.nextRef + 1 < heap.nextRef + 3
    omega
  · change heap.nextRef + 2 < heap.nextRef + 3
    omega
  · change heap.nextRef ≠ heap.nextRef + 1
    omega
  · change heap.nextRef ≠ heap.nextRef + 2
    omega
  · change heap.nextRef + 1 ≠ heap.nextRef + 2
    omega

theorem initialized_positions (heap : Heap) (queue : Ref_MinHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).positions vertex = -1 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, set_MinHeap_vertices,
    set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size]

theorem new_heap_layout (heap : Heap) :
    (emptyLayout heap).Valid (newHeap heap) heap.nextObject := by
  exact initialization_layout (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject (by simp [is_MinHeap])

theorem new_heap_positions (heap : Heap) (vertex : Int) :
    (newHeap heap).read (emptyLayout heap).positions vertex = -1 := by
  exact initialized_positions (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject vertex

theorem new_heap_clocks (heap : Heap) : (newHeap heap).clocks = heap.clocks := rfl

@[simp] theorem keys_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_keys (heap.write ref index value) queue = field_MinHeap_keys heap queue := rfl

@[simp] theorem size_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_MinHeap) :
    field_MinHeap_size (heap.write ref index value) queue = field_MinHeap_size heap queue := rfl

def insertedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) : Heap :=
  set_MinHeap_size (((heap.write layout.keys vertex key).write layout.vertices 0 vertex).write
    layout.positions vertex 0) queue 1

theorem insert_empty_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (empty : layout.size = 0) (vertex key : Int)
    (absent : heap.read layout.positions vertex < 0) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key)
      (insertedHeap heap queue layout vertex key) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_true _ _ _
    (by simp [valid.readPositions, absent]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc14 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc13 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc12 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc11 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc9 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc7 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc5 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_size] using! valid.object))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc3 _ _ _)
  simp only [vertices_write, positions_write, size_write,
    valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    Option.getD_some, empty, Int.zero_add]
  apply Reaches.trans ((sift_up_root_summary _ _
    (by simpa [is_MinHeap, set_MinHeap_size] using! valid.object)).2 _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

theorem inserted_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    { layout with size := 1 }.Valid (insertedHeap heap queue layout vertex key) queue := by
  constructor
  · simpa [insertedHeap, is_MinHeap, set_MinHeap_size] using! valid.object
  · simpa [insertedHeap, field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using! valid.readVertices
  · simpa [insertedHeap, field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using! valid.readPositions
  · simpa [insertedHeap, field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using! valid.readKeys
  · exact field_MinHeap_size_set _ _ _ valid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem inserted_vertex (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (insertedHeap heap queue layout vertex key).read layout.vertices 0 = vertex := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write, separate]

theorem inserted_position (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) :
    (insertedHeap heap queue layout vertex key).read layout.positions vertex = 0 := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write]

theorem inserted_key (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (insertedHeap heap queue layout vertex key).read layout.keys vertex = key := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm separateVertices, Ne.symm separatePositions]

theorem inserted_clocks (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) :
    (insertedHeap heap queue layout vertex key).clocks = heap.clocks := rfl

def poppedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Heap :=
  (set_MinHeap_size (swapHeap heap layout 0 0) queue 0).write
    layout.positions (heap.read layout.vertices 0) (-1)

theorem pop_singleton_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (singleton : layout.size = 1) :
    MinHeap.pop_min.Call heap queue (poppedHeap heap queue layout)
      (heap.read layout.vertices 0) := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 0
  have positions : field_MinHeap_positions
      (set_MinHeap_size (swapHeap heap layout 0 0) queue 0) queue = some layout.positions := by
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_false _ _ _ (by simp [valid.readSize, singleton]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc17 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc16 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc14 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc12 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc11 _ _ _)
  simp only [valid.readSize, valid.readVertices, Option.getD_some, singleton, Int.sub_self]
  apply Reaches.trans ((swap_summary heap queue layout valid 0 0).2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc10 _ _ _ swappedValid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc9 _ _ _
    (by simpa [positions] using! swappedValid.positionsAllocated))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc7_false _ _ _ (by simp))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc2 _ _ _)
  simp only [positions, Option.getD_some]
  exact Reaches.single (Step.MinHeap_pop_min_pc1 _ _ _)

theorem popped_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    { layout with size := 0 }.Valid (poppedHeap heap queue layout) queue := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 0
  constructor
  · change is_MinHeap (set_MinHeap_size (swapHeap heap layout 0 0) queue 0) queue
    simpa [is_MinHeap, set_MinHeap_size] using swappedValid.object
  · simp only [poppedHeap, vertices_write]
    simpa [field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using swappedValid.readVertices
  · simp only [poppedHeap, positions_write]
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  · simp only [poppedHeap, keys_write]
    simpa [field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using swappedValid.readKeys
  · simpa [poppedHeap] using field_MinHeap_size_set _ _ 0 swappedValid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem popped_position (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) :
    (poppedHeap heap queue layout).read layout.positions (heap.read layout.vertices 0) = -1 := by
  simp [poppedHeap]

theorem popped_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (poppedHeap heap queue layout).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [poppedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm separateVertices, Ne.symm separatePositions]

theorem popped_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (poppedHeap heap queue layout).read layout.vertices index = heap.read layout.vertices index := by
  simp [poppedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write, separate]
  split <;> simp_all

theorem popped_cost (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) :
    Heap.cost heap (poppedHeap heap queue layout) = Clocks.single "heap_swaps" 1 := by
  exact swap_cost heap layout 0 0

-- Client-owned arrays, such as Dijkstra's distances and settled flags, are
-- unchanged by creating and manipulating this separate priority queue.
theorem new_heap_read_old (heap : Heap) (ref : SeqRef) (index : Int)
    (allocated : ref < heap.nextRef) :
    (newHeap heap).read ref index = heap.read ref index := by
  have first : ref ≠ heap.nextRef := Nat.ne_of_lt allocated
  have second : ref ≠ heap.nextRef + 1 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))
  have third : ref ≠ heap.nextRef + 2 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))
  simp [newHeap, initializedHeap, set_MinHeap_vertices, set_MinHeap_positions,
    set_MinHeap_keys, set_MinHeap_size, Heap.read, Heap.allocate, Heap.allocateObject,
    first, second, third, Nat.add_assoc]

theorem inserted_read_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (vertex key : Int) (ref : SeqRef) (index : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions)
    (notKeys : ref ≠ layout.keys) :
    (insertedHeap heap queue layout vertex key).read ref index = heap.read ref index := by
  simp [insertedHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions, notKeys]

theorem popped_read_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (ref : SeqRef) (index : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions) :
    (poppedHeap heap queue layout).read ref index = heap.read ref index := by
  simp [poppedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions]

/-- The parent of a positive position in the zero-based binary heap. -/
def parent (index : Int) : Int := Int.fdiv (index - 1) 2

/-- Heap order concerns only the finite active prefix; priorities are arbitrary integers. -/
def Ordered (priority : Seq) (size : Int) : Prop :=
  ∀ child, 0 < child → child < size → priority (parent child) ≤ priority child

/-- Local parent comparisons imply that the root is a minimum of the active heap. -/
theorem Ordered.root_minimum {priority : Seq} {size : Int} (ordered : Ordered priority size)
    (index : Int) (nonnegative : 0 ≤ index) (within : index < size) :
    priority 0 ≤ priority index := by
  have result : ∀ n : Nat, (n : Int) < size → priority 0 ≤ priority (n : Int) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro bound
      by_cases zero : n = 0
      · subst n; exact Int.le_refl _
      · have positive : 0 < (n : Int) := by omega
        have bounds := parent_bounds (n : Int) positive
        have smaller : (parent (n : Int)).toNat < n := by
          unfold parent
          omega
        have parentBound : ((parent (n : Int)).toNat : Int) < size := by
          unfold parent
          omega
        have previous := ih _ smaller parentBound
        have parentCast : ((parent (n : Int)).toNat : Int) = parent (n : Int) :=
          Int.toNat_of_nonneg bounds.1
        rw [parentCast] at previous
        exact Int.le_trans previous (ordered _ positive bound)
  simpa [Int.toNat_of_nonneg nonnegative] using result index.toNat (by omega)

/-- At sift-up's moving position only its incoming edge may violate heap order.
    Its parent is also below its children, so exchanging parent and child is safe. -/
structure UpInvariant (priority : Seq) (size index : Int) : Prop where
  orderedExcept : ∀ child, 0 < child → child < size → child ≠ index →
    priority (parent child) ≤ priority child
  parentBelowChildren : ∀ child, 0 < child → child < size → parent child = index →
    0 < index → priority (parent index) ≤ priority child

/-- Once the exceptional edge is ordered (or the root is reached), sift-up is done. -/
theorem UpInvariant.finish {priority : Seq} {size index : Int}
    (invariant : UpInvariant priority size index)
    (done : index ≤ 0 ∨ priority (parent index) ≤ priority index) :
    Ordered priority size := by
  intro child positive bound
  by_cases same : child = index
  · subst child
    rcases done with nonpositive | ordered
    · omega
    · exact ordered
  · exact invariant.orderedExcept child positive bound same

/-- Exchanging an out-of-order position with its parent moves the single
    exceptional edge up one level; every other heap-order edge stays valid. -/
theorem UpInvariant.exchange_parent {priority : Seq} {size index : Int}
    (invariant : UpInvariant priority size index)
    (positive : 0 < index) (within : index < size)
    (outOfOrder : priority index < priority (parent index)) :
    UpInvariant (exchange priority index (parent index)) size (parent index) := by
  have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index positive
  have different : index ≠ parent index := by omega
  constructor
  · intro child childPositive childBound notParent
    by_cases atIndex : child = index
    · subst child
      rw [exchange_right, exchange_left]
      exact Int.le_of_lt outOfOrder
    · by_cases fromIndex : parent child = index
      · have below := invariant.parentBelowChildren child childPositive childBound fromIndex positive
        simpa [exchange, fromIndex, atIndex, notParent, different, Ne.symm different] using below
      · by_cases fromParent : parent child = parent index
        · have old := invariant.orderedExcept child childPositive childBound atIndex
          rw [fromParent] at old
          simpa [exchange, fromParent, atIndex, notParent] using
            Int.le_trans (Int.le_of_lt outOfOrder) old
        · simpa [exchange, fromIndex, fromParent, atIndex, notParent] using
            invariant.orderedExcept child childPositive childBound atIndex
  · intro child childPositive childBound fromParent parentPositive
    have ancestorBounds : 0 ≤ parent (parent index) ∧ parent (parent index) < parent index :=
      parent_bounds (parent index) parentPositive
    have ancestorNotParent : parent (parent index) ≠ parent index := by omega
    have ancestorNotIndex : parent (parent index) ≠ index := by omega
    have childBounds : parent child < child := (parent_bounds child childPositive).2
    have notParent : child ≠ parent index := by omega
    have oldParent := invariant.orderedExcept (parent index) parentPositive (by omega) (by omega)
    by_cases atIndex : child = index
    · subst child
      simpa [exchange, ancestorNotParent, ancestorNotIndex, different] using oldParent
    · have oldChild := invariant.orderedExcept child childPositive childBound atIndex
      rw [fromParent] at oldChild
      simpa [exchange, ancestorNotParent, ancestorNotIndex, notParent, atIndex] using
        Int.le_trans oldParent oldChild

/-- Lowering one priority is precisely the precondition that sift-up repairs. -/
theorem Ordered.decrease {priority : Seq} {size index key : Int}
    (ordered : Ordered priority size) (within : index < size)
    (lower : key ≤ priority index) :
    UpInvariant (fun position => if position = index then key else priority position) size index := by
  constructor
  · intro child positive bound different
    by_cases parentSame : parent child = index
    · have old := ordered child positive bound
      rw [parentSame] at old
      simpa [parentSame, different] using Int.le_trans lower old
    · simpa [parentSame, different] using ordered child positive bound
  · intro child positive bound fromIndex indexPositive
    have parentDifferent : parent index ≠ index := by
      have : parent index < index := (parent_bounds index indexPositive).2
      omega
    have childDifferent : child ≠ index := by
      have : parent child < child := (parent_bounds child positive).2
      omega
    have first := ordered index indexPositive within
    have second := ordered child positive bound
    rw [fromIndex] at second
    simpa [parentDifferent, childDifferent] using Int.le_trans first second

/-- The abstract priority exchange is exactly the effect of the compiled swap. -/
theorem swap_priorities (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (fun position => (swapHeap heap layout i j).read layout.keys
      ((swapHeap heap layout i j).read layout.vertices position)) =
    exchange (fun position => heap.read layout.keys (heap.read layout.vertices position)) i j := by
  funext position
  rw [swap_keys heap layout i j _ separateVertices separatePositions,
    swap_vertices heap layout i j position separate]
  simp only [exchange]
  split <;> simp_all
  split <;> simp_all

/-- A representation-level minimum statement, ready for an extraction contract. -/
theorem root_minimum_vertex (heap : Heap) (layout : Layout)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun position => heap.read layout.keys (heap.read layout.vertices position))
      layout.size)
    (vertex : Int) (present : 0 ≤ heap.read layout.positions vertex) :
    heap.read layout.keys (heap.read layout.vertices 0) ≤ heap.read layout.keys vertex := by
  obtain ⟨bound, identity⟩ := indexed.backward vertex present
  have minimum := ordered.root_minimum (heap.read layout.positions vertex) present bound
  simpa [identity] using minimum

/-- Appending an absent vertex updates both directions of the position map. -/
theorem Indexed.insert {vertices positions : Seq} {size vertex : Int}
    (indexed : Indexed vertices positions size) (nonnegative : 0 ≤ size)
    (absent : positions vertex = -1) :
    Indexed (fun index => if index = size then vertex else vertices index)
      (fun value => if value = vertex then size else positions value) (size + 1) := by
  constructor
  · intro index lower upper
    by_cases last : index = size
    · subst index; simp
    · have oldBound : index < size := by omega
      have different : vertices index ≠ vertex := by
        intro same
        have old := indexed.forward index lower oldBound
        rw [same, absent] at old
        omega
      simpa [last, different] using indexed.forward index lower oldBound
  · intro value present
    by_cases same : value = vertex
    · subst value; simp; omega
    · simp only [same, ite_false] at present ⊢
      obtain ⟨bound, identity⟩ := indexed.backward value present
      have different : positions value ≠ size := by omega
      exact ⟨by omega, by simp [different, identity]⟩
  · intro value negative
    by_cases same : value = vertex
    · subst value
      simp only [ite_true] at negative
      omega
    · simpa [same] using indexed.absent value (by simpa [same] using negative)

/-- Adding a leaf preserves all order edges except the new leaf's parent edge. -/
theorem Ordered.append {priority : Seq} {size key : Int}
    (ordered : Ordered priority size) :
    UpInvariant (fun index => if index = size then key else priority index) (size + 1) size := by
  constructor
  · intro child positive bound different
    have oldBound : child < size := by omega
    have parentBound : parent child < child := (parent_bounds child positive).2
    have parentDifferent : parent child ≠ size := by omega
    simpa [different, parentDifferent] using ordered child positive oldBound
  · intro child positive bound fromLast lastPositive
    have parentBound : parent child < child := (parent_bounds child positive).2
    omega

-- The loop proof is expressed through the named source location and its two
-- live inputs. Other temporary locals are irrelevant to the specification.
def AtSiftUp (state : Configuration) (queue : Ref_MinHeap) (index : Int) : Prop :=
  MinHeap.sift_up.At.up_loop state ∧
    MinHeap.sift_up.Local.self state = some queue ∧
    MinHeap.sift_up.Local.i state = some index

@[simp] theorem keys_tick (heap : Heap) (name : String) (amount : Nat) (queue : Ref_MinHeap) :
    field_MinHeap_keys (heap.tick name amount) queue = field_MinHeap_keys heap queue := rfl

@[simp] theorem vertices_tick (heap : Heap) (name : String) (amount : Nat) (queue : Ref_MinHeap) :
    field_MinHeap_vertices (heap.tick name amount) queue = field_MinHeap_vertices heap queue := rfl

theorem sift_up_stop (state : Configuration) (queue : Ref_MinHeap) (index : Int)
    (location : AtSiftUp state queue index) (atRoot : index ≤ 0) :
    MinHeap.sift_up.CallFrom state state.heap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_false _ _ _
      (by simp only [decide_eq_false_iff_not]; omega))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc2 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_up_pc1 _ _ _)

theorem sift_up_ordered (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (location : AtSiftUp state queue index)
    (valid : layout.Valid state.heap queue) (positive : 0 < index)
    (ordered : state.heap.read layout.keys (state.heap.read layout.vertices
        (Int.fdiv (index - 1) 2)) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices index)) :
    MinHeap.sift_up.CallFrom state (state.heap.tick "heap_comparisons") () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    change heap.read layout.keys (heap.read layout.vertices (Int.fdiv (s.v1 - 1) 2)) ≤
      heap.read layout.keys (heap.read layout.vertices s.v1) at ordered
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_true _ _ _ (by simp [positive]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc16 _ _ _ (by decide))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc13_true _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using ordered))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc12 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_up_pc11 _ _ _)

theorem Layout.Valid.tick {layout : Layout} {heap : Heap} {queue : Ref_MinHeap}
    (valid : layout.Valid heap queue) (name : String) (amount : Nat := 1) :
    layout.Valid (heap.tick name amount) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

def upHeap (heap : Heap) (layout : Layout) (index : Int) : Heap :=
  swapHeap (heap.tick "heap_comparisons") layout index (Int.fdiv (index - 1) 2)

theorem upHeap_priorities (heap : Heap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (fun position => (upHeap heap layout index).read layout.keys
      ((upHeap heap layout index).read layout.vertices position)) =
      exchange (fun position => heap.read layout.keys (heap.read layout.vertices position))
        index (parent index) := by
  simpa [upHeap, parent] using swap_priorities (heap.tick "heap_comparisons") layout
    index (parent index) separate separateVertices separatePositions

theorem upHeap_read_other (heap : Heap) (layout : Layout) (index : Int)
    (ref : SeqRef) (position : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions) :
    (upHeap heap layout index).read ref position = heap.read ref position := by
  simp [upHeap, swapHeap, Heap.read, Heap.write, notVertices, notPositions]

-- One unsuccessful comparison swaps with the parent and returns to the named
-- loop location. Any proof for the remaining loop can be plugged in here.
theorem sift_up_continue (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (finalHeap : Heap) (location : AtSiftUp state queue index)
    (valid : layout.Valid state.heap queue) (positive : 0 < index)
    (unordered : ¬ state.heap.read layout.keys (state.heap.read layout.vertices
        (Int.fdiv (index - 1) 2)) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices index))
    (remaining : ∀ nextState, AtSiftUp nextState queue (Int.fdiv (index - 1) 2) →
      nextState.heap = upHeap state.heap layout index →
      MinHeap.sift_up.CallFrom nextState finalHeap ()) :
    MinHeap.sift_up.CallFrom state finalHeap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    change ¬ heap.read layout.keys (heap.read layout.vertices (Int.fdiv (s.v1 - 1) 2)) ≤
      heap.read layout.keys (heap.read layout.vertices s.v1) at unordered
    let parent := Int.fdiv (s.v1 - 1) 2
    let nextState : Configuration := .active (upHeap heap layout s.v1)
      (.fn_MinHeap_sift_up 4 { s with
        v1 := parent
        v2 := parent
        t4 := decide (s.v1 > 0)
        t5 := ()
        t6 := s.v0
        t7 := s.v1
        t8 := parent
        t9 := decide (heap.read layout.keys (heap.read layout.vertices parent) ≤
          heap.read layout.keys (heap.read layout.vertices s.v1)) }) originalStack
    have finish := remaining nextState ⟨True.intro, rfl, rfl⟩ rfl
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_true _ _ _ (by simp [positive]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc16 _ _ _ (by decide))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc13_false _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using unordered))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc10 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc9 _ _ _ valid.object)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc8 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc7 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc6 _ _ _)
    apply Reaches.trans ((swap_summary (heap.tick "heap_comparisons") s.v0 layout
      (valid.tick "heap_comparisons") s.v1 parent).2 _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc5 _ _ _)
    simpa only [keys_tick, vertices_tick, valid.readKeys, valid.readVertices,
      Option.getD_some, Heap.read_tick] using! finish stack

-- Reordering the integer arrays leaves object fields, typed collections, and
-- all allocation counters unchanged. In particular, graph objects in a caller
-- remain available with their original fields after either sifting method.
structure OtherStoragePreserved (before after : Heap) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections

theorem OtherStoragePreserved.refl (heap : Heap) : OtherStoragePreserved heap heap :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem OtherStoragePreserved.trans {first second third : Heap}
    (initial : OtherStoragePreserved first second)
    (remaining : OtherStoragePreserved second third) : OtherStoragePreserved first third :=
  ⟨remaining.nextRef.trans initial.nextRef, remaining.nextObject.trans initial.nextObject,
    remaining.objects.trans initial.objects, remaining.nextCollection.trans initial.nextCollection,
    remaining.collections.trans initial.collections⟩

-- The remaining loop has one final heap for every configuration with these
-- source inputs. Induction follows tree depth, not the transcript length.
theorem sift_up_loop (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after,
      (∀ state, AtSiftUp state queue index → state.heap = heap →
        MinHeap.sift_up.CallFrom state after ()) ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      after.clocks "heap_comparisons" ≤ heap.clocks "heap_comparisons" + depth index ∧
      after.clocks "heap_swaps" ≤ heap.clocks "heap_swaps" + depth index ∧
      (UpInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  generalize rankEq : depth index = rank
  induction rank using Nat.strongRecOn generalizing heap index with
  | ind rank inductionHypothesis =>
    by_cases positive : 0 < index
    · have parentFacts := parent_bounds index positive
      have depthChange := parent_depth index positive
      by_cases ordered : heap.read layout.keys
          (heap.read layout.vertices (Int.fdiv (index - 1) 2)) ≤
          heap.read layout.keys (heap.read layout.vertices index)
      · refine ⟨heap.tick "heap_comparisons", ?_, valid.tick "heap_comparisons", indexed,
          ?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · intro state location sameHeap
          have validState : layout.Valid state.heap queue := by simpa [sameHeap] using valid
          have orderedState : state.heap.read layout.keys
              (state.heap.read layout.vertices (Int.fdiv (index - 1) 2)) ≤
              state.heap.read layout.keys (state.heap.read layout.vertices index) := by
            simpa [sameHeap] using ordered
          simpa [sameHeap] using sift_up_ordered state queue layout index location
            validState positive orderedState
        · simp only [Heap.clocks_tick_same]
          omega
        · simp [Heap.tick]
        · intro invariant
          exact invariant.finish (Or.inr ordered)
        · intro ref _ _ position
          exact Heap.read_tick heap "heap_comparisons" 1 ref position
        · intro vertex
          rfl
        · intro name notComparisons _
          exact Heap.clocks_tick_other heap "heap_comparisons" name notComparisons
      · let nextHeap := upHeap heap layout index
        have nextValid : layout.Valid nextHeap queue :=
          swap_preserves_layout (heap.tick "heap_comparisons") queue layout
            (valid.tick "heap_comparisons") index (Int.fdiv (index - 1) 2)
        have nextIndexed : Indexed (nextHeap.read layout.vertices)
            (nextHeap.read layout.positions) layout.size :=
          swap_preserves_indexed (heap.tick "heap_comparisons") layout index
            (Int.fdiv (index - 1) 2) valid.verticesPositions indexed
            nonnegative bound parentFacts.1 (by omega)
        obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
            unchanged, presentIff, otherClocks, storage⟩ :=
          inductionHypothesis (depth (Int.fdiv (index - 1) 2)) (by omega)
            nextHeap (Int.fdiv (index - 1) 2) nextValid nextIndexed parentFacts.1 (by omega) rfl
        refine ⟨after, ?_, afterValid, afterIndexed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro state location sameHeap
          apply sift_up_continue state queue layout index after location
            (by simpa [sameHeap] using valid) positive (by simpa [sameHeap] using ordered)
          intro nextState nextLocation nextHeapEq
          apply remaining nextState nextLocation
          simpa [sameHeap, nextHeap] using nextHeapEq
        · simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write] at comparisons
          omega
        · simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write] at swaps
          omega
        · intro invariant
          apply repair
          change UpInvariant (fun position => (upHeap heap layout index).read layout.keys
            ((upHeap heap layout index).read layout.vertices position)) layout.size (parent index)
          rw [upHeap_priorities heap layout index valid.verticesPositions valid.verticesKeys valid.positionsKeys]
          exact invariant.exchange_parent positive bound (by unfold parent; omega)
        · intro ref notVertices notPositions position
          rw [unchanged ref notVertices notPositions position]
          exact upHeap_read_other heap layout index ref position notVertices notPositions
        · intro vertex
          rw [presentIff vertex]
          exact swap_preserves_membership (heap.tick "heap_comparisons") layout index
            (Int.fdiv (index - 1) 2) valid.verticesPositions indexed nonnegative bound
            parentFacts.1 (by omega) vertex
        · intro name notComparisons notSwaps
          rw [otherClocks name notComparisons notSwaps]
          simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write, notComparisons, notSwaps]
        · exact (show OtherStoragePreserved heap nextHeap from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage
    · refine ⟨heap, ?_, valid, indexed, Nat.le_add_right _ _, Nat.le_add_right _ _,
        ?_, ?_, ?_, ?_, OtherStoragePreserved.refl heap⟩
      · intro state location sameHeap
        simpa [sameHeap] using sift_up_stop state queue index location (by omega)
      · intro invariant
        exact invariant.finish (Or.inl (by omega))
      · intro ref _ _ position
        rfl
      · intro vertex
        rfl
      · intro name _ _
        rfl

-- A valid active index always terminates. The map invariant is preserved, and
-- each of the two instrumented operation counts is at most floor(log2(i+1)).
-- Sift-up repairs its expected single-edge order exception. Keys and client
-- arrays are preserved because only the vertices and positions arrays change.
theorem sift_up_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after, MinHeap.sift_up.Call heap (queue, index) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after "heap_comparisons" ≤ depth index ∧
      Heap.cost heap after "heap_swaps" ≤ depth index ∧
      (UpInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
      unchanged, presentIff, otherClocks, storage⟩ :=
    sift_up_loop heap queue layout index valid indexed nonnegative bound
  refine ⟨after, ⟨valid.object, ?_⟩, afterValid, afterIndexed, ?_, ?_, repair,
    unchanged, presentIff, otherClocks, storage⟩
  · exact remaining (MinHeap.sift_up.initial heap (queue, index)) ⟨True.intro, rfl, rfl⟩ rfl
  · unfold Heap.cost
    omega
  · unfold Heap.cost
    omega

/-- A non-improving key leaves queue data unchanged and charges one comparison. -/
theorem push_unchanged_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (unchanged : heap.read layout.keys vertex ≤ key) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key)
      (heap.tick "heap_comparisons") () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_false _ _ _
    (by simp [valid.readPositions]; omega))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc22 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc21 _ _ _
    (by change (field_MinHeap_keys heap queue).isSome = true ∧
          (field_MinHeap_keys heap queue).getD 0 < heap.nextRef
        simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc20_false _ _ _
    (by change decide (key < (heap.tick "heap_comparisons").read
          ((field_MinHeap_keys (heap.tick "heap_comparisons") queue).getD 0) vertex) = false
        change decide (key < heap.read ((field_MinHeap_keys heap queue).getD 0) vertex) = false
        simp [valid.readKeys]; omega))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

/-- The heap seen by sift-up after an existing key is lowered. -/
def decreasedHeap (heap : Heap) (layout : Layout) (vertex key : Int) : Heap :=
  (heap.tick "heap_comparisons").write layout.keys vertex key

/-- The caller composes a sift-up contract without inspecting sift-up's transitions. -/
theorem decrease_summary (heap finalHeap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (improves : key < heap.read layout.keys vertex)
    (sift : MinHeap.sift_up.Call (decreasedHeap heap layout vertex key)
      (queue, heap.read layout.positions vertex) finalHeap ()) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key) finalHeap () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_false _ _ _
    (by simp [valid.readPositions]; omega))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc22 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc21 _ _ _
    (by change (field_MinHeap_keys heap queue).isSome = true ∧
          (field_MinHeap_keys heap queue).getD 0 < heap.nextRef
        simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc20_true _ _ _
    (by change decide (key < heap.read ((field_MinHeap_keys heap queue).getD 0) vertex) = true
        simp [valid.readKeys, improves]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc19 _ _ _
    (by change (field_MinHeap_keys heap queue).isSome = true ∧
          (field_MinHeap_keys heap queue).getD 0 < heap.nextRef
        simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc18 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc17 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc16 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc15 _ _ _)
  change Reaches Step
    (.active ((heap.tick "heap_comparisons").write
        ((field_MinHeap_keys heap queue).getD 0) vertex key)
      (.fn_MinHeap_sift_up 4 { v0 := queue, v1 := heap.read ((field_MinHeap_positions heap queue).getD 0) vertex }) _) _
  simp only [valid.readKeys, valid.readPositions, Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

/-- Preparing an absent vertex at the new last position, before sift-up. -/
def appendedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex key : Int) : Heap :=
  set_MinHeap_size (((heap.write layout.keys vertex key).write layout.vertices layout.size vertex).write
    layout.positions vertex layout.size) queue (layout.size + 1)

/-- Insertion itself is a few writes, followed by a reusable sift-up summary. -/
theorem append_summary (heap finalHeap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (absent : heap.read layout.positions vertex < 0)
    (sift : MinHeap.sift_up.Call (appendedHeap heap queue layout vertex key)
      (queue, layout.size) finalHeap ()) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key) finalHeap () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_true _ _ _
    (by simp [valid.readPositions, absent]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc14 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc13 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc12 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc11 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc9 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc7 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc5 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_size] using! valid.object))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc3 _ _ _)
  simp only [vertices_write, positions_write, size_write,
    valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)

/-- Array writes preserve the object's fields, reference bounds, and separation. -/
theorem Layout.Valid.write {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (valid : layout.Valid heap queue) (ref : SeqRef) (index value : Int) :
    layout.Valid (heap.write ref index value) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩

theorem appended_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    { layout with size := layout.size + 1 }.Valid (appendedHeap heap queue layout vertex key) queue := by
  constructor
  · simpa [appendedHeap, is_MinHeap, set_MinHeap_size] using! valid.object
  · simpa [appendedHeap, field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using! valid.readVertices
  · simpa [appendedHeap, field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using! valid.readPositions
  · simpa [appendedHeap, field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using! valid.readKeys
  · exact field_MinHeap_size_set _ _ _ valid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem appended_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key index : Int) :
    (appendedHeap heap queue layout vertex key).read layout.vertices index =
      if index = layout.size then vertex else heap.read layout.vertices index := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    valid.verticesPositions, valid.verticesKeys]

theorem appended_positions (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key value : Int) :
    (appendedHeap heap queue layout vertex key).read layout.positions value =
      if value = vertex then layout.size else heap.read layout.positions value := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm valid.verticesPositions, valid.positionsKeys]

theorem appended_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key value : Int) :
    (appendedHeap heap queue layout vertex key).read layout.keys value =
      if value = vertex then key else heap.read layout.keys value := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm valid.verticesKeys, Ne.symm valid.positionsKeys]

theorem appended_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ layout.size) (vertex key : Int)
    (absent : heap.read layout.positions vertex = -1) :
    Indexed ((appendedHeap heap queue layout vertex key).read layout.vertices)
      ((appendedHeap heap queue layout vertex key).read layout.positions) (layout.size + 1) := by
  have vertices : (appendedHeap heap queue layout vertex key).read layout.vertices =
      (fun index => if index = layout.size then vertex else heap.read layout.vertices index) :=
    funext (appended_vertices heap queue layout valid vertex key)
  have positions : (appendedHeap heap queue layout vertex key).read layout.positions =
      (fun value => if value = vertex then layout.size else heap.read layout.positions value) :=
    funext (appended_positions heap queue layout valid vertex key)
  rw [vertices, positions]
  exact indexed.insert nonnegative absent

/-- Order predicates only inspect active positions; infinite sequence tails do not matter. -/
theorem Ordered.congr {first second : Seq} {size : Int} (ordered : Ordered first size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    Ordered second size := by
  intro child positive bound
  have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
  rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
  exact ordered child positive bound

theorem UpInvariant.congr {first second : Seq} {size index : Int}
    (invariant : UpInvariant first size index)
    (within : index < size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    UpInvariant second size index := by
  constructor
  · intro child positive bound different
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
    exact invariant.orderedExcept child positive bound different
  · intro child positive bound fromIndex indexPositive
    have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index indexPositive
    rw [← same child (by omega) bound, ← same (parent index) bounds.1 (by omega)]
    exact invariant.parentBelowChildren child positive bound fromIndex indexPositive

/-- Appending an absent vertex creates exactly the local disorder that sift-up repairs. -/
theorem appended_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (vertex key : Int) (absent : heap.read layout.positions vertex = -1) :
    UpInvariant (fun index => (appendedHeap heap queue layout vertex key).read layout.keys
      ((appendedHeap heap queue layout vertex key).read layout.vertices index)) (layout.size + 1) layout.size := by
  apply (ordered.append (key := key)).congr (by omega)
  intro index lower upper
  rw [appended_keys heap queue layout valid, appended_vertices heap queue layout valid]
  by_cases last : index = layout.size
  · simp [last]
  · have oldBound : index < layout.size := by omega
    have different : heap.read layout.vertices index ≠ vertex := by
      intro same
      have old := indexed.forward index lower oldBound
      rw [same, absent] at old
      omega
    simp [last, different]

/-- Lowering a present vertex leaves the position map intact. -/
theorem decreased_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (vertex key : Int) :
    Indexed ((decreasedHeap heap layout vertex key).read layout.vertices)
      ((decreasedHeap heap layout vertex key).read layout.positions) layout.size := by
  have vertices : (decreasedHeap heap layout vertex key).read layout.vertices =
      heap.read layout.vertices := by
    funext index
    simp [decreasedHeap, valid.verticesKeys]
  have positions : (decreasedHeap heap layout vertex key).read layout.positions =
      heap.read layout.positions := by
    funext value
    simp [decreasedHeap, valid.positionsKeys]
  rw [vertices, positions]
  exact indexed

/-- The array-backed decrease changes the priority at just the vertex's active position. -/
theorem decreased_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (vertex key : Int) (present : 0 ≤ heap.read layout.positions vertex)
    (lower : key ≤ heap.read layout.keys vertex) :
    UpInvariant (fun index => (decreasedHeap heap layout vertex key).read layout.keys
      ((decreasedHeap heap layout vertex key).read layout.vertices index))
      layout.size (heap.read layout.positions vertex) := by
  obtain ⟨bound, identity⟩ := indexed.backward vertex present
  have lowerAtIndex : key ≤ heap.read layout.keys
      (heap.read layout.vertices (heap.read layout.positions vertex)) := by simpa [identity] using lower
  apply (ordered.decrease bound lowerAtIndex).congr bound
  intro index nonnegative within
  have vertices : (decreasedHeap heap layout vertex key).read layout.vertices index =
      heap.read layout.vertices index := by
    simp [decreasedHeap, Heap.read, Heap.write, valid.verticesKeys]
  rw [vertices]
  by_cases same : index = heap.read layout.positions vertex
  · subst index
    simp [decreasedHeap, identity]
  · have different : heap.read layout.vertices index ≠ vertex := by
      intro equal
      have old := indexed.forward index nonnegative within
      rw [equal] at old
      omega
    simp [decreasedHeap, same, different]

/-- A usable priority queue combines storage validity, inverse positions, and
    heap order. Clients need no program counters or transcript representation. -/
structure QueueRep (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Prop where
  valid : layout.Valid heap queue
  nonnegative : 0 ≤ layout.size
  indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size
  ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size

/-- Every constructor call supplies a valid empty priority queue. -/
theorem new_heap_rep (heap : Heap) :
    QueueRep (newHeap heap) heap.nextObject (emptyLayout heap) := by
  refine ⟨new_heap_layout heap, by simp [emptyLayout], ?_, ?_⟩
  · constructor
    · intro index lower upper
      change index < 0 at upper
      omega
    · intro vertex present
      rw [new_heap_positions] at present
      omega
    · intro vertex _
      exact new_heap_positions heap vertex
  · intro child positive upper
    change child < 0 at upper
    omega

/-- Insert one absent vertex, restore heap order, and pay at most one comparison
    and swap per parent level. No other vertex enters or leaves the queue. -/
theorem insert_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (absent : heap.read layout.positions vertex = -1) :
    ∃ after, MinHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue { layout with size := layout.size + 1 } ∧
      (∀ value, 0 ≤ after.read layout.positions value ↔
        value = vertex ∨ 0 ≤ heap.read layout.positions value) ∧
      (∀ value, after.read layout.keys value =
        if value = vertex then key else heap.read layout.keys value) ∧
      Heap.cost heap after "heap_comparisons" ≤ depth layout.size ∧
      Heap.cost heap after "heap_swaps" ≤ depth layout.size ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
        ∀ index, after.read ref index = heap.read ref index) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved (set_MinHeap_size heap queue (layout.size + 1)) after := by
  have sizeNonnegative := representation.nonnegative
  let prepared := appendedHeap heap queue layout vertex key
  let enlarged := { layout with size := layout.size + 1 }
  have valid : enlarged.Valid prepared queue :=
    appended_layout heap queue layout representation.valid vertex key
  have indexed : Indexed (prepared.read layout.vertices) (prepared.read layout.positions) enlarged.size :=
    appended_indexed heap queue layout representation.valid representation.indexed
      representation.nonnegative vertex key absent
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_up_summary prepared queue enlarged layout.size valid indexed representation.nonnegative (by dsimp [enlarged]; omega)
  refine ⟨after, append_summary heap after queue layout representation.valid vertex key (by omega) sift,
    ⟨afterValid, by dsimp [enlarged]; omega, afterIndexed, ?_⟩, ?_, ?_, comparisons, swaps, ?_, ?_, ?_⟩
  · exact repair (appended_order heap queue layout representation.valid representation.indexed
      representation.ordered vertex key absent)
  · intro value
    rw [membership value]
    change 0 ≤ (appendedHeap heap queue layout vertex key).read layout.positions value ↔ _
    rw [appended_positions heap queue layout representation.valid]
    by_cases same : value = vertex <;> simp [same, representation.nonnegative]
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    exact appended_keys heap queue layout representation.valid vertex key value
  · intro ref notVertices notPositions notKeys index
    rw [unchanged ref notVertices notPositions index]
    simp [prepared, appendedHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions, notKeys]
  · exact clocks
  · exact (show OtherStoragePreserved (set_MinHeap_size heap queue (layout.size + 1)) prepared
      from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage

/-- Lower one present key, preserving membership and size, and restore order.
    The first comparison tests improvement; remaining work is logarithmic. -/
theorem decrease_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (improves : key < heap.read layout.keys vertex) :
    ∃ after, MinHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue layout ∧
      (∀ value, 0 ≤ after.read layout.positions value ↔ 0 ≤ heap.read layout.positions value) ∧
      (∀ value, after.read layout.keys value =
        if value = vertex then key else heap.read layout.keys value) ∧
      Heap.cost heap after "heap_comparisons" ≤ depth (heap.read layout.positions vertex) + 1 ∧
      Heap.cost heap after "heap_swaps" ≤ depth (heap.read layout.positions vertex) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
        ∀ index, after.read ref index = heap.read ref index) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  let prepared := decreasedHeap heap layout vertex key
  have valid : layout.Valid prepared queue :=
    (representation.valid.tick "heap_comparisons").write layout.keys vertex key
  have indexed := decreased_indexed heap queue layout representation.valid representation.indexed vertex key
  have bound := (representation.indexed.backward vertex present).1
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_up_summary prepared queue layout (heap.read layout.positions vertex) valid indexed present bound
  refine ⟨after, decrease_summary heap after queue layout representation.valid vertex key present improves sift,
    ⟨afterValid, representation.nonnegative, afterIndexed, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact repair (decreased_order heap queue layout representation.valid representation.indexed
      representation.ordered vertex key present (Int.le_of_lt improves))
  · intro value
    rw [membership value]
    simp [prepared, decreasedHeap, representation.valid.positionsKeys]
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    by_cases same : value = vertex <;> simp [prepared, decreasedHeap, same]
  · change after.clocks "heap_comparisons" - (heap.clocks "heap_comparisons" + 1) ≤ _ at comparisons
    unfold Heap.cost
    omega
  · exact swaps
  · intro ref notVertices notPositions notKeys index
    rw [unchanged ref notVertices notPositions index]
    simp [prepared, decreasedHeap, notKeys]
  · intro name notComparisons notSwaps
    rw [clocks name notComparisons notSwaps]
    simp [prepared, decreasedHeap, Heap.tick, Heap.write, notComparisons]
  · exact (show OtherStoragePreserved heap prepared from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage

/-- An equal or larger proposed key performs exactly one comparison and keeps
    the same valid queue, all array contents, and all other counters. -/
theorem unchanged_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (present : 0 ≤ heap.read layout.positions vertex)
    (notLower : heap.read layout.keys vertex ≤ key) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key)
      (heap.tick "heap_comparisons") () ∧
      QueueRep (heap.tick "heap_comparisons") queue layout ∧
      Heap.cost heap (heap.tick "heap_comparisons") = Clocks.single "heap_comparisons" 1 := by
  refine ⟨push_unchanged_summary heap queue layout representation.valid vertex key present notLower,
    ⟨representation.valid.tick "heap_comparisons", representation.nonnegative,
      representation.indexed, representation.ordered⟩, ?_⟩
  rw [← Heap.charge_single]
  exact Heap.cost_charge heap _

/-- During sift-down, only edges leaving the moving position may be unordered.
    Its parent is below its children, so promoting the smaller child is safe. -/
structure DownInvariant (priority : Seq) (size index : Int) : Prop where
  orderedExcept : ∀ child, 0 < child → child < size → parent child ≠ index →
    priority (parent child) ≤ priority child
  parentBelowChildren : ∀ child, 0 < child → child < size → parent child = index →
    0 < index → priority (parent index) ≤ priority child

/-- Once the moving entry is below both children (including a leaf), the
    entire active prefix is a heap. -/
theorem DownInvariant.finish {priority : Seq} {size index : Int}
    (invariant : DownInvariant priority size index)
    (orderedChildren : ∀ child, 0 < child → child < size → parent child = index →
      priority index ≤ priority child) :
    Ordered priority size := by
  intro child positive bound
  by_cases fromIndex : parent child = index
  · simpa [fromIndex] using orderedChildren child positive bound fromIndex
  · exact invariant.orderedExcept child positive bound fromIndex

/-- A smaller minimum child can be promoted, moving the only possible disorder
    down one level. The sibling edge and all ancestor edges remain ordered. -/
theorem DownInvariant.exchange_minimum {priority : Seq} {size index chosen : Int}
    (invariant : DownInvariant priority size index)
    (chosenPositive : 0 < chosen) (chosenBound : chosen < size)
    (fromIndex : parent chosen = index)
    (smaller : priority chosen < priority index)
    (minimum : ∀ child, 0 < child → child < size → parent child = index →
      priority chosen ≤ priority child) :
    DownInvariant (exchange priority index chosen) size chosen := by
  have indexSmaller : index < chosen := by
    have bounds : parent chosen < chosen := (parent_bounds chosen chosenPositive).2
    omega
  have different : index ≠ chosen := by omega
  constructor
  · intro child positive bound notChosen
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    by_cases atIndex : child = index
    · subst child
      have parentNotIndex : parent index ≠ index := by omega
      have parentNotChosen : parent index ≠ chosen := by omega
      have old := invariant.parentBelowChildren chosen chosenPositive chosenBound fromIndex positive
      simpa [exchange, parentNotIndex, parentNotChosen, different] using old
    · by_cases atChosen : child = chosen
      · subst child
        rw [fromIndex, exchange_left, exchange_right]
        exact Int.le_of_lt smaller
      · by_cases parentIndex : parent child = index
        · have old := minimum child positive bound parentIndex
          simpa [exchange, atIndex, atChosen, parentIndex, different] using old
        · simpa [exchange, atIndex, atChosen, parentIndex, notChosen] using
            invariant.orderedExcept child positive bound parentIndex
  · intro child positive bound parentChosen _
    have bounds : parent child < child := (parent_bounds child positive).2
    have childNotIndex : child ≠ index := by omega
    have childNotChosen : child ≠ chosen := by omega
    have old := invariant.orderedExcept child positive bound (by omega)
    rw [parentChosen] at old
    simpa [exchange, fromIndex, different, childNotIndex, childNotChosen] using old

/-- Replacing the root and shortening an ordered active prefix establishes
    sift-down's precondition. This is the order argument for minimum removal. -/
theorem Ordered.replace_root {priority : Seq} {size shorter key : Int}
    (ordered : Ordered priority size) (shrink : shorter ≤ size) :
    DownInvariant (fun index => if index = 0 then key else priority index) shorter 0 := by
  constructor
  · intro child positive bound parentNotRoot
    have childNotRoot : child ≠ 0 := by omega
    simpa [childNotRoot, parentNotRoot] using ordered child positive (by omega)
  · intro child positive bound fromIndex rootPositive
    omega

/-- Only the active prefix matters when moving between an abstract priority
    function and its concrete heap-array representation. -/
theorem DownInvariant.congr {first second : Seq} {size index : Int}
    (invariant : DownInvariant first size index) (within : index < size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    DownInvariant second size index := by
  constructor
  · intro child positive bound different
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
    exact invariant.orderedExcept child positive bound different
  · intro child positive bound fromIndex indexPositive
    have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index indexPositive
    rw [← same child (by omega) bound, ← same (parent index) bounds.1 (by omega)]
    exact invariant.parentBelowChildren child positive bound fromIndex indexPositive

/-- Binary-tree parents give exactly the source's two child positions. -/
theorem parent_children (index child : Int) :
    parent child = index ↔ child = 2 * index + 1 ∨ child = 2 * index + 2 := by
  unfold parent
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

-- Sift-down first selects the smaller child, then compares it with the parent.
def selectedChild (heap : Heap) (layout : Layout) (index : Int) : Int :=
  if 2 * index + 2 < layout.size ∧
      heap.read layout.keys (heap.read layout.vertices (2 * index + 2)) <
      heap.read layout.keys (heap.read layout.vertices (2 * index + 1))
  then 2 * index + 2 else 2 * index + 1

def selectionComparisons (layout : Layout) (index : Int) : Nat :=
  if 2 * index + 2 < layout.size then 1 else 0

def AtSiftDown (state : Configuration) (queue : Ref_MinHeap) (index : Int) : Prop :=
  MinHeap.sift_down.At.down_loop state ∧
    MinHeap.sift_down.Local.self state = some queue ∧
    MinHeap.sift_down.Local.i state = some index

def AtChildComparison (state : Configuration) (queue : Ref_MinHeap) (index child : Int) : Prop :=
  MinHeap.sift_down.At.compare_child state ∧
    MinHeap.sift_down.Local.self state = some queue ∧
    MinHeap.sift_down.Local.i state = some index ∧
    MinHeap.sift_down.Local.child state = some child

theorem sift_down_stop (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (location : AtSiftDown state queue index)
    (valid : layout.Valid state.heap queue) (leaf : layout.size ≤ 2 * index + 1) :
    MinHeap.sift_down.CallFrom state state.heap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_down.At.down_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [valid.readSize]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc3_false _ _ _
      (by simp [valid.readSize]; omega))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc2 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_down_pc1 _ _ _)

theorem sift_down_select (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (finalHeap : Heap) (location : AtSiftDown state queue index)
    (valid : layout.Valid state.heap queue) (hasChild : 2 * index + 1 < layout.size)
    (remaining : ∀ nextState,
      AtChildComparison nextState queue index (selectedChild state.heap layout index) →
      nextState.heap = state.heap.tick "heap_comparisons" (selectionComparisons layout index) →
      MinHeap.sift_down.CallFrom nextState finalHeap ()) :
    MinHeap.sift_down.CallFrom state finalHeap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_down.At.down_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [valid.readSize]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc3_true _ _ _ (by simp [valid.readSize, hasChild]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc23 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc22 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc21 _ _ _ (by simp [valid.readSize]))
    by_cases rightPresent : 2 * s.v1 + 2 < layout.size
    · apply Reaches.prepend (Step.MinHeap_sift_down_pc20_true _ _ _
        (by simp [valid.readSize]; omega))
      apply Reaches.prepend (Step.MinHeap_sift_down_pc19 _ _ _)
      apply Reaches.prepend (Step.MinHeap_sift_down_pc18 _ _ _
        (by simp [valid.readKeys, valid.readVertices, valid.keysAllocated, valid.verticesAllocated]))
      by_cases rightSmaller : heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
          heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))
      · apply Reaches.prepend (Step.MinHeap_sift_down_pc17_true _ _ _
          (by simpa [valid.readKeys, valid.readVertices, Int.add_assoc] using rightSmaller))
        apply Reaches.prepend (Step.MinHeap_sift_down_pc16 _ _ _)
        let nextState : Configuration := .active (heap.tick "heap_comparisons")
          (.fn_MinHeap_sift_down 15 { s with
            v2 := 2 * s.v1 + 2
            v3 := 2 * s.v1 + 2
            t5 := decide (2 * s.v1 + 1 < layout.size)
            t12 := decide (2 * s.v1 + 2 < layout.size)
            t13 := decide (heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
              heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))) }) originalStack
        have finish := remaining nextState
          (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
            MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
            selectedChild, rightPresent, rightSmaller, Config.heap])
          (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
        simpa [nextState, valid.readSize, valid.readKeys, valid.readVertices, Int.add_assoc] using finish stack
      · apply Reaches.prepend (Step.MinHeap_sift_down_pc17_false _ _ _
          (by simpa [valid.readKeys, valid.readVertices, Int.add_assoc] using rightSmaller))
        let nextState : Configuration := .active (heap.tick "heap_comparisons")
          (.fn_MinHeap_sift_down 15 { s with
            v2 := 2 * s.v1 + 1
            v3 := 2 * s.v1 + 2
            t5 := decide (2 * s.v1 + 1 < layout.size)
            t12 := decide (2 * s.v1 + 2 < layout.size)
            t13 := decide (heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
              heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))) }) originalStack
        have finish := remaining nextState
          (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
            MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
            selectedChild, rightPresent, rightSmaller, Config.heap])
          (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
        simpa [nextState, valid.readSize, valid.readKeys, valid.readVertices, Int.add_assoc] using finish stack
    · apply Reaches.prepend (Step.MinHeap_sift_down_pc20_false _ _ _
        (by simp [valid.readSize]; omega))
      let nextState : Configuration := .active heap
        (.fn_MinHeap_sift_down 15 { s with
          v2 := 2 * s.v1 + 1
          v3 := 2 * s.v1 + 2
          t5 := decide (2 * s.v1 + 1 < layout.size)
          t12 := decide (2 * s.v1 + 2 < layout.size) }) originalStack
      have finish := remaining nextState
        (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
          MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
          selectedChild, rightPresent, Config.heap])
        (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
      simpa [nextState, valid.readSize, Int.add_assoc] using finish stack

theorem sift_down_ordered (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index child : Int) (location : AtChildComparison state queue index child)
    (valid : layout.Valid state.heap queue)
    (ordered : state.heap.read layout.keys (state.heap.read layout.vertices index) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices child)) :
    MinHeap.sift_down.CallFrom state (state.heap.tick "heap_comparisons") () := by
  rcases location with ⟨atCompare, readSelf, readIndex, readChild⟩
  cases state with
  | done => cases atCompare
  | active heap frame originalStack =>
    cases frame <;> try { cases atCompare }
    rename_i pc s
    have counter : pc = 15 := by
      unfold MinHeap.sift_down.At.compare_child at atCompare
      split at atCompare <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i,
      MinHeap.sift_down.Local.child] at readSelf readIndex readChild
    cases readSelf
    cases readIndex
    cases readChild
    change layout.Valid heap s.v0 at valid
    change heap.read layout.keys (heap.read layout.vertices s.v1) ≤
      heap.read layout.keys (heap.read layout.vertices s.v2) at ordered
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc13_true _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using ordered))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc12 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_down_pc11 _ _ _)

theorem sift_down_continue (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index child : Int) (finalHeap : Heap) (location : AtChildComparison state queue index child)
    (valid : layout.Valid state.heap queue)
    (unordered : ¬ state.heap.read layout.keys (state.heap.read layout.vertices index) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices child))
    (remaining : ∀ nextState, AtSiftDown nextState queue child →
      nextState.heap = swapHeap (state.heap.tick "heap_comparisons") layout index child →
      MinHeap.sift_down.CallFrom nextState finalHeap ()) :
    MinHeap.sift_down.CallFrom state finalHeap () := by
  rcases location with ⟨atCompare, readSelf, readIndex, readChild⟩
  cases state with
  | done => cases atCompare
  | active heap frame originalStack =>
    cases frame <;> try { cases atCompare }
    rename_i pc s
    have counter : pc = 15 := by
      unfold MinHeap.sift_down.At.compare_child at atCompare
      split at atCompare <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i,
      MinHeap.sift_down.Local.child] at readSelf readIndex readChild
    cases readSelf
    cases readIndex
    cases readChild
    change layout.Valid heap s.v0 at valid
    change ¬ heap.read layout.keys (heap.read layout.vertices s.v1) ≤
      heap.read layout.keys (heap.read layout.vertices s.v2) at unordered
    let nextState : Configuration := .active
      (swapHeap (heap.tick "heap_comparisons") layout s.v1 s.v2)
      (.fn_MinHeap_sift_down 4 { s with
        v1 := s.v2
        t6 := ()
        t7 := s.v0
        t8 := s.v1
        t9 := s.v2
        t10 := decide (heap.read layout.keys (heap.read layout.vertices s.v1) ≤
          heap.read layout.keys (heap.read layout.vertices s.v2)) }) originalStack
    have finish := remaining nextState ⟨True.intro, rfl, rfl⟩ rfl
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc13_false _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using unordered))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc10 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc9 _ _ _ valid.object)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc8 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc7 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc6 _ _ _)
    apply Reaches.trans ((swap_summary (heap.tick "heap_comparisons") s.v0 layout
      (valid.tick "heap_comparisons") s.v1 s.v2).2 _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc5 _ _ _)
    simpa only [keys_tick, vertices_tick, valid.readKeys, valid.readVertices,
      Option.getD_some, Heap.read_tick] using finish stack

theorem selectedChild_bounds (heap : Heap) (layout : Layout) (index : Int)
    (nonnegative : 0 ≤ index) (hasChild : 2 * index + 1 < layout.size) :
    0 < selectedChild heap layout index ∧ selectedChild heap layout index < layout.size ∧
      parent (selectedChild heap layout index) = index := by
  unfold selectedChild
  split
  · rename_i chosen
    refine ⟨by omega, chosen.1, ?_⟩
    rw [parent_children]
    exact Or.inr rfl
  · refine ⟨by omega, hasChild, ?_⟩
    rw [parent_children]
    exact Or.inl rfl

theorem selectedChild_minimum (heap : Heap) (layout : Layout) (index child : Int)
    (childBound : child < layout.size) (childOf : parent child = index) :
    heap.read layout.keys (heap.read layout.vertices (selectedChild heap layout index)) ≤
      heap.read layout.keys (heap.read layout.vertices child) := by
  have options := (parent_children index child).mp childOf
  rcases options with rfl | rfl <;> unfold selectedChild <;> split <;> rename_i selected
  · exact Int.le_of_lt selected.2
  · exact Int.le_refl _
  · exact Int.le_refl _
  · have notSmaller : ¬ heap.read layout.keys (heap.read layout.vertices (2 * index + 2)) <
        heap.read layout.keys (heap.read layout.vertices (2 * index + 1)) := by
      intro smaller
      exact selected ⟨childBound, smaller⟩
    omega

theorem depth_mono {first second : Int} (ordered : first ≤ second) : depth first ≤ depth second := by
  unfold depth
  apply (Nat.le_log2 (by omega)).2
  exact Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)

theorem selectedChild_depth (heap : Heap) (layout : Layout) (index : Int)
    (nonnegative : 0 ≤ index) :
    depth (selectedChild heap layout index) = depth index + 1 := by
  apply child_depth index _ nonnegative
  unfold selectedChild
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem selectionComparisons_bound (layout : Layout) (index : Int) :
    selectionComparisons layout index ≤ 1 := by
  unfold selectionComparisons
  split <;> decide

-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.
theorem sift_down_loop (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after,
      (∀ state, AtSiftDown state queue index → state.heap = heap →
        MinHeap.sift_down.CallFrom state after ()) ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      after.clocks "heap_comparisons" ≤ heap.clocks "heap_comparisons" +
        2 * (depth (layout.size - 1) - depth index) ∧
      after.clocks "heap_swaps" ≤ heap.clocks "heap_swaps" +
        (depth (layout.size - 1) - depth index) ∧
      (DownInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  generalize rankEq : depth (layout.size - 1) - depth index = rank
  induction rank using Nat.strongRecOn generalizing heap index with
  | ind rank inductionHypothesis =>
    by_cases hasChild : 2 * index + 1 < layout.size
    · let child := selectedChild heap layout index
      let comparedHeap := (heap.tick "heap_comparisons" (selectionComparisons layout index)).tick "heap_comparisons"
      have childFacts := selectedChild_bounds heap layout index nonnegative hasChild
      have childDepth := selectedChild_depth heap layout index nonnegative
      have depthBound : depth child ≤ depth (layout.size - 1) := depth_mono (by dsimp [child]; omega)
      have selectionBound := selectionComparisons_bound layout index
      have comparedValid : layout.Valid comparedHeap queue :=
        (valid.tick "heap_comparisons" (selectionComparisons layout index)).tick "heap_comparisons"
      by_cases ordered : heap.read layout.keys (heap.read layout.vertices index) ≤
          heap.read layout.keys (heap.read layout.vertices child)
      · refine ⟨comparedHeap, ?_, comparedValid, indexed, ?_, ?_, ?_, ?_, ?_, ?_,
          ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · intro state location sameHeap
          apply sift_down_select state queue layout index comparedHeap location
            (by simpa [sameHeap] using valid) hasChild
          intro compareState compareLocation compareHeap
          have location' : AtChildComparison compareState queue index child := by
            simpa [sameHeap, child] using compareLocation
          have valid' : layout.Valid compareState.heap queue := by
            simpa [compareHeap, sameHeap] using
              valid.tick "heap_comparisons" (selectionComparisons layout index)
          have ordered' : compareState.heap.read layout.keys (compareState.heap.read layout.vertices index) ≤
              compareState.heap.read layout.keys (compareState.heap.read layout.vertices child) := by
            simpa [compareHeap, sameHeap] using ordered
          simpa [comparedHeap, compareHeap, sameHeap] using
            sift_down_ordered compareState queue layout index child location' valid' ordered'
        · simp only [comparedHeap, Heap.clocks_tick_same]
          dsimp [child] at depthBound
          omega
        · simp [comparedHeap, Heap.tick]
        · intro invariant
          apply invariant.finish
          intro descendant _ descendantBound childOf
          exact Int.le_trans ordered (selectedChild_minimum heap layout index descendant descendantBound childOf)
        · intro ref _ _ position
          rfl
        · intro vertex
          rfl
        · intro name notComparisons _
          simp [comparedHeap, Heap.tick, notComparisons]
      · let nextHeap := swapHeap comparedHeap layout index child
        have nextValid : layout.Valid nextHeap queue :=
          swap_preserves_layout comparedHeap queue layout comparedValid index child
        have nextIndexed : Indexed (nextHeap.read layout.vertices)
            (nextHeap.read layout.positions) layout.size :=
          swap_preserves_indexed comparedHeap layout index child valid.verticesPositions indexed
            nonnegative bound (by dsimp [child]; omega) childFacts.2.1
        have smaller : depth (layout.size - 1) - depth child < rank := by
          dsimp [child] at depthBound ⊢
          omega
        obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
            unchanged, membership, otherClocks, storage⟩ :=
          inductionHypothesis (depth (layout.size - 1) - depth child) smaller nextHeap child
            nextValid nextIndexed (by dsimp [child]; omega) childFacts.2.1 rfl
        refine ⟨after, ?_, afterValid, afterIndexed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro state location sameHeap
          apply sift_down_select state queue layout index after location
            (by simpa [sameHeap] using valid) hasChild
          intro compareState compareLocation compareHeap
          apply sift_down_continue compareState queue layout index child after
            (by simpa [sameHeap, child] using compareLocation)
            (by simpa [compareHeap, sameHeap] using
              valid.tick "heap_comparisons" (selectionComparisons layout index))
            (by simpa [compareHeap, sameHeap] using ordered)
          intro nextState nextLocation nextHeapEq
          apply remaining nextState nextLocation
          simpa [nextHeap, comparedHeap, compareHeap, sameHeap] using nextHeapEq
        · simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write] at comparisons
          dsimp [child] at comparisons depthBound
          omega
        · simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write] at swaps
          dsimp [child] at swaps depthBound
          omega
        · intro invariant
          apply repair
          change DownInvariant (fun position => (swapHeap comparedHeap layout index child).read layout.keys
            ((swapHeap comparedHeap layout index child).read layout.vertices position)) layout.size child
          rw [swap_priorities comparedHeap layout index child valid.verticesPositions valid.verticesKeys valid.positionsKeys]
          exact invariant.exchange_minimum childFacts.1 childFacts.2.1 childFacts.2.2
            (by omega) (fun descendant _ descendantBound childOf =>
              selectedChild_minimum heap layout index descendant descendantBound childOf)
        · intro ref notVertices notPositions position
          rw [unchanged ref notVertices notPositions position]
          simp [nextHeap, comparedHeap, swapHeap, Heap.read, Heap.write, notVertices, notPositions]
        · intro vertex
          rw [membership vertex]
          exact swap_preserves_membership comparedHeap layout index child valid.verticesPositions
            indexed nonnegative bound (by dsimp [child]; omega) childFacts.2.1 vertex
        · intro name notComparisons notSwaps
          rw [otherClocks name notComparisons notSwaps]
          simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write, notComparisons, notSwaps]
        · exact (show OtherStoragePreserved heap nextHeap from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage
    · refine ⟨heap, ?_, valid, indexed, Nat.le_add_right _ _, Nat.le_add_right _ _,
        ?_, ?_, ?_, ?_, OtherStoragePreserved.refl heap⟩
      · intro state location sameHeap
        simpa [sameHeap] using sift_down_stop state queue layout index location
          (by simpa [sameHeap] using valid) (by omega)
      · intro invariant
        apply invariant.finish
        intro child _ childBound childOf
        have children := (parent_children index child).mp childOf
        omega
      · intro ref _ _ position
        rfl
      · intro vertex
        rfl
      · intro name _ _
        rfl

-- The public contract allows arbitrary initial priorities. Its conditional
-- repair clause explains when this terminating run also restores heap order.
theorem sift_down_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after, MinHeap.sift_down.Call heap (queue, index) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after "heap_comparisons" ≤ 2 * (depth (layout.size - 1) - depth index) ∧
      Heap.cost heap after "heap_swaps" ≤ depth (layout.size - 1) - depth index ∧
      (DownInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
      unchanged, membership, otherClocks, storage⟩ :=
    sift_down_loop heap queue layout index valid indexed nonnegative bound
  refine ⟨after, ⟨valid.object, ?_⟩, afterValid, afterIndexed, ?_, ?_, repair,
    unchanged, membership, otherClocks, storage⟩
  · exact remaining (MinHeap.sift_down.initial heap (queue, index)) ⟨True.intro, rfl, rfl⟩ rfl
  · unfold Heap.cost
    omega
  · unfold Heap.cost
    omega

/-- The heap after moving the old root to the last position, shrinking the
    active prefix, and marking that old root absent, before any sift-down. -/
def removedHeap (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) : Heap :=
  (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)).write
    layout.positions (heap.read layout.vertices 0) (-1)

theorem removed_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    { layout with size := layout.size - 1 }.Valid (removedHeap heap queue layout) queue := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 (layout.size - 1)
  constructor
  · change is_MinHeap (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue
      (layout.size - 1)) queue
    simpa [is_MinHeap, set_MinHeap_size] using swappedValid.object
  · simp only [removedHeap, vertices_write]
    simpa [field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using swappedValid.readVertices
  · simp only [removedHeap, positions_write]
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  · simp only [removedHeap, keys_write]
    simpa [field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using swappedValid.readKeys
  · simpa [removedHeap] using field_MinHeap_size_set _ _ (layout.size - 1) swappedValid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem removed_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (removedHeap heap queue layout).read layout.vertices index =
      exchange (heap.read layout.vertices) 0 (layout.size - 1) index := by
  have preserved : (removedHeap heap queue layout).read layout.vertices index =
      (swapHeap heap layout 0 (layout.size - 1)).read layout.vertices index := by
    simp [removedHeap, set_MinHeap_size, Heap.read, Heap.write, separate]
  exact preserved.trans (swap_vertices heap layout 0 (layout.size - 1) index separate)

theorem removed_positions (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int) :
    (removedHeap heap queue layout).read layout.positions vertex =
      if vertex = heap.read layout.vertices 0 then -1
      else (swapHeap heap layout 0 (layout.size - 1)).read layout.positions vertex := by
  simp [removedHeap, set_MinHeap_size, Heap.read, Heap.write]

/-- Removing the last entry of an indexed prefix preserves its inverse map.
    This purely mathematical lemma also covers a singleton prefix. -/
theorem Indexed.remove_last (vertices positions : Seq) (size : Int)
    (indexed : Indexed vertices positions size) (nonempty : 0 < size) :
    Indexed vertices (fun vertex => if vertex = vertices (size - 1) then -1 else positions vertex)
      (size - 1) := by
  have lastNonnegative : 0 ≤ size - 1 := by omega
  have lastBound : size - 1 < size := by omega
  constructor
  · intro index nonnegative bound
    have notLast : vertices index ≠ vertices (size - 1) := by
      intro same
      have equal := indexed.distinct nonnegative (by omega) lastNonnegative lastBound same
      omega
    simpa [notLast] using indexed.forward index nonnegative (by omega)
  · intro vertex nonnegative
    have notLast : vertex ≠ vertices (size - 1) := by
      intro same
      simp [same] at nonnegative
    simp only [notLast, ite_false] at nonnegative ⊢
    obtain ⟨bound, identity⟩ := indexed.backward vertex nonnegative
    have different : positions vertex ≠ size - 1 := by
      intro same
      rw [same] at identity
      exact notLast identity.symm
    exact ⟨by omega, identity⟩
  · intro vertex negative
    by_cases same : vertex = vertices (size - 1)
    · simp [same]
    · simp only [same, ite_false] at negative ⊢
      exact indexed.absent vertex negative

/-- Shrinking after the swap removes exactly one entry and preserves all
    inverse-map invariants, before heap order is repaired by sift-down. -/
theorem removed_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonempty : 0 < layout.size) :
    Indexed ((removedHeap heap queue layout).read layout.vertices)
      ((removedHeap heap queue layout).read layout.positions) (layout.size - 1) := by
  let swapped := swapHeap heap layout 0 (layout.size - 1)
  have swappedIndexed : Indexed (swapped.read layout.vertices) (swapped.read layout.positions)
      layout.size :=
    swap_preserves_indexed heap layout 0 (layout.size - 1) valid.verticesPositions indexed
      (by omega) nonempty (by omega) (by omega)
  have last : swapped.read layout.vertices (layout.size - 1) = heap.read layout.vertices 0 := by
    simp [swapped, swap_vertices heap layout 0 (layout.size - 1) _ valid.verticesPositions]
  have vertices : (removedHeap heap queue layout).read layout.vertices =
      swapped.read layout.vertices := by
    funext index
    rw [removed_vertices heap queue layout index valid.verticesPositions]
    exact (swap_vertices heap layout 0 (layout.size - 1) index valid.verticesPositions).symm
  have positions : (removedHeap heap queue layout).read layout.positions =
      fun vertex => if vertex = swapped.read layout.vertices (layout.size - 1) then -1
        else swapped.read layout.positions vertex := by
    funext vertex
    rw [removed_positions, last]
  rw [vertices, positions]
  exact swappedIndexed.remove_last _ _ _ nonempty

/-- Membership after removal is old membership excluding the old root. -/
theorem removed_membership (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonempty : 0 < layout.size) (vertex : Int) :
    0 ≤ (removedHeap heap queue layout).read layout.positions vertex ↔
      0 ≤ heap.read layout.positions vertex ∧ vertex ≠ heap.read layout.vertices 0 := by
  rw [removed_positions]
  by_cases same : vertex = heap.read layout.vertices 0
  · simp [same]
  · simpa [same] using
      swap_preserves_membership heap layout 0 (layout.size - 1) valid.verticesPositions
        indexed (by omega) nonempty (by omega) (by omega) vertex

theorem removed_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (removedHeap heap queue layout).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [removedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm separateVertices, Ne.symm separatePositions]

theorem removed_read_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (ref : SeqRef) (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions)
    (index : Int) :
    (removedHeap heap queue layout).read ref index = heap.read ref index := by
  simp [removedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions]

theorem removed_cost (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) :
    Heap.cost heap (removedHeap heap queue layout) = Clocks.single "heap_swaps" 1 := by
  exact swap_cost heap layout 0 (layout.size - 1)

theorem removed_clocks_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (name : String) (notSwaps : name ≠ "heap_swaps") :
    (removedHeap heap queue layout).clocks name = heap.clocks name := by
  change (heap.tick "heap_swaps").clocks name = heap.clocks name
  exact Heap.clocks_tick_other heap "heap_swaps" name notSwaps

/-- Removing from a queue of at least two vertices composes a single swap and
    the supplied sift-down summary. The returned vertex is the original root. -/
theorem pop_with_sift_summary (heap after : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (multiple : 1 < layout.size)
    (sift : MinHeap.sift_down.Call (removedHeap heap queue layout) (queue, 0) after ()) :
    MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_false _ _ _ (by simp [valid.readSize]; omega))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc17 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc16 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc14 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc12 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc11 _ _ _)
  simp only [valid.readSize, valid.readVertices, Option.getD_some]
  apply Reaches.trans ((swap_summary heap queue layout valid 0 (layout.size - 1)).2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc10 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc9 _ _ _
    (by simpa [swapHeap, set_MinHeap_size, field_MinHeap_positions, is_MinHeap,
      valid.object, valid.readPositions] using!
      show (field_MinHeap_positions heap queue).isSome = true ∧
        (field_MinHeap_positions heap queue).getD 0 < heap.nextRef from
      by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc7_true _ _ _ (by simp; omega))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc5 _ _ _
    (by change is_MinHeap (set_MinHeap_size
          (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)) queue
        simpa [is_MinHeap, set_MinHeap_size] using
          (swap_preserves_layout heap queue layout valid 0 (layout.size - 1)).object))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc3 _ _ _)
  have positions : field_MinHeap_positions
      (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)) queue =
      some layout.positions := by
    simpa [field_MinHeap_positions, set_MinHeap_size, is_MinHeap] using! valid.readPositions
  simp only [positions, Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_pop_min_pc1 _ _ _)

/-- The public representation immediately supplies the root's minimum contract. -/
theorem QueueRep.root_minimum {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (vertex : Int)
    (present : 0 ≤ heap.read layout.positions vertex) :
    heap.read layout.keys (heap.read layout.vertices 0) ≤ heap.read layout.keys vertex :=
  root_minimum_vertex heap layout representation.indexed representation.ordered vertex present

/-- A represented empty queue has no present vertices, including outside the
    graph's vertex range. Its absent-position sentinel is exactly -1. -/
theorem QueueRep.empty_positions {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (empty : layout.size = 0) (vertex : Int) :
    heap.read layout.positions vertex = -1 := by
  apply representation.indexed.absent
  by_cases present : 0 ≤ heap.read layout.positions vertex
  · have bound := (representation.indexed.backward vertex present).1
    omega
  · omega

theorem pop_empty_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (empty : layout.size = 0) :
    MinHeap.pop_min.Call heap queue heap (-1) ∧
      (∀ vertex, heap.read layout.positions vertex = -1) ∧
      Heap.cost heap heap = (fun _ => 0) := by
  refine ⟨pop_empty_summary heap queue layout.size representation.valid.object
    representation.valid.readSize (by omega), representation.empty_positions empty, ?_⟩
  funext name
  simp [Heap.cost]

/-- On the shortened active prefix, root removal replaces only the root's
    priority. Existing descendants retain their old ordering. -/
theorem removed_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (multiple : 1 < layout.size) :
    DownInvariant (fun index => (removedHeap heap queue layout).read layout.keys
      ((removedHeap heap queue layout).read layout.vertices index)) (layout.size - 1) 0 := by
  apply (ordered.replace_root (shorter := layout.size - 1)
    (key := heap.read layout.keys (heap.read layout.vertices (layout.size - 1))) (by omega)).congr (by omega)
  intro index nonnegative bound
  rw [removed_keys heap queue layout _ valid.verticesKeys valid.positionsKeys,
    removed_vertices heap queue layout index valid.verticesPositions]
  have notLast : index ≠ layout.size - 1 := by omega
  have rootNotLast : (0 : Int) ≠ layout.size - 1 := by omega
  by_cases root : index = 0 <;> simp [exchange, root, notLast, rootNotLast]

/-- Minimum extraction's client contract: remove one minimum-priority vertex,
    preserve every other key, restore the queue, and bound the two cost clocks. -/
structure Extracted (before after : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int) : Prop where
  representation : QueueRep after queue { layout with size := layout.size - 1 }
  wasPresent : 0 ≤ before.read layout.positions vertex
  minimum : ∀ value, 0 ≤ before.read layout.positions value →
    before.read layout.keys vertex ≤ before.read layout.keys value
  membership : ∀ value, 0 ≤ after.read layout.positions value ↔
    0 ≤ before.read layout.positions value ∧ value ≠ vertex
  keys : ∀ value, after.read layout.keys value = before.read layout.keys value
  comparisons : Heap.cost before after "heap_comparisons" ≤ 2 * depth (layout.size - 2)
  swaps : Heap.cost before after "heap_swaps" ≤ depth (layout.size - 2) + 1
  otherArrays : ∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions →
    ∀ index, after.read ref index = before.read ref index
  otherClocks : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
    after.clocks name = before.clocks name
  otherStorage : OtherStoragePreserved (set_MinHeap_size before queue (layout.size - 1)) after

/-- Extracting a singleton needs only its implemented self-swap. -/
theorem pop_singleton_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (singleton : layout.size = 1) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  have nonempty : 0 < layout.size := by omega
  have same : removedHeap heap queue layout = poppedHeap heap queue layout := by
    simp only [removedHeap, singleton, Int.sub_self, poppedHeap]
  refine ⟨removedHeap heap queue layout, ?_, ?_⟩
  · rw [same]
    exact pop_singleton_summary heap queue layout representation.valid singleton
  · constructor
    · refine ⟨removed_layout heap queue layout representation.valid, by simp [singleton],
        removed_indexed heap queue layout representation.valid representation.indexed nonempty, ?_⟩
      intro child positive bound
      change child < layout.size - 1 at bound
      omega
    · rw [representation.indexed.forward 0 (by omega) nonempty]
      omega
    · exact representation.root_minimum
    · exact removed_membership heap queue layout representation.valid representation.indexed nonempty
    · exact fun value => removed_keys heap queue layout value representation.valid.verticesKeys
        representation.valid.positionsKeys
    · rw [removed_cost]
      simp [Clocks.single]
    · rw [removed_cost]
      simp [Clocks.single]
    · exact removed_read_other heap queue layout
    · intro name _ notSwaps
      exact removed_clocks_other heap queue layout name notSwaps
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- For a larger queue, the caller supplies sift-down's proved contract after
    the root/last exchange. The proof never inspects sift-down transitions. -/
theorem pop_multiple_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (multiple : 1 < layout.size) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  let prepared := removedHeap heap queue layout
  let shorter := { layout with size := layout.size - 1 }
  have valid : shorter.Valid prepared queue := removed_layout heap queue layout representation.valid
  have indexed : Indexed (prepared.read layout.vertices) (prepared.read layout.positions) shorter.size :=
    removed_indexed heap queue layout representation.valid representation.indexed (by omega)
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_down_summary prepared queue shorter 0 valid indexed (by omega) (by dsimp [shorter]; omega)
  refine ⟨after, pop_with_sift_summary heap after queue layout representation.valid multiple sift, ?_⟩
  constructor
  · refine ⟨afterValid, by dsimp [shorter]; omega, afterIndexed, ?_⟩
    exact repair (removed_order heap queue layout representation.valid representation.ordered multiple)
  · rw [representation.indexed.forward 0 (by omega) (by omega)]
    omega
  · exact representation.root_minimum
  · intro value
    rw [membership value]
    exact removed_membership heap queue layout representation.valid representation.indexed (by omega) value
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    exact removed_keys heap queue layout value representation.valid.verticesKeys representation.valid.positionsKeys
  · simpa [Heap.cost, prepared, removedHeap, swapHeap, Heap.tick, Heap.write,
      set_MinHeap_size, shorter, depth, Int.sub_sub] using! comparisons
  · have bound : after.clocks "heap_swaps" - (heap.clocks "heap_swaps" + 1) ≤
        depth (layout.size - 2) := by
      simpa [Heap.cost, prepared, removedHeap, swapHeap, Heap.tick, Heap.write,
        set_MinHeap_size, shorter, depth, Int.sub_sub] using! swaps
    unfold Heap.cost
    omega
  · intro ref notVertices notPositions index
    rw [unchanged ref notVertices notPositions index]
    exact removed_read_other heap queue layout ref notVertices notPositions index
  · intro name notComparisons notSwaps
    rw [clocks name notComparisons notSwaps]
    exact removed_clocks_other heap queue layout name notSwaps
  · exact (show OtherStoragePreserved (set_MinHeap_size heap queue (layout.size - 1)) prepared
      from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage

/-- Every nonempty represented queue has a terminating minimum extraction with
    logarithmic operation costs and a reusable heap-level postcondition. -/
theorem pop_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (nonempty : 0 < layout.size) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  by_cases multiple : 1 < layout.size
  · exact pop_multiple_correct heap queue layout representation multiple
  · exact pop_singleton_correct heap queue layout representation (by omega)

/-- Ordinary output users can state minimum correctness and costs without
    mentioning the internal root position or the final heap. -/
theorem pop_minimum_output (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (nonempty : 0 < layout.size) :
    ∃ vertex costs, MinHeap.pop_min.ReturnsWithCost (heap, queue) vertex costs ∧
      0 ≤ heap.read layout.positions vertex ∧
      (∀ value, 0 ≤ heap.read layout.positions value →
        heap.read layout.keys vertex ≤ heap.read layout.keys value) ∧
      costs "heap_comparisons" ≤ 2 * depth (layout.size - 2) ∧
      costs "heap_swaps" ≤ depth (layout.size - 2) + 1 := by
  obtain ⟨after, run, effect⟩ := pop_correct heap queue layout representation nonempty
  exact ⟨heap.read layout.vertices 0, Heap.cost heap after,
    ⟨after, ⟨run.1, run.2.root⟩, rfl⟩, effect.wasPresent, effect.minimum,
    effect.comparisons, effect.swaps⟩

/-- Emptiness is observed through a public method with no mutation or ticks. -/
theorem is_empty_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    MinHeap.is_empty.Call heap queue heap (decide (layout.size ≤ 0)) := by
  refine ⟨valid.object, ?_⟩
  intro caller
  apply Reaches.prepend (Step.MinHeap_is_empty_pc2 _ _ caller (by simp [valid.readSize]))
  simpa [valid.readSize] using
    (Reaches.single (Step.MinHeap_is_empty_pc1 heap
      ({ v0 := queue, t1 := decide (layout.size ≤ 0) } : State_MinHeap_is_empty) caller))

end BinaryModuleAnalysis
