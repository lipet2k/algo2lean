import Algo.fibonacci_heap.Points
import Algo2LeanLib.FibonacciConsolidation
import Algo2LeanLib.HeapFrame
import Algo2LeanLib.FibonacciDeleteMin
import Algo2LeanLib.FibonacciStorage
import Algo2LeanLib.FibonacciRootInsertion
import Algo2LeanLib.FibonacciRebuild
import Algo2LeanLib.FibonacciKeyUpdate

/-!
Analysis outline:
- `new_heap_representation`: Empty Fibonacci heap representation.
- `QueueRep.update`: Insertion and decrease-key amortized contract.
- `QueueRep.pop_minimum`: Minimum extraction amortized contract.
-/

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

namespace FibonacciModuleAnalysis

-- Storage descriptions are independent of the mathematical forest invariant.
-- This lets local ring facts apply inside any caller and at any named location.
structure Layout where
  keys : SeqRef
  parents : SeqRef
  children : SeqRef
  left : SeqRef
  right : SeqRef
  degrees : SeqRef
  marks : SeqRef
  present : SeqRef
  table : SeqRef
  minimum : Int
  size : Int

def Layout.refs (layout : Layout) : List SeqRef :=
  [layout.keys, layout.parents, layout.children, layout.left, layout.right, layout.degrees, layout.marks, layout.present, layout.table]

structure Layout.Valid (layout : Layout) (heap : Heap) (queue : Ref_FibonacciHeap) : Prop where
  object : is_FibonacciHeap heap queue
  readKeys : field_FibonacciHeap_keys heap queue = some layout.keys
  readParents : field_FibonacciHeap_parents heap queue = some layout.parents
  readChildren : field_FibonacciHeap_children heap queue = some layout.children
  readLeft : field_FibonacciHeap_left heap queue = some layout.left
  readRight : field_FibonacciHeap_right heap queue = some layout.right
  readDegrees : field_FibonacciHeap_degrees heap queue = some layout.degrees
  readMarks : field_FibonacciHeap_marks heap queue = some layout.marks
  readPresent : field_FibonacciHeap_present heap queue = some layout.present
  readTable : field_FibonacciHeap_table heap queue = some layout.table
  readMinimum : field_FibonacciHeap_minimum heap queue = some layout.minimum
  readSize : field_FibonacciHeap_size heap queue = some layout.size
  keysAllocated : layout.keys < heap.nextRef
  parentsAllocated : layout.parents < heap.nextRef
  childrenAllocated : layout.children < heap.nextRef
  leftAllocated : layout.left < heap.nextRef
  rightAllocated : layout.right < heap.nextRef
  degreesAllocated : layout.degrees < heap.nextRef
  marksAllocated : layout.marks < heap.nextRef
  presentAllocated : layout.present < heap.nextRef
  tableAllocated : layout.table < heap.nextRef
  separate : layout.refs.Nodup

@[simp] theorem keys_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_keys (heap.write ref index value) queue =
      field_FibonacciHeap_keys heap queue := rfl

@[simp] theorem parents_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_parents (heap.write ref index value) queue =
      field_FibonacciHeap_parents heap queue := rfl

@[simp] theorem children_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_children (heap.write ref index value) queue =
      field_FibonacciHeap_children heap queue := rfl

@[simp] theorem left_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_left (heap.write ref index value) queue =
      field_FibonacciHeap_left heap queue := rfl

@[simp] theorem right_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_right (heap.write ref index value) queue =
      field_FibonacciHeap_right heap queue := rfl

@[simp] theorem degrees_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_degrees (heap.write ref index value) queue =
      field_FibonacciHeap_degrees heap queue := rfl

@[simp] theorem marks_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_marks (heap.write ref index value) queue =
      field_FibonacciHeap_marks heap queue := rfl

@[simp] theorem present_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_present (heap.write ref index value) queue =
      field_FibonacciHeap_present heap queue := rfl

@[simp] theorem table_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_table (heap.write ref index value) queue =
      field_FibonacciHeap_table heap queue := rfl

@[simp] theorem minimum_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_minimum (heap.write ref index value) queue =
      field_FibonacciHeap_minimum heap queue := rfl

@[simp] theorem size_write (heap : Heap) (ref : SeqRef) (index value : Int)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_size (heap.write ref index value) queue =
      field_FibonacciHeap_size heap queue := rfl

-- Detaching a vertex changes four links and does not require a whole run.
def removeHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let before := heap.read layout.left vertex
  let after := heap.read layout.right vertex
  (((heap.write layout.right before after).write layout.left after before).write
    layout.left vertex vertex).write layout.right vertex vertex

theorem remove_from_ring_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    FibonacciHeap.remove_from_ring.Call heap (queue, vertex)
      (removeHeap heap layout vertex) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc8 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc7 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc6 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc5 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc4 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc3 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc2 _ _ _)
  simp only [left_write, right_write, valid.readLeft, valid.readRight,
    Option.getD_some, removeHeap]
  exact Reaches.single (Step.FibonacciHeap_remove_from_ring_pc1 _ _ _)

theorem remove_preserves_layout (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    layout.Valid (removeHeap heap layout vertex) queue := by
  exact ⟨valid.object, valid.readKeys, valid.readParents, valid.readChildren, valid.readLeft, valid.readRight, valid.readDegrees, valid.readMarks, valid.readPresent, valid.readTable, valid.readMinimum, valid.readSize, valid.keysAllocated, valid.parentsAllocated, valid.childrenAllocated, valid.leftAllocated, valid.rightAllocated, valid.degreesAllocated, valid.marksAllocated, valid.presentAllocated, valid.tableAllocated, valid.separate⟩

theorem remove_cost (heap : Heap) (layout : Layout) (vertex : Int) :
    Heap.cost heap (removeHeap heap layout vertex) = (fun _ => 0) := by
  funext clock
  simp [removeHeap, Heap.cost, Heap.write]

theorem remove_other_array (heap : Heap) (layout : Layout) (vertex : Int)
    (ref : SeqRef) (notLeft : ref ≠ layout.left) (notRight : ref ≠ layout.right)
    (index : Int) :
    (removeHeap heap layout vertex).read ref index = heap.read ref index := by
  simp [removeHeap, Heap.read, Heap.write, notLeft, notRight]

theorem remove_is_singleton (heap : Heap) (layout : Layout) (vertex : Int)
    (separate : layout.left ≠ layout.right) :
    (removeHeap heap layout vertex).read layout.left vertex = vertex ∧
      (removeHeap heap layout vertex).read layout.right vertex = vertex := by
  simp [removeHeap, Heap.read, Heap.write, separate]

-- Initialization follows the source allocation order. The exact-effect
-- statement can be reused without opening this method's transition rules.
def initializedHeap (heap : Heap) (queue : Ref_FibonacciHeap) : Heap :=
  let h0 := set_FibonacciHeap_keys (heap.allocate (fun _ => 0)) queue heap.nextRef
  let h1 := set_FibonacciHeap_parents (h0.allocate (fun _ => -1)) queue h0.nextRef
  let h2 := set_FibonacciHeap_children (h1.allocate (fun _ => -1)) queue h1.nextRef
  let h3 := set_FibonacciHeap_left (h2.allocate (fun _ => 0)) queue h2.nextRef
  let h4 := set_FibonacciHeap_right (h3.allocate (fun _ => 0)) queue h3.nextRef
  let h5 := set_FibonacciHeap_degrees (h4.allocate (fun _ => 0)) queue h4.nextRef
  let h6 := set_FibonacciHeap_marks (h5.allocate (fun _ => 0)) queue h5.nextRef
  let h7 := set_FibonacciHeap_present (h6.allocate (fun _ => 0)) queue h6.nextRef
  let h8 := set_FibonacciHeap_table (h7.allocate (fun _ => -1)) queue h7.nextRef
  set_FibonacciHeap_size (set_FibonacciHeap_minimum h8 queue (-1)) queue 0

def emptyLayout (heap : Heap) : Layout :=
  ⟨heap.nextRef, heap.nextRef + 1, heap.nextRef + 2, heap.nextRef + 3, heap.nextRef + 4, heap.nextRef + 5, heap.nextRef + 6, heap.nextRef + 7, heap.nextRef + 8, -1, 0⟩

theorem initialized_object (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    is_FibonacciHeap (initializedHeap heap queue) queue := by
  simpa [initializedHeap, is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid

theorem initialization_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    FibonacciHeap.__init__.Call heap queue (initializedHeap heap queue) () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap___init___pc40 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc39 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc38 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc37 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc36 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc35 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc34 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc33 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc32 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc31 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc30 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc29 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc28 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc27 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc26 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc25 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc24 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc23 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc22 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc21 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc20 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc19 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc18 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc17 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc16 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc15 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc14 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc13 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc12 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc11 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc10 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc9 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc8 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc7 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc6 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc5 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc4 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc3 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc2 _ _ _)
  exact Reaches.single (Step.FibonacciHeap___init___pc1 _ _ _)

def newHeap (heap : Heap) : Heap :=
  initializedHeap (heap.allocateObject "fibonacci_heap.FibonacciHeap") heap.nextObject

theorem new_heap_summary (heap : Heap) :
    FibonacciHeap.Call heap () (newHeap heap) heap.nextObject := by
  have allocated : is_FibonacciHeap (heap.allocateObject "fibonacci_heap.FibonacciHeap") heap.nextObject := by
    simp [is_FibonacciHeap]
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_pc6 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pc5 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pc4 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pc3 _ _ _)
  apply Reaches.trans ((initialization_summary _ _ allocated).2 _)
  apply Reaches.prepend (Step.FibonacciHeap_pc2 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_pc1 _ _ _ (initialized_object _ _ allocated))

theorem initialization_layout (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    (emptyLayout heap).Valid (initializedHeap heap queue) queue := by
  constructor
  · exact initialized_object heap queue valid
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_keys, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_parents, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_children, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_left, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_right, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_degrees, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_marks, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_present, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_table, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_minimum, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asInt, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_size, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asInt, Nat.add_assoc]
  · change heap.nextRef < heap.nextRef + 9
    omega
  · change heap.nextRef + 1 < heap.nextRef + 9
    omega
  · change heap.nextRef + 2 < heap.nextRef + 9
    omega
  · change heap.nextRef + 3 < heap.nextRef + 9
    omega
  · change heap.nextRef + 4 < heap.nextRef + 9
    omega
  · change heap.nextRef + 5 < heap.nextRef + 9
    omega
  · change heap.nextRef + 6 < heap.nextRef + 9
    omega
  · change heap.nextRef + 7 < heap.nextRef + 9
    omega
  · change heap.nextRef + 8 < heap.nextRef + 9
    omega
  · simp [Layout.refs, emptyLayout]

theorem initialized_keys (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).keys vertex = 0 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_parents (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).parents vertex = -1 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_table (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).table vertex = -1 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_children (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).children vertex = -1 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_left (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).left vertex = 0 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_right (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).right vertex = 0 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_degrees (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).degrees vertex = 0 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_marks (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).marks vertex = 0 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem initialized_present (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).present vertex = 0 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

theorem new_heap_layout (heap : Heap) :
    (emptyLayout heap).Valid (newHeap heap) heap.nextObject := by
  exact initialization_layout (heap.allocateObject "fibonacci_heap.FibonacciHeap") heap.nextObject
    (by simp [is_FibonacciHeap])

theorem initialization_cost (heap : Heap) (queue : Ref_FibonacciHeap) :
    Heap.cost heap (initializedHeap heap queue) = (fun _ => 0) := by
  funext clock
  simp [initializedHeap, Heap.cost, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

@[simp] theorem keys_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_keys (heap.tick clock amount) queue =
      field_FibonacciHeap_keys heap queue := rfl

@[simp] theorem parents_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_parents (heap.tick clock amount) queue =
      field_FibonacciHeap_parents heap queue := rfl

@[simp] theorem children_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_children (heap.tick clock amount) queue =
      field_FibonacciHeap_children heap queue := rfl

@[simp] theorem left_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_left (heap.tick clock amount) queue =
      field_FibonacciHeap_left heap queue := rfl

@[simp] theorem right_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_right (heap.tick clock amount) queue =
      field_FibonacciHeap_right heap queue := rfl

@[simp] theorem degrees_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_degrees (heap.tick clock amount) queue =
      field_FibonacciHeap_degrees heap queue := rfl

@[simp] theorem marks_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_marks (heap.tick clock amount) queue =
      field_FibonacciHeap_marks heap queue := rfl

@[simp] theorem present_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_present (heap.tick clock amount) queue =
      field_FibonacciHeap_present heap queue := rfl

@[simp] theorem table_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_table (heap.tick clock amount) queue =
      field_FibonacciHeap_table heap queue := rfl

@[simp] theorem minimum_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_minimum (heap.tick clock amount) queue =
      field_FibonacciHeap_minimum heap queue := rfl

@[simp] theorem size_tick (heap : Heap) (clock : String) (amount : Nat)
    (queue : Ref_FibonacciHeap) :
    field_FibonacciHeap_size (heap.tick clock amount) queue =
      field_FibonacciHeap_size heap queue := rfl

def rootHeaderHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  (heap.write layout.parents vertex (-1)).write layout.marks vertex 0

def insertRingHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let after := heap.read layout.right layout.minimum
  (((heap.write layout.left vertex layout.minimum).write layout.right vertex after).write
    layout.right layout.minimum vertex).write layout.left after vertex

def addRootHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  let prepared := rootHeaderHeap heap layout vertex
  if layout.minimum < 0 then
    set_FibonacciHeap_minimum
      ((prepared.write layout.left vertex vertex).write layout.right vertex vertex) queue vertex
  else
    let linked := (insertRingHeap prepared layout vertex).tick "heap_comparisons"
    if linked.read layout.keys vertex < linked.read layout.keys layout.minimum then
      set_FibonacciHeap_minimum linked queue vertex
    else linked

theorem add_root_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    FibonacciHeap.add_root.Call heap (queue, vertex)
      (addRootHeap heap queue layout vertex) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_add_root_pc19 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_add_root_pc18 _ _ _
    (by simp [valid.readMarks, valid.marksAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_add_root_pc17 _ _ _
    (by simp [valid.readMinimum]))
  simp only [marks_write, minimum_write, valid.readParents, valid.readMarks, valid.readMinimum, Option.getD_some]
  by_cases empty : layout.minimum < 0
  · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc16_true _ _ _
      (by simp [empty]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc5 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc4 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    simp only [left_write, right_write, valid.readLeft, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc3 _ _ _ valid.object)
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc2 _ _ _)
    simpa only [addRootHeap, if_pos empty, rootHeaderHeap, left_write, right_write,
      parents_write, marks_write, valid.readParents, valid.readMarks, valid.readLeft,
      valid.readRight, Option.getD_some] using
      (Reaches.single (Step.FibonacciHeap_add_root_pc1 _ _ _))
  · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc16_false _ _ _
      (by simp [empty]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc15 _ _ _
      (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc14 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    simp only [minimum_write, right_write, valid.readMinimum, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc13 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc12 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc11 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc10 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    simp only [left_write, right_write, valid.readLeft, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc9 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc8 _ _ _
      (by simp [valid.readKeys, valid.keysAllocated]))
    simp only [keys_write, keys_tick, valid.readKeys, Option.getD_some]
    let linked := (insertRingHeap (rootHeaderHeap heap layout vertex) layout vertex).tick
      "heap_comparisons"
    by_cases smaller : linked.read layout.keys vertex < linked.read layout.keys layout.minimum
    · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc7_true _ _ _
        (by simpa [linked, insertRingHeap, rootHeaderHeap, valid.readParents,
          valid.readMarks, valid.readLeft, valid.readRight, valid.readKeys,
          valid.readMinimum] using smaller))
      apply Reaches.prepend (Step.FibonacciHeap_add_root_pc6 _ _ _ valid.object)
      apply Reaches.prepend (Step.FibonacciHeap_add_root_pc2 _ _ _)
      have effect : addRootHeap heap queue layout vertex =
          set_FibonacciHeap_minimum linked queue vertex := by
        unfold addRootHeap
        rw [if_neg empty]
        exact if_pos smaller
      rw [effect]
      simpa only [linked, insertRingHeap,
        rootHeaderHeap, left_write, right_write, parents_write, marks_write,
        minimum_write, valid.readParents, valid.readMarks, valid.readLeft,
        valid.readRight, valid.readMinimum, Option.getD_some] using
        (Reaches.single (Step.FibonacciHeap_add_root_pc1 _ _ _))
    · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc7_false _ _ _
        (by simpa [linked, insertRingHeap, rootHeaderHeap, valid.readParents,
          valid.readMarks, valid.readLeft, valid.readRight, valid.readKeys,
          valid.readMinimum] using smaller))
      apply Reaches.prepend (Step.FibonacciHeap_add_root_pc2 _ _ _)
      have effect : addRootHeap heap queue layout vertex = linked := by
        unfold addRootHeap
        rw [if_neg empty]
        exact if_neg smaller
      rw [effect]
      simpa only [linked, insertRingHeap,
        rootHeaderHeap, left_write, right_write, parents_write, marks_write,
        minimum_write, valid.readParents, valid.readMarks, valid.readLeft,
        valid.readRight, valid.readMinimum, Option.getD_some] using
        (Reaches.single (Step.FibonacciHeap_add_root_pc1 _ _ _))

theorem add_root_cost (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) :
    Heap.cost heap (addRootHeap heap queue layout vertex) =
      if layout.minimum < 0 then (fun _ => 0) else Clocks.single "heap_comparisons" 1 := by
  unfold addRootHeap
  split
  · funext clock
    simp_all [Heap.cost, rootHeaderHeap, set_FibonacciHeap_minimum]
  · dsimp only
    split <;> funext clock <;> by_cases clock = "heap_comparisons" <;>
      simp_all [Heap.cost, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        Heap.tick, Clocks.single]

theorem add_root_other_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (ref : SeqRef) (notParents : ref ≠ layout.parents)
    (notMarks : ref ≠ layout.marks) (notLeft : ref ≠ layout.left)
    (notRight : ref ≠ layout.right) (index : Int) :
    (addRootHeap heap queue layout vertex).read ref index = heap.read ref index := by
  unfold addRootHeap
  split
  · simp [rootHeaderHeap, set_FibonacciHeap_minimum, Heap.read, Heap.write,
      notParents, notMarks, notLeft, notRight]
  · dsimp only
    split <;> simp [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
      Heap.read, Heap.write, notParents, notMarks, notLeft, notRight]

theorem Layout.Valid.write (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (ref : SeqRef) (index value : Int) :
    layout.Valid (heap.write ref index value) queue := by
  exact ⟨valid.object, valid.readKeys, valid.readParents, valid.readChildren, valid.readLeft, valid.readRight, valid.readDegrees, valid.readMarks, valid.readPresent, valid.readTable, valid.readMinimum, valid.readSize, valid.keysAllocated, valid.parentsAllocated, valid.childrenAllocated, valid.leftAllocated, valid.rightAllocated, valid.degreesAllocated, valid.marksAllocated, valid.presentAllocated, valid.tableAllocated, valid.separate⟩

theorem Layout.Valid.tick (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (clock : String) (amount : Nat) :
    layout.Valid (heap.tick clock amount) queue := by
  exact ⟨valid.object, valid.readKeys, valid.readParents, valid.readChildren, valid.readLeft, valid.readRight, valid.readDegrees, valid.readMarks, valid.readPresent, valid.readTable, valid.readMinimum, valid.readSize, valid.keysAllocated, valid.parentsAllocated, valid.childrenAllocated, valid.leftAllocated, valid.rightAllocated, valid.degreesAllocated, valid.marksAllocated, valid.presentAllocated, valid.tableAllocated, valid.separate⟩

def linkHeaderHeap (heap : Heap) (layout : Layout) (child parent : Int) : Heap :=
  (heap.write layout.parents child parent).write layout.marks child 0

def linkRingHeap (heap : Heap) (layout : Layout) (child parent : Int) : Heap :=
  let first := heap.read layout.children parent
  if first < 0 then
    (heap.write layout.left child child).write layout.right child child
  else
    let before := heap.read layout.left first
    (((heap.write layout.left child before).write layout.right child first).write
      layout.right before child).write layout.left first child

def linkHeap (heap : Heap) (layout : Layout) (child parent : Int) : Heap :=
  let prepared := linkHeaderHeap heap layout child parent
  let ring := linkRingHeap prepared layout child parent
  let headed := ring.write layout.children parent child
  (headed.write layout.degrees parent (headed.read layout.degrees parent + 1)).tick "heap_links"

-- A link's compiled contract is independent of any whole-heap invariant.
-- Its callers separately establish equal degree, key order, and disjoint trees.
theorem link_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (child parent : Int) :
    FibonacciHeap.link.Call heap (queue, child, parent)
      (linkHeap heap layout child parent) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_link_pc17 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_link_pc16 _ _ _
    (by simp [valid.readMarks, valid.marksAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_link_pc15 _ _ _
    (by simp [valid.readChildren, valid.childrenAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_link_pc14 _ _ _)
  simp only [marks_write, children_write, valid.readParents, valid.readMarks,
    valid.readChildren, Option.getD_some]
  by_cases empty : (linkHeaderHeap heap layout child parent).read layout.children parent < 0
  · apply Reaches.prepend (Step.FibonacciHeap_link_pc13_true _ _ _
      (by simpa [linkHeaderHeap] using empty))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc7 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc6 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc5 _ _ _
      (by simp [valid.readChildren, valid.childrenAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc4 _ _ _
      (by simp [valid.readDegrees, valid.degreesAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc3 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_link_pc2 _ _ _)
    simp only [linkHeap, linkRingHeap, linkHeaderHeap,
      left_write, right_write, children_write, degrees_write, valid.readLeft,
      valid.readRight, valid.readChildren, valid.readDegrees, Option.getD_some]
    simp only [linkHeaderHeap] at empty
    rw [if_pos empty]
    exact Reaches.single (Step.FibonacciHeap_link_pc1 _ _ _)
  · apply Reaches.prepend (Step.FibonacciHeap_link_pc13_false _ _ _
      (by simpa [linkHeaderHeap] using empty))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc12 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc11 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc10 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc9 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc8 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    simp only [left_write, right_write, valid.readLeft, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_link_pc5 _ _ _
      (by simp [valid.readChildren, valid.childrenAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc4 _ _ _
      (by simp [valid.readDegrees, valid.degreesAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc3 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_link_pc2 _ _ _)
    simp only [linkHeap, linkRingHeap, linkHeaderHeap,
      children_write, degrees_write, valid.readChildren, valid.readDegrees, Option.getD_some]
    simp only [linkHeaderHeap] at empty
    rw [if_neg empty]
    exact Reaches.single (Step.FibonacciHeap_link_pc1 _ _ _)

theorem link_preserves_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (child parent : Int) :
    layout.Valid (linkHeap heap layout child parent) queue := by
  unfold linkHeap
  apply Layout.Valid.tick
  apply Layout.Valid.write
  apply Layout.Valid.write
  unfold linkRingHeap
  dsimp only
  split
  · repeat apply Layout.Valid.write
    exact valid
  · repeat apply Layout.Valid.write
    exact valid


theorem link_cost (heap : Heap) (layout : Layout) (child parent : Int) :
    Heap.cost heap (linkHeap heap layout child parent) = Clocks.single "heap_links" 1 := by
  unfold linkHeap linkRingHeap
  dsimp only
  split <;> funext clock <;> by_cases clock = "heap_links" <;>
    simp_all [Heap.cost, Heap.tick, linkHeaderHeap, Clocks.single]

theorem link_other_array (heap : Heap) (layout : Layout) (child parent : Int)
    (ref : SeqRef) (notParents : ref ≠ layout.parents) (notMarks : ref ≠ layout.marks)
    (notLeft : ref ≠ layout.left) (notRight : ref ≠ layout.right)
    (notChildren : ref ≠ layout.children) (notDegrees : ref ≠ layout.degrees) (index : Int) :
    (linkHeap heap layout child parent).read ref index = heap.read ref index := by
  unfold linkHeap linkRingHeap
  dsimp only
  split <;> simp [linkHeaderHeap, Heap.read, Heap.write,
    notParents, notMarks, notLeft, notRight, notChildren, notDegrees]

def cutHeaderHeap (heap : Heap) (layout : Layout) (vertex parent : Int) : Heap :=
  if heap.read layout.children parent = vertex then
    heap.write layout.children parent
      (if heap.read layout.right vertex = vertex then -1 else heap.read layout.right vertex)
  else heap

def cutTailHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) : Heap :=
  let decreased := heap.write layout.degrees parent (heap.read layout.degrees parent - 1)
  let detached := removeHeap decreased layout vertex
  (addRootHeap detached queue layout vertex).tick "heap_cuts"

def cutHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) : Heap :=
  cutTailHeap (cutHeaderHeap heap layout vertex parent) queue layout vertex parent

-- The proof composes the checked ring-removal and root-insertion contracts.
-- Their internal transitions are not revisited when a cut is verified.
theorem cut_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    FibonacciHeap.cut.Call heap (queue, vertex, parent)
      (cutHeap heap queue layout vertex parent) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  have finish (prepared : Heap) (state : State_FibonacciHeap_cut)
      (ready : layout.Valid prepared state.v0) :
      Reaches Step (.active prepared (.fn_FibonacciHeap_cut 12 state) stack)
        (resumeConfig (cutTailHeap prepared state.v0 layout state.v1 state.v2)
          (.fn_FibonacciHeap_cut ()) stack) := by
    let decreased := prepared.write layout.degrees state.v2
      (prepared.read layout.degrees state.v2 - 1)
    have decreasedValid : layout.Valid decreased state.v0 :=
      Layout.Valid.write _ _ _ ready _ _ _
    have detachedValid := remove_preserves_layout decreased state.v0 layout decreasedValid state.v1
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc12 _ _ _
      (by simp [ready.readDegrees, ready.degreesAllocated]))
    simp only [ready.readDegrees, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc11 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc10 _ _ _ ready.object)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc9 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc8 _ _ _)
    apply Reaches.trans ((remove_from_ring_summary decreased state.v0 layout
      decreasedValid state.v1).2 _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc7 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc6 _ _ _ detachedValid.object)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc5 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc4 _ _ _)
    apply Reaches.trans ((add_root_summary _ state.v0 layout detachedValid state.v1).2 _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc3 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc2 _ _ _)
    exact Reaches.single (Step.FibonacciHeap_cut_pc1 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_cut_pc18 _ _ _
    (by simp [valid.readChildren, valid.childrenAllocated]))
  by_cases head : heap.read layout.children parent = vertex
  · apply Reaches.prepend (Step.FibonacciHeap_cut_pc17_true _ _ _
      (by simp [valid.readChildren, head]))
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc16 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    by_cases singleton : heap.read layout.right vertex = vertex
    · apply Reaches.prepend (Step.FibonacciHeap_cut_pc15_true _ _ _
        (by simp [valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_cut_pc13 _ _ _
        (by simp [valid.readChildren, valid.childrenAllocated]))
      simp only [cutHeap, cutHeaderHeap, if_pos head, if_pos singleton,
        valid.readChildren, valid.readRight, Option.getD_some]
      apply finish
      exact Layout.Valid.write _ _ _ valid _ _ _
    · apply Reaches.prepend (Step.FibonacciHeap_cut_pc15_false _ _ _
        (by simp [valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_cut_pc14 _ _ _
        (by simp [valid.readRight, valid.rightAllocated, valid.readChildren,
          valid.childrenAllocated]))
      simp only [cutHeap, cutHeaderHeap, if_pos head, if_neg singleton,
        valid.readChildren, valid.readRight, Option.getD_some]
      apply finish
      exact Layout.Valid.write _ _ _ valid _ _ _
  · apply Reaches.prepend (Step.FibonacciHeap_cut_pc17_false _ _ _
      (by simp [valid.readChildren, head]))
    simp only [cutHeap, cutHeaderHeap, if_neg head, valid.readChildren, Option.getD_some]
    apply finish
    exact valid

theorem Layout.Valid.set_minimum (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (minimum : Int) :
    { layout with minimum := minimum }.Valid (set_FibonacciHeap_minimum heap queue minimum) queue := by
  constructor
  · simpa [set_FibonacciHeap_minimum, is_FibonacciHeap] using valid.object
  · simpa [field_FibonacciHeap_keys, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readKeys
  · simpa [field_FibonacciHeap_parents, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readParents
  · simpa [field_FibonacciHeap_children, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readChildren
  · simpa [field_FibonacciHeap_left, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readLeft
  · simpa [field_FibonacciHeap_right, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readRight
  · simpa [field_FibonacciHeap_degrees, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readDegrees
  · simpa [field_FibonacciHeap_marks, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readMarks
  · simpa [field_FibonacciHeap_present, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readPresent
  · simpa [field_FibonacciHeap_table, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readTable
  · exact field_FibonacciHeap_minimum_set heap queue minimum valid.object
  · simpa [field_FibonacciHeap_size, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readSize
  · exact valid.keysAllocated
  · exact valid.parentsAllocated
  · exact valid.childrenAllocated
  · exact valid.leftAllocated
  · exact valid.rightAllocated
  · exact valid.degreesAllocated
  · exact valid.marksAllocated
  · exact valid.presentAllocated
  · exact valid.tableAllocated
  · exact valid.separate

def addRootLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  if layout.minimum < 0 then { layout with minimum := vertex }
  else
    let linked := (insertRingHeap (rootHeaderHeap heap layout vertex) layout vertex).tick
      "heap_comparisons"
    if linked.read layout.keys vertex < linked.read layout.keys layout.minimum then
      { layout with minimum := vertex }
    else layout

theorem add_root_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (addRootLayout heap layout vertex).Valid (addRootHeap heap queue layout vertex) queue := by
  unfold addRootHeap addRootLayout
  dsimp only
  split
  · apply Layout.Valid.set_minimum
    repeat apply Layout.Valid.write
    exact valid
  · split
    · apply Layout.Valid.set_minimum
      apply Layout.Valid.tick
      repeat apply Layout.Valid.write
      exact valid
    · apply Layout.Valid.tick
      repeat apply Layout.Valid.write
      exact valid

def cutLayout (heap : Heap) (layout : Layout) (vertex parent : Int) : Layout :=
  let headed := cutHeaderHeap heap layout vertex parent
  let decreased := headed.write layout.degrees parent (headed.read layout.degrees parent - 1)
  addRootLayout (removeHeap decreased layout vertex) layout vertex

theorem cut_header_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    layout.Valid (cutHeaderHeap heap layout vertex parent) queue := by
  unfold cutHeaderHeap
  split
  · exact Layout.Valid.write _ _ _ valid _ _ _
  · exact valid

theorem cut_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).Valid (cutHeap heap queue layout vertex parent) queue := by
  unfold cutHeap cutTailHeap cutLayout
  apply Layout.Valid.tick
  apply add_root_layout
  apply remove_preserves_layout
  apply Layout.Valid.write
  exact cut_header_layout heap queue layout valid vertex parent

theorem add_root_parents (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex index : Int) :
    (addRootHeap heap queue layout vertex).read layout.parents index =
      if index = vertex then -1 else heap.read layout.parents index := by
  have separated : layout.parents ≠ layout.marks ∧ layout.parents ≠ layout.left ∧
      layout.parents ≠ layout.right := by
    have fresh := (List.nodup_cons.mp (List.nodup_cons.mp valid.separate).2).1
    constructor
    · intro same
      exact fresh (by simp [same])
    · constructor
      · intro same
        exact fresh (by simp [same])
      · intro same
        exact fresh (by simp [same])
  unfold addRootHeap
  split
  · simp [rootHeaderHeap, set_FibonacciHeap_minimum, Heap.read, Heap.write,
      separated.1, separated.2.1, separated.2.2]
  · dsimp only
    split <;> simp [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
      Heap.read, Heap.write, separated.1, separated.2.1, separated.2.2]

theorem cut_header_parents (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent index : Int) :
    (cutHeaderHeap heap layout vertex parent).read layout.parents index =
      heap.read layout.parents index := by
  have separate : layout.parents ≠ layout.children := by
    have fresh := (List.nodup_cons.mp (List.nodup_cons.mp valid.separate).2).1
    intro same
    exact fresh (by simp [same])
  unfold cutHeaderHeap
  split <;> simp [Heap.read, Heap.write, separate]

theorem cut_parents (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent index : Int) :
    (cutHeap heap queue layout vertex parent).read layout.parents index =
      if index = vertex then -1 else heap.read layout.parents index := by
  have separated : layout.parents ≠ layout.degrees ∧ layout.parents ≠ layout.left ∧
      layout.parents ≠ layout.right := by
    have fresh := (List.nodup_cons.mp (List.nodup_cons.mp valid.separate).2).1
    constructor
    · intro same
      exact fresh (by simp [same])
    · constructor
      · intro same
        exact fresh (by simp [same])
      · intro same
        exact fresh (by simp [same])
  let headed := cutHeaderHeap heap layout vertex parent
  let decreased := headed.write layout.degrees parent (headed.read layout.degrees parent - 1)
  have ready : layout.Valid decreased queue :=
    Layout.Valid.write _ _ _ (cut_header_layout heap queue layout valid vertex parent) _ _ _
  have detached := remove_preserves_layout decreased queue layout ready vertex
  change (addRootHeap (removeHeap decreased layout vertex) queue layout vertex).read
    layout.parents index = _
  rw [add_root_parents _ _ _ detached]
  rw [remove_other_array _ _ _ _ separated.2.1 separated.2.2]
  simp only [decreased, Heap.read_write_other_ref _ _ _ _ _ _ separated.1]
  exact congrArg (fun value => if index = vertex then -1 else value)
    (cut_header_parents heap queue layout valid vertex parent index)

@[simp] theorem add_root_layout_parents (heap : Heap) (layout : Layout) (vertex : Int) :
    (addRootLayout heap layout vertex).parents = layout.parents := by
  unfold addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem add_root_layout_marks (heap : Heap) (layout : Layout) (vertex : Int) :
    (addRootLayout heap layout vertex).marks = layout.marks := by
  unfold addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem cut_layout_parents (heap : Heap) (layout : Layout) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).parents = layout.parents := by
  simp [cutLayout]

@[simp] theorem cut_layout_marks (heap : Heap) (layout : Layout) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).marks = layout.marks := by
  simp [cutLayout]

-- Ranking every parent pointer is a strong sufficient termination premise.
-- The scoped parent-rank invariant restricts the ordering to active vertices, so unused
-- sequence cells can remain unconstrained. Cutting edges preserves either form.
def ParentRank (heap : Heap) (layout : Layout) (rank : Int → Nat) : Prop :=
  ∀ vertex, 0 ≤ heap.read layout.parents vertex →
    rank (heap.read layout.parents vertex) < rank vertex

theorem cut_parent_rank (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank)
    (vertex parent : Int) :
    ParentRank (cutHeap heap queue layout vertex parent) (cutLayout heap layout vertex parent) rank := by
  intro index nonnegative
  simp only [cut_layout_parents] at nonnegative ⊢
  rw [cut_parents heap queue layout valid vertex parent index] at nonnegative ⊢
  by_cases same : index = vertex
  · simp [same] at nonnegative
  · simpa [same] using parents index (by simpa [same] using nonnegative)

-- A source-facing description of the cascade's exact heap changes. It records
-- actual cuts and marks, independently of the compiler's temporary states.
inductive CascadeEffect (queue : Ref_FibonacciHeap) :
    Heap → Layout → Int → Heap → Layout → Nat → Prop where
  | root (heap : Heap) (layout : Layout) (vertex : Int)
      (root : heap.read layout.parents vertex < 0) :
      CascadeEffect queue heap layout vertex heap layout 0
  | mark (heap : Heap) (layout : Layout) (vertex : Int)
      (nonroot : 0 ≤ heap.read layout.parents vertex) (unmarked : heap.read layout.marks vertex = 0) :
      CascadeEffect queue heap layout vertex (heap.write layout.marks vertex 1) layout 0
  | cut {heap after : Heap} {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
      (nonroot : 0 ≤ heap.read layout.parents vertex) (marked : heap.read layout.marks vertex ≠ 0)
      (rest : CascadeEffect queue
        (cutHeap heap queue layout vertex (heap.read layout.parents vertex))
        (cutLayout heap layout vertex (heap.read layout.parents vertex))
        (heap.read layout.parents vertex) after finalLayout cuts) :
      CascadeEffect queue heap layout vertex after finalLayout (cuts + 1)

theorem cascade_effect_exists (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank)
    (vertex : Int) :
    ∃ after finalLayout cuts, CascadeEffect queue heap layout vertex after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
  have terminate : ∀ depth heap layout vertex, rank vertex = depth → layout.Valid heap queue →
      ParentRank heap layout rank →
      ∃ after finalLayout cuts, CascadeEffect queue heap layout vertex after finalLayout cuts ∧
        finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth ih =>
      intro before current node ranked ready acyclic
      by_cases root : before.read current.parents node < 0
      · exact ⟨before, current, 0, .root _ _ _ root, ready, Nat.zero_le _⟩
      have nonroot : 0 ≤ before.read current.parents node := by omega
      by_cases unmarked : before.read current.marks node = 0
      · exact ⟨before.write current.marks node 1, current, 0,
          .mark _ _ _ nonroot unmarked, Layout.Valid.write _ _ _ ready _ _ _, Nat.zero_le _⟩
      let parent := before.read current.parents node
      let nextHeap := cutHeap before queue current node parent
      let nextLayout := cutLayout before current node parent
      have descends : rank parent < depth := by
        simpa only [parent, ranked] using acyclic node nonroot
      obtain ⟨after, finalLayout, cuts, effect, finalValid, bounded⟩ :=
        ih (rank parent) descends nextHeap nextLayout parent rfl
          (cut_layout before queue current ready node parent)
          (cut_parent_rank before queue current ready rank acyclic node parent)
      refine ⟨after, finalLayout, cuts + 1, .cut nonroot unmarked effect, finalValid, ?_⟩
      omega
  exact terminate (rank vertex) heap layout vertex rfl valid parents

theorem cascade_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (vertex : Int) (cuts : Nat)
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts) :
    FibonacciHeap.cascading_cut.Call heap (queue, vertex) after () := by
  have loop : ∀ before current node final finalLayout count,
      CascadeEffect queue before current node final finalLayout count → current.Valid before queue →
      ∀ (state : State_FibonacciHeap_cascading_cut) stack,
      Reaches Step (.active before (.fn_FibonacciHeap_cascading_cut 4
        { state with v0 := queue, v1 := node, v2 := before.read current.parents node }) stack)
        (resumeConfig final (.fn_FibonacciHeap_cascading_cut ()) stack) := by
    intro before current node final finalLayout count execution
    induction execution with
    | root before current node root =>
      intro ready state stack
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc4 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc3_false _ _ _
        (by simp; omega))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc2 _ _ _)
      exact Reaches.single (Step.FibonacciHeap_cascading_cut_pc1 _ _ _)
    | mark before current node nonroot unmarked =>
      intro ready state stack
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc4 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc3_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc16 _ _ _
        (by simp [ready.readMarks, ready.marksAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc15_true _ _ _
        (by simp [ready.readMarks, unmarked]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc14 _ _ _
        (by simp [ready.readMarks, ready.marksAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc13 _ _ _)
      simp only [ready.readMarks, Option.getD_some]
      exact Reaches.single (Step.FibonacciHeap_cascading_cut_pc12 _ _ _)
    | @cut before final current finalLayout node count nonroot marked rest ih =>
      intro ready state stack
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc4 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc3_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc16 _ _ _
        (by simp [ready.readMarks, ready.marksAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc15_false _ _ _
        (by simp [ready.readMarks, marked]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc11 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc10 _ _ _ ready.object)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc9 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc8 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc7 _ _ _)
      apply Reaches.trans ((cut_summary before queue current ready node
        (before.read current.parents node)).2 _)
      have nextReady := cut_layout before queue current ready node (before.read current.parents node)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc6 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc5 _ _ _
        (by simpa [nextReady.readParents] using nextReady.parentsAllocated))
      simpa only [ready.readMarks, nextReady.readParents, Option.getD_some] using
        ih nextReady { state with t4 := decide (before.read current.parents node ≥ 0), t5 := (), t6 := queue, t7 := node, t8 := before.read current.parents node, t9 := decide (before.read current.marks node = 0) } stack
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc17 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  simpa only [valid.readParents, Option.getD_some] using
    loop heap layout vertex after finalLayout cuts effect valid {} stack

-- This is a terminating compiled execution, derived from decreasing parents;
-- it does not ask the caller to supply a transcript or a cascade result.
theorem cascading_cut_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank)
    (vertex : Int) :
    ∃ after finalLayout cuts, FibonacciHeap.cascading_cut.Call heap (queue, vertex) after () ∧
      CascadeEffect queue heap layout vertex after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
  obtain ⟨after, finalLayout, cuts, effect, ready, bounded⟩ :=
    cascade_effect_exists heap queue layout valid rank parents vertex
  exact ⟨after, finalLayout, cuts,
    cascade_effect_summary heap after queue layout finalLayout valid vertex cuts effect,
    effect, ready, bounded⟩

/-- Ordinary field observations; this description is independent of execution. -/
def snapshot (heap : Heap) (layout : Layout) : Algo2Lean.Fibonacci.Snapshot :=
  ⟨heap.read layout.keys, heap.read layout.parents, heap.read layout.children,
    heap.read layout.left, heap.read layout.right, heap.read layout.degrees,
    heap.read layout.marks, heap.read layout.present, heap.read layout.table,
    layout.minimum, layout.size⟩

/-- The queue's concrete storage realizes a finite, ordered Fibonacci forest. -/
structure QueueRep (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (forest : Algo2Lean.Fibonacci.Forest) : Prop where
  layoutValid : layout.Valid heap queue
  represented : Algo2Lean.Fibonacci.Represented (snapshot heap layout) forest

theorem initialization_representation (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    QueueRep (initializedHeap heap queue) queue (emptyLayout heap) [] := by
  refine ⟨initialization_layout heap queue valid, ?_⟩
  apply Algo2Lean.Fibonacci.Represented.empty
  · exact initialized_present heap queue
  · rfl
  · rfl
  · exact initialized_table heap queue

theorem new_heap_representation (heap : Heap) :
    QueueRep (newHeap heap) heap.nextObject (emptyLayout heap) [] := by
  exact initialization_representation (heap.allocateObject "fibonacci_heap.FibonacciHeap") heap.nextObject
    (by simp [is_FibonacciHeap])

theorem QueueRep.minimum {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (nonempty : forest ≠ []) :
    0 ≤ layout.minimum ∧ heap.read layout.present layout.minimum = 1 ∧
      ∀ vertex, heap.read layout.present vertex ≠ 0 →
        heap.read layout.keys layout.minimum ≤ heap.read layout.keys vertex :=
  rep.represented.minimum_key nonempty

theorem QueueRep.empty_iff {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest) :
    layout.minimum < 0 ↔ forest = [] := rep.represented.empty_iff


end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

/-- Reading whether a queue is empty preserves its complete heap and clocks. -/
theorem is_empty_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) :
    FibonacciHeap.is_empty.Call heap queue heap (decide (layout.size ≤ 0)) := by
  refine ⟨valid.object, ?_⟩
  intro caller
  apply Reaches.prepend (Step.FibonacciHeap_is_empty_pc2 _ _ _ (by simp [valid.readSize]))
  simp only [valid.readSize, Option.getD_some]
  exact Reaches.single (Step.FibonacciHeap_is_empty_pc1 _ _ _)

/-- The concrete emptiness test agrees with the reusable finite entry model. -/
theorem QueueRep.is_empty {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest) :
    FibonacciHeap.is_empty.Call heap queue heap forest.entries.isEmpty := by
  have size : layout.size = (forest.entries.length : Int) := rep.represented.size
  have result : decide (layout.size ≤ 0) = forest.entries.isEmpty := by
    cases entries : forest.entries with
    | nil => simp [entries] at size; simp [size]
    | cons first rest =>
      have positive : 0 < layout.size := by rw [size, entries]; simp
      simp [show ¬ layout.size ≤ 0 by omega]
  simpa only [result] using is_empty_summary heap queue layout rep.layoutValid

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

theorem Layout.Valid.set_size (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (size : Int) :
    { layout with size := size }.Valid (set_FibonacciHeap_size heap queue size) queue := by
  constructor
  · simpa [set_FibonacciHeap_size, is_FibonacciHeap] using valid.object
  · simpa [field_FibonacciHeap_keys, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readKeys
  · simpa [field_FibonacciHeap_parents, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readParents
  · simpa [field_FibonacciHeap_children, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readChildren
  · simpa [field_FibonacciHeap_left, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readLeft
  · simpa [field_FibonacciHeap_right, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readRight
  · simpa [field_FibonacciHeap_degrees, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readDegrees
  · simpa [field_FibonacciHeap_marks, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readMarks
  · simpa [field_FibonacciHeap_present, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readPresent
  · simpa [field_FibonacciHeap_table, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readTable
  · simpa [field_FibonacciHeap_minimum, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readMinimum
  · exact field_FibonacciHeap_size_set heap queue size valid.object
  · exact valid.keysAllocated
  · exact valid.parentsAllocated
  · exact valid.childrenAllocated
  · exact valid.leftAllocated
  · exact valid.rightAllocated
  · exact valid.degreesAllocated
  · exact valid.marksAllocated
  · exact valid.presentAllocated
  · exact valid.tableAllocated
  · exact valid.separate

/-- An existing handle receiving no better key keeps all storage unchanged. -/
theorem push_unchanged_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (present : heap.read layout.present vertex ≠ 0)
    (noBetter : heap.read layout.keys vertex ≤ key) :
    FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
      ((heap.tick "heap_operations").tick "heap_comparisons") () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc44 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc43 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc42_false _ _ _
    (by simpa [valid.readPresent] using present))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc27 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc26 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc25_true _ _ _
    (by simpa [valid.readKeys] using noBetter))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc24 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc23 _ _ _)

/-- An empty queue returns the sentinel and charges one public operation. -/
theorem pop_empty_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (empty : layout.minimum < 0) :
    FibonacciHeap.pop_min.Call heap queue (heap.tick "heap_operations") (-1) := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc42 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc41 _ _ _
    (by simp [valid.readMinimum]))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc40 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc39_true _ _ _
    (by simp [valid.readMinimum, empty]))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc38 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_pop_min_pc37 _ _ _)

/-- Initialize the inserted vertex and increment the public size before root insertion. -/
def insertionHeaderHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : Heap :=
  set_FibonacciHeap_size
    (((((heap.tick "heap_operations").write layout.keys vertex key).write
      layout.children vertex (-1)).write layout.degrees vertex 0).write
      layout.present vertex 1) queue (layout.size + 1)

def insertionHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : Heap :=
  addRootHeap (insertionHeaderHeap heap queue layout vertex key) queue
    { layout with size := layout.size + 1 } vertex

def insertionLayout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : Layout :=
  addRootLayout (insertionHeaderHeap heap queue layout vertex key)
    { layout with size := layout.size + 1 } vertex

theorem insertion_header_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    { layout with size := layout.size + 1 }.Valid
      (insertionHeaderHeap heap queue layout vertex key) queue := by
  apply Layout.Valid.set_size
  repeat apply Layout.Valid.write
  exact Layout.Valid.tick _ _ _ valid _ _

theorem insertion_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionLayout heap queue layout vertex key).Valid
      (insertionHeap heap queue layout vertex key) queue := by
  apply add_root_layout
  exact insertion_header_layout heap queue layout valid vertex key

/-- A new handle is initialized once, then reuses the independent root insertion proof. -/
theorem push_insert_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (absent : heap.read layout.present vertex = 0) :
    FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
      (insertionHeap heap queue layout vertex key) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc44 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc43 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc42_true _ _ _
    (by simp [valid.readPresent, absent]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc41 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc40 _ _ _
    (by simp [valid.readChildren, valid.childrenAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc39 _ _ _
    (by simp [valid.readDegrees, valid.degreesAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc38 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc37 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc36 _ _ _
    (by simp [valid.readSize]))
  simp only [keys_tick, children_write, children_tick, degrees_write,
    degrees_tick, present_write, present_tick, size_write, size_tick,
    valid.readKeys, valid.readChildren, valid.readDegrees, valid.readPresent,
    valid.readSize, Option.getD_some]
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc35 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc34 _ _ _ valid.object)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc33 _ _ _)
  have ready := insertion_header_layout heap queue layout valid vertex key
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc32 _ _ _ ready.object)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc31 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc30 _ _ _)
  apply Reaches.trans ((add_root_summary _ _ _ ready vertex).2 _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc29 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc28 _ _ _)

/-- Remove the last childless root, clear membership, and make the queue empty. -/
def singletonPopHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) : Heap :=
  let removed := removeHeap (heap.tick "heap_operations") layout layout.minimum
  set_FibonacciHeap_minimum
    (set_FibonacciHeap_size (removed.write layout.present layout.minimum 0)
      queue (layout.size - 1)) queue (-1)

theorem singleton_pop_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    { layout with minimum := -1, size := layout.size - 1 }.Valid
      (singletonPopHeap heap queue layout) queue := by
  apply Layout.Valid.set_minimum _ _ { layout with size := layout.size - 1 }
  apply Layout.Valid.set_size
  apply Layout.Valid.write
  apply remove_preserves_layout
  exact Layout.Valid.tick _ _ _ valid _ _

/-- Only the local root header is needed to execute the singleton branch. -/
theorem pop_singleton_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (nonempty : 0 ≤ layout.minimum)
    (childless : heap.read layout.children layout.minimum < 0)
    (onlyRoot : heap.read layout.right layout.minimum = layout.minimum) :
    FibonacciHeap.pop_min.Call heap queue
      (singletonPopHeap heap queue layout) layout.minimum := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc42 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc41 _ _ _
    (by simp [valid.readMinimum]))
  simp only [minimum_tick, valid.readMinimum, Option.getD_some]
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc40 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc39_false _ _ _
    (by simp; omega))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc21 _ _ _
    (by simp [valid.readChildren, valid.childrenAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc20_false _ _ _
    (by simp [valid.readChildren]; omega))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc19 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc18 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc17 _ _ _ valid.object)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc16 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc15 _ _ _)
  have ticked := Layout.Valid.tick heap queue layout valid "heap_operations" 1
  apply Reaches.trans ((remove_from_ring_summary _ _ _ ticked layout.minimum).2 _)
  have removed := remove_preserves_layout _ _ _ ticked layout.minimum
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc14 _ _ _
    (by simp [removed.readPresent, removed.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc13 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc12 _ _ _
    (by simp [removed.readSize]))
  simp only [size_write, removed.readPresent, removed.readSize, Option.getD_some]
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc11 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc10 _ _ _ removed.object)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc9 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc8_true _ _ _
    (by simp [valid.readRight, onlyRoot]))
  have resized := Layout.Valid.set_size _ _ _
    (Layout.Valid.write _ _ _ removed layout.present layout.minimum 0) (layout.size - 1)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc3 _ _ _ resized.object)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc2 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_pop_min_pc1 _ _ _)

/-- The unchanged-key branch charges exactly one operation and one comparison. -/
theorem push_unchanged_cost (heap : Heap) :
    Heap.cost heap ((heap.tick "heap_operations").tick "heap_comparisons") =
      fun clock => Clocks.single "heap_operations" 1 clock +
        Clocks.single "heap_comparisons" 1 clock := by
  funext clock
  by_cases op : clock = "heap_operations" <;>
    by_cases cmp : clock = "heap_comparisons" <;> simp_all [Heap.cost, Clocks.single]

theorem pop_empty_cost (heap : Heap) :
    Heap.cost heap (heap.tick "heap_operations") = Clocks.single "heap_operations" 1 := by
  funext clock
  by_cases op : clock = "heap_operations" <;> simp_all [Heap.cost, Clocks.single]

theorem pop_singleton_cost (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) :
    Heap.cost heap (singletonPopHeap heap queue layout) =
      Clocks.single "heap_operations" 1 := by
  funext clock
  by_cases op : clock = "heap_operations" <;>
    simp_all [singletonPopHeap, removeHeap, set_FibonacciHeap_size,
      set_FibonacciHeap_minimum, Heap.cost, Clocks.single]

theorem insertion_cost (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) :
    Heap.cost heap (insertionHeap heap queue layout vertex key) = fun clock =>
      Clocks.single "heap_operations" 1 clock +
        (if layout.minimum < 0 then 0 else Clocks.single "heap_comparisons" 1 clock) := by
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · funext clock
    by_cases op : clock = "heap_operations" <;>
      simp_all [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_size,
        set_FibonacciHeap_minimum, Heap.cost, Clocks.single]
  · split <;> funext clock <;> by_cases op : clock = "heap_operations" <;>
      by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [insertionHeaderHeap, rootHeaderHeap, insertRingHeap,
        set_FibonacciHeap_size, set_FibonacciHeap_minimum, Heap.cost, Clocks.single]

/-- A client's disjoint sequence is untouched by insertion. -/
theorem insertion_other_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    (insertionHeap heap queue layout vertex key).read ref index = heap.read ref index := by
  have different := outside
  simp only [Layout.refs, List.mem_cons, not_or] at different
  unfold insertionHeap
  rw [add_root_other_array _ _ { layout with size := layout.size + 1 } _ ref different.2.1 different.2.2.2.2.2.2.1
    different.2.2.2.1 different.2.2.2.2.1]
  simp [insertionHeaderHeap, set_FibonacciHeap_size, Heap.read, Heap.write,
    different.1, different.2.2.1, different.2.2.2.2.2.1,
    different.2.2.2.2.2.2.2.1]

/-- A client's disjoint sequence is untouched by singleton removal. -/
theorem pop_singleton_other_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    (singletonPopHeap heap queue layout).read ref index = heap.read ref index := by
  have different := outside
  simp only [Layout.refs, List.mem_cons, not_or] at different
  change ((removeHeap (heap.tick "heap_operations") layout layout.minimum).write
    layout.present layout.minimum 0).read ref index = _
  rw [Heap.read_write_other_ref _ _ _ _ _ _ different.2.2.2.2.2.2.2.1]
  rw [remove_other_array _ _ _ _ different.2.2.2.1 different.2.2.2.2.1]
  rfl

/-- Root insertion clears the mark of the added root. -/
theorem add_root_mark (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (addRootHeap heap queue layout vertex).read layout.marks vertex = 0 := by
  have separate : layout.marks ≠ layout.left ∧ layout.marks ≠ layout.right := by
    constructor <;> intro same <;> have all := valid.separate <;>
      simp_all [Layout.refs, List.nodup_cons]
  unfold addRootHeap
  split
  · simp [rootHeaderHeap, set_FibonacciHeap_minimum, Heap.read, Heap.write,
      separate.1, separate.2]
  · dsimp only
    split <;> simp [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
      Heap.read, Heap.write, separate.1, separate.2]

/-- The new vertex has the supplied key, no parent or children, and present membership. -/
theorem insertion_vertex (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    let final := insertionHeap heap queue layout vertex key
    final.read layout.keys vertex = key ∧
      final.read layout.children vertex = -1 ∧
      final.read layout.degrees vertex = 0 ∧
      final.read layout.present vertex = 1 ∧
      final.read layout.parents vertex = -1 ∧
      final.read layout.marks vertex = 0 := by
  have ready := insertion_header_layout heap queue layout valid vertex key
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold insertionHeap
    rw [add_root_other_array _ _ {layout with size := layout.size + 1} _ layout.keys (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])
      (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])]
    simp only [insertionHeaderHeap, set_FibonacciHeap_size]
    change (((((heap.tick "heap_operations").write layout.keys vertex key).write layout.children vertex (-1)).write layout.degrees vertex 0).write layout.present vertex 1).read layout.keys vertex = key
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (by intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]),
      Heap.read_write_other_ref _ _ _ _ _ _ (by intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]),
      Heap.read_write_other_ref _ _ _ _ _ _ (by intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]), Heap.read_write_same]
  · unfold insertionHeap
    rw [add_root_other_array _ _ {layout with size := layout.size + 1} _ layout.children (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])
      (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])]
    simp only [insertionHeaderHeap, set_FibonacciHeap_size]
    change (((((heap.tick "heap_operations").write layout.keys vertex key).write layout.children vertex (-1)).write layout.degrees vertex 0).write layout.present vertex 1).read layout.children vertex = -1
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (by intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]),
      Heap.read_write_other_ref _ _ _ _ _ _ (by intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]), Heap.read_write_same]
  · unfold insertionHeap
    rw [add_root_other_array _ _ {layout with size := layout.size + 1} _ layout.degrees (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])
      (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])]
    simp only [insertionHeaderHeap, set_FibonacciHeap_size]
    change (((((heap.tick "heap_operations").write layout.keys vertex key).write layout.children vertex (-1)).write layout.degrees vertex 0).write layout.present vertex 1).read layout.degrees vertex = 0
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (by intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]), Heap.read_write_same]
  · unfold insertionHeap
    rw [add_root_other_array _ _ {layout with size := layout.size + 1} _ layout.present (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])
      (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons]) (by dsimp; intro same; have all := valid.separate; simp_all [Layout.refs, List.nodup_cons])]
    simp only [insertionHeaderHeap, set_FibonacciHeap_size]
    change (((((heap.tick "heap_operations").write layout.keys vertex key).write layout.children vertex (-1)).write layout.degrees vertex 0).write layout.present vertex 1).read layout.present vertex = 1
    exact Heap.read_write_same _ _ _ _
  · exact (add_root_parents _ _ _ ready vertex vertex).trans (if_pos rfl)
  · exact add_root_mark _ _ _ ready vertex

/-- Inserting into an empty queue creates a singleton circular root ring. -/
theorem insertion_empty_ring (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) (empty : layout.minimum < 0) :
    let final := insertionHeap heap queue layout vertex key
    final.read layout.left vertex = vertex ∧ final.read layout.right vertex = vertex ∧
      (insertionLayout heap queue layout vertex key).minimum = vertex := by
  have separate : layout.left ≠ layout.right := by
    have fresh := (List.nodup_cons.mp (List.nodup_cons.mp
      (List.nodup_cons.mp (List.nodup_cons.mp valid.separate).2).2).2).1
    intro same
    exact fresh (by simp [same])
  simp [insertionHeap, addRootHeap, insertionLayout, addRootLayout, empty,
    set_FibonacciHeap_minimum, Heap.read, Heap.write, separate]

theorem insertion_size (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) :
    (insertionLayout heap queue layout vertex key).size = layout.size + 1 := by
  unfold insertionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- Singleton removal clears precisely the removed vertex's membership flag. -/
theorem pop_singleton_membership (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (index : Int) :
    (singletonPopHeap heap queue layout).read layout.present index =
      if index = layout.minimum then 0 else heap.read layout.present index := by
  have separate : layout.present ≠ layout.left ∧ layout.present ≠ layout.right := by
    constructor <;> intro same <;> have all := valid.separate <;>
      simp_all [Layout.refs, List.nodup_cons]
  change ((removeHeap (heap.tick "heap_operations") layout layout.minimum).write
    layout.present layout.minimum 0).read layout.present index = _
  by_cases same : index = layout.minimum
  · simp [same]
  · rw [Heap.read_write_other_index _ _ _ _ _ same]
    rw [remove_other_array _ _ _ _ separate.1 separate.2]
    simp [same]

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

/-- Unlink the next child from its parent's child header before promoting it. -/
def promotionHeaderHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let child := heap.read layout.children vertex
  if heap.read layout.right child = child then heap.write layout.children vertex (-1)
  else heap.write layout.children vertex (heap.read layout.right child)

def promotionDetachedHeap (heap : Heap) (layout : Layout) (vertex : Int) : Heap :=
  let child := heap.read layout.children vertex
  let headed := promotionHeaderHeap heap layout vertex
  removeHeap (headed.write layout.degrees vertex (headed.read layout.degrees vertex - 1))
    layout child

def promotionHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  (addRootHeap (promotionDetachedHeap heap layout vertex) queue layout
    (heap.read layout.children vertex)).tick "heap_promotions"

def promotionLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  addRootLayout (promotionDetachedHeap heap layout vertex) layout
    (heap.read layout.children vertex)

theorem promotion_header_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    layout.Valid (promotionHeaderHeap heap layout vertex) queue := by
  unfold promotionHeaderHeap
  dsimp only
  split <;> exact Layout.Valid.write _ _ _ valid _ _ _

theorem promotion_detached_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    layout.Valid (promotionDetachedHeap heap layout vertex) queue := by
  apply remove_preserves_layout
  apply Layout.Valid.write
  exact promotion_header_layout heap queue layout valid vertex

theorem promotion_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (promotionLayout heap layout vertex).Valid (promotionHeap heap queue layout vertex) queue := by
  apply Layout.Valid.tick
  apply add_root_layout
  exact promotion_detached_layout heap queue layout valid vertex

/-- The child-promotion loop's finite operational effect. Existence is proved
    separately from a finite child-ring invariant; no transcript is an input. -/
inductive PromotionEffect (queue : Ref_FibonacciHeap) (vertex : Int) :
    Heap → Layout → Heap → Layout → Nat → Prop where
  | done (heap : Heap) (layout : Layout)
      (childless : heap.read layout.children vertex < 0) :
      PromotionEffect queue vertex heap layout heap layout 0
  | next {heap after : Heap} {layout finalLayout : Layout} {count : Nat}
      (hasChild : 0 ≤ heap.read layout.children vertex)
      (rest : PromotionEffect queue vertex (promotionHeap heap queue layout vertex)
        (promotionLayout heap layout vertex) after finalLayout count) :
      PromotionEffect queue vertex heap layout after finalLayout (count + 1)

theorem promotion_effect_layout (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int) (count : Nat)
    (effect : PromotionEffect queue vertex heap layout after finalLayout count)
    (valid : layout.Valid heap queue) : finalLayout.Valid after queue := by
  induction effect with
  | done _ _ _ => exact valid
  | @next before after current finalLayout count hasChild rest ih =>
    exact ih (promotion_layout before queue current valid vertex)

/-- Remove the selected root, clear membership, and decrement size. -/
def extractionHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  set_FibonacciHeap_size ((removeHeap heap layout vertex).write layout.present vertex 0)
    queue (layout.size - 1)

def extractionLayout (layout : Layout) : Layout := { layout with size := layout.size - 1 }

theorem extraction_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (extractionLayout layout).Valid (extractionHeap heap queue layout vertex) queue := by
  apply Layout.Valid.set_size
  apply Layout.Valid.write
  exact remove_preserves_layout heap queue layout valid vertex

/-- A nonempty remainder calls the independently verified consolidation method.
    The constructor records that precise call contract, not a pop-min correctness claim. -/
inductive ExtractionEffect (queue : Ref_FibonacciHeap) (vertex : Int)
    (heap : Heap) (layout : Layout) : Heap → Layout → Prop where
  | last (onlyRoot : heap.read layout.right vertex = vertex) :
      ExtractionEffect queue vertex heap layout
        (set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex) queue (-1))
        { extractionLayout layout with minimum := -1 }
  | consolidate {after : Heap} {finalLayout : Layout}
      (moreRoots : heap.read layout.right vertex ≠ vertex)
      (call : FibonacciHeap.consolidate.Call
        (set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex)
          queue (heap.read layout.right vertex)) queue after ())
      (resultLayout : finalLayout.Valid after queue) :
      ExtractionEffect queue vertex heap layout after finalLayout

theorem extraction_effect_layout (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int)
    (effect : ExtractionEffect queue vertex heap layout after finalLayout)
    (valid : layout.Valid heap queue) : finalLayout.Valid after queue := by
  cases effect with
  | last onlyRoot =>
    exact Layout.Valid.set_minimum _ _ _ (extraction_layout heap queue layout valid vertex) _
  | consolidate moreRoots call resultLayout => exact resultLayout

/-- Operational pop-min effects: inspect the minimum, promote children, remove it,
    and, when required, reuse one separate consolidation call. -/
inductive PopEffect (queue : Ref_FibonacciHeap) (heap : Heap) (layout : Layout) :
    Heap → Layout → Int → Nat → Prop where
  | empty (empty : layout.minimum < 0) :
      PopEffect queue heap layout (heap.tick "heap_operations") layout (-1) 0
  | nonempty {promoted after : Heap} {promotedLayout finalLayout : Layout} {count : Nat}
      (nonempty : 0 ≤ layout.minimum)
      (promote : PromotionEffect queue layout.minimum (heap.tick "heap_operations")
        layout promoted promotedLayout count)
      (extract : ExtractionEffect queue layout.minimum promoted promotedLayout after finalLayout) :
      PopEffect queue heap layout after finalLayout layout.minimum count

/-- Every finite local promotion/extraction effect is an actual compiled call.
    The only external premise inside the effect is the separate consolidation call. -/
theorem pop_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (output : Int) (count : Nat)
    (effect : PopEffect queue heap layout after finalLayout output count) :
    FibonacciHeap.pop_min.Call heap queue after output := by
  have finish : ∀ before current final lastLayout vertex,
      ExtractionEffect queue vertex before current final lastLayout → current.Valid before queue →
      ∀ (state : State_FibonacciHeap_pop_min) stack,
      Reaches Step (.active before (.fn_FibonacciHeap_pop_min 19
        {state with v0 := queue, v1 := vertex}) stack)
        (resumeConfig final (.fn_FibonacciHeap_pop_min vertex) stack) := by
    intro before current final lastLayout vertex execution ready state stack
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc19 _ _ _
      (by simp [ready.readRight, ready.rightAllocated]))
    simp only [ready.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc18 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc17 _ _ _ ready.object)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc16 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc15 _ _ _)
    apply Reaches.trans ((remove_from_ring_summary before queue current ready vertex).2 _)
    have removed := remove_preserves_layout before queue current ready vertex
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc14 _ _ _
      (by simp [removed.readPresent, removed.presentAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc13 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc12 _ _ _
      (by simp [removed.readSize]))
    simp only [size_write, removed.readPresent, removed.readSize, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc11 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc10 _ _ _ removed.object)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc9 _ _ _)
    have resized := extraction_layout before queue current ready vertex
    cases execution with
    | last onlyRoot =>
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc8_true _ _ _
        (by simp [onlyRoot]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc3 _ _ _ resized.object)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc2 _ _ _)
      exact Reaches.single (Step.FibonacciHeap_pop_min_pc1 _ _ _)
    | consolidate moreRoots call resultLayout =>
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc8_false _ _ _
        (by simp [moreRoots]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc7 _ _ _ resized.object)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc6 _ _ _)
      have selected := Layout.Valid.set_minimum _ _ _ resized (before.read current.right vertex)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc5 _ _ _ selected.object)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc4 _ _ _)
      apply Reaches.trans (call.2 _)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc2 _ _ _)
      exact Reaches.single (Step.FibonacciHeap_pop_min_pc1 _ _ _)
  have loop : ∀ vertex before current promoted promotedLayout count,
      PromotionEffect queue vertex before current promoted promotedLayout count →
      current.Valid before queue →
      ∀ final lastLayout, ExtractionEffect queue vertex promoted promotedLayout final lastLayout →
      ∀ (state : State_FibonacciHeap_pop_min) stack,
      Reaches Step (.active before (.fn_FibonacciHeap_pop_min 21
        {state with v0 := queue, v1 := vertex}) stack)
        (resumeConfig final (.fn_FibonacciHeap_pop_min vertex) stack) := by
    intro vertex before current promoted promotedLayout count execution
    induction execution with
    | done before current childless =>
      intro ready final lastLayout extraction state stack
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc21 _ _ _
        (by simp [ready.readChildren, ready.childrenAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc20_false _ _ _
        (by simp [ready.readChildren]; omega))
      simpa only [ready.readChildren, Option.getD_some] using
        finish before current final lastLayout vertex extraction ready
        {state with t14 := decide (before.read current.children vertex ≥ 0)} stack
    | @next before promoted current promotedLayout count hasChild rest ih =>
      intro ready final lastLayout extraction state stack
      have advance : ∀ (locals : State_FibonacciHeap_pop_min),
          Reaches Step (.active (promotionHeaderHeap before current vertex)
            (.fn_FibonacciHeap_pop_min 31 {locals with v0 := queue, v1 := vertex, v2 := before.read current.children vertex}) stack)
            (resumeConfig final (.fn_FibonacciHeap_pop_min vertex) stack) := by
        intro locals
        have headed := promotion_header_layout before queue current ready vertex
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc31 _ _ _
          (by simp [headed.readDegrees, headed.degreesAllocated]))
        simp only [headed.readDegrees, Option.getD_some]
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc30 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc29 _ _ _ headed.object)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc28 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc27 _ _ _)
        have decreased := Layout.Valid.write _ _ _ headed current.degrees vertex
          ((promotionHeaderHeap before current vertex).read current.degrees vertex - 1)
        apply Reaches.trans ((remove_from_ring_summary _ _ _ decreased
          (before.read current.children vertex)).2 _)
        have detached := promotion_detached_layout before queue current ready vertex
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc26 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc25 _ _ _ detached.object)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc24 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc23 _ _ _)
        apply Reaches.trans ((add_root_summary _ _ _ detached
          (before.read current.children vertex)).2 _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc22 _ _ _)
        exact ih (promotion_layout before queue current ready vertex) final lastLayout extraction
          {locals with v2 := before.read current.children vertex, t15 := (), t16 := queue, t17 := before.read current.children vertex, t18 := (), t19 := queue, t20 := before.read current.children vertex} stack
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc21 _ _ _
        (by simp [ready.readChildren, ready.childrenAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc20_true _ _ _
        (by simp [ready.readChildren, hasChild]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc36 _ _ _
        (by simp [ready.readChildren, ready.childrenAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc35 _ _ _
        (by simp [ready.readRight, ready.rightAllocated]))
      simp only [ready.readChildren, ready.readRight, Option.getD_some]
      by_cases onlyChild : before.read current.right (before.read current.children vertex) =
          before.read current.children vertex
      · apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc34_true _ _ _
          (by simp [onlyChild]))
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc32 _ _ _
          (by simp [ready.readChildren, ready.childrenAllocated]))
        simpa only [promotionHeaderHeap, if_pos onlyChild, ready.readChildren, Option.getD_some] using
          advance {state with t14 := decide (before.read current.children vertex ≥ 0), t21 := decide (before.read current.right (before.read current.children vertex) = before.read current.children vertex)}
      · apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc34_false _ _ _
          (by simp [onlyChild]))
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc33 _ _ _
          (by simp [ready.readChildren, ready.childrenAllocated, ready.readRight, ready.rightAllocated]))
        simpa only [promotionHeaderHeap, if_neg onlyChild, ready.readChildren,
          ready.readRight, Option.getD_some] using
          advance {state with t14 := decide (before.read current.children vertex ≥ 0), t21 := decide (before.read current.right (before.read current.children vertex) = before.read current.children vertex)}
  cases effect with
  | empty empty => exact pop_empty_summary heap queue layout valid empty
  | @nonempty promoted after promotedLayout finalLayout count nonempty promote extract =>
    refine ⟨valid.object, ?_⟩
    intro stack
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc42 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc41 _ _ _
      (by simp [valid.readMinimum]))
    simp only [minimum_tick, valid.readMinimum, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc40 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc39_false _ _ _
      (by simp; omega))
    exact loop layout.minimum (heap.tick "heap_operations") layout promoted promotedLayout count
      promote (Layout.Valid.tick _ _ _ valid _ _) after finalLayout extract
      {t22 := decide (layout.minimum < 0)} stack

theorem pop_effect_layout (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (output : Int) (count : Nat)
    (effect : PopEffect queue heap layout after finalLayout output count) :
    finalLayout.Valid after queue := by
  cases effect with
  | empty empty => exact Layout.Valid.tick _ _ _ valid _ _
  | @nonempty promoted after promotedLayout finalLayout count nonempty promote extract =>
    exact extraction_effect_layout _ _ _ _ _ _ extract
      (promotion_effect_layout _ _ _ _ _ _ _ promote (Layout.Valid.tick _ _ _ valid _ _))

def lowerKeyHeap (heap : Heap) (layout : Layout) (vertex key : Int) : Heap :=
  ((heap.tick "heap_operations").tick "heap_comparisons").write layout.keys vertex key

def finishDecreaseHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : Heap :=
  let compared := heap.tick "heap_comparisons"
  if heap.read layout.keys vertex < heap.read layout.keys layout.minimum then
    set_FibonacciHeap_minimum compared queue vertex
  else compared

def finishDecreaseLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  if heap.read layout.keys vertex < heap.read layout.keys layout.minimum then
    { layout with minimum := vertex }
  else layout

theorem lower_key_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    layout.Valid (lowerKeyHeap heap layout vertex key) queue := by
  apply Layout.Valid.write
  apply Layout.Valid.tick
  apply Layout.Valid.tick
  exact valid

theorem lower_key_parent_rank (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank)
    (vertex key : Int) : ParentRank (lowerKeyHeap heap layout vertex key) layout rank := by
  have separate : layout.parents ≠ layout.keys := by
    have fresh := (List.nodup_cons.mp valid.separate).1
    intro same
    exact fresh (by simp [same])
  simpa [ParentRank, lowerKeyHeap, Heap.read, Heap.write, separate] using parents

theorem finish_decrease_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (finishDecreaseLayout heap layout vertex).Valid (finishDecreaseHeap heap queue layout vertex) queue := by
  unfold finishDecreaseHeap finishDecreaseLayout
  split
  · apply Layout.Valid.set_minimum
    exact Layout.Valid.tick _ _ _ valid _ _
  · exact Layout.Valid.tick _ _ _ valid _ _

theorem CascadeEffect.valid {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts)
    (valid : layout.Valid heap queue) : finalLayout.Valid after queue := by
  induction effect with
  | root => exact valid
  | mark => exact Layout.Valid.write _ _ _ valid _ _ _
  | cut nonroot marked rest ih =>
    exact ih (cut_layout _ _ _ valid _ _)

-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.
inductive DecreaseEffect (queue : Ref_FibonacciHeap) (vertex key : Int) :
    Heap → Layout → Heap → Layout → Nat → Prop where
  | root (heap : Heap) (layout : Layout) (root : heap.read layout.parents vertex < 0) :
      DecreaseEffect queue vertex key heap layout
        (finishDecreaseHeap heap queue layout vertex) (finishDecreaseLayout heap layout vertex) 0
  | ordered (heap : Heap) (layout : Layout) (nonroot : 0 ≤ heap.read layout.parents vertex)
      (ordered : heap.read layout.keys (heap.read layout.parents vertex) ≤ key) :
      DecreaseEffect queue vertex key heap layout
        (finishDecreaseHeap (heap.tick "heap_comparisons") queue layout vertex)
        (finishDecreaseLayout (heap.tick "heap_comparisons") layout vertex) 0
  | cut {heap after : Heap} {layout finalLayout : Layout} {cuts : Nat}
      (nonroot : 0 ≤ heap.read layout.parents vertex)
      (unordered : key < heap.read layout.keys (heap.read layout.parents vertex))
      (rest : CascadeEffect queue
        (cutHeap (heap.tick "heap_comparisons") queue layout vertex (heap.read layout.parents vertex))
        (cutLayout (heap.tick "heap_comparisons") layout vertex (heap.read layout.parents vertex))
        (heap.read layout.parents vertex) after finalLayout cuts) :
      DecreaseEffect queue vertex key heap layout
        (finishDecreaseHeap after queue finalLayout vertex)
        (finishDecreaseLayout after finalLayout vertex) (cuts + 1)

theorem decrease_effect_exists (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank)
    (vertex key : Int) :
    ∃ after finalLayout cuts, DecreaseEffect queue vertex key heap layout after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
  by_cases root : heap.read layout.parents vertex < 0
  · exact ⟨_, _, 0, .root _ _ root, finish_decrease_layout _ _ _ valid _, Nat.zero_le _⟩
  have nonroot : 0 ≤ heap.read layout.parents vertex := by omega
  by_cases ordered : heap.read layout.keys (heap.read layout.parents vertex) ≤ key
  · exact ⟨_, _, 0, .ordered _ _ nonroot ordered,
      finish_decrease_layout _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _, Nat.zero_le _⟩
  have unordered : key < heap.read layout.keys (heap.read layout.parents vertex) := by omega
  let compared := heap.tick "heap_comparisons"
  let parent := heap.read layout.parents vertex
  have ready : layout.Valid compared queue := Layout.Valid.tick _ _ _ valid _ _
  have ranked : ParentRank compared layout rank := parents
  obtain ⟨after, finalLayout, cuts, effect, finalValid, bounded⟩ :=
    cascade_effect_exists (cutHeap compared queue layout vertex parent) queue
      (cutLayout compared layout vertex parent) (cut_layout _ _ _ ready _ _) rank
      (cut_parent_rank _ _ _ ready rank ranked _ _) parent
  refine ⟨_, _, cuts + 1, .cut nonroot unordered effect,
    finish_decrease_layout _ _ _ finalValid _, ?_⟩
  have shorter := parents vertex nonroot
  change cuts ≤ rank (heap.read layout.parents vertex) at bounded
  omega

theorem decrease_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (vertex key : Int)
    (present : heap.read layout.present vertex ≠ 0) (smaller : key < heap.read layout.keys vertex)
    (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) :
    FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () := by
  have finish (prepared : Heap) (current : Layout) (ready : current.Valid prepared queue)
      (state : State_FibonacciHeap_push_or_decrease) (stack : Stack) :
      Reaches Step (.active prepared (.fn_FibonacciHeap_push_or_decrease 6
        { state with v0 := queue, v1 := vertex }) stack)
        (resumeConfig (finishDecreaseHeap prepared queue current vertex)
          (.fn_FibonacciHeap_push_or_decrease ()) stack) := by
    apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc6 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc5 _ _ _
      (by simp [ready.readKeys, ready.readMinimum, ready.keysAllocated]))
    by_cases lower : prepared.read current.keys vertex < prepared.read current.keys current.minimum
    · apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc4_true _ _ _
        (by simp [ready.readKeys, ready.readMinimum, lower]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc3 _ _ _ ready.object)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc2 _ _ _)
      simp only [finishDecreaseHeap, if_pos lower]
      exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc1 _ _ _)
    · apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc4_false _ _ _
        (by simp [ready.readKeys, ready.readMinimum, lower]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc2 _ _ _)
      simp only [finishDecreaseHeap, if_neg lower]
      exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc1 _ _ _)
  have tail : ∀ prepared current final finalLayout count,
      DecreaseEffect queue vertex key prepared current final finalLayout count →
      current.Valid prepared queue → ∀ (state : State_FibonacciHeap_push_or_decrease) stack,
      Reaches Step (.active prepared (.fn_FibonacciHeap_push_or_decrease 20
        { state with v0 := queue, v1 := vertex, v2 := key, v3 := prepared.read current.parents vertex }) stack)
        (resumeConfig final (.fn_FibonacciHeap_push_or_decrease ()) stack) := by
    intro prepared current final finalLayout count execution ready state stack
    cases execution with
    | root prepared root =>
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc20 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc19_false _ _ _ (by simp; omega))
      exact finish prepared current ready
        { state with v2 := key, v3 := prepared.read current.parents vertex, t6 := decide (prepared.read current.parents vertex ≥ 0) } stack
    | ordered prepared nonroot ordered =>
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc20 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc19_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc18 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc17 _ _ _
        (by simp [ready.readKeys, ready.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc16_false _ _ _
        (by simp [ready.readKeys]; omega))
      simpa only [keys_tick, ready.readKeys, Option.getD_some, Heap.read_tick] using
        finish (prepared.tick "heap_comparisons") current (Layout.Valid.tick _ _ _ ready _ _)
          { state with v2 := key, v3 := prepared.read current.parents vertex, t6 := decide (prepared.read current.parents vertex ≥ 0), t7 := decide (key < prepared.read current.keys (prepared.read current.parents vertex)) } stack
    | @cut middle _ middleLayout count nonroot unordered cascade =>
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc20 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc19_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc18 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc17 _ _ _
        (by simp [ready.readKeys, ready.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc16_true _ _ _
        (by simp [ready.readKeys, unordered]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc15 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc14 _ _ _ ready.object)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc13 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc12 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc11 _ _ _)
      have comparedReady := Layout.Valid.tick _ _ _ ready "heap_comparisons" 1
      apply Reaches.trans ((cut_summary _ queue current comparedReady vertex
        (prepared.read current.parents vertex)).2 _)
      have cutReady := cut_layout _ queue current comparedReady vertex
        (prepared.read current.parents vertex)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc10 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc9 _ _ _ cutReady.object)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc8 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc7 _ _ _)
      apply Reaches.trans ((cascade_effect_summary _ middle queue _ middleLayout cutReady
        (prepared.read current.parents vertex) count cascade).2 _)
      simpa only [keys_tick, ready.readKeys, Option.getD_some, Heap.read_tick] using
        finish middle middleLayout (cascade.valid cutReady)
          { state with v2 := key, v3 := prepared.read current.parents vertex, t6 := decide (prepared.read current.parents vertex ≥ 0), t7 := decide (key < prepared.read current.keys (prepared.read current.parents vertex)), t8 := (), t9 := queue, t10 := prepared.read current.parents vertex, t11 := (), t12 := queue, t13 := vertex, t14 := prepared.read current.parents vertex } stack
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc44 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc43 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc42_false _ _ _
    (by simp [valid.readPresent, present]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc27 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc26 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc25_false _ _ _
    (by simp [valid.readKeys]; omega))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc22 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc21 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  simpa only [lowerKeyHeap, keys_tick, parents_write, parents_tick, valid.readKeys,
    valid.readParents, valid.readPresent, present_tick, Option.getD_some, Heap.read_tick] using
    tail (lowerKeyHeap heap layout vertex key) layout after finalLayout cuts effect
      (lower_key_layout _ _ _ valid _ _)
      { t15 := decide (key ≥ heap.read layout.keys vertex),
        t17 := decide (heap.read layout.present vertex = 0) } stack

theorem push_decrease_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank)
    (vertex key : Int) (present : heap.read layout.present vertex ≠ 0)
    (smaller : key < heap.read layout.keys vertex) :
    ∃ after finalLayout cuts, FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key) layout after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
  obtain ⟨after, finalLayout, cuts, effect, ready, bounded⟩ :=
    decrease_effect_exists (lowerKeyHeap heap layout vertex key) queue layout
      (lower_key_layout _ _ _ valid _ _) rank (lower_key_parent_rank _ _ _ valid rank parents _ _) vertex key
  exact ⟨after, finalLayout, cuts,
    decrease_effect_summary heap after queue layout finalLayout valid vertex key present smaller cuts effect,
    effect, ready, bounded⟩


theorem add_root_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (clock : String) :
    (addRootHeap heap queue layout vertex).clocks clock = heap.clocks clock +
      Clocks.single "heap_comparisons" (if layout.minimum < 0 then 0 else 1) clock := by
  unfold addRootHeap
  split
  · simp_all [rootHeaderHeap, set_FibonacciHeap_minimum, Clocks.single]
  · dsimp only
    split <;> by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum, Clocks.single]

/-- A cut changes only two clocks; the root insertion needs at most one comparison. -/
theorem cut_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) (clock : String) :
    (cutHeap heap queue layout vertex parent).clocks clock = heap.clocks clock +
      Clocks.single "heap_cuts" 1 clock +
      Clocks.single "heap_comparisons" (if layout.minimum < 0 then 0 else 1) clock := by
  have header : (cutHeaderHeap heap layout vertex parent).clocks clock = heap.clocks clock := by
    unfold cutHeaderHeap
    split <;> rfl
  unfold cutHeap cutTailHeap
  dsimp only
  simp only [Heap.tick]
  rw [add_root_clocks]
  by_cases cut : clock = "heap_cuts" <;>
    simp_all [removeHeap, Clocks.single, Nat.add_comm]

/-- Cascades perform exactly their recorded cuts, at most that many comparisons,
    and leave every other clock unchanged. -/
theorem CascadeEffect.clocks {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts) :
    ∃ comparisons, comparisons ≤ cuts ∧ ∀ clock,
      after.clocks clock = heap.clocks clock + Clocks.single "heap_cuts" cuts clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  induction effect with
  | root => exact ⟨0, by omega, by intro clock; simp [Clocks.single]⟩
  | mark => exact ⟨0, by omega, by intro clock; simp [Clocks.single]⟩
  | @cut before after current final node count nonroot marked rest ih =>
    obtain ⟨comparisons, bounded, equation⟩ := ih
    refine ⟨comparisons + (if current.minimum < 0 then 0 else 1), ?_, ?_⟩
    · split <;> omega
    · intro clock
      rw [equation, cut_clocks]
      by_cases cut : clock = "heap_cuts" <;> by_cases cmp : clock = "heap_comparisons" <;>
        simp_all [Clocks.single] <;> omega

/-- Cutting or marking never introduces a parent edge, so the same rank continues
    to justify termination of later cascades. -/
theorem CascadeEffect.parent_rank {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank) :
    ParentRank after finalLayout rank := by
  induction effect with
  | root => exact parents
  | @mark before current node nonroot unmarked =>
    have separate : current.parents ≠ current.marks := by
      intro same
      have all := valid.separate
      simp_all [Layout.refs, List.nodup_cons]
    simpa [ParentRank, Heap.read, Heap.write, separate] using parents
  | cut nonroot marked rest ih =>
    exact ih (cut_layout _ _ _ valid _ _) (cut_parent_rank _ _ _ valid rank parents _ _)

/-- A caller's disjoint sequence is unchanged by a cut. -/
theorem cut_other_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    (cutHeap heap queue layout vertex parent).read ref index = heap.read ref index := by
  have different := outside
  simp only [Layout.refs, List.mem_cons, not_or] at different
  unfold cutHeap cutTailHeap
  change (addRootHeap _ queue layout vertex).read ref index = _
  rw [add_root_other_array _ _ _ _ _ different.2.1 different.2.2.2.2.2.2.1
    different.2.2.2.1 different.2.2.2.2.1]
  rw [remove_other_array _ _ _ _ different.2.2.2.1 different.2.2.2.2.1]
  rw [Heap.read_write_other_ref _ _ _ _ _ _ different.2.2.2.2.2.1]
  unfold cutHeaderHeap
  split <;> simp [Heap.read, Heap.write, different.2.2.1]

@[simp] theorem add_root_layout_refs (heap : Heap) (layout : Layout) (vertex : Int) :
    (addRootLayout heap layout vertex).refs = layout.refs := by
  unfold addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem cut_layout_refs (heap : Heap) (layout : Layout) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).refs = layout.refs := by simp [cutLayout]

theorem CascadeEffect.other_array {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts)
    (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    after.read ref index = heap.read ref index := by
  induction effect with
  | root => rfl
  | @mark before current node nonroot unmarked =>
    have separate : ref ≠ current.marks := by
      intro same
      exact outside (by simp [Layout.refs, same])
    exact Heap.read_write_other_ref _ _ _ _ _ _ separate
  | cut nonroot marked rest ih =>
    rw [ih (by simpa using outside)]
    exact cut_other_array _ _ _ _ _ _ outside _

theorem finish_decrease_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (clock : String) :
    (finishDecreaseHeap heap queue layout vertex).clocks clock =
      heap.clocks clock + Clocks.single "heap_comparisons" 1 clock := by
  unfold finishDecreaseHeap
  split <;> by_cases same : clock = "heap_comparisons" <;>
    simp_all [set_FibonacciHeap_minimum, Clocks.single]

/-- Full decrease has constant overhead plus one cut and at most one comparison
    for each removed parent edge. -/
theorem DecreaseEffect.clocks {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (effect : DecreaseEffect queue vertex key heap layout after finalLayout cuts) :
    ∃ comparisons, comparisons ≤ cuts + 2 ∧ ∀ clock,
      after.clocks clock = heap.clocks clock + Clocks.single "heap_cuts" cuts clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  cases effect with
  | root =>
    refine ⟨1, by omega, ?_⟩
    intro clock
    simp [finish_decrease_clocks, Clocks.single]
  | ordered =>
    refine ⟨2, by omega, ?_⟩
    intro clock
    rw [finish_decrease_clocks]
    by_cases same : clock = "heap_comparisons" <;> simp_all [Clocks.single] <;> omega
  | @cut middle _ middleLayout count nonroot unordered cascade =>
    obtain ⟨comparisons, bounded, equation⟩ := cascade.clocks
    refine ⟨comparisons + (if layout.minimum < 0 then 0 else 1) + 2, ?_, ?_⟩
    · split <;> omega
    · intro clock
      rw [finish_decrease_clocks, equation, cut_clocks]
      by_cases cut : clock = "heap_cuts" <;> by_cases cmp : clock = "heap_comparisons" <;>
        simp_all [Clocks.single] <;> omega

@[simp] theorem finish_decrease_layout_refs (heap : Heap) (layout : Layout) (vertex : Int) :
    (finishDecreaseLayout heap layout vertex).refs = layout.refs := by
  unfold finishDecreaseLayout
  split <;> rfl

theorem finish_decrease_parent_rank (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (rank : Int → Nat) (parents : ParentRank heap layout rank) (vertex : Int) :
    ParentRank (finishDecreaseHeap heap queue layout vertex) (finishDecreaseLayout heap layout vertex) rank := by
  unfold finishDecreaseHeap finishDecreaseLayout
  split <;> exact parents

theorem DecreaseEffect.parent_rank {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (effect : DecreaseEffect queue vertex key heap layout after finalLayout cuts)
    (valid : layout.Valid heap queue) (rank : Int → Nat) (parents : ParentRank heap layout rank) :
    ParentRank after finalLayout rank := by
  cases effect with
  | root => exact finish_decrease_parent_rank _ _ _ rank parents _
  | ordered => exact finish_decrease_parent_rank (heap.tick "heap_comparisons") queue layout rank parents vertex
  | cut nonroot unordered cascade =>
    apply finish_decrease_parent_rank
    apply cascade.parent_rank (cut_layout _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _) rank
    exact cut_parent_rank _ _ _ (Layout.Valid.tick _ _ _ valid _ _) rank parents _ _

theorem finish_decrease_read (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (ref : SeqRef) (index : Int) :
    (finishDecreaseHeap heap queue layout vertex).read ref index = heap.read ref index := by
  unfold finishDecreaseHeap
  split <;> rfl

theorem DecreaseEffect.other_array {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (effect : DecreaseEffect queue vertex key heap layout after finalLayout cuts)
    (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    after.read ref index = heap.read ref index := by
  cases effect with
  | root => exact finish_decrease_read _ _ _ _ _ _
  | ordered => exact finish_decrease_read _ _ _ _ _ _
  | cut nonroot unordered cascade =>
    rw [finish_decrease_read, cascade.other_array ref (by simpa using outside) index]
    exact cut_other_array _ _ _ _ _ _ outside _

/-- Public strict decrease charges one operation, exactly the cuts, and at most
    cuts+3 comparisons. All remaining clocks have zero cost. -/
theorem push_decrease_cost (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) :
    ∃ comparisons, comparisons ≤ cuts + 3 ∧ Heap.cost heap after = fun clock =>
      Clocks.single "heap_operations" 1 clock + Clocks.single "heap_cuts" cuts clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  obtain ⟨comparisons, bounded, equation⟩ := effect.clocks
  refine ⟨comparisons + 1, by omega, ?_⟩
  funext clock
  unfold Heap.cost
  rw [equation]
  by_cases op : clock = "heap_operations" <;> by_cases cut : clock = "heap_cuts" <;>
    by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [lowerKeyHeap, Clocks.single] <;> omega

theorem push_decrease_other_array (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts)
    (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    after.read ref index = heap.read ref index := by
  rw [effect.other_array ref outside index]
  have separate : ref ≠ layout.keys := by
    intro same
    exact outside (by simp [Layout.refs, same])
  exact Heap.read_write_other_ref _ _ _ _ _ _ separate


/-- Only vertices in the chosen active domain need a parent ranking. Unused
    sequence cells remain entirely unconstrained. -/
def ScopedParentRank (heap : Heap) (layout : Layout) (active : Int → Prop)
    (rank : Int → Nat) : Prop :=
  ∀ vertex, active vertex → 0 ≤ heap.read layout.parents vertex →
    active (heap.read layout.parents vertex) ∧
      rank (heap.read layout.parents vertex) < rank vertex

theorem cut_scoped_parent_rank (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (active : Int → Prop) (rank : Int → Nat)
    (parents : ScopedParentRank heap layout active rank) (vertex parent : Int) :
    ScopedParentRank (cutHeap heap queue layout vertex parent)
      (cutLayout heap layout vertex parent) active rank := by
  intro index member nonnegative
  simp only [cut_layout_parents] at nonnegative ⊢
  rw [cut_parents heap queue layout valid vertex parent index] at nonnegative ⊢
  by_cases same : index = vertex
  · simp [same] at nonnegative
  · simpa [same] using parents index member (by simpa [same] using nonnegative)

theorem lower_key_scoped_parent_rank (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (active : Int → Prop) (rank : Int → Nat)
    (parents : ScopedParentRank heap layout active rank) (vertex key : Int) :
    ScopedParentRank (lowerKeyHeap heap layout vertex key) layout active rank := by
  have separate : layout.parents ≠ layout.keys := by
    have fresh := (List.nodup_cons.mp valid.separate).1
    intro same
    exact fresh (by simp [same])
  simpa [ScopedParentRank, lowerKeyHeap, Heap.read, Heap.write, separate] using parents

/-- A finite active parent forest suffices for cascade termination. -/
theorem cascade_effect_exists_scoped (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (active : Int → Prop) (rank : Int → Nat)
    (parents : ScopedParentRank heap layout active rank) (vertex : Int) (member : active vertex) :
    ∃ after finalLayout cuts, CascadeEffect queue heap layout vertex after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
  have terminate : ∀ depth heap layout vertex, rank vertex = depth → layout.Valid heap queue →
      ScopedParentRank heap layout active rank → active vertex →
      ∃ after finalLayout cuts, CascadeEffect queue heap layout vertex after finalLayout cuts ∧
        finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth ih =>
      intro before current node ranked ready acyclic member
      by_cases root : before.read current.parents node < 0
      · exact ⟨before, current, 0, .root _ _ _ root, ready, Nat.zero_le _⟩
      have nonroot : 0 ≤ before.read current.parents node := by omega
      by_cases unmarked : before.read current.marks node = 0
      · exact ⟨before.write current.marks node 1, current, 0,
          .mark _ _ _ nonroot unmarked, Layout.Valid.write _ _ _ ready _ _ _, Nat.zero_le _⟩
      let parent := before.read current.parents node
      let nextHeap := cutHeap before queue current node parent
      let nextLayout := cutLayout before current node parent
      have next := acyclic node member nonroot
      have descends : rank parent < depth := by
        simpa only [parent, ranked] using next.2
      obtain ⟨after, finalLayout, cuts, effect, finalValid, bounded⟩ :=
        ih (rank parent) descends nextHeap nextLayout parent rfl
          (cut_layout before queue current ready node parent)
          (cut_scoped_parent_rank before queue current ready active rank acyclic node parent) next.1
      refine ⟨after, finalLayout, cuts + 1, .cut nonroot unmarked effect, finalValid, ?_⟩
      omega
  exact terminate (rank vertex) heap layout vertex rfl valid parents member

theorem decrease_effect_exists_scoped (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (active : Int → Prop) (rank : Int → Nat)
    (parents : ScopedParentRank heap layout active rank) (vertex key : Int) (member : active vertex) :
    ∃ after finalLayout cuts, DecreaseEffect queue vertex key heap layout after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
  by_cases root : heap.read layout.parents vertex < 0
  · exact ⟨_, _, 0, .root _ _ root, finish_decrease_layout _ _ _ valid _, Nat.zero_le _⟩
  have nonroot : 0 ≤ heap.read layout.parents vertex := by omega
  by_cases ordered : heap.read layout.keys (heap.read layout.parents vertex) ≤ key
  · exact ⟨_, _, 0, .ordered _ _ nonroot ordered,
      finish_decrease_layout _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _, Nat.zero_le _⟩
  have unordered : key < heap.read layout.keys (heap.read layout.parents vertex) := by omega
  let compared := heap.tick "heap_comparisons"
  let parent := heap.read layout.parents vertex
  have ready : layout.Valid compared queue := Layout.Valid.tick _ _ _ valid _ _
  have ranked : ScopedParentRank compared layout active rank := parents
  have next := parents vertex member nonroot
  obtain ⟨after, finalLayout, cuts, effect, finalValid, bounded⟩ :=
    cascade_effect_exists_scoped (cutHeap compared queue layout vertex parent) queue
      (cutLayout compared layout vertex parent) (cut_layout _ _ _ ready _ _) active rank
      (cut_scoped_parent_rank _ _ _ ready active rank ranked _ _) parent next.1
  refine ⟨_, _, cuts + 1, .cut nonroot unordered effect,
    finish_decrease_layout _ _ _ finalValid _, ?_⟩
  change cuts ≤ rank (heap.read layout.parents vertex) at bounded
  omega

/-- This public termination contract requires no facts about unused handles. -/
theorem push_decrease_summary_scoped (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (active : Int → Prop) (rank : Int → Nat)
    (parents : ScopedParentRank heap layout active rank) (vertex key : Int)
    (member : active vertex) (present : heap.read layout.present vertex ≠ 0)
    (smaller : key < heap.read layout.keys vertex) :
    ∃ after finalLayout cuts,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
        layout after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ rank vertex := by
  obtain ⟨after, finalLayout, cuts, effect, ready, bounded⟩ :=
    decrease_effect_exists_scoped (lowerKeyHeap heap layout vertex key) queue layout
      (lower_key_layout _ _ _ valid _ _) active rank
      (lower_key_scoped_parent_rank _ _ _ valid active rank parents _ _) vertex key member
  exact ⟨after, finalLayout, cuts,
    decrease_effect_summary heap after queue layout finalLayout valid vertex key present smaller cuts effect,
    effect, ready, bounded⟩

end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

@[simp] theorem promotion_layout_refs (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).refs = layout.refs := by
  exact add_root_layout_refs _ _ _

theorem promotion_layout_nonempty (heap : Heap) (layout : Layout) (vertex : Int)
    (nonempty : 0 ≤ layout.minimum) (hasChild : 0 ≤ heap.read layout.children vertex) :
    0 ≤ (promotionLayout heap layout vertex).minimum := by
  unfold promotionLayout addRootLayout
  rw [if_neg (by omega)]
  dsimp only
  split
  · exact hasChild
  · exact nonempty

/-- A promotion in a nonempty queue charges one promotion and one key comparison. -/
theorem promotion_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (nonempty : 0 ≤ layout.minimum) (clock : String) :
    (promotionHeap heap queue layout vertex).clocks clock = heap.clocks clock +
      Clocks.single "heap_promotions" 1 clock + Clocks.single "heap_comparisons" 1 clock := by
  have headerClocks : (promotionHeaderHeap heap layout vertex).clocks = heap.clocks := by
    unfold promotionHeaderHeap
    dsimp only
    split <;> rfl
  unfold promotionHeap addRootHeap
  rw [if_neg (by omega)]
  dsimp only
  split <;> by_cases promotion : clock = "heap_promotions" <;>
    by_cases comparison : clock = "heap_comparisons" <;>
    simp [promotionDetachedHeap, rootHeaderHeap, insertRingHeap, headerClocks,
      removeHeap, set_FibonacciHeap_minimum, Clocks.single, Heap.tick, promotion, comparison, Nat.add_comm]

theorem promotion_effect_clocks (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int) (count : Nat)
    (effect : PromotionEffect queue vertex heap layout after finalLayout count)
    (nonempty : 0 ≤ layout.minimum) (clock : String) :
    after.clocks clock = heap.clocks clock + count *
      (Clocks.single "heap_promotions" 1 clock + Clocks.single "heap_comparisons" 1 clock) := by
  induction effect with
  | done _ _ _ => simp
  | @next before after current finalLayout count hasChild rest ih =>
    rw [ih (promotion_layout_nonempty before current vertex nonempty hasChild),
      promotion_clocks before queue current vertex nonempty clock]
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem promotion_effect_cost (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int) (count : Nat)
    (effect : PromotionEffect queue vertex heap layout after finalLayout count)
    (nonempty : 0 ≤ layout.minimum) :
    Heap.cost heap after = fun clock => count *
      (Clocks.single "heap_promotions" 1 clock + Clocks.single "heap_comparisons" 1 clock) := by
  funext clock
  simp only [Heap.cost, promotion_effect_clocks _ _ _ _ _ _ _ effect nonempty]
  omega

/-- Valid compiled calls never decrease a clock, including consolidation's nested calls. -/
theorem consolidation_clocks_monotone (heap after : Heap) (queue : Ref_FibonacciHeap)
    (call : FibonacciHeap.consolidate.Call heap queue after ()) (clock : String) :
    heap.clocks clock ≤ after.clocks clock := by
  have resumeHeap (heap : Heap) (result : Result) (stack : Stack) :
      (resumeConfig heap result stack).heap = heap := by cases stack <;> rfl
  have transitions : ∀ before after, Step before after →
      before.heap.clocks clock ≤ after.heap.clocks clock := by
    intro before after transition
    cases transition <;> (try simp only [resumeHeap]) <;> simp [Config.heap,
      set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children,
      set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees,
      set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table,
      set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.tick] <;> split <;> omega
  exact (call.2 []).invariant (fun state => heap.clocks clock ≤ state.heap.clocks clock)
    (Nat.le_refl _) (fun before after step earlier => Nat.le_trans earlier (transitions before after step))

theorem extraction_effect_clocks_monotone (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int)
    (effect : ExtractionEffect queue vertex heap layout after finalLayout) (clock : String) :
    heap.clocks clock ≤ after.clocks clock := by
  cases effect with
  | last onlyRoot => exact Nat.le_refl _
  | consolidate moreRoots call resultLayout =>
    exact consolidation_clocks_monotone _ _ _ call clock

/-- Extraction itself charges no clock; its remainder is precisely the consolidation call's cost. -/
theorem extraction_consolidation_cost (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (vertex : Int) :
    Heap.cost heap after = Heap.cost
      (set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex)
        queue (heap.read layout.right vertex)) after := rfl

/-- Public removal costs split into one operation, the counted child promotions,
    and the separate consolidation cost. The extraction phase contributes no ticks. -/
theorem pop_nonempty_cost (heap promoted after : Heap) (queue : Ref_FibonacciHeap)
    (layout promotedLayout finalLayout : Layout) (count : Nat)
    (nonempty : 0 ≤ layout.minimum)
    (promote : PromotionEffect queue layout.minimum (heap.tick "heap_operations")
      layout promoted promotedLayout count)
    (extract : ExtractionEffect queue layout.minimum promoted promotedLayout after finalLayout) :
    Heap.cost heap after = fun clock => Clocks.single "heap_operations" 1 clock +
      count * (Clocks.single "heap_promotions" 1 clock + Clocks.single "heap_comparisons" 1 clock) +
      Heap.cost promoted after clock := by
  funext clock
  have promotion := promotion_effect_clocks _ _ _ _ _ _ _ promote nonempty clock
  have monotone := extraction_effect_clocks_monotone _ _ _ _ _ _ extract clock
  by_cases operation : clock = "heap_operations" <;>
    simp_all [Heap.cost, Clocks.single] <;> omega

/-- Only the queue's own sequences can be modified by a child promotion. -/
theorem promotion_other_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    (promotionHeap heap queue layout vertex).read ref index = heap.read ref index := by
  have different := outside
  simp only [Layout.refs, List.mem_cons, not_or] at different
  simp only [promotionHeap, Heap.read_tick]
  rw [add_root_other_array _ _ _ _ ref different.2.1 different.2.2.2.2.2.2.1
    different.2.2.2.1 different.2.2.2.2.1]
  unfold promotionDetachedHeap
  rw [remove_other_array _ _ _ _ different.2.2.2.1 different.2.2.2.2.1]
  rw [Heap.read_write_other_ref _ _ _ _ _ _ different.2.2.2.2.2.1]
  unfold promotionHeaderHeap
  dsimp only
  split <;> exact Heap.read_write_other_ref _ _ _ _ _ _ different.2.2.1

theorem promotion_effect_other_array (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int) (count : Nat)
    (effect : PromotionEffect queue vertex heap layout after finalLayout count)
    (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    after.read ref index = heap.read ref index := by
  induction effect with
  | done _ _ _ => rfl
  | @next before after current finalLayout count hasChild rest ih =>
    rw [ih (by simpa using outside)]
    exact promotion_other_array before queue current vertex ref outside index

theorem extraction_other_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (ref : SeqRef) (outside : ref ∉ layout.refs) (index : Int) :
    (extractionHeap heap queue layout vertex).read ref index = heap.read ref index := by
  have different := outside
  simp only [Layout.refs, List.mem_cons, not_or] at different
  change ((removeHeap heap layout vertex).write layout.present vertex 0).read ref index = _
  rw [Heap.read_write_other_ref _ _ _ _ _ _ different.2.2.2.2.2.2.2.1]
  exact remove_other_array _ _ _ _ different.2.2.2.1 different.2.2.2.2.1 index

theorem promotion_effect_refs (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int) (count : Nat)
    (effect : PromotionEffect queue vertex heap layout after finalLayout count) :
    finalLayout.refs = layout.refs := by
  induction effect with
  | done _ _ _ => rfl
  | next _ _ ih => exact ih.trans (promotion_layout_refs _ _ _)

/-- A consolidation client-storage contract composes with the entire pop operation. -/
theorem pop_effect_other_array (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (output : Int) (count : Nat)
    (effect : PopEffect queue heap layout after finalLayout output count)
    (ref : SeqRef) (outside : ref ∉ layout.refs)
    (consolidateFrame : ∀ (before : Heap) (current : Layout) (final : Heap), current.Valid before queue → ref ∉ current.refs →
      FibonacciHeap.consolidate.Call before queue final () →
      ∀ index, final.read ref index = before.read ref index)
    (index : Int) : after.read ref index = heap.read ref index := by
  cases effect with
  | empty empty => rfl
  | @nonempty promoted after promotedLayout finalLayout count nonempty promote extract =>
    have ready := promotion_effect_layout _ _ _ _ _ _ _ promote (Layout.Valid.tick _ _ _ valid _ _)
    have untouched := promotion_effect_other_array _ _ _ _ _ _ _ promote ref outside index
    have remainingOutside : ref ∉ promotedLayout.refs := by
      simpa only [promotion_effect_refs _ _ _ _ _ _ _ promote] using outside
    cases extract with
    | last onlyRoot => exact (extraction_other_array promoted queue promotedLayout layout.minimum ref remainingOutside index).trans untouched
    | consolidate moreRoots call resultLayout =>
      have resized := extraction_layout _ _ _ ready layout.minimum
      have selected := Layout.Valid.set_minimum _ _ _ resized (promoted.read promotedLayout.right layout.minimum)
      rw [consolidateFrame _ _ _ selected (by exact remainingOutside) call index]
      exact (extraction_other_array promoted queue promotedLayout layout.minimum ref remainingOutside index).trans untouched

end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

open Algo2Lean.Fibonacci.Rings

/-- A finite child ring, with the two root insertion handles outside it. This
    excludes root/child aliasing without requiring a complete forest invariant. -/
structure PendingChildren (heap : Heap) (layout : Layout) (vertex : Int)
    (children : List Int) : Prop where
  ring : RingOrEmpty (heap.read layout.left) (heap.read layout.right) children
  header : heap.read layout.children vertex = match children with | [] => -1 | first :: _ => first
  nonnegative : ∀ child ∈ children, 0 ≤ child
  minimumNonnegative : 0 ≤ layout.minimum
  minimumOutside : layout.minimum ∉ children
  successorOutside : heap.read layout.right layout.minimum ∉ children

theorem remove_left_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (removeHeap heap layout vertex).read layout.left =
      removeLeft (heap.read layout.left) (heap.read layout.right) vertex := by
  have separate : layout.left ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  funext index
  simp [removeHeap, removeLeft, write, Heap.read, Heap.write, separate]

theorem remove_right_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (removeHeap heap layout vertex).read layout.right =
      removeRight (heap.read layout.left) (heap.read layout.right) vertex := by
  have separate : layout.right ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  funext index
  simp [removeHeap, removeRight, write, Heap.read, Heap.write, separate]

theorem add_root_left_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) (nonempty : 0 ≤ layout.minimum) :
    (addRootHeap heap queue layout vertex).read layout.left =
      insertAfterLeft (heap.read layout.left) (heap.read layout.right) layout.minimum vertex := by
  have different : layout.left ≠ layout.right ∧ layout.left ≠ layout.parents ∧
      layout.left ≠ layout.marks ∧ layout.right ≠ layout.parents ∧ layout.right ≠ layout.marks := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro same <;> have all := valid.separate <;>
      simp_all [Layout.refs, List.nodup_cons]
  unfold addRootHeap
  rw [if_neg (by omega)]
  dsimp only
  split <;> funext index <;>
    simp [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum, insertAfterLeft,
      write, Heap.read, Heap.write, different.1, different.2.1, different.2.2.1,
      different.2.2.2.1, different.2.2.2.2]

theorem add_root_right_array (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) (nonempty : 0 ≤ layout.minimum) :
    (addRootHeap heap queue layout vertex).read layout.right =
      insertAfterRight (heap.read layout.right) layout.minimum vertex := by
  have different : layout.right ≠ layout.left ∧ layout.right ≠ layout.parents ∧
      layout.right ≠ layout.marks := by
    refine ⟨?_, ?_, ?_⟩ <;> intro same <;> have all := valid.separate <;>
      simp_all [Layout.refs, List.nodup_cons]
  unfold addRootHeap
  rw [if_neg (by omega)]
  dsimp only
  split <;> funext index <;>
    simp [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum, insertAfterRight,
      write, Heap.read, Heap.write, different.1, different.2.1, different.2.2]

@[simp] theorem promotion_layout_left (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).left = layout.left := by
  unfold promotionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem promotion_layout_right (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).right = layout.right := by
  unfold promotionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

@[simp] theorem promotion_layout_children (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).children = layout.children := by
  unfold promotionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem promotion_minimum_cases (heap : Heap) (layout : Layout) (vertex : Int) :
    (promotionLayout heap layout vertex).minimum = layout.minimum ∨
      (promotionLayout heap layout vertex).minimum = heap.read layout.children vertex := by
  unfold promotionLayout addRootLayout
  split
  · exact Or.inr rfl
  · dsimp only
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem promotion_header_left (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (promotionHeaderHeap heap layout vertex).read layout.left = heap.read layout.left := by
  have separate : layout.left ≠ layout.children := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  unfold promotionHeaderHeap
  dsimp only
  split <;> funext index <;> exact Heap.read_write_other_ref _ _ _ _ _ _ separate

theorem promotion_header_right (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (promotionHeaderHeap heap layout vertex).read layout.right = heap.read layout.right := by
  have separate : layout.right ≠ layout.children := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  unfold promotionHeaderHeap
  dsimp only
  split <;> funext index <;> exact Heap.read_write_other_ref _ _ _ _ _ _ separate

theorem promotion_detached_left (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (promotionDetachedHeap heap layout vertex).read layout.left =
      removeLeft (heap.read layout.left) (heap.read layout.right) (heap.read layout.children vertex) := by
  have different : layout.left ≠ layout.degrees ∧ layout.right ≠ layout.degrees := by
    constructor <;> intro same <;> have all := valid.separate <;>
      simp_all [Layout.refs, List.nodup_cons]
  have headed := promotion_header_layout heap queue layout valid vertex
  unfold promotionDetachedHeap
  rw [remove_left_array _ _ _ (Layout.Valid.write _ _ _ headed _ _ _)]
  have left : ((promotionHeaderHeap heap layout vertex).write layout.degrees vertex
      ((promotionHeaderHeap heap layout vertex).read layout.degrees vertex - 1)).read layout.left =
      heap.read layout.left := by
    funext index
    rw [Heap.read_write_other_ref _ _ _ _ _ _ different.1, promotion_header_left _ _ _ valid]
  have right : ((promotionHeaderHeap heap layout vertex).write layout.degrees vertex
      ((promotionHeaderHeap heap layout vertex).read layout.degrees vertex - 1)).read layout.right =
      heap.read layout.right := by
    funext index
    rw [Heap.read_write_other_ref _ _ _ _ _ _ different.2, promotion_header_right _ _ _ valid]
  rw [left, right]

theorem promotion_detached_right (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (promotionDetachedHeap heap layout vertex).read layout.right =
      removeRight (heap.read layout.left) (heap.read layout.right) (heap.read layout.children vertex) := by
  have different : layout.left ≠ layout.degrees ∧ layout.right ≠ layout.degrees := by
    constructor <;> intro same <;> have all := valid.separate <;>
      simp_all [Layout.refs, List.nodup_cons]
  have headed := promotion_header_layout heap queue layout valid vertex
  unfold promotionDetachedHeap
  rw [remove_right_array _ _ _ (Layout.Valid.write _ _ _ headed _ _ _)]
  have left : ((promotionHeaderHeap heap layout vertex).write layout.degrees vertex
      ((promotionHeaderHeap heap layout vertex).read layout.degrees vertex - 1)).read layout.left =
      heap.read layout.left := by
    funext index
    rw [Heap.read_write_other_ref _ _ _ _ _ _ different.1, promotion_header_left _ _ _ valid]
  have right : ((promotionHeaderHeap heap layout vertex).write layout.degrees vertex
      ((promotionHeaderHeap heap layout vertex).read layout.degrees vertex - 1)).read layout.right =
      heap.read layout.right := by
    funext index
    rw [Heap.read_write_other_ref _ _ _ _ _ _ different.2, promotion_header_right _ _ _ valid]
  rw [left, right]

theorem promotion_child_header (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (promotionHeap heap queue layout vertex).read layout.children vertex =
      if heap.read layout.right (heap.read layout.children vertex) = heap.read layout.children vertex
      then -1 else heap.read layout.right (heap.read layout.children vertex) := by
  have different : layout.children ≠ layout.parents ∧ layout.children ≠ layout.marks ∧
      layout.children ≠ layout.left ∧ layout.children ≠ layout.right ∧ layout.children ≠ layout.degrees := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro same <;> have all := valid.separate <;>
      simp_all [Layout.refs, List.nodup_cons]
  simp only [promotionHeap, Heap.read_tick]
  rw [add_root_other_array _ _ _ _ _ different.1 different.2.1 different.2.2.1 different.2.2.2.1]
  unfold promotionDetachedHeap
  rw [remove_other_array _ _ _ _ different.2.2.1 different.2.2.2.1,
    Heap.read_write_other_ref _ _ _ _ _ _ different.2.2.2.2]
  unfold promotionHeaderHeap
  dsimp only
  split <;> exact Heap.read_write_same _ _ _ _

/-- One promotion removes exactly the displayed child and preserves the remaining finite ring. -/
theorem PendingChildren.promote (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex child : Int) (tail : List Int)
    (pending : PendingChildren heap layout vertex (child :: tail)) :
    PendingChildren (promotionHeap heap queue layout vertex)
      (promotionLayout heap layout vertex) vertex tail := by
  have ring : Ring (heap.read layout.left) (heap.read layout.right) (child :: tail) :=
    pending.ring.resolve_left (by simp)
  have header : heap.read layout.children vertex = child := pending.header
  have fresh : child ∉ tail := (List.nodup_cons.mp ring.unique).1
  have minChild : layout.minimum ≠ child := by
    intro same
    exact pending.minimumOutside (by simp [same])
  have minBefore : layout.minimum ≠ heap.read layout.left child := by
    intro same
    exact pending.minimumOutside (same.symm ▸ (ring.neighbors (by simp)).1)
  have oldNext : removeRight (heap.read layout.left) (heap.read layout.right)
      child layout.minimum = heap.read layout.right layout.minimum := by
    simp [removeRight, write, minChild, minBefore]
  have detached := promotion_detached_layout heap queue layout valid vertex
  have newLeft : (promotionHeap heap queue layout vertex).read layout.left =
      insertAfterLeft
        (removeLeft (heap.read layout.left) (heap.read layout.right) child)
        (removeRight (heap.read layout.left) (heap.read layout.right) child)
        layout.minimum child := by
    change (addRootHeap (promotionDetachedHeap heap layout vertex) queue layout
      (heap.read layout.children vertex)).read layout.left = _
    rw [add_root_left_array _ _ _ detached _ pending.minimumNonnegative,
      promotion_detached_left _ _ _ valid, promotion_detached_right _ _ _ valid, header]
  have newRight : (promotionHeap heap queue layout vertex).read layout.right =
      insertAfterRight
        (removeRight (heap.read layout.left) (heap.read layout.right) child)
        layout.minimum child := by
    change (addRootHeap (promotionDetachedHeap heap layout vertex) queue layout
      (heap.read layout.children vertex)).read layout.right = _
    rw [add_root_right_array _ _ _ detached _ pending.minimumNonnegative,
      promotion_detached_right _ _ _ valid, header]
  have notChild (index : Int) (member : index ∈ tail) : index ≠ child := by
    intro same
    exact fresh (same ▸ member)
  have notMin (index : Int) (member : index ∈ tail) : index ≠ layout.minimum := by
    intro same
    exact pending.minimumOutside (by simp [← same, member])
  have notNext (index : Int) (member : index ∈ tail) : index ≠ heap.read layout.right layout.minimum := by
    intro same
    exact pending.successorOutside (by simp [← same, member])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [promotion_layout_left, promotion_layout_right, newLeft, newRight]
    rcases ring.remove_head with empty | remaining
    · exact Or.inl empty
    · apply Or.inr
      apply remaining.frame
      · intro index member
        simp [insertAfterLeft, write, oldNext, notChild index member, notNext index member]
      · intro index member
        simp [insertAfterRight, write, notChild index member, notMin index member]
  · rw [promotion_layout_children, promotion_child_header _ _ _ valid, header]
    cases tail with
    | nil => simp [ring.singleton_pointers.2]
    | cons next rest =>
      have distinct : next ≠ child := by
        intro same
        exact fresh (by simp [same])
      simp [ring.head_next.1, distinct]
  · intro index member
    exact pending.nonnegative index (by simp [member])
  · exact promotion_layout_nonempty heap layout vertex pending.minimumNonnegative
      (by rw [header]; exact pending.nonnegative child (by simp))
  · rcases promotion_minimum_cases heap layout vertex with old | promoted
    · rw [old]
      intro member
      exact pending.minimumOutside (by simp [member])
    · rw [promoted, header]
      exact fresh
  · simp only [promotion_layout_right, newRight]
    rcases promotion_minimum_cases heap layout vertex with old | promoted
    · rw [old]
      simpa [insertAfterRight, write] using fresh
    · rw [promoted, header]
      have outside : heap.read layout.right layout.minimum ∉ tail := by
        intro member
        exact pending.successorOutside (by simp [member])
      simpa [insertAfterRight, write, Ne.symm minChild, oldNext] using outside

/-- Finite child rings give a terminating promotion effect with exactly one
    iteration per original child, without supplying a trace or a loop execution. -/
theorem promotion_effect_exists (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) (children : List Int)
    (pending : PendingChildren heap layout vertex children) :
    ∃ after finalLayout, PromotionEffect queue vertex heap layout after finalLayout children.length ∧
      finalLayout.Valid after queue ∧ PendingChildren after finalLayout vertex [] := by
  induction children generalizing heap layout with
  | nil =>
    have header : heap.read layout.children vertex = -1 := pending.header
    have childless : heap.read layout.children vertex < 0 := by rw [header]; decide
    exact ⟨heap, layout, .done _ _ childless, valid, pending⟩
  | cons child tail ih =>
    have header : heap.read layout.children vertex = child := pending.header
    have hasChild : 0 ≤ heap.read layout.children vertex := by
      rw [header]
      exact pending.nonnegative child (by simp)
    obtain ⟨after, finalLayout, effect, ready, finished⟩ :=
      ih (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex)
        (promotion_layout heap queue layout valid vertex)
        (pending.promote heap queue layout valid vertex child tail)
    exact ⟨after, finalLayout, .next hasChild effect, ready, finished⟩

/-- A disjoint root ring supplies the two root handles excluded by the local
    child-loop invariant. Full represented forests establish these finite rings. -/
theorem pending_children_of_rings (heap : Heap) (layout : Layout) (vertex : Int)
    (roots children : List Int)
    (rootRing : Ring (heap.read layout.left) (heap.read layout.right) roots)
    (childRing : RingOrEmpty (heap.read layout.left) (heap.read layout.right) children)
    (header : heap.read layout.children vertex = match children with | [] => -1 | first :: _ => first)
    (minimumMember : layout.minimum ∈ roots) (minimumNonnegative : 0 ≤ layout.minimum)
    (childNonnegative : ∀ child ∈ children, 0 ≤ child)
    (disjoint : ∀ root ∈ roots, root ∉ children) :
    PendingChildren heap layout vertex children := by
  exact ⟨childRing, header, childNonnegative, minimumNonnegative,
    disjoint layout.minimum minimumMember,
    disjoint _ (rootRing.neighbors minimumMember).2⟩

end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

/-- One degree-table visit clears its bucket before reconnecting its root. -/
def rebuildClear (heap : Heap) (layout : Layout) (degree : Int) : Heap :=
  (heap.tick "heap_degree_scans").write layout.table degree (-1)

def rebuildHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (degree : Int) : Heap :=
  let cleared := rebuildClear heap layout degree
  let vertex := heap.read layout.table degree
  if vertex < 0 then cleared else addRootHeap cleared queue layout vertex

def rebuildLayout (heap : Heap) (layout : Layout) (degree : Int) : Layout :=
  if heap.read layout.table degree < 0 then layout
  else addRootLayout (rebuildClear heap layout degree) layout (heap.read layout.table degree)

theorem rebuild_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree : Int) :
    (rebuildLayout heap layout degree).Valid (rebuildHeap heap queue layout degree) queue := by
  unfold rebuildLayout rebuildHeap
  dsimp only
  split
  · exact Layout.Valid.write _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _ _
  · exact add_root_layout _ _ _ (Layout.Valid.write _ _ _
      (Layout.Valid.tick _ _ _ valid _ _) _ _ _) _

/-- A finite interval of degree buckets, with the exact mutation at each visit. -/
inductive RebuildEffect (queue : Ref_FibonacciHeap) (maximum : Int) :
    Heap → Layout → Int → Heap → Layout → Prop where
  | done (heap : Heap) (layout : Layout) (degree : Int) (finished : maximum < degree) :
      RebuildEffect queue maximum heap layout degree heap layout
  | step {heap after : Heap} {layout finalLayout : Layout} {degree : Int}
      (remaining : degree ≤ maximum)
      (rest : RebuildEffect queue maximum (rebuildHeap heap queue layout degree)
        (rebuildLayout heap layout degree) (degree + 1) after finalLayout) :
      RebuildEffect queue maximum heap layout degree after finalLayout

theorem rebuild_exists (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree maximum : Int) :
    ∃ after finalLayout, RebuildEffect queue maximum heap layout degree after finalLayout ∧
      finalLayout.Valid after queue := by
  have terminate : ∀ fuel : Nat, ∀ before current index,
      (maximum + 1 - index).toNat = fuel → current.Valid before queue →
      ∃ after finalLayout, RebuildEffect queue maximum before current index after finalLayout ∧
        finalLayout.Valid after queue := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro before current index measure ready
      by_cases done : maximum < index
      · exact ⟨before, current, .done _ _ _ done, ready⟩
      have remaining : index ≤ maximum := by omega
      have smaller : (maximum + 1 - (index + 1)).toNat < fuel := by omega
      obtain ⟨after, finalLayout, rest, finalReady⟩ :=
        ih _ smaller (rebuildHeap before queue current index)
          (rebuildLayout before current index) (index + 1) rfl
          (rebuild_layout before queue current ready index)
      exact ⟨after, finalLayout, .step remaining rest, finalReady⟩
  exact terminate _ heap layout degree rfl valid

private theorem rebuild_effect_reaches (queue : Ref_FibonacciHeap) (maximum : Int)
    (heap after : Heap) (layout finalLayout : Layout) (degree : Int)
    (valid : layout.Valid heap queue)
    (effect : RebuildEffect queue maximum heap layout degree after finalLayout)
    (state : State_FibonacciHeap_consolidate) (stack : Stack) :
    Reaches Step (.active heap (.fn_FibonacciHeap_consolidate 4
      { state with v0 := queue, v1 := layout.table, v2 := maximum, v4 := degree }) stack)
      (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
  induction effect generalizing state with
  | done heap layout degree finished =>
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc4 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc3_false _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc2 _ _ _)
    exact Reaches.single (Step.FibonacciHeap_consolidate_pc1 _ _ _)
  | @step heap after layout finalLayout degree remaining rest ih =>
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc4 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc3_true _ _ _ (by simp [remaining]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc14 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc13 _ _ _ valid.tableAllocated)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc12 _ _ _ valid.tableAllocated)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc11 _ _ _)
    have nextValid := rebuild_layout heap queue layout valid degree
    by_cases absent : heap.read layout.table degree < 0
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc10_false _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc5 _ _ _)
      simpa only [rebuildHeap, rebuildLayout, absent, ↓reduceIte, rebuildClear, Heap.read_tick] using
        ih nextValid { state with t8 := decide (degree ≤ maximum), t9 := decide (heap.read layout.table degree ≥ 0), v3 := heap.read layout.table degree }
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc10_true _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc9 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc8 _ _ _ valid.object)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc7 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc6 _ _ _)
      have clearValid : layout.Valid (rebuildClear heap layout degree) queue :=
        Layout.Valid.write _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _ _
      apply Reaches.trans ((add_root_summary _ _ _ clearValid (heap.read layout.table degree)).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc5 _ _ _)
      have tableSame : (rebuildLayout heap layout degree).table = layout.table := by
        simp only [rebuildLayout, absent, ↓reduceIte]
        unfold addRootLayout
        split
        · rfl
        · dsimp only
          split <;> rfl
      have subsequent := ih nextValid { state with t8 := decide (degree ≤ maximum), t9 := decide (heap.read layout.table degree ≥ 0), v3 := heap.read layout.table degree, t10 := (), t11 := queue, t12 := heap.read layout.table degree }
      rw [tableSame] at subsequent
      simpa only [rebuildHeap, absent, ↓reduceIte, Heap.read_tick] using subsequent

/-- Clear the colliding bucket before comparing and linking its two roots. -/
def collisionStart (heap : Heap) (layout : Layout) (degree : Int) : Heap :=
  (heap.write layout.table degree (-1)).tick "heap_comparisons"

def collisionParent (heap : Heap) (layout : Layout) (vertex degree : Int) : Int :=
  let ready := collisionStart heap layout degree
  let other := heap.read layout.table degree
  if ready.read layout.keys other < ready.read layout.keys vertex then other else vertex

def collisionChild (heap : Heap) (layout : Layout) (vertex degree : Int) : Int :=
  let ready := collisionStart heap layout degree
  let other := heap.read layout.table degree
  if ready.read layout.keys other < ready.read layout.keys vertex then vertex else other

def collisionHeap (heap : Heap) (layout : Layout) (vertex degree : Int) : Heap :=
  linkHeap (collisionStart heap layout degree) layout (collisionChild heap layout vertex degree)
    (collisionParent heap layout vertex degree)

theorem collision_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree : Int) :
    layout.Valid (collisionHeap heap layout vertex degree) queue := by
  apply link_preserves_layout
  apply Layout.Valid.tick
  exact Layout.Valid.write _ _ _ valid _ _ _

/-- One equal-degree collision per link; the final bucket is empty. -/
inductive CollisionEffect (layout : Layout) : Heap → Int → Int → Heap → Int → Int → Nat → Prop where
  | done (heap : Heap) (vertex degree : Int) (empty : heap.read layout.table degree < 0) :
      CollisionEffect layout heap vertex degree heap vertex degree 0
  | step {heap after : Heap} {vertex degree finalVertex finalDegree : Int} {links : Nat}
      (occupied : 0 ≤ heap.read layout.table degree)
      (rest : CollisionEffect layout (collisionHeap heap layout vertex degree)
        (collisionParent heap layout vertex degree) (degree + 1) after finalVertex finalDegree links) :
      CollisionEffect layout heap vertex degree after finalVertex finalDegree (links + 1)

/-- Buckets at and above this exclusive limit are unused. -/
def TableTailEmpty (heap : Heap) (layout : Layout) (limit : Int) : Prop :=
  ∀ degree, limit ≤ degree → heap.read layout.table degree < 0

theorem collision_table (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree index : Int) :
    (collisionHeap heap layout vertex degree).read layout.table index =
      if index = degree then -1 else heap.read layout.table index := by
  have separate : layout.table ≠ layout.parents ∧ layout.table ≠ layout.marks ∧
      layout.table ≠ layout.left ∧ layout.table ≠ layout.right ∧
      layout.table ≠ layout.children ∧ layout.table ≠ layout.degrees := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro same <;>
      have all := valid.separate <;> simp_all [Layout.refs, List.nodup_cons]
  unfold collisionHeap
  rw [link_other_array _ _ _ _ _ separate.1 separate.2.1 separate.2.2.1
    separate.2.2.2.1 separate.2.2.2.2.1 separate.2.2.2.2.2]
  simp [collisionStart, Heap.read, Heap.write]

theorem collision_tail_empty (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree limit : Int)
    (tail : TableTailEmpty heap layout limit) :
    TableTailEmpty (collisionHeap heap layout vertex degree) layout limit := by
  intro index above
  rw [collision_table heap queue layout valid vertex degree index]
  split
  · omega
  · exact tail index above

theorem collision_exists (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree limit : Int)
    (tail : TableTailEmpty heap layout limit) :
    ∃ after finalVertex finalDegree links,
      CollisionEffect layout heap vertex degree after finalVertex finalDegree links ∧
      layout.Valid after queue := by
  have terminate : ∀ fuel : Nat, ∀ before vertex index,
      (limit + 1 - index).toNat = fuel → layout.Valid before queue → TableTailEmpty before layout limit →
      ∃ after finalVertex finalDegree links,
        CollisionEffect layout before vertex index after finalVertex finalDegree links ∧
        layout.Valid after queue := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro before vertex index measure ready emptyTail
      by_cases empty : before.read layout.table index < 0
      · exact ⟨before, vertex, index, 0, .done _ _ _ empty, ready⟩
      have occupied : 0 ≤ before.read layout.table index := by omega
      have below : index < limit := by
        by_cases above : limit ≤ index
        · have impossible := emptyTail index above
          omega
        · omega
      have smaller : (limit + 1 - (index + 1)).toNat < fuel := by omega
      obtain ⟨after, finalVertex, finalDegree, links, rest, readyAfter⟩ := ih _ smaller
        (collisionHeap before layout vertex index) (collisionParent before layout vertex index) (index + 1) rfl
        (collision_layout before queue layout ready vertex index)
        (collision_tail_empty before queue layout ready vertex index limit emptyTail)
      exact ⟨after, finalVertex, finalDegree, links + 1, .step occupied rest, readyAfter⟩
  exact terminate _ heap vertex degree rfl valid tail

private theorem collision_effect_reaches (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (vertex degree finalVertex finalDegree : Int) (links : Nat)
    (valid : layout.Valid heap queue)
    (effect : CollisionEffect layout heap vertex degree after finalVertex finalDegree links)
    (state : State_FibonacciHeap_consolidate) (stack : Stack) :
    ∃ finalState : State_FibonacciHeap_consolidate,
      finalState.v0 = queue ∧ finalState.v1 = layout.table ∧ finalState.v2 = state.v2 ∧
      finalState.v3 = finalVertex ∧ finalState.v4 = finalDegree ∧
      Reaches Step (.active heap (.fn_FibonacciHeap_consolidate 23
        {state with v0 := queue, v1 := layout.table, v3 := vertex, v4 := degree}) stack)
        (.active after (.fn_FibonacciHeap_consolidate 21 finalState) stack) := by
  induction effect generalizing state with
  | done heap vertex degree empty =>
    refine ⟨{state with v0 := queue, v1 := layout.table, v3 := vertex, v4 := degree, t15 := decide (heap.read layout.table degree ≥ 0)}, rfl, rfl, rfl, rfl, rfl, ?_⟩
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc23 _ _ _ valid.tableAllocated)
    exact Reaches.single (Step.FibonacciHeap_consolidate_pc22_false _ _ _ (by simp; omega))
  | @step heap after vertex degree finalVertex finalDegree links occupied rest ih =>
    let ready := collisionStart heap layout degree
    let other := heap.read layout.table degree
    have readyValid : layout.Valid ready queue :=
      Layout.Valid.tick _ _ _ (Layout.Valid.write _ _ _ valid _ _ _) _ _
    have nextValid := collision_layout heap queue layout valid vertex degree
    by_cases better : ready.read layout.keys other < ready.read layout.keys vertex
    · dsimp only [ready, other, collisionStart] at better
      let nextState : State_FibonacciHeap_consolidate :=
        {state with v0 := queue, v1 := layout.table, v3 := other, v4 := degree + 1, v5 := vertex, v6 := vertex, t15 := decide (heap.read layout.table degree ≥ 0), t16 := (), t17 := queue, t18 := vertex, t19 := other, t20 := decide (ready.read layout.keys other < ready.read layout.keys vertex)}
      obtain ⟨finalState, self, table, maximum, output, degreeOut, tail⟩ := ih nextValid nextState
      refine ⟨finalState, self, table, maximum, output, degreeOut, ?_⟩
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc23 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc22_true _ _ _ (by simp [occupied]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc37 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc36 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc35 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc34 _ _ _
        (by simp [valid.readKeys, valid.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc33_true _ _ _
        (by simpa only [keys_tick, keys_write, valid.readKeys, Option.getD_some, decide_eq_true_eq, decide_eq_false_iff_not] using better))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc32 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc31 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc30 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc29 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc28 _ _ _ readyValid.object)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc27 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc26 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc25 _ _ _)
      apply Reaches.trans ((link_summary ready queue layout readyValid vertex other).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc24 _ _ _)
      simpa only [collisionHeap, collisionParent, collisionChild, collisionStart, better, ↓reduceIte,
        nextState, ready, other, keys_tick, keys_write, valid.readKeys, Option.getD_some] using tail
    · dsimp only [ready, other, collisionStart] at better
      let nextState : State_FibonacciHeap_consolidate :=
        {state with v0 := queue, v1 := layout.table, v3 := vertex, v4 := degree + 1, v5 := other, t15 := decide (heap.read layout.table degree ≥ 0), t16 := (), t17 := queue, t18 := other, t19 := vertex, t20 := decide (ready.read layout.keys other < ready.read layout.keys vertex)}
      obtain ⟨finalState, self, table, maximum, output, degreeOut, tail⟩ := ih nextValid nextState
      refine ⟨finalState, self, table, maximum, output, degreeOut, ?_⟩
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc23 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc22_true _ _ _ (by simp [occupied]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc37 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc36 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc35 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc34 _ _ _
        (by simp [valid.readKeys, valid.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc33_false _ _ _
        (by simpa only [keys_tick, keys_write, valid.readKeys, Option.getD_some, decide_eq_true_eq, decide_eq_false_iff_not] using better))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc29 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc28 _ _ _ readyValid.object)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc27 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc26 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc25 _ _ _)
      apply Reaches.trans ((link_summary ready queue layout readyValid other vertex).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc24 _ _ _)
      simpa only [collisionHeap, collisionParent, collisionChild, collisionStart, better, ↓reduceIte,
        nextState, ready, other, keys_tick, keys_write, valid.readKeys, Option.getD_some] using tail

/-- Detach the next pending root before looking it up in the degree table. -/
def pendingMinimum (heap : Heap) (layout : Layout) : Int :=
  if heap.read layout.right layout.minimum = layout.minimum then -1
  else heap.read layout.right layout.minimum

def detachLayout (heap : Heap) (layout : Layout) : Layout :=
  {layout with minimum := pendingMinimum heap layout}

def detachHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) : Heap :=
  (removeHeap (set_FibonacciHeap_minimum heap queue (pendingMinimum heap layout)) layout
    layout.minimum).tick "heap_root_scans"

theorem detach_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) : (detachLayout heap layout).Valid (detachHeap heap queue layout) queue := by
  apply Layout.Valid.tick
  apply remove_preserves_layout
  exact Layout.Valid.set_minimum heap queue layout valid (pendingMinimum heap layout)

theorem CollisionEffect.layout_valid {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout : Layout} {vertex degree finalVertex finalDegree : Int} {links : Nat}
    (effect : CollisionEffect layout heap vertex degree after finalVertex finalDegree links)
    (valid : layout.Valid heap queue) : layout.Valid after queue := by
  induction effect with
  | done => exact valid
  | step occupied rest ih => exact ih (collision_layout _ _ _ valid _ _)

/-- Pending roots are consumed once; each detached root resolves collisions,
    then stores its surviving tree in the now-empty degree bucket. -/
inductive ConsumeEffect (queue : Ref_FibonacciHeap) :
    Heap → Layout → Int → Heap → Layout → Nat → Nat → Prop where
  | done {heap after : Heap} {layout finalLayout : Layout} {maximum : Int}
      (empty : layout.minimum < 0)
      (rebuild : RebuildEffect queue maximum heap layout 0 after finalLayout) :
      ConsumeEffect queue heap layout maximum after finalLayout 0 0
  | next {heap merged after : Heap} {layout finalLayout : Layout}
      {maximum vertex degree : Int} {links tailRoots tailLinks : Nat}
      (pending : 0 ≤ layout.minimum)
      (collisions : CollisionEffect (detachLayout heap layout)
        (detachHeap heap queue layout) layout.minimum
        ((detachHeap heap queue layout).read layout.degrees layout.minimum)
        merged vertex degree links)
      (rest : ConsumeEffect queue (merged.write layout.table degree vertex)
        (detachLayout heap layout) (max maximum degree) after finalLayout tailRoots tailLinks) :
      ConsumeEffect queue heap layout maximum after finalLayout (tailRoots + 1) (links + tailLinks)

private theorem consume_effect_reaches (queue : Ref_FibonacciHeap)
    (heap after : Heap) (layout finalLayout : Layout) (maximum : Int) (roots links : Nat)
    (valid : layout.Valid heap queue)
    (effect : ConsumeEffect queue heap layout maximum after finalLayout roots links)
    (state : State_FibonacciHeap_consolidate) (stack : Stack) :
    Reaches Step (.active heap (.fn_FibonacciHeap_consolidate 17
      {state with v0 := queue, v1 := layout.table, v2 := maximum}) stack)
      (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
  induction effect generalizing state with
  | @done heap after layout finalLayout maximum empty rebuild =>
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc17 _ _ _ (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc16_false _ _ _ (by simp [valid.readMinimum]; omega))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc15 _ _ _)
    simpa only [valid.readMinimum, Option.getD_some] using
      rebuild_effect_reaches queue maximum heap after layout finalLayout 0 valid rebuild
        {state with t13 := decide (layout.minimum ≥ 0)} stack
  | @next heap merged after layout finalLayout maximum vertex degree links tailRoots tailLinks pending collisions rest ih =>
    let detached := detachHeap heap queue layout
    let detachedLayout := detachLayout heap layout
    have detachedReady := detach_layout heap queue layout valid
    have mergedReady := collisions.layout_valid detachedReady
    have storedReady := Layout.Valid.write merged queue detachedLayout mergedReady layout.table degree vertex
    have finish (atCollision : State_FibonacciHeap_consolidate)
        (readSelf : atCollision.v0 = queue) (readTable : atCollision.v1 = layout.table)
        (readMaximum : atCollision.v2 = maximum) (readVertex : atCollision.v3 = layout.minimum)
        (readDegree : atCollision.v4 = detached.read layout.degrees layout.minimum) :
        Reaches Step (.active detached (.fn_FibonacciHeap_consolidate 23 atCollision) stack)
          (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
      obtain ⟨last, self, table, maximumSame, vertexSame, degreeSame, collisionRun⟩ :=
        collision_effect_reaches detached merged queue detachedLayout layout.minimum
          (detached.read layout.degrees layout.minimum) vertex degree links detachedReady collisions atCollision stack
      have actual : {atCollision with v0 := queue, v1 := detachedLayout.table, v3 := layout.minimum, v4 := detached.read layout.degrees layout.minimum} = atCollision := by
        cases atCollision
        simp_all [detachedLayout, detachLayout]
      rw [actual] at collisionRun
      apply Reaches.trans collisionRun
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc21 _ _ _ (by simpa [table] using mergedReady.tableAllocated))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc20 _ _ _)
      have maximumValue : last.v2 = maximum := maximumSame.trans readMaximum
      by_cases larger : maximum < degree
      · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc19_true _ _ _ (by simp [degreeSame, maximumValue, larger]))
        apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc18 _ _ _)
        have next := ih storedReady {last with t14 := decide (degree > maximum)}
        simpa only [self, table, degreeSame, vertexSame, maximumValue, Int.max_eq_right (Int.le_of_lt larger), detachedLayout, detachLayout] using next
      · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc19_false _ _ _ (by simp [degreeSame, maximumValue, larger]))
        have next := ih storedReady {last with t14 := decide (degree > maximum)}
        simpa only [self, table, degreeSame, vertexSame, maximumValue, Int.max_eq_left (by omega : degree ≤ maximum), detachedLayout, detachLayout] using next
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc17 _ _ _ (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc16_true _ _ _ (by simp [valid.readMinimum, pending]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc48 _ _ _ (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc47 _ _ _ (by simp [valid.readRight, valid.rightAllocated]))
    have tail (prepared : Heap) (current : Layout) (ready : current.Valid prepared queue)
        (sameRefs : current.keys = layout.keys ∧ current.parents = layout.parents ∧ current.children = layout.children ∧
          current.left = layout.left ∧ current.right = layout.right ∧ current.degrees = layout.degrees ∧
          current.marks = layout.marks ∧ current.present = layout.present ∧ current.table = layout.table)
        (state : State_FibonacciHeap_consolidate) (self : state.v0 = queue) (table : state.v1 = layout.table)
        (maximumValue : state.v2 = maximum) (vertexValue : state.v3 = layout.minimum)
        (sameHeap : (removeHeap prepared current layout.minimum).tick "heap_root_scans" = detached) :
        Reaches Step (.active prepared (.fn_FibonacciHeap_consolidate 43 state) stack)
          (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
      have detachedReady' := Layout.Valid.tick (removeHeap prepared current layout.minimum) queue current (remove_preserves_layout prepared queue current ready layout.minimum) "heap_root_scans" 1
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc43 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc42 _ _ _ (by simpa [self] using ready.object))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc41 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc40 _ _ _)
      simp only [self, vertexValue]
      apply Reaches.trans ((remove_from_ring_summary prepared queue current ready layout.minimum).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc39 _ _ _)
      rw [sameHeap]
      have readyDetached : current.Valid detached queue := sameHeap ▸ detachedReady'
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc38 _ _ _
        (by rw [readyDetached.readDegrees]; exact ⟨rfl, readyDetached.degreesAllocated⟩))
      simp only [readyDetached.readDegrees, Option.getD_some, sameRefs.2.2.2.2.2.1]
      exact finish _ rfl table maximumValue rfl rfl
    by_cases singleton : heap.read layout.right layout.minimum = layout.minimum
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc46_true _ _ _ (by simp [valid.readMinimum, valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc44 _ _ _ valid.object)
      apply tail _ {layout with minimum := -1} (Layout.Valid.set_minimum heap queue layout valid (-1))
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ rfl rfl rfl
        (by simp [valid.readMinimum])
      simp [detached, detachHeap, pendingMinimum, singleton, removeHeap]
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc46_false _ _ _ (by simp [valid.readMinimum, valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc45 _ _ _ (by simp [valid.readRight, valid.rightAllocated, valid.object]))
      simp only [valid.readMinimum, valid.readRight, Option.getD_some]
      apply tail _ {layout with minimum := heap.read layout.right layout.minimum}
        (Layout.Valid.set_minimum heap queue layout valid _) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ rfl rfl rfl rfl
      simp [detached, detachHeap, pendingMinimum, singleton, removeHeap]

/-- All three consolidation phases compose through checked local call summaries. -/
theorem consolidate_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (roots links : Nat) (valid : layout.Valid heap queue)
    (effect : ConsumeEffect queue heap layout (-1) after finalLayout roots links) :
    FibonacciHeap.consolidate.Call heap queue after () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc50 _ _ _ (by simp [valid.readTable]))
  apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc49 _ _ _)
  simpa only [valid.readTable, Option.getD_some] using
    consume_effect_reaches queue heap after layout finalLayout (-1) roots links valid effect {} stack


private theorem snapshot_ext (before after : Algo2Lean.Fibonacci.Snapshot)
    (keys : before.keys = after.keys) (parents : before.parents = after.parents)
    (children : before.children = after.children) (left : before.left = after.left)
    (right : before.right = after.right) (degrees : before.degrees = after.degrees)
    (marks : before.marks = after.marks) (present : before.present = after.present)
    (table : before.table = after.table) (minimum : before.minimum = after.minimum)
    (size : before.size = after.size) : before = after := by
  cases before
  cases after
  simp_all

theorem insertion_read_keys (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.keys =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.keys) vertex key := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, keys_parents,
        keys_children, keys_left, keys_right, keys_degrees, keys_marks, keys_present, eq_self,
        true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, keys_parents, keys_children, keys_left, keys_right,
        keys_degrees, keys_marks, keys_present, eq_self, true_and, false_and, if_false]

theorem insertion_read_parents (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.parents =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.parents) vertex (-1) := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have parents_keys : layout.parents ≠ layout.keys := Ne.symm (different.1.1)
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, parents_keys,
        parents_children, parents_left, parents_right, parents_degrees, parents_marks,
        parents_present, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, parents_keys, parents_children, parents_left,
        parents_right, parents_degrees, parents_marks, parents_present, eq_self, true_and,
        false_and, if_false]

theorem insertion_read_children (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.children =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.children) vertex (-1) := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have children_keys : layout.children ≠ layout.keys := Ne.symm (different.1.2.1)
  have children_parents : layout.children ≠ layout.parents := Ne.symm (different.2.1.1)
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, children_keys,
        children_parents, children_left, children_right, children_degrees, children_marks,
        children_present, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, children_keys, children_parents, children_left,
        children_right, children_degrees, children_marks, children_present, eq_self, true_and,
        false_and, if_false]

theorem insertion_read_left (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.left =
      if layout.minimum < 0 then Algo2Lean.Fibonacci.Rings.write (heap.read layout.left) vertex vertex else Algo2Lean.Fibonacci.Rings.insertAfterLeft (heap.read layout.left) (heap.read layout.right) layout.minimum vertex := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have left_keys : layout.left ≠ layout.keys := Ne.symm (different.1.2.2.1)
  have left_parents : layout.left ≠ layout.parents := Ne.symm (different.2.1.2.1)
  have left_children : layout.left ≠ layout.children := Ne.symm (different.2.2.1.1)
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_keys : layout.right ≠ layout.keys := Ne.symm (different.1.2.2.2.1)
  have right_children : layout.right ≠ layout.children := Ne.symm (different.2.2.1.2.1)
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_parents : layout.right ≠ layout.parents := Ne.symm (different.2.1.2.2.1)
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, left_keys,
        left_parents, left_children, left_right, left_degrees, left_marks, left_present, eq_self,
        true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, Algo2Lean.Fibonacci.Rings.insertAfterLeft, left_keys,
        left_parents, left_children, left_right, left_degrees, left_marks, left_present, right_keys,
        right_children, right_degrees, right_present, right_parents, right_marks, eq_self, true_and,
        false_and, if_false]

theorem insertion_read_right (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.right =
      if layout.minimum < 0 then Algo2Lean.Fibonacci.Rings.write (heap.read layout.right) vertex vertex else Algo2Lean.Fibonacci.Rings.insertAfterRight (heap.read layout.right) layout.minimum vertex := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have right_keys : layout.right ≠ layout.keys := Ne.symm (different.1.2.2.2.1)
  have right_parents : layout.right ≠ layout.parents := Ne.symm (different.2.1.2.2.1)
  have right_children : layout.right ≠ layout.children := Ne.symm (different.2.2.1.2.1)
  have right_left : layout.right ≠ layout.left := Ne.symm (different.2.2.2.1.1)
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, right_keys,
        right_parents, right_children, right_left, right_degrees, right_marks, right_present,
        eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, Algo2Lean.Fibonacci.Rings.insertAfterRight, right_keys,
        right_parents, right_children, right_left, right_degrees, right_marks, right_present,
        eq_self, true_and, false_and, if_false]

theorem insertion_read_degrees (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.degrees =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.degrees) vertex 0 := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have degrees_keys : layout.degrees ≠ layout.keys := Ne.symm (different.1.2.2.2.2.1)
  have degrees_parents : layout.degrees ≠ layout.parents := Ne.symm (different.2.1.2.2.2.1)
  have degrees_children : layout.degrees ≠ layout.children := Ne.symm (different.2.2.1.2.2.1)
  have degrees_left : layout.degrees ≠ layout.left := Ne.symm (different.2.2.2.1.2.1)
  have degrees_right : layout.degrees ≠ layout.right := Ne.symm (different.2.2.2.2.1.1)
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, degrees_keys,
        degrees_parents, degrees_children, degrees_left, degrees_right, degrees_marks,
        degrees_present, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, degrees_keys, degrees_parents, degrees_children,
        degrees_left, degrees_right, degrees_marks, degrees_present, eq_self, true_and, false_and,
        if_false]

theorem insertion_read_marks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.marks =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.marks) vertex 0 := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have marks_keys : layout.marks ≠ layout.keys := Ne.symm (different.1.2.2.2.2.2.1)
  have marks_parents : layout.marks ≠ layout.parents := Ne.symm (different.2.1.2.2.2.2.1)
  have marks_children : layout.marks ≠ layout.children := Ne.symm (different.2.2.1.2.2.2.1)
  have marks_left : layout.marks ≠ layout.left := Ne.symm (different.2.2.2.1.2.2.1)
  have marks_right : layout.marks ≠ layout.right := Ne.symm (different.2.2.2.2.1.2.1)
  have marks_degrees : layout.marks ≠ layout.degrees := Ne.symm (different.2.2.2.2.2.1.1)
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, marks_keys,
        marks_parents, marks_children, marks_left, marks_right, marks_degrees, marks_present,
        eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, marks_keys, marks_parents, marks_children, marks_left,
        marks_right, marks_degrees, marks_present, eq_self, true_and, false_and, if_false]

theorem insertion_read_present (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.present =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.present) vertex 1 := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have present_keys : layout.present ≠ layout.keys := Ne.symm (different.1.2.2.2.2.2.2.1)
  have present_parents : layout.present ≠ layout.parents := Ne.symm (different.2.1.2.2.2.2.2.1)
  have present_children : layout.present ≠ layout.children := Ne.symm (different.2.2.1.2.2.2.2.1)
  have present_left : layout.present ≠ layout.left := Ne.symm (different.2.2.2.1.2.2.2.1)
  have present_right : layout.present ≠ layout.right := Ne.symm (different.2.2.2.2.1.2.2.1)
  have present_degrees : layout.present ≠ layout.degrees := Ne.symm (different.2.2.2.2.2.1.2.1)
  have present_marks : layout.present ≠ layout.marks := Ne.symm (different.2.2.2.2.2.2.1.1)
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, present_keys,
        present_parents, present_children, present_left, present_right, present_degrees,
        present_marks, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, present_keys, present_parents, present_children,
        present_left, present_right, present_degrees, present_marks, eq_self, true_and, false_and,
        if_false]

theorem insertion_read_table (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.table =
      heap.read layout.table := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have table_keys : layout.table ≠ layout.keys := Ne.symm (different.1.2.2.2.2.2.2.2)
  have table_parents : layout.table ≠ layout.parents := Ne.symm (different.2.1.2.2.2.2.2.2)
  have table_children : layout.table ≠ layout.children := Ne.symm (different.2.2.1.2.2.2.2.2)
  have table_left : layout.table ≠ layout.left := Ne.symm (different.2.2.2.1.2.2.2.2)
  have table_right : layout.table ≠ layout.right := Ne.symm (different.2.2.2.2.1.2.2.2)
  have table_degrees : layout.table ≠ layout.degrees := Ne.symm (different.2.2.2.2.2.1.2.2)
  have table_marks : layout.table ≠ layout.marks := Ne.symm (different.2.2.2.2.2.2.1.2)
  have table_present : layout.table ≠ layout.present := Ne.symm (different.2.2.2.2.2.2.2)
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, table_keys, table_parents, table_children,
        table_left, table_right, table_degrees, table_marks, table_present, eq_self, false_and,
        if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick, table_keys,
        table_parents, table_children, table_left, table_right, table_degrees, table_marks,
        table_present, eq_self, false_and, if_false]


theorem insertion_minimum (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (freshMinimum : layout.minimum < 0 ∨ vertex ≠ layout.minimum) :
    (insertionLayout heap queue layout vertex key).minimum =
      if layout.minimum < 0 then vertex
      else if key < heap.read layout.keys layout.minimum then vertex else layout.minimum := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  unfold insertionLayout addRootLayout
  dsimp only
  by_cases empty : layout.minimum < 0
  · simp [empty]
  · have fresh : layout.minimum ≠ vertex := Ne.symm (freshMinimum.resolve_left empty)
    simp [empty, insertionHeaderHeap, rootHeaderHeap, insertRingHeap,
      set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
      keys_parents, keys_children, keys_left, keys_right, keys_degrees, keys_marks,
      keys_present, fresh]
    split <;> rfl

theorem insertion_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (freshMinimum : layout.minimum < 0 ∨ vertex ≠ layout.minimum) :
    snapshot (insertionHeap heap queue layout vertex key)
      (insertionLayout heap queue layout vertex key) =
        (snapshot heap layout).insertSingleton vertex key := by
  have fields := add_root_layout_refs (insertionHeaderHeap heap queue layout vertex key)
    {layout with size := layout.size + 1} vertex
  change (insertionLayout heap queue layout vertex key).refs = layout.refs at fields
  simp only [Layout.refs, List.cons.injEq] at fields
  apply snapshot_ext
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).keys = _
    rw [fields.1]
    exact insertion_read_keys heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).parents = _
    rw [fields.2.1]
    exact insertion_read_parents heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).children = _
    rw [fields.2.2.1]
    exact insertion_read_children heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).left = _
    rw [fields.2.2.2.1]
    exact insertion_read_left heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).right = _
    rw [fields.2.2.2.2.1]
    exact insertion_read_right heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).degrees = _
    rw [fields.2.2.2.2.2.1]
    exact insertion_read_degrees heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).marks = _
    rw [fields.2.2.2.2.2.2.1]
    exact insertion_read_marks heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).present = _
    rw [fields.2.2.2.2.2.2.2.1]
    exact insertion_read_present heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).table = _
    rw [fields.2.2.2.2.2.2.2.2.1]
    exact insertion_read_table heap queue layout valid vertex key
  · exact insertion_minimum heap queue layout valid vertex key freshMinimum
  · exact insertion_size heap queue layout vertex key

/-- Fresh insertion preserves the complete finite-forest representation and
    inserts precisely the supplied key/handle pair. -/
theorem QueueRep.insert {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (nonnegative : 0 ≤ vertex) (absent : heap.read layout.present vertex = 0) :
    ∃ afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
        (insertionHeap heap queue layout vertex key) () ∧
      QueueRep (insertionHeap heap queue layout vertex key) queue
        (insertionLayout heap queue layout vertex key) afterForest ∧
      afterForest.entries.Perm ((vertex, key) :: forest.entries) ∧
      afterForest.length = forest.length + 1 ∧ afterForest.marks = forest.marks := by
  have fresh : layout.minimum < 0 ∨ vertex ≠ layout.minimum := by
    by_cases empty : layout.minimum < 0
    · exact Or.inl empty
    · right
      have nonempty : forest ≠ [] := by intro same; exact empty (rep.empty_iff.mpr same)
      have minimum := (rep.minimum nonempty).2.1
      intro same
      rw [same, minimum] at absent
      contradiction
  obtain ⟨afterForest, represented, entries, roots, marks⟩ :=
    rep.represented.insert_singleton (key := key) nonnegative absent
  refine ⟨afterForest, push_insert_summary heap queue layout rep.layoutValid vertex key absent,
    ⟨insertion_layout heap queue layout rep.layoutValid vertex key, ?_⟩, entries, roots, marks⟩
  rw [insertion_snapshot heap queue layout rep.layoutValid vertex key fresh]
  exact represented

/-- The event model counts each explicitly instrumented primitive category once. -/
def heapEventWork (before after : Heap) : Nat :=
  let cost := Heap.cost before after
  cost "heap_operations" + cost "heap_comparisons" + cost "heap_links" +
    cost "heap_cuts" + cost "heap_root_scans" + cost "heap_degree_scans" + cost "heap_promotions"

theorem insertion_event_work (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : heapEventWork heap (insertionHeap heap queue layout vertex key) ≤ 2 := by
  unfold heapEventWork
  rw [insertion_cost]
  by_cases empty : layout.minimum < 0 <;> simp [empty, Clocks.single]

theorem push_decrease_event_work (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) : heapEventWork heap after ≤ 2 * cuts + 4 := by
  obtain ⟨comparisons, bounded, equation⟩ :=
    push_decrease_cost heap after queue layout finalLayout vertex key cuts effect
  simp [heapEventWork, equation, Clocks.single]
  omega

/-- Insertion's measured compiled work plus newly deposited potential is at
    most six. The stored forest and contents are preserved by the same run. -/
theorem QueueRep.insert_amortized {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (nonnegative : 0 ≤ vertex) (absent : heap.read layout.present vertex = 0) :
    ∃ afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
        (insertionHeap heap queue layout vertex key) () ∧
      QueueRep (insertionHeap heap queue layout vertex key) queue
        (insertionLayout heap queue layout vertex key) afterForest ∧
      afterForest.entries.Perm ((vertex, key) :: forest.entries) ∧
      heapEventWork heap (insertionHeap heap queue layout vertex key) +
        Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
          Algo2Lean.Fibonacci.scaledPotential forest.counts + 6 := by
  obtain ⟨afterForest, execution, represented, contents, roots, marks⟩ := rep.insert vertex key nonnegative absent
  refine ⟨afterForest, execution, represented, contents, ?_⟩
  have bound := Algo2Lean.Fibonacci.insertion_work_bound forest.length forest.marks
    (heapEventWork heap (insertionHeap heap queue layout vertex key))
    (insertion_event_work heap queue layout vertex key)
  simpa only [Algo2Lean.Fibonacci.Forest.counts, roots, marks] using bound

/-- The finite represented forest supplies termination without assumptions on
    any unused integer sequence index. -/
theorem QueueRep.parent_rank {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest) :
    ScopedParentRank heap layout (fun vertex => heap.read layout.present vertex ≠ 0)
      forest.parentRank := by
  intro vertex active nonroot
  exact rep.represented.parent_rank active nonroot

/-- Every strict decrease of a present vertex in a represented finite forest
    has a compiled execution, with at most its initial ancestor rank many cuts. -/
theorem QueueRep.decrease_execution {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (present : heap.read layout.present vertex ≠ 0)
    (smaller : key < heap.read layout.keys vertex) :
    ∃ after finalLayout cuts,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
        layout after finalLayout cuts ∧
      finalLayout.Valid after queue ∧ cuts ≤ forest.parentRank vertex := by
  exact push_decrease_summary_scoped heap queue layout rep.layoutValid _ forest.parentRank
    rep.parent_rank vertex key present present smaller


/-- The compiled link performs precisely the shared forest-storage operation. -/
theorem link_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (child parent : Int) :
    snapshot (linkHeap heap layout child parent) layout =
      (snapshot heap layout).link child parent := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  by_cases empty : heap.read layout.children parent < 0
  all_goals
    simp only [Heap.read] at empty
    apply snapshot_ext
    all_goals try funext index
    all_goals simp [snapshot, linkHeap, linkRingHeap, linkHeaderHeap, Heap.read, Heap.write, Heap.tick,
      Algo2Lean.Fibonacci.Snapshot.link, Algo2Lean.Fibonacci.Rings.write,
      Algo2Lean.Fibonacci.Rings.insertBeforeLeft, Algo2Lean.Fibonacci.Rings.insertBeforeRight,
      empty, keys_parents, keys_children, keys_left, keys_right, keys_degrees, keys_marks,
      parents_children, parents_left, parents_right, parents_degrees, parents_marks, children_left,
      children_right, children_degrees, children_marks, left_right, left_degrees, left_marks,
      right_degrees, right_marks, degrees_marks, Ne.symm parents_children, Ne.symm parents_left,
      Ne.symm parents_right, Ne.symm parents_degrees, Ne.symm parents_marks, Ne.symm
      parents_present, Ne.symm parents_table, Ne.symm children_left, Ne.symm children_right, Ne.symm
      children_degrees, Ne.symm children_marks, Ne.symm children_present, Ne.symm children_table,
      Ne.symm left_right, Ne.symm left_degrees, Ne.symm left_marks, Ne.symm left_present, Ne.symm
      left_table, Ne.symm right_degrees, Ne.symm right_marks, Ne.symm right_present, Ne.symm
      right_table, Ne.symm degrees_marks, Ne.symm degrees_present, Ne.symm degrees_table, Ne.symm
      marks_present, Ne.symm marks_table]

/-- Root insertion matches the forest-storage effect for any detached tree. -/
theorem add_root_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    snapshot (addRootHeap heap queue layout vertex) (addRootLayout heap layout vertex) =
      (snapshot heap layout).addRoot vertex := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  by_cases empty : layout.minimum < 0
  · apply snapshot_ext
    all_goals try funext index
    all_goals simp [snapshot, addRootHeap, addRootLayout, rootHeaderHeap, set_FibonacciHeap_minimum, Heap.read,
      Heap.write, Heap.writeField, Algo2Lean.Fibonacci.Snapshot.addRoot,
      Algo2Lean.Fibonacci.Rings.write, empty, keys_parents, keys_left, keys_right, keys_marks,
      parents_left, parents_right, parents_marks, children_left, children_right, children_marks,
      left_right, left_marks, right_marks, degrees_marks, Ne.symm parents_children, Ne.symm
      parents_left, Ne.symm parents_right, Ne.symm parents_degrees, Ne.symm parents_marks, Ne.symm
      parents_present, Ne.symm parents_table, Ne.symm left_right, Ne.symm left_degrees, Ne.symm
      left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm right_degrees, Ne.symm
      right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm marks_present, Ne.symm
      marks_table]
  · by_cases smaller : heap.read layout.keys vertex < heap.read layout.keys layout.minimum
    all_goals
      simp only [Heap.read] at smaller
      apply snapshot_ext
      all_goals try funext index
      all_goals simp [snapshot, addRootHeap, addRootLayout, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
      Heap.read, Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Snapshot.addRoot,
      Algo2Lean.Fibonacci.Rings.write, Algo2Lean.Fibonacci.Rings.insertAfterLeft,
      Algo2Lean.Fibonacci.Rings.insertAfterRight, empty, smaller, keys_parents, keys_left,
      keys_right, keys_marks, parents_left, parents_right, parents_marks, children_left,
      children_right, children_marks, left_right, left_marks, right_marks, degrees_marks, Ne.symm
      parents_children, Ne.symm parents_left, Ne.symm parents_right, Ne.symm parents_degrees,
      Ne.symm parents_marks, Ne.symm parents_present, Ne.symm parents_table, Ne.symm left_right,
      Ne.symm left_degrees, Ne.symm left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm
      right_degrees, Ne.symm right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm
      marks_present, Ne.symm marks_table]


@[simp] theorem snapshot_tick (heap : Heap) (layout : Layout) (clock : String) (amount : Nat) :
    snapshot (heap.tick clock amount) layout = snapshot heap layout := rfl

theorem table_write_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree value : Int) :
    snapshot (heap.write layout.table degree value) layout =
      {snapshot heap layout with table := Algo2Lean.Fibonacci.Rings.write (heap.read layout.table) degree value} := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, Heap.read, Heap.write,
    Algo2Lean.Fibonacci.Rings.write, keys, parents, children, left, right, degrees, marks, present]

private theorem rebuild_clear_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree : Int) :
    snapshot (rebuildClear heap layout degree) layout =
      {snapshot heap layout with table := Algo2Lean.Fibonacci.Rings.write (heap.read layout.table) degree (-1)} := by
  exact table_write_snapshot (heap.tick "heap_degree_scans") queue layout
    (Layout.Valid.tick _ _ _ valid _ _) degree (-1)

/-- A compiler-level table visit implements exactly the pure reconstruction step. -/
theorem rebuild_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree : Int) :
    snapshot (rebuildHeap heap queue layout degree) (rebuildLayout heap layout degree) =
      (snapshot heap layout).rebuildAt degree := by
  unfold rebuildHeap rebuildLayout Algo2Lean.Fibonacci.Snapshot.rebuildAt
  dsimp only
  have readTable : (snapshot heap layout).table = heap.read layout.table := rfl
  simp only [readTable]
  by_cases empty : heap.read layout.table degree < 0
  · simp only [if_pos empty]
    exact rebuild_clear_snapshot heap queue layout valid degree
  · simp only [if_neg empty]
    have ready : layout.Valid (rebuildClear heap layout degree) queue :=
      Layout.Valid.write _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _ _
    rw [add_root_snapshot _ _ _ ready]
    rw [rebuild_clear_snapshot heap queue layout valid degree]

theorem rebuild_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (degree : Int) (clock : String) :
    (rebuildHeap heap queue layout degree).clocks clock = heap.clocks clock +
      Clocks.single "heap_degree_scans" 1 clock + Clocks.single "heap_comparisons"
        (if heap.read layout.table degree < 0 then 0 else if layout.minimum < 0 then 0 else 1) clock := by
  unfold rebuildHeap
  dsimp only
  split
  · by_cases scan : clock = "heap_degree_scans" <;> simp_all [rebuildClear, Clocks.single]
  · rw [add_root_clocks]
    by_cases scan : clock = "heap_degree_scans" <;> simp_all [rebuildClear, Clocks.single]

/-- Every finite pure reconstruction is realized by the compiled loop, with
    exactly its comparisons and one degree-scan tick per visited bucket. -/
theorem realize_bucket_rebuild (maximum : Int) (before after : Algo2Lean.Fibonacci.Snapshot)
    (degree : Int) (insertions comparisons : Nat)
    (execution : Algo2Lean.Fibonacci.BucketRebuild maximum before degree after insertions comparisons)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ finalHeap finalLayout,
      RebuildEffect queue maximum heap layout degree finalHeap finalLayout ∧
      finalLayout.Valid finalHeap queue ∧ snapshot finalHeap finalLayout = after ∧
      ∀ clock, finalHeap.clocks clock = heap.clocks clock +
        Clocks.single "heap_degree_scans" (maximum + 1 - degree).toNat clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  induction execution generalizing heap layout with
  | done state degree past =>
    refine ⟨heap, layout, .done _ _ _ past, valid, observed, ?_⟩
    intro clock
    have zero : (maximum + 1 - degree).toNat = 0 := by omega
    simp [zero, Clocks.single]
  | @skip state final index count comparisons inside empty rest ih =>
    have next : snapshot (rebuildHeap heap queue layout index) (rebuildLayout heap layout index) =
        state.rebuildAt index := by rw [rebuild_snapshot heap queue layout valid, observed]
    obtain ⟨finalHeap, finalLayout, effect, ready, result, clocks⟩ :=
      ih (rebuildHeap heap queue layout index) (rebuildLayout heap layout index)
        (rebuild_layout heap queue layout valid index) next
    refine ⟨finalHeap, finalLayout, .step inside effect, ready, result, ?_⟩
    have empty' : heap.read layout.table index < 0 := by
      change (snapshot heap layout).table index < 0
      rw [observed]
      exact empty
    have count : (maximum + 1 - index).toNat = (maximum + 1 - (index + 1)).toNat + 1 := by omega
    intro clock
    rw [clocks, rebuild_clocks]
    simp only [if_pos empty']
    by_cases scan : clock = "heap_degree_scans" <;> by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [Clocks.single] <;> omega
  | @insert state final index count comparisons inside occupied rest ih =>
    have next : snapshot (rebuildHeap heap queue layout index) (rebuildLayout heap layout index) =
        state.rebuildAt index := by rw [rebuild_snapshot heap queue layout valid, observed]
    obtain ⟨finalHeap, finalLayout, effect, ready, result, clocks⟩ :=
      ih (rebuildHeap heap queue layout index) (rebuildLayout heap layout index)
        (rebuild_layout heap queue layout valid index) next
    refine ⟨finalHeap, finalLayout, .step inside effect, ready, result, ?_⟩
    have occupied' : ¬heap.read layout.table index < 0 := by
      have same : heap.read layout.table index = state.table index := congrArg (fun s => s.table index) observed
      omega
    have minimum : layout.minimum = state.minimum := congrArg Algo2Lean.Fibonacci.Snapshot.minimum observed
    have count : (maximum + 1 - index).toNat = (maximum + 1 - (index + 1)).toNat + 1 := by omega
    intro clock
    rw [clocks, rebuild_clocks]
    simp only [if_neg occupied', minimum]
    by_cases scan : clock = "heap_degree_scans" <;> by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [Clocks.single] <;> omega

/-- Reconstruction of finite degree buckets produces a complete heap and the
    exact compiled scan/comparison costs; clients need no loop transcript. -/
theorem rebuild_from_buckets (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (roots : Algo2Lean.Fibonacci.Forest) (maximum : Int)
    (represented : Algo2Lean.Fibonacci.SplitRepresented (snapshot heap layout) [] roots)
    (buckets : Algo2Lean.Fibonacci.Buckets (snapshot heap layout) roots)
    (bound : Algo2Lean.Fibonacci.ScratchBound (snapshot heap layout) maximum) :
    ∃ finalHeap finalLayout forest comparisons,
      RebuildEffect queue maximum heap layout 0 finalHeap finalLayout ∧
      QueueRep finalHeap queue finalLayout forest ∧ forest.Perm roots ∧
      (forest.map Algo2Lean.Fibonacci.Node.degree).Nodup ∧ comparisons ≤ forest.length ∧
      Heap.cost heap finalHeap = fun clock =>
        Clocks.single "heap_degree_scans" (maximum + 1).toNat clock +
          Clocks.single "heap_comparisons" comparisons clock := by
  obtain ⟨after, forest, comparisons, execution, ready, contents, unique, charged⟩ :=
    Algo2Lean.Fibonacci.rebuild_complete (snapshot heap layout) roots maximum represented buckets bound
  obtain ⟨finalHeap, finalLayout, effect, finalValid, observed, clocks⟩ :=
    realize_bucket_rebuild maximum (snapshot heap layout) after 0 roots.length comparisons
      execution heap queue layout valid rfl
  refine ⟨finalHeap, finalLayout, forest, comparisons, effect, ⟨finalValid, ?_⟩,
    contents, unique, charged, ?_⟩
  · rw [observed]
    exact ready
  · funext clock
    unfold Heap.cost
    rw [clocks]
    simp only [Int.sub_zero]
    omega

/-- Degree-table scans and root-key comparisons are the complete work of the
    compiled reconstruction loop. -/
theorem rebuild_event_work (heap finalHeap : Heap) (maximum : Int) (comparisons : Nat)
    (cost : Heap.cost heap finalHeap = fun clock =>
      Clocks.single "heap_degree_scans" (maximum + 1).toNat clock +
        Clocks.single "heap_comparisons" comparisons clock) :
    heapEventWork heap finalHeap = (maximum + 1).toNat + comparisons := by
  simp [heapEventWork, cost, Clocks.single, Nat.add_comm]

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

theorem detach_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    snapshot (detachHeap heap queue layout) (detachLayout heap layout) =
      (snapshot heap layout).detachMinimum := by
  have keys_left : layout.keys ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have keys_right : layout.keys ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have parents_left : layout.parents ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have parents_right : layout.parents ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have children_left : layout.children ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have children_right : layout.children ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have left_right : layout.left ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have right_left : layout.right ≠ layout.left := Ne.symm left_right
  have degrees_left : layout.degrees ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_right : layout.degrees ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have marks_left : layout.marks ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have marks_right : layout.marks ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have present_left : layout.present ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have present_right : layout.present ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_left : layout.table ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_right : layout.table ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, detachHeap, detachLayout, pendingMinimum, removeHeap,
    set_FibonacciHeap_minimum, Heap.read, Heap.write, Heap.writeField, Heap.tick,
    Algo2Lean.Fibonacci.Snapshot.detachMinimum, Algo2Lean.Fibonacci.Rings.removeLeft,
    Algo2Lean.Fibonacci.Rings.removeRight, Algo2Lean.Fibonacci.Rings.write,
    keys_left, keys_right, parents_left, parents_right, children_left, children_right, left_right, right_left, degrees_left, degrees_right, marks_left, marks_right, present_left, present_right, table_left, table_right]


theorem collision_parent_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree : Int) :
    collisionParent heap layout vertex degree = (snapshot heap layout).collisionParent vertex degree := by
  have different : layout.keys ≠ layout.table := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  simp [collisionParent, collisionStart, Algo2Lean.Fibonacci.Snapshot.collisionParent,
    snapshot, Heap.read, Heap.write, different]

theorem collision_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree : Int) :
    snapshot (collisionHeap heap layout vertex degree) layout =
      (snapshot heap layout).collision vertex degree := by
  have different : layout.keys ≠ layout.table := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have ready : layout.Valid (collisionStart heap layout degree) queue := Layout.Valid.tick _ _ _ (Layout.Valid.write _ _ _ valid layout.table degree (-1)) "heap_comparisons" 1
  unfold collisionHeap
  rw [link_snapshot (collisionStart heap layout degree) queue layout ready]
  simp only [collisionStart, snapshot_tick, table_write_snapshot heap queue layout valid degree (-1)]
  simp only [collisionChild, collisionParent, collisionStart, Heap.read_tick]
  simp only [Heap.read_write_other_ref _ _ _ _ _ _ different]
  unfold Algo2Lean.Fibonacci.Snapshot.collision
  dsimp only [snapshot]
  split <;> rfl

theorem detach_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (clock : String) :
    (detachHeap heap queue layout).clocks clock = heap.clocks clock + Clocks.single "heap_root_scans" 1 clock := by
  by_cases clock = "heap_root_scans" <;> simp_all [detachHeap, removeHeap, Heap.tick, Clocks.single, set_FibonacciHeap_minimum, Heap.writeField]

theorem collision_clocks (heap : Heap) (layout : Layout) (vertex degree : Int) (clock : String) :
    (collisionHeap heap layout vertex degree).clocks clock = heap.clocks clock +
      Clocks.single "heap_comparisons" 1 clock + Clocks.single "heap_links" 1 clock := by
  unfold collisionHeap linkHeap linkRingHeap
  dsimp only
  split <;> by_cases clock = "heap_links" <;> by_cases clock = "heap_comparisons" <;> simp_all [linkHeaderHeap, collisionStart, Heap.tick, Clocks.single]

/-- Every finite mathematical collision trace is realized by the compiled
    pointer operations with precisely one comparison and one link per collision. -/
theorem realize_bucket_collisions (before after : Algo2Lean.Fibonacci.Snapshot)
    (vertex degree finalVertex finalDegree : Int) (links : Nat)
    (run : Algo2Lean.Fibonacci.BucketCollisions before vertex degree after finalVertex finalDegree links)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ finalHeap,
      CollisionEffect layout heap vertex degree finalHeap finalVertex finalDegree links ∧
      layout.Valid finalHeap queue ∧ snapshot finalHeap layout = after ∧
      ∀ clock, finalHeap.clocks clock = heap.clocks clock +
        Clocks.single "heap_comparisons" links clock + Clocks.single "heap_links" links clock := by
  induction run generalizing heap layout with
  | done state vertex degree empty =>
    refine ⟨heap, .done _ _ _ ?_, valid, observed, ?_⟩
    · change (snapshot heap layout).table degree < 0
      rw [observed]
      exact empty
    · intro clock
      simp [Clocks.single]
  | @step state after vertex degree result finalDegree links occupied rest ih =>
    have next : snapshot (collisionHeap heap layout vertex degree) layout = state.collision vertex degree := by
      rw [collision_snapshot heap queue layout valid, observed]
    have parent : collisionParent heap layout vertex degree = state.collisionParent vertex degree := by
      rw [collision_parent_snapshot heap queue layout valid, observed]
    obtain ⟨finalHeap, effect, finalValid, finalObserved, clocks⟩ := ih
      (collisionHeap heap layout vertex degree) layout (collision_layout heap queue layout valid vertex degree) next
    refine ⟨finalHeap, .step ?_ (by simpa only [parent] using effect), finalValid, finalObserved, ?_⟩
    · change 0 ≤ (snapshot heap layout).table degree
      rw [observed]
      exact occupied
    · intro clock
      rw [clocks, collision_clocks]
      by_cases clock = "heap_comparisons" <;> by_cases clock = "heap_links" <;>
        simp_all [Clocks.single, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


/-- Realize the finite pending-root phase. The continuation can use any verified
    reconstruction of its final buckets; clocks are counted independently. -/
theorem realize_root_consumption (before after : Algo2Lean.Fibonacci.Snapshot)
    (maximum finalMaximum : Int) (roots links : Nat)
    (run : Algo2Lean.Fibonacci.RootConsumption before maximum after finalMaximum roots links)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ tailHeap tailLayout,
      tailLayout.Valid tailHeap queue ∧ snapshot tailHeap tailLayout = after ∧
      (∀ finalHeap finalLayout, RebuildEffect queue finalMaximum tailHeap tailLayout 0 finalHeap finalLayout →
        ConsumeEffect queue heap layout maximum finalHeap finalLayout roots links) ∧
      (∀ clock, tailHeap.clocks clock = heap.clocks clock +
        Clocks.single "heap_root_scans" roots clock +
        Clocks.single "heap_comparisons" links clock + Clocks.single "heap_links" links clock) := by
  induction run generalizing heap layout with
  | done state maximum empty =>
    refine ⟨heap, layout, valid, observed, ?_, ?_⟩
    · intro finalHeap finalLayout rebuild
      apply ConsumeEffect.done _ rebuild
      change (snapshot heap layout).minimum < 0
      rw [observed]
      exact empty
    · intro clock
      simp [Clocks.single]
  | @step before merged after maximum vertex degree finalMaximum links roots tailLinks nonempty collisions rest ih =>
    have detachedSnapshot : snapshot (detachHeap heap queue layout) (detachLayout heap layout) = before.detachMinimum := by
      rw [detach_snapshot heap queue layout valid, observed]
    have detachedValid := detach_layout heap queue layout valid
    obtain ⟨mergedHeap, collisionEffect, mergedValid, mergedSnapshot, collisionClocks⟩ :=
      realize_bucket_collisions _ _ _ _ _ _ _ collisions
        (detachHeap heap queue layout) queue (detachLayout heap layout) detachedValid detachedSnapshot
    have minimum : layout.minimum = before.minimum := congrArg Algo2Lean.Fibonacci.Snapshot.minimum observed
    have inputDegree : before.detachMinimum.degrees before.minimum =
        (detachHeap heap queue layout).read layout.degrees layout.minimum := by
      rw [← detachedSnapshot, ← minimum]
      rfl
    have storedSnapshot : snapshot (mergedHeap.write layout.table degree vertex) (detachLayout heap layout) =
        {merged with table := Algo2Lean.Fibonacci.Rings.write merged.table degree vertex} := by
      calc
        _ = {(snapshot mergedHeap (detachLayout heap layout)) with table := Algo2Lean.Fibonacci.Rings.write (snapshot mergedHeap (detachLayout heap layout)).table degree vertex} :=
            table_write_snapshot mergedHeap queue (detachLayout heap layout) mergedValid degree vertex
        _ = _ := by rw [mergedSnapshot]
    obtain ⟨tailHeap, tailLayout, tailValid, tailSnapshot, continuation, tailClocks⟩ :=
      ih (mergedHeap.write layout.table degree vertex) (detachLayout heap layout)
        (Layout.Valid.write _ _ _ mergedValid _ _ _) storedSnapshot
    refine ⟨tailHeap, tailLayout, tailValid, tailSnapshot, ?_, ?_⟩
    · intro finalHeap finalLayout rebuild
      apply ConsumeEffect.next (by omega)
        (by rw [inputDegree, ← minimum] at collisionEffect; exact collisionEffect)
        (continuation finalHeap finalLayout rebuild)
    · intro clock
      rw [tailClocks]
      change mergedHeap.clocks clock + _ + _ + _ = _
      rw [collisionClocks, detach_clocks]
      by_cases clock = "heap_root_scans" <;> by_cases clock = "heap_comparisons" <;>
        by_cases clock = "heap_links" <;> simp_all [Clocks.single] <;> omega


theorem RebuildEffect.clocks_monotone {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {maximum degree : Int}
    (effect : RebuildEffect queue maximum heap layout degree after finalLayout) :
    ∀ clock, heap.clocks clock ≤ after.clocks clock := by
  induction effect with
  | done => intro clock; exact Nat.le_refl _
  | @step before after current final index inside rest ih =>
    intro clock
    have next := rebuild_clocks before queue current index clock
    have later := ih clock
    omega

/-- Consolidation starts from a finite pending-root ring, not a preselected
    global minimum. It returns a represented heap, preserves every entry and
    mark, and exposes the exact instrumented work of all three phases. -/
theorem consolidate_from_forest (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (forest : Algo2Lean.Fibonacci.Forest)
    (represented : Algo2Lean.Fibonacci.SplitRepresented (snapshot heap layout) forest [])
    (emptyTable : ∀ degree, heap.read layout.table degree < 0) :
    ∃ finalHeap finalLayout afterForest links scans comparisons,
      FibonacciHeap.consolidate.Call heap queue finalHeap () ∧
      ConsumeEffect queue heap layout (-1) finalHeap finalLayout forest.length links ∧
      QueueRep finalHeap queue finalLayout afterForest ∧
      afterForest.entries.Perm forest.entries ∧ afterForest.marks = forest.marks ∧
      links + afterForest.length = forest.length ∧
      afterForest.length ≤ 2 * forest.entries.length.log2 + 2 ∧
      scans ≤ 2 * forest.entries.length.log2 + 2 ∧ comparisons ≤ afterForest.length ∧
      Heap.cost heap finalHeap = fun clock =>
        Clocks.single "heap_root_scans" forest.length clock +
        Clocks.single "heap_comparisons" (links + comparisons) clock +
        Clocks.single "heap_links" links clock + Clocks.single "heap_degree_scans" scans clock := by
  have inputSize : (snapshot heap layout).size = forest.entries.length := by
    simpa only [List.append_nil] using represented.size
  have emptyBuckets := Algo2Lean.Fibonacci.Buckets.empty (state := snapshot heap layout) emptyTable
  have bound : Algo2Lean.Fibonacci.ScratchBound (snapshot heap layout) (-1) := by
    intro degree above
    exact emptyTable degree
  obtain ⟨after, buckets, maximum, links, pureRun, splitRep, table, maxBound, logarithmic,
      rootCount, finalSize, entries, marks⟩ :=
    represented.consume_roots emptyBuckets (-1) bound forest.entries.length inputSize (by omega)
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at rootCount entries marks
  obtain ⟨tailHeap, tailLayout, ready, observed, continuation, clocks⟩ :=
    realize_root_consumption _ _ _ _ _ _ pureRun heap queue layout valid rfl
  obtain ⟨finalHeap, finalLayout, afterForest, comparisons, rebuild, finalRep, permutation,
      unique, comparisonBound, rebuildCost⟩ :=
    rebuild_from_buckets tailHeap queue tailLayout ready buckets maximum
      (by rw [observed]; exact splitRep) (by rw [observed]; exact table)
      (by rw [observed]; exact maxBound)
  have effect := continuation finalHeap finalLayout rebuild
  have finalRootCount : links + afterForest.length = forest.length := by
    rw [permutation.length_eq]
    exact rootCount
  have rootsBound := table.roots_bound maxBound
  have maxNat : maximum.toNat ≤ 2 * forest.entries.length.log2 + 1 := by omega
  refine ⟨finalHeap, finalLayout, afterForest, links, (maximum + 1).toNat, comparisons,
    consolidate_effect_summary _ _ _ _ _ _ _ valid effect, effect, finalRep,
    (Algo2Lean.Fibonacci.Forest.entries_perm permutation).trans entries,
    (Algo2Lean.Fibonacci.Forest.marks_perm permutation).trans marks, finalRootCount,
    ?_, by omega, comparisonBound, ?_⟩
  · rw [permutation.length_eq]
    omega
  · funext clock
    have prefixClocks := clocks clock
    have suffix := congrFun rebuildCost clock
    have monotone := rebuild.clocks_monotone clock
    unfold Heap.cost at suffix ⊢
    by_cases clock = "heap_root_scans" <;> by_cases clock = "heap_comparisons" <;>
      by_cases clock = "heap_links" <;> by_cases clock = "heap_degree_scans" <;>
      simp_all [Clocks.single] <;> omega

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

/-- Removing a ring node touches only this queue's declared storage. -/
theorem remove_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (removeHeap heap layout vertex) layout.refs [queue] := by
  unfold removeHeap
  repeat' apply Heap.Modifies.write
  all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]

theorem add_root_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (addRootHeap heap queue layout vertex) layout.refs [queue] := by
  unfold addRootHeap
  dsimp only
  split
  · simp only [set_FibonacciHeap_minimum, rootHeaderHeap]
    repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]
  · split <;> simp only [set_FibonacciHeap_minimum, insertRingHeap, rootHeaderHeap]
    all_goals repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField | apply Heap.Modifies.tick
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]

theorem link_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (child parent : Int) :
    heap.Modifies (linkHeap heap layout child parent) layout.refs [queue] := by
  unfold linkHeap linkRingHeap
  dsimp only
  split <;> simp only [linkHeaderHeap]
  all_goals repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.tick
  all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]

theorem collision_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex degree : Int) :
    heap.Modifies (collisionHeap heap layout vertex degree) layout.refs [queue] := by
  have ready := ((Heap.Modifies.refl heap layout.refs [queue]).write layout.table degree (-1)
    (by simp [Layout.refs])).tick "heap_comparisons"
  exact ready.trans (link_frame _ queue layout _ _)

theorem detach_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) :
    heap.Modifies (detachHeap heap queue layout) layout.refs [queue] := by
  have prepare := (Heap.Modifies.refl heap layout.refs [queue]).writeField queue "minimum"
    (.intValue (pendingMinimum heap layout)) (by simp)
  exact (prepare.trans (remove_frame _ queue layout _)).tick "heap_root_scans"

theorem rebuild_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (degree : Int) :
    heap.Modifies (rebuildHeap heap queue layout degree) layout.refs [queue] := by
  have clear := ((Heap.Modifies.refl heap layout.refs [queue]).tick "heap_degree_scans").write
    layout.table degree (-1) (by simp [Layout.refs])
  unfold rebuildHeap
  dsimp only
  split
  · exact clear
  · exact clear.trans (add_root_frame _ queue layout _)

@[simp] theorem rebuild_layout_refs (heap : Heap) (layout : Layout) (degree : Int) :
    (rebuildLayout heap layout degree).refs = layout.refs := by
  unfold rebuildLayout
  split
  · rfl
  · exact add_root_layout_refs _ _ _

theorem RebuildEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {maximum degree : Int}
    (effect : RebuildEffect queue maximum heap layout degree after finalLayout) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | done => exact ⟨.refl _ _ _, rfl⟩
  | @step before after current final degree inside rest ih =>
    rw [rebuild_layout_refs] at ih
    exact ⟨(rebuild_frame before queue current degree).trans ih.1, ih.2⟩

theorem CollisionEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout : Layout} {vertex degree finalVertex finalDegree : Int} {links : Nat}
    (effect : CollisionEffect layout heap vertex degree after finalVertex finalDegree links) :
    heap.Modifies after layout.refs [queue] := by
  induction effect with
  | done => exact .refl _ _ _
  | step occupied rest ih => exact (collision_frame _ queue _ _ _).trans ih

theorem ConsumeEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {maximum : Int} {roots links : Nat}
    (effect : ConsumeEffect queue heap layout maximum after finalLayout roots links) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | done empty rebuild => exact rebuild.frame
  | @next before merged after current final maximum vertex degree links tailRoots tailLinks pending collisions rest ih =>
    have changed := (detach_frame before queue current).trans (collisions.frame (queue := queue))
    have stored := changed.write current.table degree vertex (by simp [Layout.refs])
    exact ⟨stored.trans ih.1, ih.2⟩

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- The first part of a cut matches the pure child-removal effect. -/
theorem remove_child_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    let headed := cutHeaderHeap heap layout vertex parent
    let decreased := headed.write layout.degrees parent (headed.read layout.degrees parent - 1)
    snapshot (removeHeap decreased layout vertex) layout =
      (snapshot heap layout).removeChild vertex parent := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  by_cases first : heap.read layout.children parent = vertex
  all_goals
    simp only [Heap.read] at first
    apply snapshot_ext
    all_goals try funext index
    all_goals simp [snapshot, cutHeaderHeap, removeHeap, Heap.read, Heap.write,
      Algo2Lean.Fibonacci.Snapshot.removeChild, Algo2Lean.Fibonacci.Rings.removeLeft,
      Algo2Lean.Fibonacci.Rings.removeRight, Algo2Lean.Fibonacci.Rings.write, first, keys_children, keys_left, keys_right, keys_degrees, parents_children, parents_left, parents_right, parents_degrees, children_left, children_right, children_degrees, left_right, left_degrees, right_degrees, Ne.symm children_left, Ne.symm children_right, Ne.symm children_degrees, Ne.symm children_marks, Ne.symm children_present, Ne.symm children_table, Ne.symm left_right, Ne.symm left_degrees, Ne.symm left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm right_degrees, Ne.symm right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm degrees_marks, Ne.symm degrees_present, Ne.symm degrees_table]
    all_goals rintro rfl; rfl

/-- The compiled cut and the pure pointer update have exactly the same snapshot. -/
theorem cut_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    snapshot (cutHeap heap queue layout vertex parent) (cutLayout heap layout vertex parent) =
      (snapshot heap layout).cut vertex parent := by
  unfold cutHeap cutTailHeap cutLayout
  simp only [snapshot_tick]
  let headed := cutHeaderHeap heap layout vertex parent
  let decreased := headed.write layout.degrees parent (headed.read layout.degrees parent - 1)
  have ready : layout.Valid (removeHeap decreased layout vertex) queue :=
    remove_preserves_layout _ _ _
      (Layout.Valid.write _ _ _ (cut_header_layout heap queue layout valid vertex parent) _ _ _) vertex
  rw [add_root_snapshot _ _ _ ready]
  rw [remove_child_snapshot heap queue layout valid vertex parent]
  rfl

/-- Mark changes are ordinary one-cell updates, independent of the call stack. -/
theorem mark_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) (marked : Bool) :
    snapshot (heap.write layout.marks vertex (if marked then 1 else 0)) layout =
      (snapshot heap layout).setMark vertex marked := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, Heap.read, Heap.write,
    Algo2Lean.Fibonacci.Snapshot.setMark, Algo2Lean.Fibonacci.Rings.write, keys_marks, parents_marks, children_marks, left_marks, right_marks, degrees_marks, Ne.symm marks_present, Ne.symm marks_table]

/-- The compiler's cascade effect and the shared finite-forest execution use
    the same snapshots and count the same cuts. -/
theorem CascadeEffect.snapshot {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts)
    (valid : layout.Valid heap queue) :
    Algo2Lean.Fibonacci.CascadeRun (snapshot heap layout) (snapshot after finalLayout) vertex cuts := by
  induction effect with
  | root before current node root => exact .root root
  | @mark before current node nonroot unmarked =>
    have markedSnapshot := mark_snapshot before queue current valid node true
    change FibonacciModuleAnalysis.snapshot (before.write current.marks node 1) current =
      (FibonacciModuleAnalysis.snapshot before current).setMark node true at markedSnapshot
    rw [markedSnapshot]
    exact .mark nonroot unmarked
  | @cut before after current final node count nonroot marked rest ih =>
    apply Algo2Lean.Fibonacci.CascadeRun.cut nonroot marked
    have next := ih (cut_layout before queue current valid node (before.read current.parents node))
    rw [cut_snapshot before queue current valid] at next
    exact next

/-- A forest-level cascade proof can be reused directly as a compiled call
    summary, preserving its final snapshot and exact number of cuts. -/
theorem realize_cascade_run (before after : Algo2Lean.Fibonacci.Snapshot) (vertex : Int) (cuts : Nat)
    (execution : Algo2Lean.Fibonacci.CascadeRun before after vertex cuts)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ finalHeap finalLayout,
      CascadeEffect queue heap layout vertex finalHeap finalLayout cuts ∧
      finalLayout.Valid finalHeap queue ∧ snapshot finalHeap finalLayout = after := by
  induction execution generalizing heap layout with
  | @root state vertex root =>
    refine ⟨heap, layout, .root heap layout vertex ?_, valid, observed⟩
    change (snapshot heap layout).parents vertex < 0
    rw [observed]
    exact root
  | @mark state vertex nonroot unmarked =>
    have parent : 0 ≤ heap.read layout.parents vertex := by
      change 0 ≤ (snapshot heap layout).parents vertex
      rw [observed]
      exact nonroot
    have clear : heap.read layout.marks vertex = 0 := by
      change (snapshot heap layout).marks vertex = 0
      rw [observed]
      exact unmarked
    refine ⟨heap.write layout.marks vertex 1, layout, .mark heap layout vertex parent clear,
      Layout.Valid.write _ _ _ valid _ _ _, ?_⟩
    have markedSnapshot := mark_snapshot heap queue layout valid vertex true
    change snapshot (heap.write layout.marks vertex 1) layout =
      (snapshot heap layout).setMark vertex true at markedSnapshot
    rw [markedSnapshot, observed]
  | @cut state final vertex count nonroot marked next ih =>
    have parent : 0 ≤ heap.read layout.parents vertex := by
      change 0 ≤ (snapshot heap layout).parents vertex
      rw [observed]
      exact nonroot
    have marked' : heap.read layout.marks vertex ≠ 0 := by
      change (snapshot heap layout).marks vertex ≠ 0
      rw [observed]
      exact marked
    have parentRead : heap.read layout.parents vertex = state.parents vertex :=
      congrArg (fun state => state.parents vertex) observed
    have nextObserved :
        snapshot (cutHeap heap queue layout vertex (heap.read layout.parents vertex))
          (cutLayout heap layout vertex (heap.read layout.parents vertex)) =
            state.cut vertex (state.parents vertex) := by
      rw [cut_snapshot heap queue layout valid, observed, parentRead]
    obtain ⟨finalHeap, finalLayout, effect, ready, result⟩ :=
      ih (cutHeap heap queue layout vertex (heap.read layout.parents vertex))
        (cutLayout heap layout vertex (heap.read layout.parents vertex))
        (cut_layout heap queue layout valid vertex _) nextObserved
    refine ⟨finalHeap, finalLayout, .cut parent marked' ?_, ready, result⟩
    simpa only [parentRead] using effect

/-- The public operation's initial key update has no other observable effect. -/
theorem lower_key_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    snapshot (lowerKeyHeap heap layout vertex key) layout =
      (snapshot heap layout).lowerKey vertex key := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, lowerKeyHeap, Heap.read, Heap.write, Heap.tick,
    Algo2Lean.Fibonacci.Snapshot.lowerKey, Algo2Lean.Fibonacci.Rings.write,
    Ne.symm keys_parents, Ne.symm keys_children, Ne.symm keys_left, Ne.symm keys_right,
    Ne.symm keys_degrees, Ne.symm keys_marks, Ne.symm keys_present, Ne.symm keys_table]

/-- The final comparison changes only the minimum pointer. -/
theorem finish_decrease_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) :
    snapshot (finishDecreaseHeap heap queue layout vertex) (finishDecreaseLayout heap layout vertex) =
      (snapshot heap layout).finishDecrease vertex := by
  unfold finishDecreaseHeap finishDecreaseLayout
  dsimp only
  split <;> apply snapshot_ext
  all_goals try funext index
  all_goals simp_all [snapshot, Algo2Lean.Fibonacci.Snapshot.finishDecrease,
    set_FibonacciHeap_minimum, Heap.writeField, Heap.read, Heap.tick] <;> omega

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- Cutting and repairing parent links stays inside the queue's footprint. -/
theorem cut_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) : heap.Modifies (cutHeap heap queue layout vertex parent) layout.refs [queue] := by
  have header : heap.Modifies (cutHeaderHeap heap layout vertex parent) layout.refs [queue] := by
    unfold cutHeaderHeap
    split
    · exact (Heap.Modifies.refl _ _ _).write _ _ _ (by simp [Layout.refs])
    · exact .refl _ _ _
  have decreased := header.write layout.degrees parent
    ((cutHeaderHeap heap layout vertex parent).read layout.degrees parent - 1) (by simp [Layout.refs])
  exact ((decreased.trans (remove_frame _ queue layout vertex)).trans
    (add_root_frame _ queue layout vertex)).tick "heap_cuts"

theorem CascadeEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | root => exact ⟨.refl _ _ _, rfl⟩
  | mark => exact ⟨(Heap.Modifies.refl _ _ _).write _ _ _ (by simp [Layout.refs]), rfl⟩
  | cut nonroot marked rest ih =>
    rw [cut_layout_refs] at ih
    exact ⟨(cut_frame _ _ _ _ _).trans ih.1, ih.2⟩

theorem finish_decrease_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : heap.Modifies (finishDecreaseHeap heap queue layout vertex) layout.refs [queue] := by
  unfold finishDecreaseHeap
  dsimp only
  split
  · exact ((Heap.Modifies.refl _ _ _).tick "heap_comparisons").writeField queue "minimum" (.intValue vertex) (by simp)
  · exact (Heap.Modifies.refl _ _ _).tick "heap_comparisons"

theorem DecreaseEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (effect : DecreaseEffect queue vertex key heap layout after finalLayout cuts) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  cases effect with
  | root => exact ⟨finish_decrease_frame _ _ _ _, finish_decrease_layout_refs _ _ _⟩
  | ordered => exact ⟨((Heap.Modifies.refl _ _ _).tick "heap_comparisons").trans
      (finish_decrease_frame _ _ _ _), finish_decrease_layout_refs _ _ _⟩
  | @cut middle _ middleLayout count nonroot unordered cascade =>
    have framed := cascade.frame
    rw [cut_layout_refs] at framed
    have finished := finish_decrease_frame middle queue middleLayout vertex
    rw [framed.2] at finished
    exact ⟨(((Heap.Modifies.refl _ _ _).tick "heap_comparisons").trans (cut_frame _ _ _ _ _)).trans
      (framed.1.trans finished), (finish_decrease_layout_refs _ _ _).trans framed.2⟩

theorem push_decrease_frame (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  have preparation := (((Heap.Modifies.refl heap layout.refs [queue]).tick "heap_operations").tick
    "heap_comparisons").write layout.keys vertex key (by simp [Layout.refs])
  exact ⟨preparation.trans effect.frame.1, effect.frame.2⟩

theorem insertion_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : heap.Modifies (insertionHeap heap queue layout vertex key) layout.refs [queue] ∧
      (insertionLayout heap queue layout vertex key).refs = layout.refs := by
  have header : heap.Modifies (insertionHeaderHeap heap queue layout vertex key) layout.refs [queue] := by
    unfold insertionHeaderHeap set_FibonacciHeap_size
    repeat' first | apply Heap.Modifies.writeField | apply Heap.Modifies.write | apply Heap.Modifies.tick
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]
  exact ⟨header.trans (add_root_frame _ _ _ _), add_root_layout_refs _ _ _⟩

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- The complete set of clocks owned by the heap implementation. -/
def heapClocks : List String :=
  ["heap_operations", "heap_comparisons", "heap_links", "heap_cuts",
    "heap_root_scans", "heap_degree_scans", "heap_promotions"]

/-- Client bookkeeping clocks survive every queue call unchanged. -/
def PreservesOtherClocks (before after : Heap) : Prop :=
  ∀ clock, clock ∉ heapClocks → after.clocks clock = before.clocks clock

theorem push_decrease_clocks (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) :
    ∃ comparisons, comparisons ≤ cuts + 3 ∧ ∀ clock,
      after.clocks clock = heap.clocks clock + Clocks.single "heap_operations" 1 clock +
        Clocks.single "heap_cuts" cuts clock + Clocks.single "heap_comparisons" comparisons clock := by
  obtain ⟨comparisons, bounded, equation⟩ := effect.clocks
  refine ⟨comparisons + 1, by omega, ?_⟩
  intro clock
  rw [equation]
  by_cases op : clock = "heap_operations" <;> by_cases cut : clock = "heap_cuts" <;>
    by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [lowerKeyHeap, Clocks.single] <;> omega

/-- A public update contract records the call, its local footprint, and its exact
    operation/cut/comparison cost. The forest proof supplies the snapshot. -/
structure UpdateContract (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat) : Prop where
  summary : FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after ()
  valid : finalLayout.Valid after queue
  frame : heap.Modifies after layout.refs [queue]
  refs : finalLayout.refs = layout.refs
  clocks : ∃ comparisons, comparisons ≤ cuts + 3 ∧ ∀ clock,
    after.clocks clock = heap.clocks clock + Clocks.single "heap_operations" 1 clock +
      Clocks.single "heap_cuts" cuts clock + Clocks.single "heap_comparisons" comparisons clock

theorem UpdateContract.cost {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (contract : UpdateContract heap after queue layout finalLayout vertex key cuts) :
    ∃ comparisons, comparisons ≤ cuts + 3 ∧ Heap.cost heap after = fun clock =>
      Clocks.single "heap_operations" 1 clock + Clocks.single "heap_cuts" cuts clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  obtain ⟨comparisons, bounded, clocks⟩ := contract.clocks
  refine ⟨comparisons, bounded, ?_⟩
  funext clock
  simp [Heap.cost, clocks clock]
  omega

/-- The cut accounting exposes a constant amount of extra work per cut. -/
theorem UpdateContract.event_work {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (contract : UpdateContract heap after queue layout finalLayout vertex key cuts) :
    heapEventWork heap after ≤ 2 * cuts + 4 := by
  obtain ⟨comparisons, bounded, equation⟩ := contract.cost
  simp [heapEventWork, equation, Clocks.single]
  omega

theorem UpdateContract.other_clocks {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (contract : UpdateContract heap after queue layout finalLayout vertex key cuts) :
    PreservesOtherClocks heap after := by
  obtain ⟨_, _, clocks⟩ := contract.clocks
  intro clock outside
  have separate : clock ≠ "heap_operations" ∧ clock ≠ "heap_cuts" ∧ clock ≠ "heap_comparisons" := by
    simp only [heapClocks, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    exact ⟨outside.1, outside.2.2.2.1, outside.2.1⟩
  simp [clocks clock, Clocks.single, separate.1, separate.2.1, separate.2.2]

private theorem decrease_contract (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue)
    (vertex key : Int) (present : heap.read layout.present vertex ≠ 0)
    (smaller : key < heap.read layout.keys vertex) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) (ready : finalLayout.Valid after queue) :
    UpdateContract heap after queue layout finalLayout vertex key cuts :=
  ⟨decrease_effect_summary heap after queue layout finalLayout valid vertex key present smaller cuts effect,
    ready, (push_decrease_frame heap after queue layout finalLayout vertex key cuts effect).1,
    (push_decrease_frame heap after queue layout finalLayout vertex key cuts effect).2,
    push_decrease_clocks heap after queue layout finalLayout vertex key cuts effect⟩

/-- Each forest-level decrease executes the compiled method with exactly the
    same snapshot and cuts. No caller transition or transcript is inspected. -/
theorem realize_decrease_run (before after : Algo2Lean.Fibonacci.Snapshot) (vertex key : Int) (cuts : Nat)
    (execution : Algo2Lean.Fibonacci.DecreaseRun before after vertex key cuts)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before)
    (present : heap.read layout.present vertex ≠ 0) :
    ∃ finalHeap finalLayout,
      UpdateContract heap finalHeap queue layout finalLayout vertex key cuts ∧
      snapshot finalHeap finalLayout = after := by
  cases execution with
  | unchanged noDecrease =>
    have noBetter : heap.read layout.keys vertex ≤ key := by
      change (snapshot heap layout).keys vertex ≤ key
      rw [observed]
      exact noDecrease
    refine ⟨(heap.tick "heap_operations").tick "heap_comparisons", layout, ?_, observed⟩
    refine ⟨push_unchanged_summary heap queue layout valid vertex key present noBetter,
      Layout.Valid.tick _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _,
      ((Heap.Modifies.refl _ _ _).tick "heap_operations").tick "heap_comparisons", rfl, 1, by omega, ?_⟩
    intro clock
    by_cases operation : clock = "heap_operations" <;> by_cases comparison : clock = "heap_comparisons" <;>
      simp_all [Heap.tick, Clocks.single] <;> omega
  | root decreased root =>
    let prepared := lowerKeyHeap heap layout vertex key
    have prepareValid : layout.Valid prepared queue := lower_key_layout heap queue layout valid vertex key
    have prepareSnapshot : snapshot prepared layout = before.lowerKey vertex key :=
      (lower_key_snapshot heap queue layout valid vertex key).trans (congrArg (fun state => state.lowerKey vertex key) observed)
    have smaller : key < heap.read layout.keys vertex := by
      change key < (snapshot heap layout).keys vertex
      rw [observed]
      exact decreased
    have noParent : prepared.read layout.parents vertex < 0 := by
      change (snapshot prepared layout).parents vertex < 0
      rw [prepareSnapshot]
      exact root
    refine ⟨finishDecreaseHeap prepared queue layout vertex, finishDecreaseLayout prepared layout vertex,
      decrease_contract heap _ queue layout _ valid vertex key present smaller 0 (.root _ _ noParent)
        (finish_decrease_layout _ _ _ prepareValid _), ?_⟩
    rw [finish_decrease_snapshot, prepareSnapshot]
  | ordered decreased nonroot ordered =>
    let prepared := lowerKeyHeap heap layout vertex key
    have prepareValid : layout.Valid prepared queue := lower_key_layout heap queue layout valid vertex key
    have prepareSnapshot : snapshot prepared layout = before.lowerKey vertex key :=
      (lower_key_snapshot heap queue layout valid vertex key).trans (congrArg (fun state => state.lowerKey vertex key) observed)
    have smaller : key < heap.read layout.keys vertex := by
      change key < (snapshot heap layout).keys vertex
      rw [observed]
      exact decreased
    have hasParent : 0 ≤ prepared.read layout.parents vertex := by
      change 0 ≤ (snapshot prepared layout).parents vertex
      rw [prepareSnapshot]
      exact nonroot
    have parentKey : prepared.read layout.keys (prepared.read layout.parents vertex) ≤ key := by
      change (snapshot prepared layout).keys ((snapshot prepared layout).parents vertex) ≤ key
      rw [prepareSnapshot]
      exact ordered
    refine ⟨finishDecreaseHeap (prepared.tick "heap_comparisons") queue layout vertex,
      finishDecreaseLayout (prepared.tick "heap_comparisons") layout vertex,
      decrease_contract heap _ queue layout _ valid vertex key present smaller 0 (.ordered _ _ hasParent parentKey)
        (finish_decrease_layout _ _ _ (Layout.Valid.tick _ _ _ prepareValid _ _) _), ?_⟩
    rw [finish_decrease_snapshot, snapshot_tick, prepareSnapshot]
  | cascading decreased nonroot violates cascade =>
    rename_i middle count
    let prepared := lowerKeyHeap heap layout vertex key
    let compared := prepared.tick "heap_comparisons"
    have prepareValid : layout.Valid prepared queue := lower_key_layout heap queue layout valid vertex key
    have compareValid : layout.Valid compared queue := Layout.Valid.tick _ _ _ prepareValid _ _
    have prepareSnapshot : snapshot prepared layout = before.lowerKey vertex key :=
      (lower_key_snapshot heap queue layout valid vertex key).trans (congrArg (fun state => state.lowerKey vertex key) observed)
    have smaller : key < heap.read layout.keys vertex := by
      change key < (snapshot heap layout).keys vertex
      rw [observed]
      exact decreased
    have hasParent : 0 ≤ prepared.read layout.parents vertex := by
      change 0 ≤ (snapshot prepared layout).parents vertex
      rw [prepareSnapshot]
      exact nonroot
    have parentRead : prepared.read layout.parents vertex = before.parents vertex :=
      congrArg (fun state => state.parents vertex) prepareSnapshot
    have parentKey : key < prepared.read layout.keys (prepared.read layout.parents vertex) := by
      change key < (snapshot prepared layout).keys ((snapshot prepared layout).parents vertex)
      rw [prepareSnapshot]
      exact violates
    have cutObserved : snapshot (cutHeap compared queue layout vertex (prepared.read layout.parents vertex))
        (cutLayout compared layout vertex (prepared.read layout.parents vertex)) =
          (before.lowerKey vertex key).cut vertex (before.parents vertex) := by
      rw [cut_snapshot compared queue layout compareValid, snapshot_tick, prepareSnapshot, parentRead]
    obtain ⟨finalHeap, finalLayout, effect, ready, result⟩ := realize_cascade_run _ _ _ count cascade
      (cutHeap compared queue layout vertex (prepared.read layout.parents vertex)) queue
      (cutLayout compared layout vertex (prepared.read layout.parents vertex))
      (cut_layout compared queue layout compareValid vertex _) cutObserved
    have cascadeEffect : CascadeEffect queue
        (cutHeap compared queue layout vertex (prepared.read layout.parents vertex))
        (cutLayout compared layout vertex (prepared.read layout.parents vertex))
        (prepared.read layout.parents vertex) finalHeap finalLayout count := by
      simpa only [parentRead] using effect
    refine ⟨finishDecreaseHeap finalHeap queue finalLayout vertex,
      finishDecreaseLayout finalHeap finalLayout vertex,
      decrease_contract heap _ queue layout _ valid vertex key present smaller (count + 1)
        (.cut hasParent parentKey cascadeEffect) (finish_decrease_layout _ _ _ ready _), ?_⟩
    rw [finish_decrease_snapshot, result]

/-- Insertion touches only the operation and comparison counters. -/
theorem insertion_other_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : PreservesOtherClocks heap (insertionHeap heap queue layout vertex key) := by
  intro clock outside
  have operation : clock ≠ "heap_operations" := by
    intro same; exact outside (by simp [heapClocks, same])
  have comparison : clock ≠ "heap_comparisons" := by
    intro same; exact outside (by simp [heapClocks, same])
  unfold insertionHeap
  rw [add_root_clocks]
  simp [insertionHeaderHeap, set_FibonacciHeap_size, Heap.tick, Clocks.single, operation, comparison]

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- Fresh insertion adds exactly one binding and preserves all existing bindings. -/
theorem QueueRep.insert_contents {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest afterForest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (absent : heap.read layout.present vertex = 0)
    (entries : afterForest.entries.Perm ((vertex, key) :: forest.entries)) :
    ∀ v k, (v, k) ∈ afterForest.entries ↔
      (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ forest.entries) := by
  have unused : ∀ old, (vertex, old) ∉ forest.entries := by
    intro old member
    have present := (rep.represented.entry member).2
    change heap.read layout.present vertex = 1 at present
    omega
  intro v k
  rw [entries.mem_iff]
  simp only [List.mem_cons, Prod.mk.injEq]
  constructor
  · rintro (same | member)
    · exact Or.inl same
    · refine Or.inr ⟨?_, member⟩
      intro same
      subst v
      exact unused k member
  · rintro (same | ⟨_, member⟩)
    · exact Or.inl same
    · exact Or.inr member

/-- A single entry replacement has the expected pointwise map interface. -/
theorem QueueRep.replacement_contents {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (before : List (Int × Int)) (vertex oldKey key : Int)
    (changed : Algo2Lean.Fibonacci.EntryChange before forest.entries vertex oldKey key) :
    ∀ v k, (v, k) ∈ forest.entries ↔
      (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ before) := by
  have inserted := changed.new_member
  have newKey := (rep.represented.entry inserted).1
  obtain ⟨unchanged, beforeEntries, afterEntries⟩ := changed
  intro v k
  constructor
  · intro member
    by_cases same : v = vertex
    · subst v
      have readKey := (rep.represented.entry member).1
      exact Or.inl ⟨rfl, readKey.symm.trans newKey⟩
    · refine Or.inr ⟨same, ?_⟩
      have remaining := afterEntries.mem_iff.mp member
      simp only [List.mem_cons, Prod.mk.injEq] at remaining
      rcases remaining with ⟨impossible, _⟩ | old
      · exact False.elim (same impossible)
      · exact beforeEntries.mem_iff.mpr (by simp [old])
  · rintro (⟨rfl, rfl⟩ | ⟨different, member⟩)
    · exact inserted
    · have remaining := beforeEntries.mem_iff.mp member
      simp only [List.mem_cons, Prod.mk.injEq] at remaining
      rcases remaining with ⟨impossible, _⟩ | old
      · exact False.elim (different impossible)
      · exact afterEntries.mem_iff.mpr (by simp [old])

/-- Every strict improvement of a represented binding runs the actual compiled
    method, preserves the queue representation, and costs at most twenty
    amortized heap events. The caller sees a one-binding map update. -/
theorem QueueRep.decrease {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (present : heap.read layout.present vertex ≠ 0)
    (smaller : key < heap.read layout.keys vertex) :
    ∃ after finalLayout afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue finalLayout afterForest ∧
      (∀ v k, (v, k) ∈ afterForest.entries ↔
        (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ forest.entries)) ∧
      heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs ∧
      PreservesOtherClocks heap after ∧
      heapEventWork heap after + Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
        Algo2Lean.Fibonacci.scaledPotential forest.counts + 20 := by
  obtain ⟨finalSnapshot, afterForest, cuts, execution, represented, changed, accounting⟩ :=
    rep.represented.decrease vertex key present smaller
  obtain ⟨after, finalLayout, contract, observed⟩ := realize_decrease_run _ _ vertex key cuts execution
    heap queue layout rep.layoutValid rfl present
  have finalRep : QueueRep after queue finalLayout afterForest := ⟨contract.valid, by rw [observed]; exact represented⟩
  refine ⟨after, finalLayout, afterForest, contract.summary, finalRep,
    finalRep.replacement_contents _ _ _ _ changed, contract.frame, contract.refs, contract.other_clocks, ?_⟩
  apply accounting.work_bound
  have work := contract.event_work
  omega

/-- Push-or-decrease is a complete modular queue contract: one public call, an
    exact one-binding update, a local storage footprint, and a constant amortized
    charge. Its statement exposes no rings, degree tables, or transitions. -/
theorem QueueRep.update {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (nonnegative : 0 ≤ vertex)
    (improvement : ∀ old, (vertex, old) ∈ forest.entries → key < old) :
    ∃ after finalLayout afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue finalLayout afterForest ∧
      (∀ v k, (v, k) ∈ afterForest.entries ↔
        (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ forest.entries)) ∧
      heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs ∧
      PreservesOtherClocks heap after ∧
      heapEventWork heap after + Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
        Algo2Lean.Fibonacci.scaledPotential forest.counts + 20 := by
  by_cases absent : heap.read layout.present vertex = 0
  · obtain ⟨afterForest, execution, represented, entries, amortized⟩ := rep.insert_amortized vertex key nonnegative absent
    exact ⟨_, _, afterForest, execution, represented, rep.insert_contents vertex key absent entries,
      (insertion_frame heap queue layout vertex key).1, (insertion_frame heap queue layout vertex key).2,
      insertion_other_clocks heap queue layout vertex key, by omega⟩
  · apply rep.decrease vertex key absent
    obtain ⟨old, member⟩ := (rep.represented.presence vertex).mp absent
    have readKey := (rep.represented.entry member).1
    change heap.read layout.keys vertex = old at readKey
    rw [readKey]
    exact improvement old member

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

/-- Child promotion uses the same pointer changes as a cut; only its clock differs. -/
theorem promotion_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    snapshot (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex) =
      (snapshot heap layout).promoteChild vertex := by
  have header : promotionHeaderHeap heap layout vertex =
      cutHeaderHeap heap layout (heap.read layout.children vertex) vertex := by
    simp only [promotionHeaderHeap, cutHeaderHeap]
    split <;> rfl
  have same : snapshot (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex) =
      snapshot (cutHeap heap queue layout (heap.read layout.children vertex) vertex)
        (cutLayout heap layout (heap.read layout.children vertex) vertex) := by
    simp only [promotionHeap, promotionLayout, promotionDetachedHeap, cutHeap, cutTailHeap, cutLayout,
      snapshot_tick, header]
  rw [same, cut_snapshot heap queue layout valid]
  rfl

theorem realize_promotions (before after : Algo2Lean.Fibonacci.Snapshot) (vertex : Int) (count : Nat)
    (run : Algo2Lean.Fibonacci.PromotionRun vertex before after count)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ promoted finalLayout, PromotionEffect queue vertex heap layout promoted finalLayout count ∧
      finalLayout.Valid promoted queue ∧ snapshot promoted finalLayout = after := by
  induction run generalizing heap layout with
  | done state childless =>
    refine ⟨heap, layout, .done _ _ ?_, valid, observed⟩
    change (snapshot heap layout).children vertex < 0
    rw [observed]
    exact childless
  | @next before after count hasChild rest ih =>
    have next : snapshot (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex) =
        before.promoteChild vertex := by rw [promotion_snapshot heap queue layout valid, observed]
    obtain ⟨promoted, finalLayout, effect, ready, result⟩ := ih
      (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex)
      (promotion_layout heap queue layout valid vertex) next
    refine ⟨promoted, finalLayout, .next ?_ effect, ready, result⟩
    change 0 ≤ (snapshot heap layout).children vertex
    rw [observed]
    exact hasChild

/-- Source effects after promotion, before the optional consolidation call. -/
def removeMinimumHeap (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) : Heap :=
  set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex) queue
    (if heap.read layout.right vertex = vertex then -1 else heap.read layout.right vertex)

def removeMinimumLayout (heap : Heap) (layout : Layout) (vertex : Int) : Layout :=
  {extractionLayout layout with minimum := if heap.read layout.right vertex = vertex then -1 else heap.read layout.right vertex}

theorem remove_minimum_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (removeMinimumLayout heap layout vertex).Valid (removeMinimumHeap heap queue layout vertex) queue :=
  Layout.Valid.set_minimum _ _ _ (extraction_layout heap queue layout valid vertex) _

theorem remove_minimum_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    snapshot (removeMinimumHeap heap queue layout vertex) (removeMinimumLayout heap layout vertex) =
      (snapshot heap layout).extractRoot vertex := by
  have keys_left : layout.keys ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have keys_right : layout.keys ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have keys_present : layout.keys ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have parents_left : layout.parents ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have parents_right : layout.parents ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have parents_present : layout.parents ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have children_left : layout.children ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have children_right : layout.children ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have children_present : layout.children ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have left_right : layout.left ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have left_present : layout.left ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have right_left : layout.right ≠ layout.left := Ne.symm left_right
  have right_present : layout.right ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_left : layout.degrees ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_right : layout.degrees ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_present : layout.degrees ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have marks_left : layout.marks ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have marks_right : layout.marks ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have marks_present : layout.marks ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have present_left : layout.present ≠ layout.left := Ne.symm left_present
  have present_right : layout.present ≠ layout.right := Ne.symm right_present
  have table_left : layout.table ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_right : layout.table ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_present : layout.table ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, removeMinimumHeap, removeMinimumLayout, extractionHeap, extractionLayout,
    removeHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField,
    Algo2Lean.Fibonacci.Snapshot.extractRoot, Algo2Lean.Fibonacci.Rings.removeLeft,
    Algo2Lean.Fibonacci.Rings.removeRight, Algo2Lean.Fibonacci.Rings.write,
    keys_left, keys_right, keys_present, parents_left, parents_right, parents_present, children_left, children_right, children_present, left_right, left_present, right_left, right_present, degrees_left, degrees_right, degrees_present, marks_left, marks_right, marks_present, present_left, present_right, table_left, table_right, table_present]

/-- Promotion frames compose independently of the forest argument. -/
theorem promotion_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (promotionHeap heap queue layout vertex) layout.refs [queue] := by
  have header : heap.Modifies (promotionHeaderHeap heap layout vertex) layout.refs [queue] := by
    unfold promotionHeaderHeap
    dsimp only
    split <;> exact (Heap.Modifies.refl _ _ _).write _ _ _ (by simp [Layout.refs])
  have decreased := header.write layout.degrees vertex ((promotionHeaderHeap heap layout vertex).read layout.degrees vertex - 1) (by simp [Layout.refs])
  have detached := decreased.trans (remove_frame _ queue layout (heap.read layout.children vertex))
  exact (detached.trans (add_root_frame _ queue layout _)).tick "heap_promotions"

theorem PromotionEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {count : Nat}
    (effect : PromotionEffect queue vertex heap layout after finalLayout count) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | done => exact ⟨.refl _ _ _, rfl⟩
  | @next before after current final count hasChild rest ih =>
    rw [promotion_layout_refs] at ih
    exact ⟨(promotion_frame before queue current vertex).trans ih.1, ih.2⟩

theorem remove_minimum_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (removeMinimumHeap heap queue layout vertex) layout.refs [queue] := by
  unfold removeMinimumHeap extractionHeap set_FibonacciHeap_minimum set_FibonacciHeap_size
  repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField
  all_goals first | exact remove_frame _ _ _ _ | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]


/-- Finish a minimum deletion by reusing the independently verified
    consolidation contract; the empty case performs no additional work. -/
theorem extract_from_pending (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) (pending : Algo2Lean.Fibonacci.Forest)
    (represented : Algo2Lean.Fibonacci.SplitRepresented
      (snapshot (removeMinimumHeap heap queue layout vertex) (removeMinimumLayout heap layout vertex)) pending [])
    (scratch : ∀ degree, (removeMinimumHeap heap queue layout vertex).read layout.table degree < 0) :
    ∃ after finalLayout forest links scans comparisons,
      ExtractionEffect queue vertex heap layout after finalLayout ∧ QueueRep after queue finalLayout forest ∧
      forest.entries.Perm pending.entries ∧ forest.marks = pending.marks ∧
      links + forest.length = pending.length ∧ forest.length ≤ 2 * pending.entries.length.log2 + 2 ∧
      scans ≤ 2 * pending.entries.length.log2 + 2 ∧ comparisons ≤ forest.length ∧
      heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs ∧
      ∀ clock, after.clocks clock = heap.clocks clock +
        Clocks.single "heap_root_scans" pending.length clock +
        Clocks.single "heap_comparisons" (links + comparisons) clock +
        Clocks.single "heap_links" links clock + Clocks.single "heap_degree_scans" scans clock := by
  let removed := removeMinimumHeap heap queue layout vertex
  let current := removeMinimumLayout heap layout vertex
  have ready : current.Valid removed queue := remove_minimum_layout heap queue layout valid vertex
  have framed : heap.Modifies removed layout.refs [queue] := remove_minimum_frame heap queue layout vertex
  by_cases last : heap.read layout.right vertex = vertex
  · have minimum : (snapshot removed current).minimum = -1 := by
      simp only [snapshot, current, removeMinimumLayout, last, ↓reduceIte]
    have empty : pending = [] := by
      rcases represented.cursor with empty | ⟨root, member, pointer⟩
      · exact empty.1
      · have nonnegative := represented.nonnegative root.vertex root.key
          (List.mem_flatMap.mpr ⟨root, by simpa using member, root.root_entry⟩)
        change (snapshot removed current).minimum = root.vertex at pointer
        omega
    subst pending
    have rep : Algo2Lean.Fibonacci.Represented (snapshot removed current) [] :=
      ⟨represented.valid, represented.pendingRing, represented.stored,
        represented.nonnegative, represented.presence, represented.size,
        Or.inl ⟨rfl, minimum⟩, scratch⟩
    have effect : ExtractionEffect queue vertex heap layout removed current := by
      simpa only [removed, current, removeMinimumHeap, removeMinimumLayout, last, ↓reduceIte] using
        (ExtractionEffect.last (queue := queue) (layout := layout) last)
    refine ⟨removed, current, [], 0, 0, 0, effect, ⟨ready, rep⟩,
      .refl _, rfl, by simp, by simp, by simp, by simp, framed, rfl, ?_⟩
    intro clock
    change heap.clocks clock = _
    simp [Clocks.single]
  · obtain ⟨after, finalLayout, forest, links, scans, comparisons, call, effect, finalRep,
        entries, marks, rootCount, rootBound, scanBound, comparisonBound, cost⟩ :=
      consolidate_from_forest removed queue current ready pending represented scratch
    have called : FibonacciHeap.consolidate.Call
        (set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex)
          queue (heap.read layout.right vertex)) queue after () := by
      simpa only [removed, removeMinimumHeap, if_neg last] using call
    refine ⟨after, finalLayout, forest, links, scans, comparisons,
      .consolidate last called finalRep.layoutValid, finalRep, entries, marks,
      rootCount, rootBound, scanBound, comparisonBound,
      framed.trans effect.frame.1, effect.frame.2, ?_⟩
    intro clock
    have monotone := consolidation_clocks_monotone removed after queue call clock
    have counted := congrFun cost clock
    change after.clocks clock - heap.clocks clock = _ at counted
    change heap.clocks clock ≤ after.clocks clock at monotone
    omega


/-- Public delete-min contract: exact entries, isolated mutation, and the
    amortized cost of the actual compiled call. -/
structure PopContract (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (forest : Algo2Lean.Fibonacci.Forest) (after : Heap) (finalLayout : Layout)
    (afterForest : Algo2Lean.Fibonacci.Forest) : Prop where
  execution : FibonacciHeap.pop_min.Call heap queue after layout.minimum
  represented : QueueRep after queue finalLayout afterForest
  contents : ((layout.minimum, heap.read layout.keys layout.minimum) :: afterForest.entries).Perm forest.entries
  frame : heap.Modifies after layout.refs [queue]
  refs : finalLayout.refs = layout.refs
  otherClocks : PreservesOtherClocks heap after
  amortized : heapEventWork heap after + Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
    Algo2Lean.Fibonacci.scaledPotential forest.counts + 12 * (2 * forest.entries.length.log2 + 2)

/-- A represented nonempty queue has a terminating, correct, logarithmically
    amortized minimum extraction, without a supplied execution transcript. -/
theorem QueueRep.pop_minimum {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (nonempty : forest ≠ []) :
    ∃ after finalLayout afterForest, PopContract heap queue layout forest after finalLayout afterForest := by
  have nonnegative : 0 ≤ layout.minimum := (rep.represented.minimum_key nonempty).1
  obtain ⟨deleted, pending, count, deletion, splitRep, scratch, deletedEntries, rootCount, marksBound, degreeBound⟩ :=
    rep.represented.delete_minimum nonempty
  cases deletion with
  | @finish promoted count promotions =>
    obtain ⟨promotedHeap, promotedLayout, promotionEffect, promotedValid, promotedSnapshot⟩ :=
      realize_promotions _ _ _ _ promotions (heap.tick "heap_operations") queue layout
        (Layout.Valid.tick _ _ _ rep.layoutValid _ _) rfl
    have removedSnapshot : snapshot (removeMinimumHeap promotedHeap queue promotedLayout layout.minimum)
        (removeMinimumLayout promotedHeap promotedLayout layout.minimum) = promoted.extractRoot layout.minimum := by
      rw [remove_minimum_snapshot promotedHeap queue promotedLayout promotedValid, promotedSnapshot]
    obtain ⟨after, finalLayout, afterForest, links, scans, comparisons, extractionEffect, finalRep,
        entries, marks, linkCount, rootsBound, scanBound, comparisonBound, extractionFrame, extractionRefs, extractionClocks⟩ :=
      extract_from_pending promotedHeap queue promotedLayout promotedValid layout.minimum pending
        (by rw [removedSnapshot]; exact splitRep)
        (by
          intro degree
          change (snapshot (removeMinimumHeap promotedHeap queue promotedLayout layout.minimum)
            (removeMinimumLayout promotedHeap promotedLayout layout.minimum)).table degree < 0
          rw [removedSnapshot]
          exact scratch degree)
    have effect : PopEffect queue heap layout after finalLayout layout.minimum count :=
      .nonempty nonnegative promotionEffect extractionEffect
    have promotionFrame := promotionEffect.frame
    have fullFrame : heap.Modifies after layout.refs [queue] :=
      (((Heap.Modifies.refl heap layout.refs [queue]).tick "heap_operations").trans promotionFrame.1).trans
        (by simpa only [promotionFrame.2] using extractionFrame)
    have fullContents : ((layout.minimum, heap.read layout.keys layout.minimum) :: afterForest.entries).Perm forest.entries :=
      (entries.cons _).trans deletedEntries
    have clocks := promotion_effect_clocks _ _ _ _ _ _ _ promotionEffect nonnegative
    have extractionCost : Heap.cost promotedHeap after = fun clock =>
        Clocks.single "heap_root_scans" pending.length clock +
        Clocks.single "heap_comparisons" (links + comparisons) clock +
        Clocks.single "heap_links" links clock + Clocks.single "heap_degree_scans" scans clock := by
      funext clock
      unfold Heap.cost
      rw [extractionClocks]
      omega
    have popCost := pop_nonempty_cost heap promotedHeap after queue layout promotedLayout finalLayout count
      nonnegative promotionEffect extractionEffect
    have work : heapEventWork heap after = 1 + 2 * count + pending.length + 2 * links + comparisons + scans := by
      simp [heapEventWork, popCost, extractionCost, Clocks.single]
      omega
    refine ⟨after, finalLayout, afterForest, ⟨pop_effect_summary _ _ _ _ _ rep.layoutValid _ _ effect,
      finalRep, fullContents, fullFrame, extractionRefs.trans promotionFrame.2, ?_, ?_⟩⟩
    · intro clock outside
      have notOperation : clock ≠ "heap_operations" := by intro same; exact outside (by simp [heapClocks, same])
      have notPromotions : clock ≠ "heap_promotions" := by intro same; exact outside (by simp [heapClocks, same])
      have notComparisons : clock ≠ "heap_comparisons" := by intro same; exact outside (by simp [heapClocks, same])
      have notRoots : clock ≠ "heap_root_scans" := by intro same; exact outside (by simp [heapClocks, same])
      have notLinks : clock ≠ "heap_links" := by intro same; exact outside (by simp [heapClocks, same])
      have notDegrees : clock ≠ "heap_degree_scans" := by intro same; exact outside (by simp [heapClocks, same])
      rw [extractionClocks, clocks]
      simp [Clocks.single, Heap.tick, notOperation, notPromotions, notComparisons, notRoots, notLinks, notDegrees]
    · have size := deletedEntries.length_eq
      simp only [List.length_cons] at size
      have logBound := Algo2Lean.Fibonacci.log2_mono (show pending.entries.length ≤ forest.entries.length by omega)
      simp only [Algo2Lean.Fibonacci.scaledPotential, Algo2Lean.Fibonacci.potential, Algo2Lean.Fibonacci.Forest.counts]
      rw [work]
      omega

end FibonacciModuleAnalysis
