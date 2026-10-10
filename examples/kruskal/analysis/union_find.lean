import Algo.union_find.Points
import Algo.union_find.Facts
import Algo2LeanLib.UnionFindAmortized
import Algo2LeanLib.CallCost
import Algo2LeanLib.Footprint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Reusable contracts for the compiled union-find implementation.

`find_contract` and `union_contract` give the exact model, storage, and clock
effects of full path compression and union by rank. `find_amortized` and
`union_amortized` bound incremental work using a shared inverse-Ackermann
potential. The simpler `find_summary` and `union_summary` retain logarithmic
worst-case bounds, partition guarantees, and protection for caller storage.

The forest and rank invariants are independent of generated code and graphs.
Constructor correctness is in the companion `union_find_init` analysis. Costs
count the explicit source clocks and compose from arbitrary initial counters.
-/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated

/-- A parent path ending at a root, with its number of non-root edges. -/
inductive ParentPath (parent : Seq) : Int → Int → Nat → Prop where
  | root (vertex : Int) (fixed : parent vertex = vertex) :
      ParentPath parent vertex vertex 0
  | next (vertex root : Int) (length : Nat) (different : parent vertex ≠ vertex)
      (tail : ParentPath parent (parent vertex) root length) :
      ParentPath parent vertex root (length + 1)

/-- Exact storage and clock effects of recursive path compression. The number
    of parent links is supplied by the independently established path witness. -/
def findHeap (heap : Heap) (parent : SeqRef) (vertex root : Int) : Nat → Heap
  | 0 => heap.tick "uf_find"
  | length + 1 =>
      ((findHeap (heap.tick "uf_find") parent (heap.read parent vertex) root length).write
        parent vertex root).tick "uf_compress"

@[simp] theorem findHeap_nextRef (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) : (findHeap heap parent vertex root length).nextRef = heap.nextRef := by
  induction length generalizing heap vertex with
  | zero => rfl
  | succ length ih => simp [findHeap, Heap.write, ih]

@[simp] theorem findHeap_objects (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) : (findHeap heap parent vertex root length).objects = heap.objects := by
  induction length generalizing heap vertex with
  | zero => rfl
  | succ length ih => simp [findHeap, Heap.write, ih]

@[simp] theorem findHeap_nextObject (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) : (findHeap heap parent vertex root length).nextObject = heap.nextObject := by
  induction length generalizing heap vertex with
  | zero => rfl
  | succ length ih => simp [findHeap, Heap.write, ih]

/-- Compression leaves every other sequence unchanged, including ranks. -/
theorem findHeap_other (heap : Heap) (parent other : SeqRef) (vertex root : Int)
    (length : Nat) (different : other ≠ parent) :
    (findHeap heap parent vertex root length).read other = heap.read other := by
  induction length generalizing heap vertex with
  | zero => rfl
  | succ length ih =>
    funext index
    simpa only [findHeap, Heap.tick_store, Heap.read, Heap.write,
      if_neg (show ¬ (other = parent ∧ index = vertex) from fun same => different same.1)] using
      congrFun (ih (heap.tick "uf_find") (heap.read parent vertex)) index

/-- Counts reflect every recursive lookup and every parent-pointer rewrite. -/
theorem findHeap_clocks (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) (clock : String) :
    (findHeap heap parent vertex root length).clocks clock = heap.clocks clock +
      (if clock = "uf_find" then length + 1 else 0) +
      (if clock = "uf_compress" then length else 0) := by
  induction length generalizing heap vertex with
  | zero => by_cases same : clock = "uf_find" <;> simp [findHeap, Heap.tick, same]
  | succ length ih =>
    simp only [findHeap, Heap.tick, Heap.write]
    rw [ih]
    by_cases first : clock = "uf_find" <;> by_cases second : clock = "uf_compress" <;>
      simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Lookup follows a finite parent path and compresses it on return. It can run
    beneath any caller stack and requires no graph-specific invariant. -/
theorem find_path (length : Nat) (heap : Heap) (object : Ref_UnionFind) (parent : SeqRef)
    (vertex root : Int) (valid : is_UnionFind heap object)
    (readParent : field_UnionFind_parent heap object = some parent)
    (allocated : parent < heap.nextRef)
    (path : ParentPath (heap.read parent) vertex root length) :
    UnionFind.find.Call heap (object, vertex) (findHeap heap parent vertex root length) root := by
  induction length generalizing heap vertex with
  | zero =>
    cases path with
    | root vertex fixed =>
      refine ⟨valid, ?_⟩
      intro caller
      apply Reaches.prepend (Step.UnionFind_find_pc15 _ _ _ (by simp [readParent]))
      apply Reaches.prepend (Step.UnionFind_find_pc14 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc13 _ _ _ (by simpa [readParent] using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc12_true _ _ _ (by simpa [readParent] using fixed))
      apply Reaches.prepend (Step.UnionFind_find_pc11 _ _ _)
      exact Reaches.single (Step.UnionFind_find_pc10 _ _ _)
  | succ length ih =>
    cases path with
    | next vertex root _ different tail =>
      have recursive := ih (heap.tick "uf_find") (heap.read parent vertex) valid readParent allocated tail
      refine ⟨valid, ?_⟩
      intro caller
      apply Reaches.prepend (Step.UnionFind_find_pc15 _ _ _ (by simp [readParent]))
      apply Reaches.prepend (Step.UnionFind_find_pc14 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc13 _ _ _ (by simpa [readParent] using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc12_false _ _ _ (by simpa [readParent] using different))
      apply Reaches.prepend (Step.UnionFind_find_pc9 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc8 _ _ _ valid)
      apply Reaches.prepend (Step.UnionFind_find_pc7 _ _ _ (by simpa [readParent] using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc6 _ _ _)
      simp only [readParent, Option.getD_some]
      apply (recursive.2 _).trans
      apply Reaches.prepend (Step.UnionFind_find_pc5 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc4 _ _ _ (by simpa using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc3 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc2 _ _ _)
      exact Reaches.single (Step.UnionFind_find_pc1 _ _ _)


open Algo2Lean.UnionFind (State Find compress compress_valid find_correct find_cost find_exists)

/-- Storage references are separate from the mathematical partition. -/
structure Layout where
  object : Ref_UnionFind
  parent : SeqRef
  rank : SeqRef

/-- A heap stores a valid finite disjoint-set forest with these two arrays. -/
structure Rep (heap : Heap) (layout : Layout) {n : Nat} (model : State n) : Prop where
  valid : Algo2Lean.UnionFind.Valid model
  object : is_UnionFind heap layout.object
  readParent : field_UnionFind_parent heap layout.object = some layout.parent
  readRank : field_UnionFind_rank heap layout.object = some layout.rank
  readSize : field_UnionFind_size heap layout.object = some (n : Int)
  parentAllocated : layout.parent < heap.nextRef
  rankAllocated : layout.rank < heap.nextRef
  separate : layout.parent ≠ layout.rank
  parents : ∀ vertex : Fin n, heap.read layout.parent (vertex.val : Int) = (model.parent vertex).val
  ranks : ∀ vertex : Fin n, heap.read layout.rank (vertex.val : Int) = (model.rank vertex : Int)

/-- Charging a clock does not change the represented data structure. -/
theorem Rep.tick {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (clock : String) (amount : Nat := 1) :
    Rep (heap.tick clock amount) layout model :=
  ⟨representation.valid, representation.object, representation.readParent,
    representation.readRank, representation.readSize, representation.parentAllocated,
    representation.rankAllocated, representation.separate, representation.parents,
    representation.ranks⟩

/-- The pure result of compressing one complete parent path on return. -/
abbrev findResult := @Algo2Lean.UnionFind.compressPath

@[simp] theorem findResult_representative {n : Nat} (model : State n) (vertex : Fin n)
    (length : Nat) : (findResult model vertex length).representative = model.representative := by
  induction length generalizing vertex with
  | zero => rfl
  | succ length ih => exact ih (model.parent vertex)

@[simp] theorem findResult_rank {n : Nat} (model : State n) (vertex : Fin n)
    (length : Nat) : (findResult model vertex length).rank = model.rank := by
  induction length generalizing vertex with
  | zero => rfl
  | succ length ih => exact ih (model.parent vertex)

theorem findResult_valid {n : Nat} (model : State n) (vertex : Fin n)
    (length : Nat) (valid : Algo2Lean.UnionFind.Valid model) :
    Algo2Lean.UnionFind.Valid (findResult model vertex length) := by
  induction length generalizing vertex with
  | zero => exact valid
  | succ length ih => exact compress_valid (ih (model.parent vertex)) vertex

/-- A compression write preserves the partition and every representation field. -/
theorem Rep.compress {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (vertex : Fin n) :
    Rep (heap.write layout.parent (vertex.val : Int) ((model.representative vertex).val : Int))
      layout (compress model vertex) := by
  refine ⟨compress_valid representation.valid vertex, representation.object,
    representation.readParent, representation.readRank, representation.readSize,
    representation.parentAllocated, representation.rankAllocated, representation.separate, ?_, ?_⟩
  · intro other
    by_cases same : other = vertex
    · subst other
      simp [Heap.read, Heap.write, Algo2Lean.UnionFind.compress, Algo2Lean.UnionFind.update]
    · have different : (other.val : Int) ≠ (vertex.val : Int) := by
        intro equal
        exact same (Fin.ext (by omega))
      simpa [Heap.read, Heap.write, Algo2Lean.UnionFind.compress, Algo2Lean.UnionFind.update, same, different] using
        representation.parents other
  · intro other
    simpa [Heap.read, Heap.write, Ne.symm representation.separate, Algo2Lean.UnionFind.compress] using
      representation.ranks other

/-- A finite model path is the same path read through the generated heap interface. -/
theorem model_path {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) {vertex root : Fin n} {length : Nat}
    (path : Find model vertex root length) :
    ParentPath (heap.read layout.parent) vertex.val root.val length := by
  induction path with
  | root vertex fixed =>
    apply ParentPath.root
    simpa [fixed] using representation.parents vertex
  | step vertex root length moving tail ih =>
    apply ParentPath.next _ _ _
    · rw [representation.parents vertex]
      intro equal
      exact moving (Fin.ext (by omega))
    · simpa [representation.parents vertex] using ih

/-- The exact operational heap after lookup represents the compressed model. -/
theorem findHeap_rep {n : Nat} {model : State n} {vertex root : Fin n} {length : Nat}
    (path : Find model vertex root length) (heap : Heap) (layout : Layout)
    (representation : Rep heap layout model) :
    Rep (findHeap heap layout.parent vertex.val root.val length)
      layout (findResult model vertex length) := by
  induction path generalizing heap with
  | root vertex fixed => exact representation.tick "uf_find"
  | step vertex root length moving tail ih =>
    have recursive := ih (heap.tick "uf_find") (representation.tick "uf_find")
    have result := (recursive.compress vertex).tick "uf_compress"
    have correct := (find_correct representation.valid (Find.step vertex root length moving tail)).1
    simpa [findHeap, findResult, representation.parents vertex, findResult_representative, correct] using! result

/-- Every valid lookup terminates, retains its partition and ranks, and compresses
    the traversed path. The two source clocks total at most `2 log₂ n + 1`. -/
theorem find_summary {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (vertex : Fin n) :
    ∃ after compressed,
      UnionFind.find.Call heap (layout.object, (vertex.val : Int)) after
        ((model.representative vertex).val : Int) ∧
      Rep after layout compressed ∧
      compressed.representative = model.representative ∧ compressed.rank = model.rank ∧
      Heap.cost heap after "uf_find" + Heap.cost heap after "uf_compress" ≤ 2 * Nat.log2 n + 1 := by
  obtain ⟨length, path⟩ := find_exists representation.valid vertex
  let after := findHeap heap layout.parent vertex.val (model.representative vertex).val length
  refine ⟨after, findResult model vertex length,
    find_path length heap layout.object layout.parent _ _ representation.object
      representation.readParent representation.parentAllocated (model_path representation path),
    findHeap_rep path heap layout representation, findResult_representative _ _ _, findResult_rank _ _ _, ?_⟩
  have bound := find_cost representation.valid path
  simp only [after, Heap.cost, findHeap_clocks]
  simp
  omega


@[simp] theorem parent_tick (heap : Heap) (object : Ref_UnionFind) (clock : String) (amount : Nat) :
    field_UnionFind_parent (heap.tick clock amount) object = field_UnionFind_parent heap object := rfl
@[simp] theorem rank_tick (heap : Heap) (object : Ref_UnionFind) (clock : String) (amount : Nat) :
    field_UnionFind_rank (heap.tick clock amount) object = field_UnionFind_rank heap object := rfl
@[simp] theorem parent_write (heap : Heap) (object : Ref_UnionFind) (ref : SeqRef) (index value : Int) :
    field_UnionFind_parent (heap.write ref index value) object = field_UnionFind_parent heap object := rfl
@[simp] theorem rank_write (heap : Heap) (object : Ref_UnionFind) (ref : SeqRef) (index value : Int) :
    field_UnionFind_rank (heap.write ref index value) object = field_UnionFind_rank heap object := rfl

/-- Constant-time rank-linking after the two representative lookups. -/
def unionHeap (heap : Heap) (layout : Layout) (left right : Int) : Heap :=
  let charged := heap.tick "uf_union"
  if left = right then charged
  else if heap.read layout.rank left < heap.read layout.rank right then
    charged.write layout.parent left right
  else if heap.read layout.rank right < heap.read layout.rank left then
    charged.write layout.parent right left
  else (charged.write layout.parent right left).write layout.rank left
    (heap.read layout.rank left + 1)

/-- Union composes two verified lookups with the source rank comparison and link.
    This lemma exposes only source inputs, heaps, and operation contracts. -/
theorem union_calls (before middle heap : Heap) (layout : Layout) (a b left right : Int)
    (first : UnionFind.find.Call before (layout.object,a) middle left)
    (second : UnionFind.find.Call middle (layout.object,b) heap right)
    (readParent : field_UnionFind_parent heap layout.object = some layout.parent)
    (readRank : field_UnionFind_rank heap layout.object = some layout.rank)
    (parentAllocated : layout.parent < heap.nextRef) (rankAllocated : layout.rank < heap.nextRef)
    (separate : layout.parent ≠ layout.rank) :
    UnionFind.union.Call before (layout.object,a,b) (unionHeap heap layout left right)
      (decide (left ≠ right)) := by
  refine ⟨first.1, ?_⟩
  intro caller
  apply Reaches.prepend (Step.UnionFind_union_pc25 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc24 _ _ _ (by exact first.1))
  apply Reaches.prepend (Step.UnionFind_union_pc23 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc22 _ _ _)
  apply (first.2 _).trans
  apply Reaches.prepend (Step.UnionFind_union_pc21 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc20 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc19 _ _ _ (by exact second.1))
  apply Reaches.prepend (Step.UnionFind_union_pc18 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc17 _ _ _)
  apply (second.2 _).trans
  apply Reaches.prepend (Step.UnionFind_union_pc16 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc15 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc14 _ _ _)
  by_cases same : left = right
  · apply Reaches.prepend (Step.UnionFind_union_pc13_true _ _ _ (by simpa using same))
    apply Reaches.prepend (Step.UnionFind_union_pc12 _ _ _)
    simpa [unionHeap, same] using Reaches.single (Step.UnionFind_union_pc11 _ _ caller)
  · apply Reaches.prepend (Step.UnionFind_union_pc13_false _ _ _ (by simpa using same))
    apply Reaches.prepend (Step.UnionFind_union_pc10 _ _ _ (by simpa [readRank] using rankAllocated))
    by_cases less : heap.read layout.rank left < heap.read layout.rank right
    · apply Reaches.prepend (Step.UnionFind_union_pc9_true _ _ _ (by simpa [readRank] using less))
      apply Reaches.prepend (Step.UnionFind_union_pc3 _ _ _ (by simpa [readParent] using parentAllocated))
      apply Reaches.prepend (Step.UnionFind_union_pc2 _ _ _)
      simpa [unionHeap, same, less, readParent] using Reaches.single (Step.UnionFind_union_pc1 _ _ caller)
    · apply Reaches.prepend (Step.UnionFind_union_pc9_false _ _ _ (by simpa [readRank] using less))
      apply Reaches.prepend (Step.UnionFind_union_pc8 _ _ _ (by simpa [readRank] using rankAllocated))
      by_cases more : heap.read layout.rank right < heap.read layout.rank left
      · apply Reaches.prepend (Step.UnionFind_union_pc7_true _ _ _ (by simpa [readRank] using more))
        apply Reaches.prepend (Step.UnionFind_union_pc4 _ _ _ (by simpa [readParent] using parentAllocated))
        apply Reaches.prepend (Step.UnionFind_union_pc2 _ _ _)
        simpa [unionHeap, same, less, more, readParent] using Reaches.single (Step.UnionFind_union_pc1 _ _ caller)
      · apply Reaches.prepend (Step.UnionFind_union_pc7_false _ _ _ (by simpa [readRank] using more))
        apply Reaches.prepend (Step.UnionFind_union_pc6 _ _ _ (by simpa [readParent] using parentAllocated))
        apply Reaches.prepend (Step.UnionFind_union_pc5 _ _ _ (by simpa [readRank] using rankAllocated))
        apply Reaches.prepend (Step.UnionFind_union_pc2 _ _ _)
        simpa [unionHeap, same, less, more, readParent, readRank, Heap.read_write_other_ref, Ne.symm separate] using Reaches.single (Step.UnionFind_union_pc1 _ _ caller)


/-- Heap effect of linking a lower-ranked root under a higher-ranked root. -/
def linkHeap (heap : Heap) (layout : Layout) (loser winner : Int) : Heap :=
  let linked := heap.write layout.parent loser winner
  if heap.read layout.rank loser = heap.read layout.rank winner then
    linked.write layout.rank winner (heap.read layout.rank winner + 1)
  else linked

/-- Linking exactly two roots implements the independent union-by-rank model. -/
theorem Rep.link {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (loser winner : Fin n)
    (different : loser ≠ winner) (loserRoot : model.parent loser = loser)
    (winnerRoot : model.parent winner = winner) (ordered : model.rank loser ≤ model.rank winner) :
    Rep (linkHeap heap layout loser.val winner.val) layout
      (Algo2Lean.UnionFind.link model loser winner) := by
  have valid := Algo2Lean.UnionFind.link_valid representation.valid loser winner different loserRoot winnerRoot ordered
  unfold linkHeap
  rw [representation.ranks loser, representation.ranks winner]
  by_cases tied : model.rank loser = model.rank winner
  · simp only [tied, ↓reduceIte]
    refine ⟨valid, representation.object, representation.readParent, representation.readRank,
      representation.readSize, representation.parentAllocated, representation.rankAllocated,
      representation.separate, ?_, ?_⟩
    · intro vertex
      by_cases same : vertex = loser
      · subst vertex
        simp [Heap.read, Heap.write, representation.separate, Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update]
      · have indexDifferent : (vertex.val : Int) ≠ (loser.val : Int) := by
          intro eq; exact same (Fin.ext (by omega))
        simpa [Heap.read, Heap.write, representation.separate, indexDifferent,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, same] using representation.parents vertex
    · intro vertex
      by_cases same : vertex = winner
      · subst vertex
        simp [Heap.read, Heap.write, Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, tied]
      · have indexDifferent : (vertex.val : Int) ≠ (winner.val : Int) := by
          intro eq; exact same (Fin.ext (by omega))
        simpa [Heap.read, Heap.write, Ne.symm representation.separate, indexDifferent,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, same] using representation.ranks vertex
  · have unequal : (model.rank loser : Int) ≠ (model.rank winner : Int) := by omega
    simp only [if_neg unequal]
    refine ⟨valid, representation.object, representation.readParent, representation.readRank,
      representation.readSize, representation.parentAllocated, representation.rankAllocated,
      representation.separate, ?_, ?_⟩
    · intro vertex
      by_cases same : vertex = loser
      · subst vertex
        simp [Heap.read, Heap.write, Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update]
      · have indexDifferent : (vertex.val : Int) ≠ (loser.val : Int) := by
          intro eq; exact same (Fin.ext (by omega))
        simpa [Heap.read, Heap.write, indexDifferent,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, same] using representation.parents vertex
    · intro vertex
      by_cases same : vertex = winner
      · subst vertex
        simpa [Heap.read, Heap.write, Ne.symm representation.separate,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, tied] using representation.ranks winner
      · simpa [Heap.read, Heap.write, Ne.symm representation.separate,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, tied, same] using representation.ranks vertex

/-- The source rank branches implement the pure union operation. -/
theorem unionHeap_rep {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (a b : Fin n) :
    Rep (unionHeap heap layout (model.representative a).val (model.representative b).val)
      layout (Algo2Lean.UnionFind.union model a b) := by
  let left := model.representative a
  let right := model.representative b
  have leftRoot := representation.valid.representative_root a
  have rightRoot := representation.valid.representative_root b
  change Rep (unionHeap heap layout left.val right.val) layout
    (if left = right then model else if model.rank left < model.rank right then
      Algo2Lean.UnionFind.link model left right else Algo2Lean.UnionFind.link model right left)
  by_cases same : left = right
  · simpa [unionHeap, Algo2Lean.UnionFind.union, left, right, same] using representation.tick "uf_union"
  · have valuesDifferent : (left.val : Int) ≠ (right.val : Int) := by
      intro eq; exact same (Fin.ext (by omega))
    by_cases less : model.rank left < model.rank right
    · have result := (representation.tick "uf_union").link left right same leftRoot rightRoot (by omega)
      have unequal : (model.rank left : Int) ≠ (model.rank right : Int) := by omega
      simpa [unionHeap, linkHeap, same,
        valuesDifferent, representation.ranks, less, unequal] using result
    · have result := (representation.tick "uf_union").link right left (Ne.symm same) rightRoot leftRoot (by omega)
      by_cases more : model.rank right < model.rank left
      · have unequal : (model.rank right : Int) ≠ (model.rank left : Int) := by omega
        simpa [unionHeap, linkHeap, same,
          valuesDifferent, representation.ranks, less, more, unequal] using result
      · have tied : model.rank left = model.rank right := by omega
        simpa [unionHeap, linkHeap, same,
          valuesDifferent, representation.ranks, less, more, tied] using result


/-- The sum of all four union-find source clocks. -/
def work (clocks : Clocks) : Nat :=
  clocks "uf_init" + clocks "uf_find" + clocks "uf_compress" + clocks "uf_union"

theorem findHeap_work (heap : Heap) (layout : Layout) (vertex root : Int) (length : Nat) :
    work (findHeap heap layout.parent vertex root length).clocks = work heap.clocks + 2 * length + 1 := by
  simp [work, findHeap_clocks]
  omega

@[simp] theorem unionHeap_clocks (heap : Heap) (layout : Layout) (left right : Int) (clock : String) :
    (unionHeap heap layout left right).clocks clock =
      heap.clocks clock + if clock = "uf_union" then 1 else 0 := by
  by_cases same : left = right <;>
    by_cases less : heap.read layout.rank left < heap.read layout.rank right <;>
    by_cases more : heap.read layout.rank right < heap.read layout.rank left <;>
    by_cases counter : clock = "uf_union" <;> simp [unionHeap, same, less, more, counter, Heap.tick, Heap.write]

theorem unionHeap_work (heap : Heap) (layout : Layout) (left right : Int) :
    work (unionHeap heap layout left right).clocks = work heap.clocks + 1 := by
  simp [work, unionHeap_clocks, Nat.add_assoc]

/-- Lookup changes only the owned parent array. The larger footprint lets its
    contract compose directly with a later rank update. -/
theorem findHeap_frame (heap : Heap) (layout : Layout) (vertex root : Int) (length : Nat) :
    heap.Footprint (findHeap heap layout.parent vertex root length)
      [layout.parent, layout.rank] [] [] := by
  induction length generalizing heap vertex with
  | zero => exact (Heap.Footprint.refl heap _ _ _).tick "uf_find"
  | succ length ih =>
    exact (((Heap.Footprint.refl heap _ _ _).tick "uf_find").trans
      (ih (heap.tick "uf_find") (heap.read layout.parent vertex))).write
      layout.parent vertex root (Or.inl (by simp)) |>.tick "uf_compress"

theorem unionHeap_frame (heap : Heap) (layout : Layout) (left right : Int) :
    heap.Footprint (unionHeap heap layout left right) [layout.parent, layout.rank] [] [] := by
  have charged := (Heap.Footprint.refl heap [layout.parent,layout.rank] [] []).tick "uf_union"
  unfold unionHeap
  split
  · exact charged
  · split
    · exact charged.write layout.parent left right (Or.inl (by simp))
    · split
      · exact charged.write layout.parent right left (Or.inl (by simp))
      · exact (charged.write layout.parent right left (Or.inl (by simp))).write
          layout.rank left _ (Or.inl (by simp))


/-- A method changes only its owned arrays and allocates no storage. Clocks
    have a separate, exact increment contract. -/
structure Storage (before after : Heap) (sequences : List SeqRef) : Prop where
  footprint : before.Footprint after sequences [] []
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  nextCollection : after.nextCollection = before.nextCollection

/-- Following `length` parent links performs one final root test and compresses
    every visited non-root vertex. All other clocks have zero increment. -/
def findCosts (length : Nat) : Clocks := fun clock =>
  (if clock = "uf_find" then length + 1 else 0) +
  (if clock = "uf_compress" then length else 0)

/-- Two find calls and one rank comparison/link stage make one union. -/
def unionCosts (first second : Nat) : Clocks := fun clock =>
  findCosts first clock + findCosts second clock + if clock = "uf_union" then 1 else 0

/-- The precise model produced by the source's two full compressions and link. -/
def unionResult {n : Nat} (model : State n) (a b : Fin n) (first second : Nat) : State n :=
  Algo2Lean.UnionFind.union (findResult (findResult model a first) b second) a b

/-- The exact lookup heap preserves all allocation boundaries. -/
theorem findHeap_storage (heap : Heap) (layout : Layout) (vertex root : Int) (length : Nat) :
    Storage heap (findHeap heap layout.parent vertex root length) [layout.parent] := by
  refine ⟨?_, findHeap_nextRef _ _ _ _ _, findHeap_nextObject _ _ _ _ _, ?_⟩
  · induction length generalizing heap vertex with
    | zero => exact (Heap.Footprint.refl heap _ _ _).tick "uf_find"
    | succ length ih =>
      exact (((Heap.Footprint.refl heap _ _ _).tick "uf_find").trans
        (ih (heap.tick "uf_find") (heap.read layout.parent vertex))).write
        layout.parent vertex root (Or.inl (by simp)) |>.tick "uf_compress"
  · induction length generalizing heap vertex with
    | zero => rfl
    | succ length ih =>
      simpa only [findHeap, Heap.tick_nextCollection, Heap.write_nextCollection] using
        (ih (heap.tick "uf_find") (heap.read layout.parent vertex))

/-- Lookup costs are increments from the caller's actual counters. -/
theorem findHeap_increments (heap : Heap) (parent : SeqRef) (vertex root : Int) (length : Nat) :
    heap.Increments (findHeap heap parent vertex root length) (findCosts length) := by
  intro clock
  simp [findCosts, findHeap_clocks, Nat.add_assoc]

/-- No array, object, or typed collection is allocated by the rank-link stage. -/
theorem unionHeap_storage (heap : Heap) (layout : Layout) (left right : Int) :
    Storage heap (unionHeap heap layout left right) [layout.parent, layout.rank] := by
  refine ⟨unionHeap_frame _ _ _ _, ?_, ?_, ?_⟩ <;>
    by_cases same : left = right <;>
    by_cases less : heap.read layout.rank left < heap.read layout.rank right <;>
    by_cases more : heap.read layout.rank right < heap.read layout.rank left <;>
    simp [unionHeap, same, less, more]

/-- A lookup has a finite path witness, the exact fully compressed model, a
    parent-only storage footprint, unchanged allocation boundaries, and exact
    clock increments. This contract supports later potential arguments without
    reopening the compiled transitions. -/
theorem find_contract {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (vertex : Fin n) :
    ∃ length after,
      Find model vertex (model.representative vertex) length ∧
      UnionFind.find.Call heap (layout.object, (vertex.val : Int)) after
        ((model.representative vertex).val : Int) ∧
      Rep after layout (findResult model vertex length) ∧
      Storage heap after [layout.parent] ∧
      heap.Increments after (findCosts length) := by
  obtain ⟨length, path⟩ := find_exists representation.valid vertex
  refine ⟨length, findHeap heap layout.parent vertex.val (model.representative vertex).val length,
    path, ?_, findHeap_rep path heap layout representation,
    findHeap_storage _ _ _ _ _, findHeap_increments _ _ _ _ _⟩
  exact find_path length heap layout.object layout.parent _ _ representation.object
    representation.readParent representation.parentAllocated (model_path representation path)

/-- Union exposes the two actual compressed paths and the exact final model.
    Its caller can use a logarithmic or amortized bound on those paths while
    retaining the same operational Call, mutation footprint, and cost record. -/
theorem union_contract {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (a b : Fin n) :
    ∃ first second after,
      Find model a (model.representative a) first ∧
      Find (findResult model a first) b ((findResult model a first).representative b) second ∧
      UnionFind.union.Call heap (layout.object, (a.val : Int), (b.val : Int)) after
        (decide (model.representative a ≠ model.representative b)) ∧
      Rep after layout (unionResult model a b first second) ∧
      Storage heap after [layout.parent, layout.rank] ∧
      heap.Increments after (unionCosts first second) := by
  obtain ⟨first, firstPath⟩ := find_exists representation.valid a
  let middle := findHeap heap layout.parent a.val (model.representative a).val first
  let firstModel := findResult model a first
  have firstRep : Rep middle layout firstModel := findHeap_rep firstPath heap layout representation
  obtain ⟨second, secondPath⟩ := find_exists firstRep.valid b
  let linked := findHeap middle layout.parent b.val (firstModel.representative b).val second
  let secondModel := findResult firstModel b second
  have secondRep : Rep linked layout secondModel := findHeap_rep secondPath middle layout firstRep
  have representatives : secondModel.representative = model.representative := by
    simp [secondModel, firstModel]
  let after := unionHeap linked layout (secondModel.representative a).val (secondModel.representative b).val
  have firstCall := find_path first heap layout.object layout.parent _ _ representation.object
    representation.readParent representation.parentAllocated (model_path representation firstPath)
  have secondCall := find_path second middle layout.object layout.parent _ _ firstRep.object
    firstRep.readParent firstRep.parentAllocated (model_path firstRep secondPath)
  have sourceCall := union_calls heap middle linked layout a.val b.val
    (model.representative a).val (firstModel.representative b).val firstCall secondCall
    secondRep.readParent secondRep.readRank secondRep.parentAllocated secondRep.rankAllocated secondRep.separate
  refine ⟨first, second, after, firstPath, secondPath, ?_, unionHeap_rep secondRep a b, ?_, ?_⟩
  · simpa [after, representatives, firstModel, Int.ofNat_inj, Fin.val_inj] using sourceCall
  · have firstStorage := findHeap_storage heap layout a.val (model.representative a).val first
    have secondStorage := findHeap_storage middle layout b.val (firstModel.representative b).val second
    have lastStorage := unionHeap_storage linked layout (secondModel.representative a).val (secondModel.representative b).val
    refine ⟨(findHeap_frame heap layout _ _ first).trans
      ((findHeap_frame middle layout _ _ second).trans (unionHeap_frame linked layout _ _)), ?_, ?_, ?_⟩
    · exact lastStorage.nextRef.trans (secondStorage.nextRef.trans firstStorage.nextRef)
    · exact lastStorage.nextObject.trans (secondStorage.nextObject.trans firstStorage.nextObject)
    · exact lastStorage.nextCollection.trans (secondStorage.nextCollection.trans firstStorage.nextCollection)
  · intro clock
    simp only [after, unionHeap_clocks, linked, middle, findHeap_clocks, unionCosts, findCosts]
    omega

@[simp] theorem work_findCosts (length : Nat) : work (findCosts length) = 2 * length + 1 := by
  simp [work, findCosts]
  omega

@[simp] theorem work_unionCosts (first second : Nat) :
    work (unionCosts first second) = 2 * (first + second) + 3 := by
  simp [work, unionCosts, findCosts]
  omega

/-- Exact increments add directly to total union-find work, even when the
    caller begins with nonzero counters. -/
theorem work_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    work after.clocks = work before.clocks + work costs := by
  simp only [work]
  rw [effect "uf_init", effect "uf_find", effect "uf_compress", effect "uf_union"]
  omega

/-- The exact full-compression result represents the same partition. -/
theorem unionResult_connected {n : Nat} {model : State n}
    (valid : Algo2Lean.UnionFind.Valid model) (a b : Fin n) (first second : Nat) (x y : Fin n) :
    Algo2Lean.UnionFind.Connected (unionResult model a b first second) x y ↔
      Algo2Lean.UnionFind.Connected model x y ∨
      (Algo2Lean.UnionFind.Connected model x a ∧ Algo2Lean.UnionFind.Connected model y b) ∨
      (Algo2Lean.UnionFind.Connected model x b ∧ Algo2Lean.UnionFind.Connected model y a) := by
  have compressedValid := findResult_valid (findResult model a first) b second
    (findResult_valid model a first valid)
  simpa [unionResult, Algo2Lean.UnionFind.Connected] using
    Algo2Lean.UnionFind.union_connected compressedValid a b x y

/-- Union is a reusable, terminating partition operation. It joins exactly the
    two selected components, protects caller storage, and bounds all its work.
    The bound is worst-case; it does not assert inverse-Ackermann amortization. -/
theorem union_summary {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (a b : Fin n) :
    ∃ after nextModel,
      UnionFind.union.Call heap (layout.object, (a.val : Int), (b.val : Int)) after
        (decide (model.representative a ≠ model.representative b)) ∧
      Rep after layout nextModel ∧
      (∀ x y, Algo2Lean.UnionFind.Connected nextModel x y ↔
        Algo2Lean.UnionFind.Connected model x y ∨
        (Algo2Lean.UnionFind.Connected model x a ∧ Algo2Lean.UnionFind.Connected model y b) ∨
        (Algo2Lean.UnionFind.Connected model x b ∧ Algo2Lean.UnionFind.Connected model y a)) ∧
      heap.Footprint after [layout.parent,layout.rank] [] [] ∧
      (∀ clock, clock ∉ ["uf_find","uf_compress","uf_union"] → after.clocks clock = heap.clocks clock) ∧
      work after.clocks ≤ work heap.clocks + 4 * Nat.log2 n + 3 := by
  obtain ⟨first, second, after, firstPath, secondPath, execution, represented, storage, effect⟩ :=
    union_contract heap layout model representation a b
  refine ⟨after, unionResult model a b first second, execution, represented,
    unionResult_connected representation.valid a b first second, storage.footprint, ?_, ?_⟩
  · intro clock reserved
    have different : clock ≠ "uf_find" ∧ clock ≠ "uf_compress" ∧ clock ≠ "uf_union" := by
      simpa using reserved
    simp [effect clock, unionCosts, findCosts, different.1, different.2.1, different.2.2]
  · have firstBound := find_cost representation.valid firstPath
    have secondBound := find_cost (findResult_valid model a first representation.valid) secondPath
    rw [work_increments effect, work_unionCosts]
    omega


/-- An actual lookup pays for its exact clock increments using the Ackermann
    potential. The resulting heap, partition model, and storage frame belong
    to the same call; no runtime assumption is supplied by the caller. -/
theorem find_amortized {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (vertex : Fin n) :
    ∃ after compressed,
      UnionFind.find.Call heap (layout.object, (vertex.val : Int)) after
        ((model.representative vertex).val : Int) ∧
      Rep after layout compressed ∧
      compressed.representative = model.representative ∧ compressed.rank = model.rank ∧
      Storage heap after [layout.parent] ∧
      heap.Increments after (Heap.cost heap after) ∧
      work (Heap.cost heap after) + 2 * Algo2Lean.UnionFind.potential compressed ≤
        2 * Algo2Lean.UnionFind.potential model + 2 * Algo2Lean.Ackermann.alpha n + 3 := by
  obtain ⟨length, after, path, execution, represented, storage, increments⟩ :=
    find_contract heap layout model representation vertex
  refine ⟨after, findResult model vertex length, execution, represented,
    findResult_representative _ _ _, findResult_rank _ _ _, storage,
    increments.monotone.increments, ?_⟩
  rw [increments.cost, work_findCosts]
  exact Algo2Lean.UnionFind.find_amortized representation.valid path

/-- One actual union satisfies both its worst-case bound and its amortized
    inverse-Ackermann bound. The scaled potential accounts for all find tests,
    compression writes, and the union tick. This is a composable call theorem,
    valid with arbitrary preexisting clocks and caller storage. -/
theorem union_summary_amortized {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (a b : Fin n) :
    ∃ after nextModel,
      UnionFind.union.Call heap (layout.object, (a.val : Int), (b.val : Int)) after
        (decide (model.representative a ≠ model.representative b)) ∧
      Rep after layout nextModel ∧
      (∀ x y, Algo2Lean.UnionFind.Connected nextModel x y ↔
        Algo2Lean.UnionFind.Connected model x y ∨
        (Algo2Lean.UnionFind.Connected model x a ∧ Algo2Lean.UnionFind.Connected model y b) ∨
        (Algo2Lean.UnionFind.Connected model x b ∧ Algo2Lean.UnionFind.Connected model y a)) ∧
      heap.Footprint after [layout.parent, layout.rank] [] [] ∧
      (∀ clock, clock ∉ ["uf_find", "uf_compress", "uf_union"] → after.clocks clock = heap.clocks clock) ∧
      work after.clocks ≤ work heap.clocks + 4 * Nat.log2 n + 3 ∧
      work after.clocks + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        work heap.clocks + 2 * Algo2Lean.UnionFind.potential model + 6 * Algo2Lean.Ackermann.alpha n + 7 := by
  obtain ⟨first, second, after, firstPath, secondPath, execution, represented, storage, effect⟩ :=
    union_contract heap layout model representation a b
  refine ⟨after, unionResult model a b first second, execution, represented,
    unionResult_connected representation.valid a b first second, storage.footprint, ?_, ?_, ?_⟩
  · intro clock reserved
    have different : clock ≠ "uf_find" ∧ clock ≠ "uf_compress" ∧ clock ≠ "uf_union" := by
      simpa using reserved
    simp [effect clock, unionCosts, findCosts, different.1, different.2.1, different.2.2]
  · have firstBound := find_cost representation.valid firstPath
    have secondBound := find_cost (findResult_valid model a first representation.valid) secondPath
    rw [work_increments effect, work_unionCosts]
    omega
  · have amortized := Algo2Lean.UnionFind.union_amortized representation.valid firstPath secondPath
    rw [work_increments effect, work_unionCosts]
    change work heap.clocks + (2 * (first + second) + 3) +
      2 * Algo2Lean.UnionFind.potential (Algo2Lean.UnionFind.union
        (findResult (findResult model a first) b second) a b) ≤ _
    simp only [findResult]
    omega

-- Main result: Correctness and running time
/-- Union's full client contract exposes its precise partition effect, no
    allocation, storage preservation, actual cost increments, and an amortized
    budget that telescopes when the returned model is passed to the next call. -/
theorem union_amortized {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (a b : Fin n) :
    ∃ after nextModel,
      UnionFind.union.Call heap (layout.object, (a.val : Int), (b.val : Int)) after
        (decide (model.representative a ≠ model.representative b)) ∧
      Rep after layout nextModel ∧
      (∀ x y, Algo2Lean.UnionFind.Connected nextModel x y ↔
        Algo2Lean.UnionFind.Connected model x y ∨
        (Algo2Lean.UnionFind.Connected model x a ∧ Algo2Lean.UnionFind.Connected model y b) ∨
        (Algo2Lean.UnionFind.Connected model x b ∧ Algo2Lean.UnionFind.Connected model y a)) ∧
      Storage heap after [layout.parent, layout.rank] ∧
      heap.Increments after (Heap.cost heap after) ∧
      work (Heap.cost heap after) + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        2 * Algo2Lean.UnionFind.potential model + 6 * Algo2Lean.Ackermann.alpha n + 7 := by
  obtain ⟨first, second, after, firstPath, secondPath, execution, represented, storage, increments⟩ :=
    union_contract heap layout model representation a b
  refine ⟨after, unionResult model a b first second, execution, represented,
    unionResult_connected representation.valid a b first second, storage,
    increments.monotone.increments, ?_⟩
  rw [increments.cost, work_unionCosts]
  exact Algo2Lean.UnionFind.union_amortized representation.valid firstPath secondPath

end UnionFindAnalysis
