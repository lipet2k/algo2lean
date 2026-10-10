import Algo.kruskal.Generated
import Algo.kruskal.Facts
import Algo.union_find_init.Analysis
import Algo2LeanLib.KruskalMath
import Algo2LeanLib.Footprint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's source program sorts edge identifiers, then reuses the verified
union-find contract to accept precisely the edges joining distinct components.
The graph argument is independent of the storage and transition machinery.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal Algo.kruskal.Algo2LeanGenerated
open UnionFindAnalysis
open Algo2Lean.Kruskal

/-- Completing an empty suffix returns the same selection array. -/
theorem scan_done (heap : Heap) (sets : ObjectRef) (sources targets order chosen : SeqRef)
    (index count : Int) (valid : scan_edges.ValidInput heap
      (sets, sources, targets, order, chosen, index, count)) (finished : count ≤ index) :
    scan_edges.Call heap (sets, sources, targets, order, chosen, index, count) heap chosen := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.scan_edges_pc22 _ _ _)
  apply Reaches.prepend (Step.scan_edges_pc21_true _ _ _ (by simpa using finished))
  apply Reaches.prepend (Step.scan_edges_pc20 _ _ _)
  exact Reaches.single (Step.scan_edges_pc19 _ _ _ valid.2.2.2.2)

/-- An accepted edge is marked; a rejected edge leaves the flags unchanged. -/
def selectHeap (heap : Heap) (chosen : SeqRef) (edge : Int) (accepted : Bool) : Heap :=
  if accepted then heap.write chosen edge 1 else heap

/-- One scan iteration composes a union call with the remaining scan. The
    imported union-find theorem supplies the entire data-structure operation. -/
theorem scan_continue (heap after final : Heap) (sets : ObjectRef)
    (sources targets order chosen : SeqRef) (index count : Int) (accepted : Bool)
    (valid : scan_edges.ValidInput heap (sets, sources, targets, order, chosen, index, count))
    (running : index < count) (allocated : chosen < after.nextRef)
    (lastAllocated : chosen < final.nextRef)
    (join : Algo.union_find.UnionFind.union.Call (heap.tick "kruskal")
      (sets, heap.read sources (heap.read order index), heap.read targets (heap.read order index))
      after accepted)
    (rest : scan_edges.Call (selectHeap after chosen (heap.read order index) accepted)
      (sets, sources, targets, order, chosen, index + 1, count) final chosen) :
    scan_edges.Call heap (sets, sources, targets, order, chosen, index, count) final chosen := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.scan_edges_pc22 _ _ _)
  apply Reaches.prepend (Step.scan_edges_pc21_false _ _ _ (by simp; omega))
  apply Reaches.prepend (Step.scan_edges_pc18 _ _ _ valid.2.2.2.1)
  apply Reaches.prepend (Step.scan_edges_pc17 _ _ _)
  apply Reaches.prepend (Step.scan_edges_pc16 _ _ _)
  apply Reaches.prepend (Step.scan_edges_pc15 _ _ _ valid.1)
  apply Reaches.prepend (Step.scan_edges_pc14 _ _ _ valid.2.1)
  apply Reaches.prepend (Step.scan_edges_pc13 _ _ _ valid.2.2.1)
  apply Reaches.prepend (Step.scan_edges_pc12 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller join.2).trans
  cases accepted
  all_goals
    simp only [selectHeap, Bool.false_eq_true, if_false, if_true] at rest
  case false =>
    apply Reaches.prepend (Step.scan_edges_pc11_false _ _ _ rfl)
    apply Reaches.prepend (Step.scan_edges_pc9 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc8 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc7 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc6 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc3 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc2 _ _ _)
    apply (rest.2 _).trans
    exact Reaches.single (Step.scan_edges_pc1 _ _ _ lastAllocated)
  case true =>
    apply Reaches.prepend (Step.scan_edges_pc11_true _ _ _ rfl)
    apply Reaches.prepend (Step.scan_edges_pc10 _ _ _ allocated)
    apply Reaches.prepend (Step.scan_edges_pc9 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc8 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc7 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc6 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc3 _ _ _)
    apply Reaches.prepend (Step.scan_edges_pc2 _ _ _)
    apply (rest.2 _).trans
    exact Reaches.single (Step.scan_edges_pc1 _ _ _ lastAllocated)

/-- The four client arrays and the separately represented union-find object. -/
structure ScanLayout where
  sets : UnionFindAnalysis.Layout
  sources : SeqRef
  targets : SeqRef
  order : SeqRef
  chosen : SeqRef

/-- A flag array records exactly the selected edge identifiers. -/
def Flags (values : Seq) (selected : List Edge) : Prop :=
  ∀ id : Int, values id = (if selected.any (fun edge => (edge.id : Int) == id) then 1 else 0)

/-- The unprocessed suffix of the identifier array. -/
inductive Order (heap : Heap) (ref : SeqRef) : Int → List Edge → Prop where
  | nil (index : Int) : Order heap ref index []
  | cons {index : Int} {edge : Edge} {rest : List Edge}
      (head : heap.read ref index = (edge.id : Int))
      (tail : Order heap ref (index + 1) rest) : Order heap ref index (edge :: rest)

/-- Storage, graph connectivity, and output flags agree at a scan boundary. -/
structure ScanInvariant (n : Nat) (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index : Int) (pending selected : List Edge) : Prop where
  representation : Rep heap data.sets model
  partition : ∀ u v : Fin n, Algo2Lean.UnionFind.Connected model u v ↔
    Connected selected (u.val : Int) (v.val : Int)
  bounded : ∀ edge ∈ pending,
    (0 ≤ edge.source ∧ edge.source < (n : Int)) ∧ (0 ≤ edge.target ∧ edge.target < (n : Int))
  sources : ∀ edge ∈ pending, heap.read data.sources edge.id = edge.source
  targets : ∀ edge ∈ pending, heap.read data.targets edge.id = edge.target
  ordered : Order heap data.order index pending
  flags : Flags (heap.read data.chosen) selected
  sourceAllocated : data.sources < heap.nextRef
  targetAllocated : data.targets < heap.nextRef
  orderAllocated : data.order < heap.nextRef
  chosenAllocated : data.chosen < heap.nextRef
  sourceProtected : data.sources ∉ [data.sets.parent, data.sets.rank, data.chosen]
  targetProtected : data.targets ∉ [data.sets.parent, data.sets.rank, data.chosen]
  orderProtected : data.order ∉ [data.sets.parent, data.sets.rank, data.chosen]
  chosenProtected : data.chosen ∉ [data.sets.parent, data.sets.rank]

/-- Work performed by the scan and its union-find calls. Sorting is accounted
    for separately by its reusable sorting contract. -/
def work (clocks : Clocks) : Nat := UnionFindAnalysis.work clocks + clocks "kruskal"


/-- Writing a client array leaves the union-find representation unchanged. -/
theorem Rep.write_client {n : Nat} {heap : Heap} {layout : Layout}
    {model : Algo2Lean.UnionFind.State n} (represented : Rep heap layout model)
    (ref : SeqRef) (index value : Int) (parent : ref ≠ layout.parent)
    (rank : ref ≠ layout.rank) : Rep (heap.write ref index value) layout model := by
  refine ⟨represented.valid, represented.object, represented.readParent,
    represented.readRank, represented.readSize, represented.parentAllocated,
    represented.rankAllocated, represented.separate, ?_, ?_⟩
  · intro vertex
    simpa [Heap.read, Heap.write, Ne.symm parent] using represented.parents vertex
  · intro vertex
    simpa [Heap.read, Heap.write, Ne.symm rank] using represented.ranks vertex

/-- Marking one identifier adds precisely that edge to the flag interpretation. -/
theorem Flags.select {heap : Heap} {chosen : SeqRef} {selected : List Edge}
    (flags : Flags (heap.read chosen) selected) (edge : Edge) (accepted : Bool) :
    Flags ((selectHeap heap chosen edge.id accepted).read chosen)
      (if accepted then edge :: selected else selected) := by
  cases accepted
  · exact flags
  · intro id
    by_cases same : id = (edge.id : Int)
    · subst id
      simp [selectHeap, Heap.read, Heap.write]
    · simp only [selectHeap, if_true]
      rw [Heap.read_write_other_index _ _ _ _ _ same, flags]
      simp [List.any_cons, show ¬ ((edge.id : Int) = id) from Ne.symm same]

/-- An unchanged order array represents the same pending edges. -/
theorem Order.congr {before after : Heap} {ref : SeqRef} {index : Int} {edges : List Edge}
    (ordered : Order before ref index edges) (same : after.read ref = before.read ref) :
    Order after ref index edges := by
  induction ordered with
  | nil index => exact .nil index
  | cons head tail ih => exact .cons (by simpa [same] using head) ih

/-- Adding an edge already inside a component does not alter connectivity. -/
theorem connected_redundant {selected : List Edge} {edge : Edge}
    (connected : Connected selected edge.source edge.target) (u v : Int) :
    Connected (edge :: selected) u v ↔ Connected selected u v := by
  constructor
  · intro path
    rcases connected_cons.mp path with old | forward | backward
    · exact old
    · exact forward.1.trans (connected.trans forward.2)
    · exact backward.1.trans (connected.symm.trans backward.2)
  · intro path
    exact connected_cons.mpr (Or.inl path)

/-- The union contract agrees with undirected graph connectivity, regardless
    of which root is chosen or which parent pointers are compressed. -/
theorem partition_join {n : Nat} {old next : Algo2Lean.UnionFind.State n}
    {selected : List Edge} {edge : Edge} (a b : Fin n)
    (source : (a.val : Int) = edge.source) (target : (b.val : Int) = edge.target)
    (partition : ∀ u v : Fin n, Algo2Lean.UnionFind.Connected old u v ↔
      Connected selected (u.val : Int) (v.val : Int))
    (joined : ∀ x y, Algo2Lean.UnionFind.Connected next x y ↔
      Algo2Lean.UnionFind.Connected old x y ∨
      (Algo2Lean.UnionFind.Connected old x a ∧ Algo2Lean.UnionFind.Connected old y b) ∨
      (Algo2Lean.UnionFind.Connected old x b ∧ Algo2Lean.UnionFind.Connected old y a)) :
    ∀ u v : Fin n, Algo2Lean.UnionFind.Connected next u v ↔
      Connected (edge :: selected) (u.val : Int) (v.val : Int) := by
  intro u v
  rw [joined, connected_cons]
  simp only [partition, source, target, Joined]
  constructor
  · rintro (old | ⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inl old
    · exact Or.inr (Or.inl ⟨first, second.symm⟩)
    · exact Or.inr (Or.inr ⟨first, second.symm⟩)
  · rintro (old | ⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inl old
    · exact Or.inr (Or.inl ⟨first, second.symm⟩)
    · exact Or.inr (Or.inr ⟨first, second.symm⟩)

/-- A scan iteration writes only the union-find arrays and selection flags. -/
theorem selection_frame {data : ScanLayout} {heap after : Heap}
    (frame : (heap.tick "kruskal").Footprint after [data.sets.parent, data.sets.rank] [] [])
    (edge : Edge) (accepted : Bool) :
    heap.Footprint (selectHeap after data.chosen edge.id accepted)
      [data.sets.parent, data.sets.rank, data.chosen] [] [] := by
  have charged := (Heap.Footprint.refl heap [data.sets.parent, data.sets.rank] [] []).tick "kruskal"
  have all := (charged.trans frame).weaken (moreSequences := [data.sets.parent, data.sets.rank, data.chosen]) (moreObjects := []) (moreCollections := [])
    (by
      intro ref member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) (by simp) (by simp)
  cases accepted
  · exact all
  · exact all.write data.chosen edge.id 1 (Or.inl (by simp))

/-- One iteration maintains the scan invariant and consumes one pending edge. -/
theorem ScanInvariant.advance {n : Nat} {data : ScanLayout} {heap after : Heap}
    {model nextModel : Algo2Lean.UnionFind.State n} {index : Int}
    {edge : Edge} {pending selected : List Edge}
    (invariant : ScanInvariant n data heap model index (edge :: pending) selected)
    (represented : Rep after data.sets nextModel)
    (frame : (heap.tick "kruskal").Footprint after [data.sets.parent, data.sets.rank] [] [])
    (partition : ∀ u v : Fin n, Algo2Lean.UnionFind.Connected nextModel u v ↔
      Connected (edge :: selected) (u.val : Int) (v.val : Int))
    (accepted : Bool)
    (decision : accepted = true ↔ ¬ Connected selected edge.source edge.target) :
    ScanInvariant n data (selectHeap after data.chosen edge.id accepted) nextModel
      (index + 1) pending (if accepted then edge :: selected else selected) := by
  classical
  let changed := selectHeap after data.chosen edge.id accepted
  have extended := selection_frame frame edge accepted
  have chosenSame : after.read data.chosen = heap.read data.chosen :=
    frame.read data.chosen invariant.chosenAllocated invariant.chosenProtected
  have chosenParent : data.chosen ≠ data.sets.parent := by
    have both : data.chosen ≠ data.sets.parent ∧ data.chosen ≠ data.sets.rank := by simpa using invariant.chosenProtected
    exact both.1
  have chosenRank : data.chosen ≠ data.sets.rank := by
    have both : data.chosen ≠ data.sets.parent ∧ data.chosen ≠ data.sets.rank := by simpa using invariant.chosenProtected
    exact both.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Nat.lt_of_lt_of_le invariant.sourceAllocated extended.nextRef,
    Nat.lt_of_lt_of_le invariant.targetAllocated extended.nextRef,
    Nat.lt_of_lt_of_le invariant.orderAllocated extended.nextRef,
    Nat.lt_of_lt_of_le invariant.chosenAllocated extended.nextRef,
    invariant.sourceProtected, invariant.targetProtected, invariant.orderProtected,
    invariant.chosenProtected⟩
  · cases accepted
    · exact represented
    · exact Rep.write_client represented data.chosen edge.id 1 chosenParent chosenRank
  · intro u v
    cases accepted
    · have connected : Connected selected edge.source edge.target := by simpa using decision
      exact (partition u v).trans (connected_redundant connected _ _)
    · exact partition u v
  · intro next member
    exact invariant.bounded next (List.mem_cons_of_mem edge member)
  · intro next member
    rw [extended.read data.sources invariant.sourceAllocated invariant.sourceProtected]
    exact invariant.sources next (List.mem_cons_of_mem edge member)
  · intro next member
    rw [extended.read data.targets invariant.targetAllocated invariant.targetProtected]
    exact invariant.targets next (List.mem_cons_of_mem edge member)
  · cases invariant.ordered with
    | cons head tail => exact tail.congr (extended.read data.order invariant.orderAllocated invariant.orderProtected)
  · apply Flags.select
    simpa [chosenSame] using invariant.flags


/-- A scan invariant includes precisely the compiler's allocation preconditions. -/
theorem ScanInvariant.validInput {n : Nat} {data : ScanLayout} {heap : Heap}
    {model : Algo2Lean.UnionFind.State n} {index : Int} {pending selected : List Edge}
    (invariant : ScanInvariant n data heap model index pending selected) (count : Int) :
    scan_edges.ValidInput heap (data.sets.object, data.sources, data.targets, data.order,
      data.chosen, index, count) :=
  ⟨invariant.representation.object, invariant.sourceAllocated, invariant.targetAllocated,
    invariant.orderAllocated, invariant.chosenAllocated⟩

/-- The scan terminates, follows the abstract Kruskal acceptance rule, and
    charges at most one scan tick plus the proved union bound for each edge.
    All storage outside the three private arrays is preserved. -/
theorem scan_contract {n : Nat} (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index count : Int) (pending selected : List Edge)
    (invariant : ScanInvariant n data heap model index pending selected)
    (length : index + (pending.length : Int) = count) :
    ∃ final nextModel result,
      scan_edges.Call heap (data.sets.object, data.sources, data.targets, data.order,
        data.chosen, index, count) final data.chosen ∧
      ScanInvariant n data final nextModel count [] result ∧
      Scan pending selected result ∧
      heap.Footprint final [data.sets.parent, data.sets.rank, data.chosen] [] [] ∧
      (∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
        final.clocks clock = heap.clocks clock) ∧
      work final.clocks ≤ work heap.clocks + pending.length * (4 * Nat.log2 n + 4) ∧
      work final.clocks + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          pending.length * (6 * Algo2Lean.Ackermann.alpha n + 8) := by
  classical
  induction pending generalizing heap model index selected with
  | nil =>
    have finish : index = count := by simpa using length
    subst index
    exact ⟨heap, model, selected, scan_done _ _ _ _ _ _ _ _ (invariant.validInput count) (by omega),
      invariant, .done selected, Heap.Footprint.refl _ _ _ _, by intros; rfl, by simp, by simp⟩
  | cons edge pending ih =>
    obtain ⟨sourceBounds, targetBounds⟩ := invariant.bounded edge (by simp)
    let a : Fin n := ⟨edge.source.toNat, by omega⟩
    let b : Fin n := ⟨edge.target.toNat, by omega⟩
    have aValue : (a.val : Int) = edge.source := by simp [a]; omega
    have bValue : (b.val : Int) = edge.target := by simp [b]; omega
    obtain ⟨after, nextModel, unionCall, represented, joined, frame, clocks, cost, amortized⟩ :=
      UnionFindAnalysis.union_summary_amortized (heap.tick "kruskal") data.sets model
        (invariant.representation.tick "kruskal") a b
    let accepted := decide (model.representative a ≠ model.representative b)
    have decision : accepted = true ↔ ¬ Connected selected edge.source edge.target := by
      simp only [accepted, decide_eq_true_eq]
      exact not_congr (by simpa only [Algo2Lean.UnionFind.Connected, aValue, bValue] using invariant.partition a b)
    have nextPartition := partition_join a b aValue bValue invariant.partition joined
    have nextInvariant := invariant.advance represented frame nextPartition accepted decision
    let changed := selectHeap after data.chosen edge.id accepted
    let picked := if accepted then edge :: selected else selected
    have shorter : index + 1 + (pending.length : Int) = count := by
      simp only [List.length_cons] at length
      omega
    obtain ⟨final, finalModel, result, recursive, finalInvariant, scan, suffixFrame, suffixClocks, suffixCost, suffixAmortized⟩ :=
      ih changed nextModel (index + 1) picked nextInvariant shorter
    have edgeId : heap.read data.order index = (edge.id : Int) := by
      cases invariant.ordered with
      | cons head _ => exact head
    have sourceRead : heap.read data.sources (heap.read data.order index) = (a.val : Int) := by
      rw [edgeId, aValue]
      exact invariant.sources edge (by simp)
    have targetRead : heap.read data.targets (heap.read data.order index) = (b.val : Int) := by
      rw [edgeId, bValue]
      exact invariant.targets edge (by simp)
    have localFrame := selection_frame frame edge accepted
    have localClocks (clock : String) (outside : clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"]) :
        changed.clocks clock = heap.clocks clock := by
      have notScan : clock ≠ "kruskal" := by simpa using (fun same => outside (by simp [same]))
      have notUnion : clock ∉ ["uf_find", "uf_compress", "uf_union"] := by
        intro member
        exact outside (List.mem_cons_of_mem _ member)
      have equal := clocks clock notUnion
      simp only [changed, selectHeap]
      split <;> simpa [Heap.tick, notScan] using equal
    have localCost : work changed.clocks ≤ work heap.clocks + (4 * Nat.log2 n + 4) := by
      have scanClock := clocks "kruskal" (by simp)
      have ufTick : UnionFindAnalysis.work (heap.tick "kruskal").clocks = UnionFindAnalysis.work heap.clocks := by
        simp [UnionFindAnalysis.work, Heap.tick]
      rw [ufTick] at cost
      have same : changed.clocks = after.clocks := by
        unfold changed selectHeap
        split <;> rfl
      rw [same]
      simp only [work]
      have counted : after.clocks "kruskal" = heap.clocks "kruskal" + 1 := by
        simpa [Heap.tick] using scanClock
      omega
    have localAmortized : work changed.clocks + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          (6 * Algo2Lean.Ackermann.alpha n + 8) := by
      have scanClock := clocks "kruskal" (by simp)
      have ufTick : UnionFindAnalysis.work (heap.tick "kruskal").clocks = UnionFindAnalysis.work heap.clocks := by
        simp [UnionFindAnalysis.work, Heap.tick]
      rw [ufTick] at amortized
      have same : changed.clocks = after.clocks := by
        unfold changed selectHeap
        split <;> rfl
      rw [same]
      simp only [work]
      have counted : after.clocks "kruskal" = heap.clocks "kruskal" + 1 := by
        simpa [Heap.tick] using scanClock
      omega
    refine ⟨final, finalModel, result, ?_, finalInvariant, ?_, localFrame.trans suffixFrame, ?_, ?_, ?_⟩
    · apply scan_continue heap after final data.sets.object data.sources data.targets data.order data.chosen
        index count accepted (invariant.validInput count) (by simp only [List.length_cons] at length; omega)
        (Nat.lt_of_lt_of_le invariant.chosenAllocated frame.nextRef) finalInvariant.chosenAllocated
      · simpa only [sourceRead, targetRead] using unionCall
      · simpa only [edgeId] using recursive
    · cases hacc : accepted with
      | false =>
        have connected : Connected selected edge.source edge.target := by simpa [hacc] using decision
        exact Scan.reject connected (by simpa [picked, hacc] using scan)
      | true =>
        have separate : ¬ Connected selected edge.source edge.target := decision.mp hacc
        exact Scan.accept separate (by simpa [picked, hacc] using scan)
    · intro clock outside
      exact (suffixClocks clock outside).trans (localClocks clock outside)
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The logarithmic worst-case bound remains available as a direct consequence
    of the same call contract and execution used in the amortized analysis. -/
theorem scan_verified {n : Nat} (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index count : Int) (pending selected : List Edge)
    (invariant : ScanInvariant n data heap model index pending selected)
    (length : index + (pending.length : Int) = count) :
    ∃ final nextModel result,
      scan_edges.Call heap (data.sets.object, data.sources, data.targets, data.order,
        data.chosen, index, count) final data.chosen ∧
      ScanInvariant n data final nextModel count [] result ∧
      Scan pending selected result ∧
      heap.Footprint final [data.sets.parent, data.sets.rank, data.chosen] [] [] ∧
      (∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
        final.clocks clock = heap.clocks clock) ∧
      work final.clocks ≤ work heap.clocks + pending.length * (4 * Nat.log2 n + 4) := by
  obtain ⟨final, nextModel, result, execution, finalInvariant, scan, frame, clocks, bound, _⟩ :=
    scan_contract data heap model index count pending selected invariant length
  exact ⟨final, nextModel, result, execution, finalInvariant, scan, frame, clocks, bound⟩

/-- The source-level entry point composes sorting, construction, and the scan. -/
theorem kruskal_calls (heap sorted initialized final : Heap)
    (size count : Int) (sources targets weights order : SeqRef) (sets : ObjectRef)
    (valid : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (sorting : Algo.sort_indices.sort_indices.Call heap (weights, count) sorted order)
    (construction : Algo.union_find.UnionFind.Call sorted size initialized sets)
    (scan : scan_edges.Call ((initialized.allocate (fun _ => 0)).tick "kruskal")
      (sets, sources, targets, order, initialized.nextRef, 0, count) final initialized.nextRef)
    (allocated : initialized.nextRef < final.nextRef) :
    kruskal.Call heap (size, sources, targets, weights, count) final initialized.nextRef := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.kruskal_pc20 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc19 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc18 _ _ _)
  apply (ModuleCall.summary import_2_simulates _ caller sorting.2).trans
  apply Reaches.prepend (Step.kruskal_pc17 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc16 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc15 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller construction.2).trans
  apply Reaches.prepend (Step.kruskal_pc14 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc13 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc12 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc11 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc10 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc9 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc8 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc7 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc6 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc5 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc4 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc3 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc2 _ _ _)
  apply (scan.2 _).trans
  exact Reaches.single (Step.kruskal_pc1 _ _ _ allocated)

/-- A finite array prefix determines the inductive order view. -/
theorem Order.of_indexed (heap : Heap) (ref : SeqRef) (index : Int) (pending : List Edge)
    (agreement : ∀ (i : Nat) (within : i < pending.length),
      heap.read ref (index + i) = (pending[i].id : Int)) : Order heap ref index pending := by
  induction pending generalizing index with
  | nil => exact .nil index
  | cons edge pending ih =>
    apply Order.cons
    · simpa using agreement 0 (by simp)
    · apply ih (index + 1)
      intro i within
      have shifted := agreement (i + 1) (by simpa using within)
      have indexEq : index + (↑(i + 1) : Int) = index + 1 + i := by omega
      rw [indexEq] at shifted
      simpa only [List.getElem_cons_succ] using shifted

/-- A fresh client sequence preserves the represented union-find object. -/
theorem Rep.allocate_client {n : Nat} {heap : Heap} {layout : Layout}
    {model : Algo2Lean.UnionFind.State n} (represented : Rep heap layout model) (values : Seq) :
    Rep (heap.allocate values) layout model := by
  refine ⟨represented.valid, represented.object, represented.readParent, represented.readRank,
    represented.readSize, Nat.lt_trans represented.parentAllocated (Nat.lt_succ_self _),
    Nat.lt_trans represented.rankAllocated (Nat.lt_succ_self _), represented.separate, ?_, ?_⟩
  · intro vertex
    rw [Heap.read_allocate_old _ _ _ _ represented.parentAllocated]
    exact represented.parents vertex
  · intro vertex
    rw [Heap.read_allocate_old _ _ _ _ represented.rankAllocated]
    exact represented.ranks vertex

/-- Heap at the start of the scan, after initializing singleton components and
    allocating the zero-filled selection array. -/
def initialHeap (heap : Heap) (size : Nat) : Heap :=
  ((newHeap heap size).allocate (fun _ => 0)).tick "kruskal"

/-- Private references created after sorting; the input arrays may alias. -/
def initialLayout (heap : Heap) (size : Nat) (sources targets order : SeqRef) : ScanLayout :=
  ⟨newLayout heap, sources, targets, order, (newHeap heap size).nextRef⟩

/-- Initializing the scan preserves all previously allocated sequence values. -/
theorem initial_read_old (heap : Heap) (size : Nat) (ref : SeqRef) (old : ref < heap.nextRef) :
    (initialHeap heap size).read ref = heap.read ref := by
  have refs := (constructor_allocations heap size).1
  have preserved := (constructor_frame heap size).2.1 ref old
  have allocated : ref < (newHeap heap size).nextRef := by rw [refs]; simp only [SeqRef] at *; omega
  funext index
  change ((newHeap heap size).allocate (fun _ => 0)).read ref index = heap.read ref index
  rw [Heap.read_allocate_old _ _ _ _ allocated]
  exact congrFun preserved index

/-- The initial partition has no edges and every selection flag is zero. -/
theorem initial_invariant (heap : Heap) (size : Nat) (sources targets order : SeqRef)
    (pending : List Edge)
    (sourceAllocated : sources < heap.nextRef) (targetAllocated : targets < heap.nextRef)
    (orderAllocated : order < heap.nextRef)
    (bounds : ValidInput size pending)
    (sourceValues : ∀ edge ∈ pending, heap.read sources edge.id = edge.source)
    (targetValues : ∀ edge ∈ pending, heap.read targets edge.id = edge.target)
    (ordering : ∀ (i : Nat) (within : i < pending.length), heap.read order i = (pending[i].id : Int)) :
    ScanInvariant size (initialLayout heap size sources targets order) (initialHeap heap size)
      (Algo2Lean.UnionFind.initial size) 0 pending [] := by
  have refs := (constructor_allocations heap size).1
  have sourceSame := initial_read_old heap size sources sourceAllocated
  have targetSame := initial_read_old heap size targets targetAllocated
  have orderSame := initial_read_old heap size order orderAllocated
  refine ⟨(Rep.allocate_client (constructor_rep heap size) (fun _ => 0)).tick "kruskal", ?_,
    (fun edge member => ⟨bounds.source edge member, bounds.target edge member⟩), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    rw [Algo2Lean.UnionFind.initial_connected, connected_nil]
    constructor
    · intro same; subst v; rfl
    · intro same; apply Fin.ext; omega
  · simpa only [initialLayout, sourceSame] using sourceValues
  · simpa only [initialLayout, targetSame] using targetValues
  · apply Order.of_indexed
    intro i within
    simpa only [initialLayout, orderSame, Int.zero_add] using ordering i within
  · intro id
    simp [initialHeap, initialLayout, Heap.read_allocate_new]
  · change sources < (newHeap heap size).nextRef + 1
    rw [refs]
    simp only [SeqRef] at *
    omega
  · change targets < (newHeap heap size).nextRef + 1
    rw [refs]
    simp only [SeqRef] at *
    omega
  · change order < (newHeap heap size).nextRef + 1
    rw [refs]
    simp only [SeqRef] at *
    omega
  · change (newHeap heap size).nextRef < (newHeap heap size).nextRef + 1
    omega
  · simp only [initialLayout, newLayout, List.mem_cons, List.not_mem_nil, or_false, not_or]
    rw [refs]
    simp only [SeqRef] at *
    omega
  · simp only [initialLayout, newLayout, List.mem_cons, List.not_mem_nil, or_false, not_or]
    rw [refs]
    simp only [SeqRef] at *
    omega
  · simp only [initialLayout, newLayout, List.mem_cons, List.not_mem_nil, or_false, not_or]
    rw [refs]
    simp only [SeqRef] at *
    omega
  · simp only [initialLayout, newLayout, List.mem_cons, List.not_mem_nil, or_false, not_or]
    rw [refs]
    simp only [SeqRef] at *
    omega

/-- Initialization costs one tick per vertex and one scan setup tick. -/
theorem initial_work (heap : Heap) (size : Nat) :
    work (initialHeap heap size).clocks = work heap.clocks + size + 2 := by
  simp [work, UnionFindAnalysis.work, initialHeap, constructor_clocks, Heap.tick]
  omega

/-- Initialization changes no clock other than `uf_init` and `kruskal`. -/
theorem initial_clocks (heap : Heap) (size : Nat) (clock : String)
    (notInit : clock ≠ "uf_init") (notScan : clock ≠ "kruskal") :
    (initialHeap heap size).clocks clock = heap.clocks clock := by
  simp [initialHeap, Heap.tick, notScan, constructor_clocks, notInit]

end KruskalAnalysis
