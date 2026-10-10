import Algo.kruskal.Generated
import Algo.kruskal.Facts
import Algo.kruskal.Points
import Algo.union_find_init.Analysis
import Algo2LeanLib.KruskalMath
import Algo2LeanLib.Footprint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal initializes singleton components, sorts edge identifiers, and compares
representatives before selecting an edge and applying the verified union.
The graph argument is independent of the storage and transition machinery.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal Algo.kruskal.Algo2LeanGenerated
open UnionFindAnalysis
open Algo2Lean.Kruskal

/-- An accepted edge is marked; a rejected edge leaves the flags unchanged. -/
def selectHeap (heap : Heap) (chosen : SeqRef) (edge : Int) (accepted : Bool) : Heap :=
  if accepted then heap.write chosen edge 1 else heap

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

/-- Source-facing values needed at the edge-loop boundary. -/
structure ScanLocals (data : ScanLayout) (index count : Int) (state : Configuration) : Prop where
  location : kruskal.At.scan state
  sets : kruskal.Local.sets state = some data.sets.object
  sources : kruskal.Local.sources state = some data.sources
  targets : kruskal.Local.targets state = some data.targets
  order : kruskal.Local.order state = some data.order
  chosen : kruskal.Local.chosen state = some data.chosen
  index : kruskal.Local.index state = some index
  count : kruskal.Local.count state = some count

/-- Complete the edge loop from any configuration with these local values.
    The caller's stack and irrelevant temporary variables remain unrestricted. -/
def ScanCall (data : ScanLayout) (heap : Heap) (index count : Int) (final : Heap) : Prop :=
  ∀ state, ScanLocals data index count state → state.heap = heap →
    kruskal.CallFrom state final data.chosen

/-- Completing an empty suffix returns the unchanged selection array. -/
theorem scan_done (data : ScanLayout) (heap : Heap) (index count : Int)
    (allocated : data.chosen < heap.nextRef) (finished : count ≤ index) :
    ScanCall data heap index count heap := by
  intro state reads heq
  rcases reads with ⟨location, sets, sources, targets, order, chosen, idx, cnt⟩
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | import_0 => cases location
    | import_2 => cases location
    | fn_kruskal pc s =>
      have atLoop : pc = 4 := by
        unfold kruskal.At.scan at location
        split at location <;> simp_all
      subst pc
      change h = heap at heq
      subst h
      simp [kruskal.Local.chosen, kruskal.Local.index, kruskal.Local.count] at chosen idx cnt
      intro caller
      apply Reaches.prepend (Step.kruskal_pc4 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc3_false _ _ _ (by simp [idx, cnt]; omega))
      apply Reaches.prepend (Step.kruskal_pc2 _ _ _)
      simpa only [chosen] using Reaches.single (Step.kruskal_pc1 heap _ caller (by simpa [chosen]))

/-- Two representative lookups precede the conditional selection and union.
    The union result is intentionally ignored, as in textbook MST-KRUSKAL. -/
def EdgeCalls (data : ScanLayout) (heap final : Heap) (edge a b : Int) : Prop :=
  ∃ first second left right,
    Algo.union_find.UnionFind.find.Call (heap.tick "kruskal") (data.sets.object, a) first left ∧
    Algo.union_find.UnionFind.find.Call first (data.sets.object, b) second right ∧
    (if left ≠ right then ∃ result,
      Algo.union_find.UnionFind.union.Call (second.write data.chosen edge 1)
        (data.sets.object, a, b) final result else final = second) ∧
    data.chosen < second.nextRef

/-- One source iteration reuses completed data-structure calls and the
    remaining loop, without exposing their internal transitions. -/
theorem scan_continue (data : ScanLayout) (heap after final : Heap) (index count : Int)
    (sources : data.sources < heap.nextRef) (targets : data.targets < heap.nextRef)
    (order : data.order < heap.nextRef) (running : index < count)
    (operations : EdgeCalls data heap after (heap.read data.order index)
      (heap.read data.sources (heap.read data.order index))
      (heap.read data.targets (heap.read data.order index)))
    (rest : ScanCall data after (index + 1) count final) :
    ScanCall data heap index count final := by
  obtain ⟨first, second, left, right, findA, findB, join, chosenAllocated⟩ := operations
  intro state reads heq
  rcases reads with ⟨location, sets, src, tgt, ord, chosen, idx, cnt⟩
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | import_0 => cases location
    | import_2 => cases location
    | fn_kruskal pc s =>
      have atLoop : pc = 4 := by
        unfold kruskal.At.scan at location
        split at location <;> simp_all
      subst pc
      change h = heap at heq
      subst h
      simp [kruskal.Local.sets, kruskal.Local.sources, kruskal.Local.targets,
        kruskal.Local.order, kruskal.Local.chosen, kruskal.Local.index, kruskal.Local.count]
        at sets src tgt ord chosen idx cnt
      intro caller
      apply Reaches.prepend (Step.kruskal_pc4 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc3_true _ _ _ (by simpa [idx, cnt]))
      apply Reaches.prepend (Step.kruskal_pc27 _ _ _ (by simpa [ord]))
      apply Reaches.prepend (Step.kruskal_pc26 _ _ _ (by simpa [src]))
      apply Reaches.prepend (Step.kruskal_pc25 _ _ _ (by simpa [tgt]))
      apply Reaches.prepend (Step.kruskal_pc24 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc23 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc22 _ _ _ (by simpa only [sets] using! findA.1))
      apply Reaches.prepend (Step.kruskal_pc21 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc20 _ _ _)
      simp only [sets, src, tgt, ord, chosen, idx] at *
      apply (ModuleCall.summary import_0_simulates _ caller findA.2).trans
      apply Reaches.prepend (Step.kruskal_pc19 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc18 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc17 _ _ _ (by exact findB.1))
      apply Reaches.prepend (Step.kruskal_pc16 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc15 _ _ _)
      apply (ModuleCall.summary import_0_simulates _ caller findB.2).trans
      apply Reaches.prepend (Step.kruskal_pc14 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc13 _ _ _)
      by_cases distinct : left ≠ right
      · rw [if_pos distinct] at join
        obtain ⟨result, join⟩ := join
        apply Reaches.prepend (Step.kruskal_pc12_true _ _ _ (by simpa))
        apply Reaches.prepend (Step.kruskal_pc11 _ _ _ chosenAllocated)
        apply Reaches.prepend (Step.kruskal_pc10 _ _ _)
        apply Reaches.prepend (Step.kruskal_pc9 _ _ _ (by exact join.1))
        apply Reaches.prepend (Step.kruskal_pc8 _ _ _)
        apply Reaches.prepend (Step.kruskal_pc7 _ _ _)
        apply Reaches.prepend (Step.kruskal_pc6 _ _ _)
        apply (ModuleCall.summary import_0_simulates _ caller join.2).trans
        apply Reaches.prepend (Step.kruskal_pc5 _ _ _)
        refine rest (.active _ (.fn_kruskal 4 _) []) ?_ rfl caller
        exact ⟨True.intro, by simp [kruskal.Local.sets], by simp [kruskal.Local.sources],
          by simp [kruskal.Local.targets], by simp [kruskal.Local.order],
          by simp [kruskal.Local.chosen], by simp [kruskal.Local.index],
          by simp [kruskal.Local.count, cnt]⟩
      · rw [if_neg distinct] at join
        subst after
        apply Reaches.prepend (Step.kruskal_pc12_false _ _ _ (by simp [distinct]))
        apply Reaches.prepend (Step.kruskal_pc5 _ _ _)
        refine rest (.active _ (.fn_kruskal 4 _) []) ?_ rfl caller
        exact ⟨True.intro, by simp [kruskal.Local.sets], by simp [kruskal.Local.sources],
          by simp [kruskal.Local.targets], by simp [kruskal.Local.order],
          by simp [kruskal.Local.chosen], by simp [kruskal.Local.index],
          by simp [kruskal.Local.count, cnt]⟩
/-- One iteration preserves the graph representation and consumes the first
    pending edge. Only the two disjoint-set arrays and result flags may change. -/
theorem ScanInvariant.advance {n : Nat} {data : ScanLayout} {heap after : Heap}
    {model nextModel : Algo2Lean.UnionFind.State n} {index : Int}
    {edge : Edge} {pending selected : List Edge}
    (invariant : ScanInvariant n data heap model index (edge :: pending) selected)
    (represented : Rep after data.sets nextModel)
    (frame : heap.Footprint after [data.sets.parent, data.sets.rank, data.chosen] [] [])
    (partition : ∀ u v : Fin n, Algo2Lean.UnionFind.Connected nextModel u v ↔
      Connected (edge :: selected) (u.val : Int) (v.val : Int))
    (accepted : Bool)
    (decision : accepted = true ↔ ¬ Connected selected edge.source edge.target)
    (flags : Flags (after.read data.chosen) (if accepted then edge :: selected else selected)) :
    ScanInvariant n data after nextModel (index + 1) pending
      (if accepted then edge :: selected else selected) := by
  refine ⟨represented, ?_, ?_, ?_, ?_, ?_, flags,
    Nat.lt_of_lt_of_le invariant.sourceAllocated frame.nextRef,
    Nat.lt_of_lt_of_le invariant.targetAllocated frame.nextRef,
    Nat.lt_of_lt_of_le invariant.orderAllocated frame.nextRef,
    Nat.lt_of_lt_of_le invariant.chosenAllocated frame.nextRef,
    invariant.sourceProtected, invariant.targetProtected, invariant.orderProtected,
    invariant.chosenProtected⟩
  · intro u v
    cases accepted
    · have connected : Connected selected edge.source edge.target := by simpa using decision
      exact (partition u v).trans (connected_redundant connected _ _)
    · exact partition u v
  · intro next member
    exact invariant.bounded next (List.mem_cons_of_mem edge member)
  · intro next member
    rw [frame.read data.sources invariant.sourceAllocated invariant.sourceProtected]
    exact invariant.sources next (List.mem_cons_of_mem edge member)
  · intro next member
    rw [frame.read data.targets invariant.targetAllocated invariant.targetProtected]
    exact invariant.targets next (List.mem_cons_of_mem edge member)
  · cases invariant.ordered with
    | cons head tail => exact tail.congr (frame.read data.order invariant.orderAllocated invariant.orderProtected)

/-- Comparing two components performs two reusable full-compression finds.
    Connectivity and ranks are unchanged; costs telescope through the returned
    model instead of resetting the union-find potential between operations. -/
theorem compare_components {n : Nat} (heap : Heap) (layout : UnionFindAnalysis.Layout)
    (model : Algo2Lean.UnionFind.State n) (represented : Rep heap layout model) (a b : Fin n) :
    ∃ first second compressed,
      Algo.union_find.UnionFind.find.Call heap (layout.object, (a.val : Int)) first
        ((model.representative a).val : Int) ∧
      Algo.union_find.UnionFind.find.Call first (layout.object, (b.val : Int)) second
        ((model.representative b).val : Int) ∧
      Rep second layout compressed ∧ compressed.representative = model.representative ∧
      heap.Footprint second [layout.parent, layout.rank] [] [] ∧
      (∀ clock, clock ∉ ["uf_find", "uf_compress", "uf_union"] →
        second.clocks clock = heap.clocks clock) ∧
      UnionFindAnalysis.work second.clocks ≤ UnionFindAnalysis.work heap.clocks + 4 * n.log2 + 2 ∧
      UnionFindAnalysis.work second.clocks + 2 * Algo2Lean.UnionFind.potential compressed ≤
        UnionFindAnalysis.work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          4 * Algo2Lean.Ackermann.alpha n + 6 := by
  obtain ⟨p, first, pathA, callA, repA, storageA, costsA⟩ := find_contract heap layout model represented a
  obtain ⟨q, second, pathB, callB, repB, storageB, costsB⟩ :=
    find_contract first layout (findResult model a p) repA b
  have sameA := findResult_representative model a p
  have sameB := findResult_representative (findResult model a p) b q
  have frame := storageA.footprint.trans storageB.footprint
  have firstWork := UnionFindAnalysis.work_increments costsA
  have secondWork := UnionFindAnalysis.work_increments costsB
  rw [work_findCosts] at firstWork secondWork
  have firstBound := Algo2Lean.UnionFind.find_cost represented.valid pathA
  have secondBound := Algo2Lean.UnionFind.find_cost repA.valid pathB
  have firstAmortized := Algo2Lean.UnionFind.find_amortized represented.valid pathA
  have secondAmortized := Algo2Lean.UnionFind.find_amortized repA.valid pathB
  refine ⟨first, second, _, callA, ?_, repB, sameB.trans sameA,
    frame.weaken (by simp) (by simp) (by simp), ?_, ?_, ?_⟩
  · simpa only [sameA] using callB
  · intro clock outside
    have different : clock ≠ "uf_find" ∧ clock ≠ "uf_compress" ∧ clock ≠ "uf_union" := by
      simpa using outside
    have ca := costsA clock
    have cb := costsB clock
    simp only [findCosts, different.1, different.2.1, if_false, Nat.add_zero] at ca cb
    omega
  · omega
  · change UnionFindAnalysis.work second.clocks +
      2 * Algo2Lean.UnionFind.potential (findResult (findResult model a p) b q) ≤ _
    simp only [findResult] at *
    omega

/-- The textbook edge test and conditional union reuse the independent find and
    union bounds. The rejected case performs no union and no selection write. -/
theorem edge_contract {n : Nat} (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index : Int) (edge : Edge)
    (pending selected : List Edge)
    (invariant : ScanInvariant n data heap model index (edge :: pending) selected) :
    ∃ after nextModel, ∃ accepted : Bool,
      (accepted = true ↔ ¬ Connected selected edge.source edge.target) ∧
      EdgeCalls data heap after edge.id edge.source edge.target ∧
      ScanInvariant n data after nextModel (index + 1) pending
        (if accepted then edge :: selected else selected) ∧
      heap.Footprint after [data.sets.parent, data.sets.rank, data.chosen] [] [] ∧
      (∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
        after.clocks clock = heap.clocks clock) ∧
      work after.clocks ≤ work heap.clocks + 8 * n.log2 + 6 ∧
      work after.clocks + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          10 * Algo2Lean.Ackermann.alpha n + 14 := by
  classical
  obtain ⟨sourceBounds, targetBounds⟩ := invariant.bounded edge (by simp)
  let a : Fin n := ⟨edge.source.toNat, by omega⟩
  let b : Fin n := ⟨edge.target.toNat, by omega⟩
  have av : (a.val : Int) = edge.source := by simp [a]; omega
  have bv : (b.val : Int) = edge.target := by simp [b]; omega
  obtain ⟨first, second, compressed, findA, findB, rep, same, frame, clocks, cost, amortized⟩ :=
    compare_components (heap.tick "kruskal") data.sets model
      (invariant.representation.tick "kruskal") a b
  have samePartition (u v : Fin n) : Algo2Lean.UnionFind.Connected compressed u v ↔
      Algo2Lean.UnionFind.Connected model u v := by simp only [Algo2Lean.UnionFind.Connected, same]
  have separateChosen : data.chosen ≠ data.sets.parent ∧ data.chosen ≠ data.sets.rank := by
    simpa using invariant.chosenProtected
  have chosenAllocated : data.chosen < second.nextRef :=
    Nat.lt_of_lt_of_le invariant.chosenAllocated frame.nextRef
  have flags : Flags (second.read data.chosen) selected := by
    rw [frame.read data.chosen invariant.chosenAllocated invariant.chosenProtected]
    exact invariant.flags
  have beforeFrame := (Heap.Footprint.refl heap [data.sets.parent, data.sets.rank] [] []).tick "kruskal"
  have prefixFrame := beforeFrame.trans frame
  have ufTick : UnionFindAnalysis.work (heap.tick "kruskal").clocks =
      UnionFindAnalysis.work heap.clocks := by simp [UnionFindAnalysis.work, Heap.tick]
  rw [ufTick] at cost amortized
  have scanClock : second.clocks "kruskal" = heap.clocks "kruskal" + 1 := by
    simpa [Heap.tick] using clocks "kruskal" (by simp)
  by_cases distinct : model.representative a ≠ model.representative b
  · obtain ⟨after, nextModel, join, represented, joined, unionFrame, unionClocks, unionCost, unionAmortized⟩ :=
      union_summary_amortized (second.write data.chosen edge.id 1) data.sets compressed
        (Rep.write_client rep _ _ _ separateChosen.1 separateChosen.2) a b
    have writtenFrame := (prefixFrame.weaken
      (moreSequences := [data.sets.parent, data.sets.rank, data.chosen])
      (moreObjects := []) (moreCollections := [])
      (by simp) (by simp) (by simp)).write data.chosen edge.id 1 (Or.inl (by simp))
    have wholeFrame := writtenFrame.trans (unionFrame.weaken (by simp) (by simp) (by simp))
    have decision : decide (model.representative a ≠ model.representative b) = true ↔
        ¬ Connected selected edge.source edge.target := by
      simp only [decide_eq_true_eq]
      exact not_congr (by simpa only [Algo2Lean.UnionFind.Connected, av, bv] using invariant.partition a b)
    have partition := partition_join a b av bv
      (fun u v => (samePartition u v).trans (invariant.partition u v)) joined
    have finalFlags : Flags (after.read data.chosen) (edge :: selected) := by
      rw [unionFrame.read data.chosen chosenAllocated invariant.chosenProtected]
      simpa [selectHeap] using Flags.select (heap := second) (chosen := data.chosen) (edge := edge) flags true
    refine ⟨after, nextModel, true, ?_, ?_, ?_, wholeFrame, ?_, ?_, ?_⟩
    · simpa [distinct] using decision
    · refine ⟨first, second, ((model.representative a).val : Int), ((model.representative b).val : Int),
        ?_, ?_, ?_, chosenAllocated⟩
      · simpa only [av] using findA
      · simpa only [bv] using findB
      · have values : ((model.representative a).val : Int) ≠ ((model.representative b).val : Int) := by
          intro equal; apply distinct; apply Fin.ext; omega
        rw [if_pos values]
        exact ⟨_, by simpa only [av, bv] using join⟩
    · simpa only [dif_pos, if_pos, decide_eq_true distinct] using
        invariant.advance represented wholeFrame partition (decide (model.representative a ≠ model.representative b))
          decision (by simpa only [decide_eq_true distinct, if_true] using finalFlags)
    · intro clock outside
      have ns : clock ≠ "kruskal" := by simp_all
      have nu : clock ∉ ["uf_find", "uf_compress", "uf_union"] := by simp_all
      exact (unionClocks clock nu).trans (by simpa [Heap.tick, ns] using clocks clock nu)
    · have us := unionClocks "kruskal" (by simp)
      simp only [Heap.write_clocks] at unionCost us
      simp only [work]
      omega
    · have us := unionClocks "kruskal" (by simp)
      simp only [Heap.write_clocks] at unionAmortized us
      simp only [work]
      omega
  · have connected : Connected selected edge.source edge.target := by
      have eq : Algo2Lean.UnionFind.Connected model a b := by
        simpa [Algo2Lean.UnionFind.Connected] using distinct
      simpa only [av, bv] using (invariant.partition a b).mp eq
    have partition (u v : Fin n) : Algo2Lean.UnionFind.Connected compressed u v ↔
        Connected (edge :: selected) (u.val : Int) (v.val : Int) :=
      (samePartition u v).trans ((invariant.partition u v).trans (connected_redundant connected _ _).symm)
    have wholeFrame := prefixFrame.weaken
      (moreSequences := [data.sets.parent, data.sets.rank, data.chosen])
      (moreObjects := []) (moreCollections := []) (by simp) (by simp) (by simp)
    refine ⟨second, compressed, false, by simp [connected], ?_, ?_, wholeFrame, ?_, ?_, ?_⟩
    · refine ⟨first, second, ((model.representative a).val : Int), ((model.representative b).val : Int),
        ?_, ?_, ?_, chosenAllocated⟩
      · simpa only [av] using findA
      · simpa only [bv] using findB
      · have values : ((model.representative a).val : Int) = ((model.representative b).val : Int) := by
          simp_all
        simp [values]
    · simpa only [decide_eq_false distinct, Bool.false_eq_true, if_false] using
        invariant.advance rep wholeFrame partition false (by simp [connected]) flags
    · intro clock outside
      have ns : clock ≠ "kruskal" := by simp_all
      have nu : clock ∉ ["uf_find", "uf_compress", "uf_union"] := by simp_all
      simpa [Heap.tick, ns] using clocks clock nu
    · simp only [work]; omega
    · simp only [work]; omega
/-- The edge loop terminates and follows the abstract Kruskal scan. Each edge
    costs two finds and, only when accepted, a union; potentials telescope
    across every call on the same mutable disjoint-set object. -/
theorem scan_contract {n : Nat} (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index count : Int) (pending selected : List Edge)
    (invariant : ScanInvariant n data heap model index pending selected)
    (length : index + (pending.length : Int) = count) :
    ∃ final nextModel result,
      ScanCall data heap index count final ∧
      ScanInvariant n data final nextModel count [] result ∧
      Scan pending selected result ∧
      heap.Footprint final [data.sets.parent, data.sets.rank, data.chosen] [] [] ∧
      (∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
        final.clocks clock = heap.clocks clock) ∧
      work final.clocks ≤ work heap.clocks + pending.length * (8 * n.log2 + 6) ∧
      work final.clocks + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          pending.length * (10 * Algo2Lean.Ackermann.alpha n + 14) := by
  classical
  induction pending generalizing heap model index selected with
  | nil =>
    have finish : index = count := by simpa using length
    subst index
    exact ⟨heap, model, selected, scan_done data heap count count invariant.chosenAllocated (by omega),
      invariant, .done selected, Heap.Footprint.refl _ _ _ _, by intros; rfl, by simp, by simp⟩
  | cons edge pending ih =>
    obtain ⟨after, nextModel, accepted, decision, operations, nextInvariant, frame, clocks, cost, amortized⟩ :=
      edge_contract data heap model index edge pending selected invariant
    have shorter : index + 1 + (pending.length : Int) = count := by
      simp only [List.length_cons] at length
      omega
    obtain ⟨final, finalModel, result, rest, finalInvariant, scan, suffixFrame, suffixClocks, suffixCost, suffixAmortized⟩ :=
      ih after nextModel (index + 1) (if accepted then edge :: selected else selected) nextInvariant shorter
    have edgeId : heap.read data.order index = (edge.id : Int) := by
      cases invariant.ordered with
      | cons head _ => exact head
    have sourceRead : heap.read data.sources (heap.read data.order index) = edge.source := by
      rw [edgeId]
      exact invariant.sources edge (by simp)
    have targetRead : heap.read data.targets (heap.read data.order index) = edge.target := by
      rw [edgeId]
      exact invariant.targets edge (by simp)
    refine ⟨final, finalModel, result, ?_, finalInvariant, ?_, frame.trans suffixFrame, ?_, ?_, ?_⟩
    · apply scan_continue data heap after final index count invariant.sourceAllocated
        invariant.targetAllocated invariant.orderAllocated (by simp only [List.length_cons] at length; omega)
      · rw [sourceRead, targetRead, edgeId]
        exact operations
      · exact rest
    · cases hacc : accepted with
      | false =>
        have connected : Connected selected edge.source edge.target := by simpa [hacc] using decision
        exact Scan.reject connected (by simpa [hacc] using scan)
      | true =>
        exact Scan.accept (decision.mp hacc) (by simpa [hacc] using scan)
    · intro clock outside
      exact (suffixClocks clock outside).trans (clocks clock outside)
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The same actual loop also satisfies the per-operation logarithmic bound. -/
theorem scan_verified {n : Nat} (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index count : Int) (pending selected : List Edge)
    (invariant : ScanInvariant n data heap model index pending selected)
    (length : index + (pending.length : Int) = count) :
    ∃ final nextModel result,
      ScanCall data heap index count final ∧
      ScanInvariant n data final nextModel count [] result ∧
      Scan pending selected result ∧
      heap.Footprint final [data.sets.parent, data.sets.rank, data.chosen] [] [] ∧
      (∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
        final.clocks clock = heap.clocks clock) ∧
      work final.clocks ≤ work heap.clocks + pending.length * (8 * n.log2 + 6) := by
  obtain ⟨final, nextModel, result, execution, finalInvariant, scan, frame, clocks, bound, _⟩ :=
    scan_contract data heap model index count pending selected invariant length
  exact ⟨final, nextModel, result, execution, finalInvariant, scan, frame, clocks, bound⟩

/-- The source entry point allocates the empty result, constructs singleton
    components, sorts the edges, and enters the explicitly named edge loop. -/
theorem kruskal_calls (heap initialized sorted final : Heap)
    (size count : Int) (sources targets weights order : SeqRef) (sets : UnionFindAnalysis.Layout)
    (valid : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (construction : Algo.union_find.UnionFind.Call (heap.allocate (fun _ => 0)) size initialized sets.object)
    (sorting : Algo.sort_indices.sort_indices.Call initialized (weights, count) sorted order)
    (scan : ScanCall ⟨sets, sources, targets, order, heap.nextRef⟩ (sorted.tick "kruskal") 0 count final) :
    kruskal.Call heap (size, sources, targets, weights, count) final heap.nextRef := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.kruskal_pc39 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc38 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc37 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc36 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc35 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller construction.2).trans
  apply Reaches.prepend (Step.kruskal_pc34 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc33 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc32 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc31 _ _ _)
  apply (ModuleCall.summary import_2_simulates _ caller sorting.2).trans
  apply Reaches.prepend (Step.kruskal_pc30 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc29 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc28 _ _ _)
  refine scan (.active _ (.fn_kruskal 4 _) []) ?_ rfl caller
  exact ⟨True.intro, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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

/-- A disjoint-set representation survives a call that preserves existing
    storage. This is the only fact about sorting needed by the union-find model. -/
theorem Rep.preserve {n : Nat} {before after : Heap} {layout : UnionFindAnalysis.Layout}
    {model : Algo2Lean.UnionFind.State n} (rep : Rep before layout model)
    (frame : before.Footprint after [] [] []) : Rep after layout model := by
  open Algo.union_find.Algo2LeanGenerated in
    have object : is_UnionFind after layout.object :=
      ⟨Nat.lt_of_lt_of_le rep.object.1 frame.nextObject,
        (frame.classes layout.object rep.object.1).trans rep.object.2⟩
    refine ⟨rep.valid, object, ?_, ?_, ?_,
      Nat.lt_of_lt_of_le rep.parentAllocated frame.nextRef,
      Nat.lt_of_lt_of_le rep.rankAllocated frame.nextRef, rep.separate, ?_, ?_⟩
    · simpa only [field_UnionFind_parent, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readParent
    · simpa only [field_UnionFind_rank, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readRank
    · simpa only [field_UnionFind_size, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readSize
    · intro vertex
      rw [frame.read layout.parent rep.parentAllocated (by simp)]
      exact rep.parents vertex
    · intro vertex
      rw [frame.read layout.rank rep.rankAllocated (by simp)]
      exact rep.ranks vertex

/-- The empty edge set is allocated before initializing singleton components. -/
def initialHeap (heap : Heap) (size : Nat) : Heap :=
  newHeap (heap.allocate (fun _ => 0)) size

/-- The result and disjoint-set arrays precede the freshly sorted edge order. -/
def initialLayout (heap : Heap) (_size : Nat) (sources targets order : SeqRef) : ScanLayout :=
  ⟨newLayout (heap.allocate (fun _ => 0)), sources, targets, order, heap.nextRef⟩

/-- Initialization preserves every caller location while creating private data. -/
theorem initial_footprint (heap : Heap) (size : Nat) :
    heap.Footprint (initialHeap heap size) [] [] [] :=
  ((Heap.Footprint.refl heap [] [] []).allocate (fun _ => 0)).trans
    (constructor_footprint (heap.allocate (fun _ => 0)) size)

/-- Initialization preserves all previously allocated sequence values. -/
theorem initial_read_old (heap : Heap) (size : Nat) (ref : SeqRef) (old : ref < heap.nextRef) :
    (initialHeap heap size).read ref = heap.read ref :=
  (initial_footprint heap size).read ref old (by simp)

/-- Sorting protects the initialized components and empty result flags. -/
theorem initial_invariant (heap sorted : Heap) (size : Nat) (sources targets order : SeqRef)
    (pending : List Edge)
    (sourceAllocated : sources < heap.nextRef) (targetAllocated : targets < heap.nextRef)
    (frame : (initialHeap heap size).Footprint sorted [] [] [])
    (fresh : (initialHeap heap size).nextRef ≤ order) (orderAllocated : order < sorted.nextRef)
    (bounds : ValidInput size pending)
    (sourceValues : ∀ edge ∈ pending, heap.read sources edge.id = edge.source)
    (targetValues : ∀ edge ∈ pending, heap.read targets edge.id = edge.target)
    (ordering : ∀ (i : Nat) (within : i < pending.length), sorted.read order i = (pending[i].id : Int)) :
    ScanInvariant size (initialLayout heap size sources targets order) (sorted.tick "kruskal")
      (Algo2Lean.UnionFind.initial size) 0 pending [] := by
  have refs : (initialHeap heap size).nextRef = heap.nextRef + 3 := by
    simpa [initialHeap, Heap.allocate] using (constructor_allocations (heap.allocate (fun _ => 0)) size).1
  have initFrame := initial_footprint heap size
  have whole := initFrame.trans frame
  have chosenInit : heap.nextRef < (initialHeap heap size).nextRef := by rw [refs]; omega
  have chosenValues : (initialHeap heap size).read heap.nextRef = (fun _ => 0) := by
    have preserve := (constructor_frame (heap.allocate (fun _ => 0)) size).2.1 heap.nextRef (by simp [Heap.allocate])
    change (newHeap (heap.allocate (fun _ => 0)) size).read heap.nextRef = _
    rw [preserve]
    funext index
    exact Heap.read_allocate_new heap (fun _ => 0) index
  have represented := Rep.preserve (constructor_rep (heap.allocate (fun _ => 0)) size) frame
  refine ⟨represented.tick "kruskal", ?_,
    (fun edge member => ⟨bounds.source edge member, bounds.target edge member⟩), ?_, ?_, ?_, ?_,
    Nat.lt_of_lt_of_le sourceAllocated whole.nextRef,
    Nat.lt_of_lt_of_le targetAllocated whole.nextRef, orderAllocated,
    Nat.lt_of_lt_of_le chosenInit frame.nextRef, ?_, ?_, ?_, ?_⟩
  · intro u v
    rw [Algo2Lean.UnionFind.initial_connected, connected_nil]
    constructor
    · intro same; subst v; rfl
    · intro same; apply Fin.ext; omega
  · intro edge member
    change sorted.read sources edge.id = edge.source
    rw [whole.read sources sourceAllocated (by simp)]
    exact sourceValues edge member
  · intro edge member
    change sorted.read targets edge.id = edge.target
    rw [whole.read targets targetAllocated (by simp)]
    exact targetValues edge member
  · apply Order.of_indexed
    intro i within
    change sorted.read order (0 + i) = _
    simpa only [Int.zero_add] using ordering i within
  · intro id
    change sorted.read heap.nextRef id = _
    rw [frame.read heap.nextRef chosenInit (by simp), chosenValues]
    simp
  all_goals
    simp only [initialLayout, newLayout, Heap.allocate_nextRef, List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega

/-- Constructing all singleton components costs V+1 initialization ticks. -/
theorem initial_work (heap : Heap) (size : Nat) :
    work (initialHeap heap size).clocks = work heap.clocks + size + 1 := by
  simp [work, UnionFindAnalysis.work, initialHeap, constructor_clocks]
  omega

/-- Initialization changes only the union-find initialization clock. -/
theorem initial_clocks (heap : Heap) (size : Nat) (clock : String)
    (notInit : clock ≠ "uf_init") :
    (initialHeap heap size).clocks clock = heap.clocks clock := by
  simp [initialHeap, constructor_clocks, notInit]

end KruskalAnalysis
