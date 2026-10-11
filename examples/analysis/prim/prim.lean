import Algo.prim.scan.Analysis
import Algo.prim.invariant.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Prim's algorithm with an abstract mutable priority queue. The proof connects
local source transitions, the cut-property invariant, and amortized operation
contracts. The Fibonacci instantiation reuses this analysis unchanged. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo2Lean.Prim
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl

/-- Predecessors describe a minimum spanning tree on the declared vertex range. -/
abbrev MinimumSpanningParents (size : Int) (adjacency : Adjacency) (root : Int) (parent : Seq) : Prop :=
  SpanningParents size.toNat (inputEdges size adjacency) root parent

variable {dependencies : Dependencies} {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)

structure LoopInvariant (state : QueueState model) (remaining : List Int) : Prop where
  storage : Storage model state
  matching : QueueMatches model state
  rootRange : 0 ≤ client.root ∧ client.root < client.size
  unique : remaining.Nodup
  members : ∀ vertex, vertex ∈ remaining ↔
    0 ≤ vertex ∧ vertex < client.size ∧ state.heap.read client.selected vertex = 0
  mathematical : ∃ chosen, Algo2Lean.Prim.Invariant (inputEdges client.size client.adjacency) client.root
    (fun vertex => state.heap.read client.selected vertex ≠ 0)
    (state.heap.read client.key) (state.heap.read client.parent) chosen

/-- A successful extraction consumes one remaining vertex and exactly its list. -/
structure Iteration (before after : QueueState model) (remaining : List Int) (vertex : Int) : Prop where
  member : vertex ∈ remaining
  invariant : LoopInvariant model after (remaining.erase vertex)
  costs : CostBounds model before after 1 (client.adjacency vertex).length
  execution : ∀ finalHeap,
    ExtractLoop dependencies after.heap client.graph client.queue client.key client.parent client.selected finalHeap →
    ExtractLoop dependencies before.heap client.graph client.queue client.key client.parent client.selected finalHeap

variable (contracts : Contracts model reservedClocks)
include contracts

/-- One queue extraction is followed by one verified adjacency scan. -/
theorem extraction_step (capacity : client.size ≤ model.capacity)
    (symmetric : PrimGraph.Symmetric client.size client.adjacency)
    (state : QueueState model) (remaining : List Int) (invariant : LoopInvariant model state remaining)
    (nonempty : state.entries model ≠ []) :
    ∃ after vertex, Iteration model state after remaining vertex := by
  have emptySummary := contracts.is_empty (state.heap.tick "queue_empty_checks") state.queueState
    (model.tick invariant.storage.queue "queue_empty_checks" 1)
  let prepared := (state.tick model "queue_empty_checks").tick model "queue_pops"
  have preparedStorage : Storage model prepared :=
    (invariant.storage.tick model "queue_empty_checks").tick model "queue_pops"
  obtain ⟨popped,vertex,key,extracted⟩ := queue_extract model contracts prepared preparedStorage nonempty
  have selected := (invariant.matching vertex key).mp extracted.member
  obtain ⟨lower,upper⟩ := model.bounded invariant.storage.queue vertex key extracted.member
  have inSize : vertex < client.size := by
    obtain ⟨chosen,math⟩ := invariant.mathematical
    rcases selected.2.1 with root | known
    · simpa [root] using invariant.rootRange.2
    · obtain ⟨edge,⟨inInput,_⟩,_,target,_⟩ := math.keys.witness vertex (by simpa using selected.1) known
      have bound := invariant.storage.graph.validInput.target edge inInput
      rw [target] at bound
      have nonnegative := invariant.storage.graph.sizeNonnegative
      omega
  have member : vertex ∈ remaining := (invariant.members vertex).mpr ⟨lower,inSize,selected.1⟩
  let marked := (popped.write model client.selected vertex 1).tick model "settlements"
  have stored : Storage model marked :=
    (extracted.storage.write model _ vertex 1 (by simp [Client.protection])).tick model "settlements"
  have keySame : marked.heap.read client.key = state.heap.read client.key := by
    change (popped.heap.write client.selected vertex 1).read client.key = _
    rw [show (popped.heap.write client.selected vertex 1).read client.key = popped.heap.read client.key by
      funext v
      exact Heap.read_write_other_ref _ _ _ _ _ _ invariant.storage.separate]
    exact extracted.key
  have parentSame : marked.heap.read client.parent = state.heap.read client.parent := by
    change (popped.heap.write client.selected vertex 1).read client.parent = _
    rw [show (popped.heap.write client.selected vertex 1).read client.parent = popped.heap.read client.parent by
      funext v
      exact Heap.read_write_other_ref _ _ _ _ _ _ invariant.storage.parentSelected]
    exact extracted.parent
  have selectedValues (v : Int) : marked.heap.read client.selected v =
      if v = vertex then 1 else state.heap.read client.selected v := by
    change (popped.heap.write client.selected vertex 1).read client.selected v = _
    simpa [Heap.read,Heap.write] using!
      congrArg (fun value => if v = vertex then 1 else value) (congrFun extracted.selected v)
  have matching : QueueMatches model marked := by
    intro v k
    change (v,k) ∈ popped.entries model ↔ _
    rw [extracted.contents]
    change v ≠ vertex ∧ (v,k) ∈ state.entries model ↔ _
    rw [invariant.matching,keySame,parentSame,selectedValues]
    by_cases same : v = vertex <;> simp [same]
  have selectedPredicate : (fun v => marked.heap.read client.selected v ≠ 0) =
      (fun v => state.heap.read client.selected v ≠ 0 ∨ v = vertex) := by
    funext v
    rw [selectedValues]
    apply propext
    by_cases same : v = vertex <;> simp [same]
  obtain ⟨chosen,mathematical⟩ := invariant.mathematical
  have rootNow : marked.heap.read client.selected client.root ≠ 0 := by
    change (fun v => marked.heap.read client.selected v ≠ 0) client.root
    rw [selectedPredicate]
    exact mathematical.root_after_selection vertex selected.2.1
  obtain ⟨head,readHead,chain⟩ := stored.graph.chains vertex lower inSize
  obtain ⟨after,scanned⟩ := scan_adjacency model contracts capacity marked vertex head
    (client.adjacency vertex) stored matching lower rootNow chain
  have scan := scanned.scan
  rw [keySame,parentSame,selectedPredicate] at scan
  have least : ∀ other, ¬ state.heap.read client.selected other ≠ 0 →
      0 ≤ state.heap.read client.parent other → state.heap.read client.key vertex ≤ state.heap.read client.key other := by
    intro other outside known
    have entry := (invariant.matching other (state.heap.read client.key other)).mpr
      ⟨by simpa using outside,Or.inr known,rfl⟩
    simpa [selected.2.2] using extracted.least other _ entry
  obtain ⟨nextChosen,nextMath⟩ := mathematical.iteration
    (invariant.storage.graph.inputEdges_reverse symmetric) vertex (by simpa using selected.1)
    lower selected.2.1 least (client.adjacency vertex) scan
    (by
      intro pair present
      obtain ⟨id,member⟩ := (inputEdges_member client.size client.adjacency vertex pair.1 pair.2).mpr ⟨lower,inSize,present⟩
      exact ⟨⟨id,vertex,pair.1,pair.2⟩,member,rfl,rfl,rfl⟩)
    (by
      intro edge member same
      have observation := inputEdges_observation member
      simpa [same] using observation.2.2)
  have next : LoopInvariant model after (remaining.erase vertex) := by
    refine ⟨scanned.storage,scanned.matching,invariant.rootRange,invariant.unique.erase vertex,?_,nextChosen,?_⟩
    · intro v
      rw [invariant.unique.mem_erase_iff,invariant.members,scanned.selected,selectedValues]
      by_cases same : v = vertex <;> simp [same]
    · apply nextMath.congr_visited
      intro v
      rw [scanned.selected]
      exact (Iff.of_eq (congrFun selectedPredicate v)).symm
  refine ⟨after,vertex,member,next,?_,?_⟩
  · simpa using (extracted_selected_cost model contracts extracted).trans model scanned.costs
  · intro finalHeap continuation
    exact extract_next dependencies state.heap popped.heap after.heap finalHeap
      client.graph client.queue client.key client.parent client.selected vertex client.heads head
      (by simpa only [List.isEmpty_eq_false_iff.mpr nonempty] using emptySummary)
      extracted.execution extracted.storage.selectedAllocated stored.graph.readHeads readHead
      scanned.execution continuation

/-- A finished loop retains the mathematical invariant and accumulated cost. -/
structure Completed (before after : QueueState model) (remaining : List Int) : Prop where
  invariant : ∃ pending, LoopInvariant model after pending
  empty : after.entries model = []
  costs : CostBounds model before after remaining.length (edgeBudget client.adjacency remaining)
  execution : ExtractLoop dependencies before.heap client.graph client.queue client.key client.parent client.selected
    (after.heap.tick "queue_empty_checks")

theorem extraction_loop (capacity : client.size ≤ model.capacity)
    (symmetric : PrimGraph.Symmetric client.size client.adjacency)
    (state : QueueState model) (remaining : List Int) (invariant : LoopInvariant model state remaining) :
    ∃ after, Completed model state after remaining := by
  suffices all : ∀ count state remaining, remaining.length = count → LoopInvariant model state remaining →
      ∃ after, Completed model state after remaining by
    exact all remaining.length state remaining rfl invariant
  intro count
  induction count using Nat.strongRecOn with
  | ind count ih =>
    intro state remaining length invariant
    by_cases empty : state.entries model = []
    · have emptySummary := contracts.is_empty (state.heap.tick "queue_empty_checks") state.queueState
        (model.tick invariant.storage.queue "queue_empty_checks" 1)
      refine ⟨state,⟨remaining,invariant⟩,empty,(CostBounds.refl model state).weaken model (Nat.zero_le _) (Nat.zero_le _),?_⟩
      exact extract_empty dependencies state.heap client.graph client.queue client.key client.parent client.selected
        invariant.storage.parentAllocated (by simpa only [empty,List.isEmpty_nil] using emptySummary)
    · obtain ⟨after,vertex,iteration⟩ := extraction_step model contracts capacity symmetric state remaining invariant empty
      have decreases := remaining_length remaining vertex iteration.member
      have smaller : (remaining.erase vertex).length < count := by omega
      obtain ⟨final,completed⟩ := ih (remaining.erase vertex).length smaller after (remaining.erase vertex) rfl iteration.invariant
      have vertices : 1 + (remaining.erase vertex).length = remaining.length := by omega
      have edges : (client.adjacency vertex).length + edgeBudget client.adjacency (remaining.erase vertex) =
          edgeBudget client.adjacency remaining := by
        have accounting := edgeBudget_erase client.adjacency remaining vertex iteration.member
        omega
      refine ⟨final,completed.invariant,completed.empty,?_,iteration.execution _ completed.execution⟩
      simpa only [vertices,edges] using iteration.costs.trans model completed.costs

/-- Counts of actual source ticks, measured relative to arbitrary initial clocks. -/
structure OperationCounts (before after : Heap) (vertices edges : Nat) : Prop where
  updates : Heap.cost before after "queue_updates" ≤ edges + 1
  pops : Heap.cost before after "queue_pops" ≤ vertices
  checks : Heap.cost before after "queue_empty_checks" ≤ vertices + 1
  visits : Heap.cost before after "edges" ≤ edges
  improvements : Heap.cost before after "improvements" ≤ edges
  settlements : Heap.cost before after "settlements" ≤ vertices

/-- The reusable generic contract proves termination, minimum spanning-tree
correctness, caller preservation, and cost increments from the same execution. -/
theorem prim_complete (capacity : client.size ≤ model.capacity)
    (before : QueueState model) (storage : Storage model before)
    (empty : before.entries model = [])
    (keys : before.heap.read client.key = fun _ => 0)
    (parents : before.heap.read client.parent = fun _ => -1)
    (flags : before.heap.read client.selected = fun _ => 0)
    (rootLower : 0 ≤ client.root) (rootUpper : client.root < client.size)
    (symmetric : PrimGraph.Symmetric client.size client.adjacency)
    (connected : Algo2Lean.Kruskal.ConnectedOn client.size.toNat (inputEdges client.size client.adjacency)) :
    ∃ after,
      prim.Call dependencies before.heap
        (client.graph,client.root,client.queue,client.key,client.parent,client.selected) after client.parent ∧
      GraphRep after client.graph client.size client.heads client.adjacency ∧
      MinimumSpanningParents client.size client.adjacency client.root (after.read client.parent) ∧
      OperationCounts before.heap after client.size.toNat (edgeBudget client.adjacency (vertexRange client.size)) ∧
      work model before.heap after ≤ before.potential model +
        model.updateBudget * (edgeBudget client.adjacency (vertexRange client.size) + 1) +
        model.popBudget * client.size.toNat ∧ client.parent < after.nextRef ∧
      client.caller.Footprint after [] [] [] := by
  let prepared := (before.write model client.key client.root 0).tick model "queue_updates"
  have preparedStorage : Storage model prepared :=
    (storage.write model _ client.root 0 (by simp [Client.protection])).tick model "queue_updates"
  obtain ⟨initial,inserted⟩ := queue_update model contracts prepared client.root 0 preparedStorage rootLower
    (by omega) (by intro key member; change (client.root,key) ∈ before.entries model at member; simp [empty] at member)
  have initialKeys : initial.heap.read client.key = fun _ => 0 := by
    rw [inserted.key]
    funext vertex
    change (before.heap.write client.key client.root 0).read client.key vertex = 0
    simpa [Heap.read,Heap.write] using
      congrArg (fun value => if vertex = client.root then 0 else value) (congrFun keys vertex)
  have initialParents : initial.heap.read client.parent = fun _ => -1 := by
    rw [inserted.parent]
    funext vertex
    change (before.heap.write client.key client.root 0).read client.parent vertex = -1
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (Ne.symm storage.keyParent)]
    exact congrFun parents vertex
  have initialFlags : initial.heap.read client.selected = fun _ => 0 := by
    rw [inserted.selected]
    funext vertex
    change (before.heap.write client.key client.root 0).read client.selected vertex = 0
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (Ne.symm storage.separate)]
    exact congrFun flags vertex
  have invariant : LoopInvariant model initial (vertexRange client.size) := by
    refine ⟨inserted.storage,?_,⟨rootLower,rootUpper⟩,vertexRange_nodup client.size,?_,[],?_⟩
    · intro vertex key
      rw [inserted.contents,initialKeys,initialParents,initialFlags]
      change (vertex = client.root ∧ key = 0) ∨ (vertex ≠ client.root ∧ (vertex,key) ∈ before.entries model) ↔ _
      simp [empty]
    · intro vertex
      rw [initialFlags]
      simp
    · rw [initialParents,initialFlags]
      simpa only [ne_self_iff_false] using
        Algo2Lean.Prim.Invariant.initial (inputEdges client.size client.adjacency) client.root (initial.heap.read client.key)
  obtain ⟨after,completed⟩ := extraction_loop model contracts capacity symmetric initial (vertexRange client.size) invariant
  obtain ⟨pending,finalInvariant⟩ := completed.invariant
  obtain ⟨chosen,math⟩ := finalInvariant.mathematical
  have rootInside : after.heap.read client.selected client.root ≠ 0 := by
    intro absent
    have entry := (finalInvariant.matching client.root (after.heap.read client.key client.root)).mpr
      ⟨absent,Or.inl rfl,rfl⟩
    simp [completed.empty] at entry
  have noKeys : ∀ vertex, ¬ after.heap.read client.selected vertex ≠ 0 → after.heap.read client.parent vertex < 0 := by
    intro vertex outside
    by_cases known : 0 ≤ after.heap.read client.parent vertex
    · have entry := (finalInvariant.matching vertex (after.heap.read client.key vertex)).mpr
        ⟨by simpa using outside,Or.inr known,rfl⟩
      simp [completed.empty] at entry
    · omega
  have correct := math.finish (storage.graph.inputEdges_reverse symmetric) storage.graph.validInput connected
    rootLower (by have sizeNonnegative := storage.graph.sizeNonnegative; omega) rootInside noKeys
  have bounds : CostBounds model initial after client.size.toNat
      (edgeBudget client.adjacency (vertexRange client.size)) := by
    simpa only [vertexRange_length] using completed.costs
  have initialClocks (name) (member : name ∈ reservedClocks) := inserted.bookkeeping name member
  refine ⟨after.heap.tick "queue_empty_checks",?_,
    finalInvariant.storage.graph.preserved (graph_frame_tick _ _ _ "queue_empty_checks" 1),correct,?_,?_,
    finalInvariant.storage.parentAllocated,
    (model.callerPreserved finalInvariant.storage.queue).tick "queue_empty_checks"⟩
  · exact initialize_summary dependencies before.heap initial.heap (after.heap.tick "queue_empty_checks")
      client.graph client.root client.queue client.key client.parent client.selected
      ⟨storage.graph.valid,model.valid storage.queue,storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated⟩
      inserted.execution completed.execution
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · have clocks := initialClocks "queue_updates" (by simp [reservedClocks])
      have count := bounds.updates
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "queue_pops" (by simp [reservedClocks])
      have count := bounds.pops
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "queue_empty_checks" (by simp [reservedClocks])
      have count := bounds.checks
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "edges" (by simp [reservedClocks])
      have count := bounds.visits
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "improvements" (by simp [reservedClocks])
      have count := bounds.improvements
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "settlements" (by simp [reservedClocks])
      have count := bounds.settlements
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
  · have initialBound := inserted.amortized
    change work model ((before.heap.write client.key client.root 0).tick "queue_updates") initial.heap + _ ≤ _ at initialBound
    rw [work_tick_left model contracts _ _ "queue_updates" (by simp [reservedClocks])] at initialBound
    change work model before.heap initial.heap + initial.potential model ≤ before.potential model + model.updateBudget at initialBound
    have finalBound := bounds.amortized
    have triangle := work_triangle model before.heap initial.heap after.heap
    rw [work_tick_right model contracts _ _ "queue_empty_checks" (by simp [reservedClocks])]
    simp only [Nat.mul_add,Nat.mul_one]
    omega

end PrimAnalysis
