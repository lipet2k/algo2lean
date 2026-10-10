import RelaxEdgeGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Analysis outline:
- `relax_summary`: Reusable edge-relaxation contract.
- `output_with_cost_iff`: Relaxation result and exact cost.
- `target_minimum`: Relaxed distance is the candidate minimum.
- `path_costs_preserved`: Distances remain costs of paths.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace RelaxEdgeAnalysis

-- The specification is ordinary mathematics over the initial distance values.
-- A negative entry means "unreached"; a reachable entry can only decrease.
def improves (dist : Seq) (u v weight : Int) : Bool :=
  decide (0 ≤ dist u ∧ 0 ≤ weight ∧ (dist v < 0 ∨ dist u + weight < dist v))

def relaxedHeap (heap : Heap) (dist : SeqRef) (u v weight : Int) : Heap :=
  let charged := heap.tick "relaxations"
  if improves (heap.read dist) u v weight then
    (charged.write dist v (heap.read dist u + weight)).tick "updates"
  else charged

def relaxationCosts (changed : Bool) : Clocks :=
  fun name => if name = "relaxations" then 1
    else if name = "updates" then (if changed then 1 else 0) else 0

-- This local fact describes the named assignment without needing a run from
-- function entry, a caller, or an entire transcript.
theorem assignment_sets_candidate {before after : Configuration}
    (transition : Step before after) (location : relax.At.improve before)
    (dist : SeqRef) (v candidate : Int)
    (readDist : relax.Local.dist before = some dist)
    (readVertex : relax.Local.v before = some v)
    (readCandidate : relax.Local.candidate before = some candidate) :
    after.heap.read dist v = candidate := by
  cases transition <;>
    simp_all [relax.At.improve, relax.Local.dist, relax.Local.v,
      relax.Local.candidate, Config.heap]

-- Three readable cases outline the proof of the function: reject the source
-- or weight, keep an already better distance, or install the new candidate.
theorem ineligible_summary (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (valid : dist < heap.nextRef)
    (ineligible : ¬ (0 ≤ heap.read dist u ∧ 0 ≤ weight)) :
    relax.Call heap (dist, u, v, weight) (heap.tick "relaxations") false := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.relax_pc12 _ _ _)
  apply Reaches.prepend (Step.relax_pc11 _ _ _ (by simpa using valid))
  apply Reaches.prepend (Step.relax_pc10_false _ _ _ (by simpa using ineligible))
  apply Reaches.prepend (Step.relax_pc2 _ _ _)
  exact Reaches.single (Step.relax_pc1 _ _ _)

theorem unchanged_summary (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (valid : dist < heap.nextRef)
    (reachable : 0 ≤ heap.read dist u) (nonnegative : 0 ≤ weight)
    (settled : 0 ≤ heap.read dist v ∧ heap.read dist v ≤ heap.read dist u + weight) :
    relax.Call heap (dist, u, v, weight) (heap.tick "relaxations") false := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.relax_pc12 _ _ _)
  apply Reaches.prepend (Step.relax_pc11 _ _ _ (by simpa using valid))
  apply Reaches.prepend (Step.relax_pc10_true _ _ _ (by simp [reachable, nonnegative]))
  apply Reaches.prepend (Step.relax_pc9 _ _ _ (by simpa using valid))
  apply Reaches.prepend (Step.relax_pc8 _ _ _ (by simp [valid]))
  apply Reaches.prepend (Step.relax_pc7_false _ _ _ (by simp; omega))
  apply Reaches.prepend (Step.relax_pc2 _ _ _)
  exact Reaches.single (Step.relax_pc1 _ _ _)

theorem improved_summary (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (valid : dist < heap.nextRef)
    (reachable : 0 ≤ heap.read dist u) (nonnegative : 0 ≤ weight)
    (better : heap.read dist v < 0 ∨ heap.read dist u + weight < heap.read dist v) :
    relax.Call heap (dist, u, v, weight)
      (((heap.tick "relaxations").write dist v (heap.read dist u + weight)).tick "updates")
      true := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.relax_pc12 _ _ _)
  apply Reaches.prepend (Step.relax_pc11 _ _ _ (by simpa using valid))
  apply Reaches.prepend (Step.relax_pc10_true _ _ _ (by simp [reachable, nonnegative]))
  apply Reaches.prepend (Step.relax_pc9 _ _ _ (by simpa using valid))
  apply Reaches.prepend (Step.relax_pc8 _ _ _ (by simp [valid]))
  apply Reaches.prepend (Step.relax_pc7_true _ _ _ (by simpa using better))
  apply Reaches.prepend (Step.relax_pc6 _ _ _ (by simpa using valid))
  apply Reaches.prepend (Step.relax_pc5 _ _ _)
  apply Reaches.prepend (Step.relax_pc4 _ _ _)
  exact Reaches.single (Step.relax_pc3 _ _ _)

-- The relaxation contract specifies the whole heap effect and applies under
-- any caller's suspended stack, allowing direct reuse in graph algorithms.
theorem relax_summary (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (valid : dist < heap.nextRef) :
    relax.Call heap (dist, u, v, weight) (relaxedHeap heap dist u v weight)
      (improves (heap.read dist) u v weight) := by
  by_cases eligible : 0 ≤ heap.read dist u ∧ 0 ≤ weight
  · by_cases better : heap.read dist v < 0 ∨ heap.read dist u + weight < heap.read dist v
    · simpa [relaxedHeap, improves, eligible.1, eligible.2, better] using
        improved_summary heap dist u v weight valid eligible.1 eligible.2 better
    · have settled : 0 ≤ heap.read dist v ∧ heap.read dist v ≤ heap.read dist u + weight := by omega
      simpa [relaxedHeap, improves, eligible.1, eligible.2, better] using
        unchanged_summary heap dist u v weight valid eligible.1 eligible.2 settled
  · have impossible : ¬ (0 ≤ heap.read dist u ∧ 0 ≤ weight ∧
        (heap.read dist v < 0 ∨ heap.read dist u + weight < heap.read dist v)) := by
      intro h
      exact eligible ⟨h.1, h.2.1⟩
    simpa [relaxedHeap, improves, impossible] using
      ineligible_summary heap dist u v weight valid eligible

theorem exact_costs (heap : Heap) (dist : SeqRef) (u v weight : Int) :
    Heap.cost heap (relaxedHeap heap dist u v weight) =
      relaxationCosts (improves (heap.read dist) u v weight) := by
  funext name
  by_cases relaxation : name = "relaxations"
  · subst name
    simp [relaxedHeap, relaxationCosts, Heap.cost, Heap.tick, Heap.write]
    split <;> simp_all
  by_cases update : name = "updates"
  · subst name
    simp [relaxedHeap, relaxationCosts, Heap.cost, Heap.tick, Heap.write]
    split <;> simp_all
  simp only [relaxedHeap]
  split <;> simp_all [relaxationCosts, Heap.cost, Heap.tick, Heap.write]

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

-- The specification describes every completed execution, not only the one
-- explicitly constructed in the summary proof.
theorem execution_correct (heap finalHeap : Heap) (dist : SeqRef) (u v weight : Int)
    (changed : Bool) (execution : relax.Run heap (dist, u, v, weight) finalHeap changed) :
    finalHeap = relaxedHeap heap dist u v weight ∧
      changed = improves (heap.read dist) u v weight := by
  have correctRun := (relax_summary heap dist u v weight execution.1).2.root
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic
    execution.2 correctRun
    (by intro next impossible; cases impossible)
    (by intro next impossible; cases impossible)
  cases same
  exact ⟨rfl, rfl⟩

theorem execution_iff (heap finalHeap : Heap) (dist : SeqRef) (u v weight : Int)
    (changed : Bool) :
    relax.Run heap (dist, u, v, weight) finalHeap changed ↔
      dist < heap.nextRef ∧ finalHeap = relaxedHeap heap dist u v weight ∧
        changed = improves (heap.read dist) u v weight := by
  constructor
  · intro execution
    exact ⟨execution.1, execution_correct heap finalHeap dist u v weight changed execution⟩
  · rintro ⟨valid, rfl, rfl⟩
    have summary := relax_summary heap dist u v weight valid
    exact ⟨summary.1, summary.2.root⟩

theorem output_with_cost (dist : Seq) (u v weight : Int) :
    relax.ReturnsWithCost (dist, u, v, weight) (improves dist u v weight)
      (relaxationCosts (improves dist u v weight)) := by
  have summary := relax_summary (({} : Heap).allocate dist) 0 u v weight (by simp [Heap.allocate])
  have costs := exact_costs (({} : Heap).allocate dist) 0 u v weight
  refine ⟨relaxedHeap (({} : Heap).allocate dist) 0 u v weight, ⟨summary.1, ?_⟩, ?_⟩
  · simpa [Heap.read, Heap.allocate] using! summary.2.root
  · simpa [Heap.read, Heap.allocate] using! costs

-- Main result: Correctness and running time
theorem output_with_cost_iff (dist : Seq) (u v weight : Int) (changed : Bool) (costs : Clocks) :
    relax.ReturnsWithCost (dist, u, v, weight) changed costs ↔
      changed = improves dist u v weight ∧ costs = relaxationCosts changed := by
  constructor
  · rintro ⟨finalHeap, execution, cost⟩
    obtain ⟨heapEffect, resultEffect⟩ := execution_correct
      (({} : Heap).allocate dist) finalHeap 0 u v weight changed execution
    have resultEffect' : changed = improves dist u v weight := by
      simpa [Heap.read, Heap.allocate] using! resultEffect
    refine ⟨resultEffect', ?_⟩
    rw [heapEffect] at cost
    have expected := cost.symm.trans (exact_costs (({} : Heap).allocate dist) 0 u v weight)
    simpa [Heap.read, Heap.allocate, resultEffect'] using! expected
  · rintro ⟨rfl, rfl⟩
    exact output_with_cost dist u v weight

-- These mathematical observations isolate the facts needed by graph proofs.
-- They do not mention program counters, frames, or the transcript structure.
theorem target_distance (heap : Heap) (dist : SeqRef) (u v weight : Int) :
    (relaxedHeap heap dist u v weight).read dist v =
      if improves (heap.read dist) u v weight then heap.read dist u + weight
      else heap.read dist v := by
  simp only [relaxedHeap]
  split <;> simp_all

theorem other_vertex (heap : Heap) (dist : SeqRef) (u v weight index : Int)
    (different : index ≠ v) :
    (relaxedHeap heap dist u v weight).read dist index = heap.read dist index := by
  simp only [relaxedHeap]
  split <;> simp_all [Heap.read_write_other_index]

theorem other_sequence (heap : Heap) (dist other : SeqRef) (u v weight index : Int)
    (different : other ≠ dist) :
    (relaxedHeap heap dist u v weight).read other index = heap.read other index := by
  simp only [relaxedHeap]
  split <;> simp_all [Heap.read_write_other_ref]

-- Even when u = v, a nonnegative self-edge never improves its source.
theorem self_edge_unchanged (heap : Heap) (dist : SeqRef) (u weight : Int) :
    relaxedHeap heap dist u u weight = heap.tick "relaxations" := by
  have noImprovement : improves (heap.read dist) u u weight = false := by
    simp [improves]
    omega
  simp [relaxedHeap, noImprovement]

theorem source_distance (heap : Heap) (dist : SeqRef) (u v weight : Int) :
    (relaxedHeap heap dist u v weight).read dist u = heap.read dist u := by
  by_cases self : u = v
  · subst v
    rw [self_edge_unchanged]
    simp
  · exact other_vertex heap dist u v weight u self

-- With a reached source and a nonnegative edge, relaxation is precisely
-- minimum selection, with the negative sentinel interpreted as infinity.
theorem target_minimum (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (reachable : 0 ≤ heap.read dist u) (nonnegative : 0 ≤ weight) :
    (relaxedHeap heap dist u v weight).read dist v =
      if heap.read dist v < 0 then heap.read dist u + weight
      else min (heap.read dist v) (heap.read dist u + weight) := by
  rw [target_distance]
  simp only [improves, reachable, nonnegative, true_and, decide_eq_true_eq]
  by_cases unreached : heap.read dist v < 0
  · simp [unreached]
  · simp only [unreached, false_or, ite_false]
    split
    · rename_i better
      exact (Int.min_eq_right (by omega)).symm
    · rename_i better
      exact (Int.min_eq_left (by omega)).symm

theorem reachable_distance_does_not_increase (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (reached : 0 ≤ heap.read dist v) :
    (relaxedHeap heap dist u v weight).read dist v ≤ heap.read dist v := by
  rw [target_distance]
  split
  · rename_i improved
    simp only [improves] at improved
    have facts : 0 ≤ heap.read dist u ∧ 0 ≤ weight ∧
        (heap.read dist v < 0 ∨ heap.read dist u + weight < heap.read dist v) := by
      simpa only [decide_eq_true_eq] using improved
    omega
  · exact Int.le_refl _

-- After a usable edge has been considered, its target is reached with a
-- distance no larger than the path obtained by extending the source path.
theorem edge_bound (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (reachable : 0 ≤ heap.read dist u) (nonnegative : 0 ≤ weight) :
    0 ≤ (relaxedHeap heap dist u v weight).read dist v ∧
      (relaxedHeap heap dist u v weight).read dist v ≤ heap.read dist u + weight := by
  rw [target_distance]
  split
  · omega
  · rename_i unchanged
    simp [improves, reachable, nonnegative] at unchanged
    omega

-- Starting from the conventional -1 sentinel preserves the convention.
theorem valid_distances_preserved (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (validDistances : ∀ index, heap.read dist index = -1 ∨ 0 ≤ heap.read dist index) :
    ∀ index, (relaxedHeap heap dist u v weight).read dist index = -1 ∨
      0 ≤ (relaxedHeap heap dist u v weight).read dist index := by
  intro index
  by_cases target : index = v
  · subst index
    rw [target_distance]
    split
    · rename_i improved
      have facts : 0 ≤ heap.read dist u ∧ 0 ≤ weight ∧
          (heap.read dist v < 0 ∨ heap.read dist u + weight < heap.read dist v) := by
        simpa [improves] using improved
      right
      omega
    · exact validDistances v
  · rw [other_vertex heap dist u v weight index target]
    exact validDistances index

-- A graph proof can instantiate pathCost with "there is a source-to-vertex
-- path of this length". Only this edge's path-extension fact is needed here.
theorem path_costs_preserved (heap : Heap) (dist : SeqRef) (u v weight : Int)
    (pathCost : Int → Int → Prop)
    (knownPaths : ∀ index, 0 ≤ heap.read dist index → pathCost index (heap.read dist index))
    (extendPath : ∀ length, pathCost u length → pathCost v (length + weight)) :
    ∀ index, 0 ≤ (relaxedHeap heap dist u v weight).read dist index →
      pathCost index ((relaxedHeap heap dist u v weight).read dist index) := by
  intro index
  by_cases target : index = v
  · subst index
    rw [target_distance]
    split
    · rename_i improved
      have facts : 0 ≤ heap.read dist u ∧ 0 ≤ weight ∧
          (heap.read dist v < 0 ∨ heap.read dist u + weight < heap.read dist v) := by
        simpa [improves] using improved
      intro _
      exact extendPath _ (knownPaths u facts.1)
    · exact knownPaths v
  · rw [other_vertex heap dist u v weight index target]
    exact knownPaths index

end RelaxEdgeAnalysis
