import Algo.sort_indices.Analysis
import Algo2LeanLib.KruskalMath

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The graph supplied to the source program consists of three integer sequences
and a finite edge count. This module translates that representation into the
finite graph model and connects the reusable sorting theorem to Kruskal's scan.
-/

open Algo2LeanGenerated Algo2Lean.Kruskal

namespace KruskalInput

/-- Endpoints lie in the declared vertex range. Weights need no restriction;
    parallel edges, self-loops, and negative weights are valid inputs. -/
structure WellFormed (size count : Int) (sources targets : Seq) : Prop where
  size_nonnegative : 0 ≤ size
  count_nonnegative : 0 ≤ count
  source_bounds : ∀ edge, 0 ≤ edge → edge < count → 0 ≤ sources edge ∧ sources edge < size
  target_bounds : ∀ edge, 0 ≤ edge → edge < count → 0 ≤ targets edge ∧ targets edge < size

/-- Each finite input position names one edge occurrence. -/
def edgeAt (sources targets weights : Seq) (identifier : Int) : Edge :=
  ⟨identifier.toNat, sources identifier, targets identifier, weights identifier⟩

/-- The mathematical graph retains the input's original occurrence order. -/
def edges (sources targets weights : Seq) (count : Int) : List Edge :=
  (Algo2Lean.FiniteIndex.range count).map (edgeAt sources targets weights)

@[simp] theorem edges_length (sources targets weights : Seq) (count : Int) :
    (edges sources targets weights count).length = count.toNat := by
  simp [edges]

@[simp] theorem edges_ids (sources targets weights : Seq) (count : Int) :
    (edges sources targets weights count).map Edge.id = List.range count.toNat := by
  simp [edges, Algo2Lean.FiniteIndex.range, List.map_map, Function.comp_def, edgeAt]

/-- Distinct positions give distinct edge identities, including parallel edges. -/
theorem edges_unique (sources targets weights : Seq) (count : Int) :
    ((edges sources targets weights count).map Edge.id).Nodup := by
  rw [edges_ids]
  exact List.nodup_range

/-- Membership connects the graph model back to the original endpoint arrays. -/
theorem edge_contents {sources targets weights : Seq} {count : Int} {edge : Edge}
    (member : edge ∈ edges sources targets weights count) :
    (edge.id : Int) < count ∧ sources edge.id = edge.source ∧
      targets edge.id = edge.target ∧ weights edge.id = edge.weight := by
  obtain ⟨identifier, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨nonnegative, within⟩ := (Algo2Lean.FiniteIndex.range_member count identifier).mp present
  simpa only [edgeAt, Int.toNat_of_nonneg nonnegative] using
    (show identifier < count ∧ sources identifier = sources identifier ∧
      targets identifier = targets identifier ∧ weights identifier = weights identifier from
      ⟨within, rfl, rfl, rfl⟩)

theorem WellFormed.valid {size count : Int} {sources targets : Seq}
    (input : WellFormed size count sources targets) (weights : Seq) :
    ValidInput size.toNat (edges sources targets weights count) := by
  refine ⟨edges_unique _ _ _ _, ?_, ?_⟩
  · intro edge member
    obtain ⟨within, source, target, weight⟩ := edge_contents member
    have bound := input.source_bounds edge.id (by omega) within
    rw [source] at bound
    exact ⟨bound.1, by omega⟩
  · intro edge member
    obtain ⟨within, source, target, weight⟩ := edge_contents member
    have bound := input.target_bounds edge.id (by omega) within
    rw [target] at bound
    exact ⟨bound.1, by omega⟩

/-- The sorted occurrence list agrees with the returned identifier sequence.
    Its fields contain only finite graph facts and sequence observations. -/
structure SortedEdges (sources targets weights order : Seq) (count : Int)
    (pending : List Edge) : Prop where
  permutation : (edges sources targets weights count).Perm pending
  sorted : Sorted pending
  length : pending.length = count.toNat
  order : ∀ (index : Nat) (within : index < pending.length),
    order index = (pending[index].id : Int)
  source : ∀ edge ∈ pending, sources edge.id = edge.source
  target : ∀ edge ∈ pending, targets edge.id = edge.target
  weight : ∀ edge ∈ pending, weights edge.id = edge.weight
  bounded : ∀ edge ∈ pending, (edge.id : Int) < count

/-- Sort the identifiers once, then obtain the sorted graph view without
    unfolding the sorting algorithm or repeating a heap proof. -/
theorem sorted_edges (sources targets weights order : Seq) (count : Int)
    (sorting : SortIndicesAnalysis.SortedPermutation weights count order) :
    ∃ pending, SortedEdges sources targets weights order count pending := by
  obtain ⟨identifiers, permutation, sorted, agreement⟩ := sorting
  let pending := identifiers.map (edgeAt sources targets weights)
  have mapped : (edges sources targets weights count).Perm pending := permutation.symm.map _
  have memberContents (edge : Edge) (member : edge ∈ pending) :=
    edge_contents (mapped.mem_iff.mpr member)
  refine ⟨pending, mapped, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sorted.map (edgeAt sources targets weights) (by intros; assumption)
  · exact mapped.length_eq.symm.trans (edges_length _ _ _ _)
  · intro index within
    have bound : index < identifiers.length := by simpa [pending] using within
    have original : identifiers[index] ∈ Algo2Lean.FiniteIndex.range count :=
      permutation.mem_iff.mp (List.getElem_mem bound)
    have nonnegative := ((Algo2Lean.FiniteIndex.range_member _ _).mp original).1
    have agrees := agreement index bound
    simpa [pending, edgeAt, getElem!_pos, bound, Int.toNat_of_nonneg nonnegative] using agrees
  · exact fun edge member => (memberContents edge member).2.1
  · exact fun edge member => (memberContents edge member).2.2.1
  · exact fun edge member => (memberContents edge member).2.2.2
  · exact fun edge member => (memberContents edge member).1

theorem SortedEdges.valid {size count : Int} {sources targets weights order : Seq} {pending : List Edge}
    (sorting : SortedEdges sources targets weights order count pending)
    (input : WellFormed size count sources targets) : ValidInput size.toNat pending := by
  constructor
  · exact (input.valid weights).identities.perm (sorting.permutation.map Edge.id)
  · intro edge member
    exact (input.valid weights).source edge (sorting.permutation.mem_iff.mpr member)
  · intro edge member
    exact (input.valid weights).target edge (sorting.permutation.mem_iff.mpr member)

/-- The scan's graph theorem applies directly to the original array input. -/
theorem SortedEdges.minimum {sources targets weights order : Seq} {count : Int}
    {pending selected : List Edge}
    (sorting : SortedEdges sources targets weights order count pending)
    (scan : Scan pending [] selected) : MinimumSpanningForest (edges sources targets weights count) selected :=
  scan.minimum_of_perm sorting.permutation sorting.sorted


/-- An occurrence identifier uniquely determines an edge of the input graph. -/
theorem edge_eq_of_id {sources targets weights : Seq} {count : Int} {first second : Edge}
    (firstMember : first ∈ edges sources targets weights count)
    (secondMember : second ∈ edges sources targets weights count)
    (same : first.id = second.id) : first = second := by
  have firstValues := edge_contents firstMember
  have secondValues := edge_contents secondMember
  cases first
  cases second
  simp_all

/-- Reading the selected flags in input order gives the same minimum forest.
    This removes the proof's reverse insertion order from the public interface. -/
theorem minimum_from_flags {sources targets weights flags : Seq} {count : Int} {selected : List Edge}
    (minimum : MinimumSpanningForest (edges sources targets weights count) selected)
    (selection : ∀ id : Int,
      flags id = (if selected.any (fun edge => (edge.id : Int) == id) then 1 else 0)) :
    MinimumSpanningForest (edges sources targets weights count)
      ((edges sources targets weights count).filter (fun edge => flags edge.id == 1)) := by
  let input := edges sources targets weights count
  let result := input.filter (fun edge => flags edge.id == 1)
  have members (edge : Edge) : edge ∈ result ↔ edge ∈ selected := by
    constructor
    · intro member
      obtain ⟨inputMember, marked⟩ := List.mem_filter.mp member
      have present : selected.any (fun chosen => (chosen.id : Int) == (edge.id : Int)) = true := by
        have flag : flags edge.id = 1 := by simpa using marked
        rw [selection] at flag
        split at flag
        · assumption
        · contradiction
      obtain ⟨chosen, chosenMember, same⟩ := List.any_eq_true.mp present
      have ids : chosen.id = edge.id := by
        have castEqual : (chosen.id : Int) = (edge.id : Int) := by simpa using same
        omega
      have equal := edge_eq_of_id (minimum.2.1.subset chosen chosenMember) inputMember ids
      simpa [equal] using chosenMember
    · intro member
      apply List.mem_filter.mpr
      refine ⟨minimum.2.1.subset edge member, ?_⟩
      have present : selected.any (fun chosen => (chosen.id : Int) == (edge.id : Int)) = true :=
        List.any_eq_true.mpr ⟨edge, member, by simp⟩
      simp [selection, present]
  have inputUnique : input.Nodup :=
    List.Pairwise.of_map Edge.id (fun a b different same => different (congrArg Edge.id same))
      (edges_unique sources targets weights count)
  have resultUnique : result.Nodup := List.filter_sublist.nodup inputUnique
  have permutation : selected.Perm result := by
    apply List.perm_iff_count.mpr
    intro edge
    rw [minimum.1.nodup.count, resultUnique.count]
    simp only [members]
  exact minimum.perm_result permutation

end KruskalInput
