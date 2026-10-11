import Algo.prim.math.Analysis

/-!
Prim's whole-loop invariant and its parent-sequence output specification.
The proof separates the first root extraction from ordinary light-edge choices,
then reuses the cut theorem and adjacency-scan lemmas at every iteration.
-/

namespace Algo2Lean.Prim

open Algo2Lean.Kruskal

/-- Parent pointers encode a minimum spanning tree rooted at the supplied root.
The root has parent `-1`; every other declared vertex has a selected incoming
edge whose source is its parent. All chosen edges belong to the input graph. -/
def SpanningParents (size : Nat) (input : List Edge) (root : Int) (parent : Int → Int) : Prop :=
  ∃ chosen, MinimumSpanningTree size input chosen ∧ parent root = -1 ∧
    (∀ edge ∈ chosen, parent edge.target = edge.source ∧ edge.target ≠ root) ∧
    (∀ vertex : Int, 0 ≤ vertex → vertex < size → vertex ≠ root →
      ∃ edge ∈ chosen, edge.target = vertex)

/-- The first iteration starts from no selected vertices. Later iterations
maintain a safe rooted tree, its boundary keys, and its parent representation. -/
structure Invariant (input : List Edge) (root : Int) (visited : Int → Prop)
    (key parent : Int → Int) (chosen : List Edge) : Prop where
  keys : Keys input visited key parent
  tree : ((∀ vertex, ¬ visited vertex) ∧ chosen = [] ∧ (∀ vertex, parent vertex = -1)) ∨
    TreeState input root visited chosen
  root_parent : parent root = -1
  parents : ∀ edge ∈ chosen, parent edge.target = edge.source ∧ edge.target ≠ root
  targets : ∀ vertex, (visited vertex ∧ vertex ≠ root) ↔ ∃ edge ∈ chosen, edge.target = vertex

theorem Invariant.initial (input : List Edge) (root : Int) (key : Int → Int) :
    Invariant input root (fun _ => False) key (fun _ => -1) [] := by
  refine ⟨Keys.initial input key, Or.inl ⟨by simp, rfl, by simp⟩, rfl, by simp, ?_⟩
  simp

/-- The root is either already selected or is the vertex selected by this first
iteration. The adjacency scan therefore always preserves the root's parent. -/
theorem Invariant.root_after_selection {input : List Edge} {root : Int} {visited : Int → Prop}
    {key parent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root visited key parent chosen) (vertex : Int)
    (root_or_known : vertex = root ∨ 0 ≤ parent vertex) : visited root ∨ root = vertex := by
  rcases invariant.tree with ⟨_, _, undiscovered⟩ | tree
  · rcases root_or_known with same | known
    · exact Or.inr same.symm
    · rw [undiscovered vertex] at known
      omega
  · exact Or.inl tree.root_visited

/-- An iteration selects one new vertex and scans its whole adjacency list.
The extracted key need only be minimum among discovered unvisited vertices. -/
theorem Invariant.iteration {input : List Edge} {root : Int} {visited : Int → Prop}
    {key parent finalKey finalParent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root visited key parent chosen) (symmetric : Symmetric input)
    (vertex : Int) (outside : ¬ visited vertex) (nonnegative : 0 ≤ vertex)
    (root_or_known : vertex = root ∨ 0 ≤ parent vertex)
    (least : ∀ other, ¬ visited other → 0 ≤ parent other → key vertex ≤ key other)
    (edges : List (Int × Int))
    (scan : KeyScan (fun value => visited value ∨ value = vertex) vertex
      edges key parent finalKey finalParent)
    (members : ∀ pair ∈ edges, ∃ edge ∈ input,
      edge.source = vertex ∧ edge.target = pair.1 ∧ edge.weight = pair.2)
    (complete : ∀ edge ∈ input, edge.source = vertex → (edge.target, edge.weight) ∈ edges) :
    ∃ nextChosen, Invariant input root (fun value => visited value ∨ value = vertex)
      finalKey finalParent nextChosen := by
  have keys := scan.keys_after_selection invariant.keys nonnegative members complete
  rcases invariant.tree with ⟨empty, chosenEmpty, undiscovered⟩ | tree
  · have isRoot : vertex = root := by
      rcases root_or_known with same | known
      · exact same
      · rw [undiscovered vertex] at known
        omega
    have nextTree : TreeState input root (fun value => visited value ∨ value = vertex) [] := by
      apply (TreeState.initial input root).congr_visited
      intro value
      constructor
      · intro same
        exact Or.inr (same.trans isRoot.symm)
      · rintro (old | same)
        · exact False.elim (empty value old)
        · exact same.trans isRoot
    refine ⟨[], keys, Or.inr nextTree, ?_, by simp, ?_⟩
    · exact (scan.visited_unchanged root (Or.inr isRoot.symm)).2.trans invariant.root_parent
    · intro value
      simp only [List.not_mem_nil, false_and, exists_false, iff_false]
      rintro ⟨old | same, notRoot⟩
      · exact empty value old
      · exact notRoot (same.trans isRoot)
  · have notRoot : vertex ≠ root := by
      intro same
      exact outside (same ▸ tree.root_visited)
    have known : 0 ≤ parent vertex := root_or_known.resolve_left notRoot
    obtain ⟨edge, light, source, target, cost, sourceInside⟩ :=
      invariant.keys.extract symmetric vertex outside known least
    have nextTree := tree.extend light sourceInside (target ▸ outside)
    rw [target] at nextTree
    refine ⟨edge :: chosen, keys, Or.inr nextTree, ?_, ?_, ?_⟩
    · exact (scan.visited_unchanged root (Or.inl tree.root_visited)).2.trans invariant.root_parent
    · intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · rw [target]
        exact ⟨(scan.visited_unchanged vertex (Or.inr rfl)).2.trans source.symm, notRoot⟩
      · obtain ⟨parentEq, targetNotRoot⟩ := invariant.parents candidate member
        exact ⟨(scan.visited_unchanged candidate.target
          (Or.inl (tree.endpoints candidate member).2)).2.trans parentEq, targetNotRoot⟩
    · intro value
      constructor
      · rintro ⟨old | same, valueNotRoot⟩
        · obtain ⟨candidate, member, targetEq⟩ := (invariant.targets value).mp ⟨old, valueNotRoot⟩
          exact ⟨candidate, List.mem_cons_of_mem edge member, targetEq⟩
        · exact ⟨edge, by simp, target.trans same.symm⟩
      · rintro ⟨candidate, member, targetEq⟩
        rcases List.mem_cons.mp member with rfl | member
        · have same : value = vertex := targetEq.symm.trans target
          exact ⟨Or.inr same, fun rootEq => notRoot (same.symm.trans rootEq)⟩
        · have old := (invariant.targets value).mpr ⟨candidate, member, targetEq⟩
          exact ⟨Or.inl old.1, old.2⟩

/-- Equivalent visited predicates may be substituted without changing keys,
chosen edges, or the output parent representation. -/
theorem Invariant.congr_visited {input : List Edge} {root : Int} {before after : Int → Prop}
    {key parent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root before key parent chosen)
    (same : ∀ vertex, before vertex ↔ after vertex) :
    Invariant input root after key parent chosen := by
  refine ⟨invariant.keys.congr_visited same, ?_, invariant.root_parent, invariant.parents, ?_⟩
  · rcases invariant.tree with ⟨empty, chosenEmpty, undiscovered⟩ | tree
    · exact Or.inl ⟨fun vertex present => empty vertex ((same vertex).mpr present),
        chosenEmpty, undiscovered⟩
    · exact Or.inr (tree.congr_visited same)
  · intro vertex
    rw [← same vertex]
    exact invariant.targets vertex

-- Main result: Correctness
/-- When the queue is empty on a connected finite graph, Prim's final parent
sequence describes a minimum spanning tree. This conclusion compares its weight
with every spanning forest; no nonnegativity of edge weights is assumed. -/
theorem Invariant.finish {size : Nat} {input : List Edge} {root : Int} {visited : Int → Prop}
    {key parent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root visited key parent chosen)
    (symmetric : Symmetric input) (valid : ValidInput size input) (connected : ConnectedOn size input)
    (rootNonnegative : 0 ≤ root) (rootBelow : root < size) (rootInside : visited root)
    (empty : ∀ vertex, ¬ visited vertex → parent vertex < 0) :
    SpanningParents size input root parent := by
  have nonempty : 0 < size := by omega
  have covered : ∀ vertex : Int, 0 ≤ vertex → vertex < size → visited vertex := by
    intro vertex lower upper
    have path : Connected input root vertex := by
      have naturalPath := connected root.toNat vertex.toNat (Nat.zero_le _) (by omega)
        (Nat.zero_le _) (by omega)
      have rootCast : (root.toNat : Int) = root := by omega
      have vertexCast : (vertex.toNat : Int) = vertex := by omega
      simpa only [rootCast, vertexCast] using naturalPath
    exact invariant.keys.reachable_of_empty symmetric rootInside
      path empty
  have tree : TreeState input root visited chosen := by
    rcases invariant.tree with ⟨none, _, _⟩ | tree
    · exact False.elim (none root rootInside)
    · exact tree
  refine ⟨chosen, tree.minimum_spanning_tree nonempty valid connected covered,
    invariant.root_parent, invariant.parents, ?_⟩
  intro vertex lower upper notRoot
  exact (invariant.targets vertex).mp ⟨covered vertex lower upper, notRoot⟩

end Algo2Lean.Prim
