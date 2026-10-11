import Algo2LeanLib.KruskalMath

/-!
The cut argument for Prim's minimum spanning tree algorithm. The graph and MST
definitions are shared with Kruskal: edge occurrences have identities, edges are
undirected, and weights are arbitrary integers. The proofs permit equal weights,
negative weights, loops, and parallel input occurrences.

`LightEdge` describes the only greedy choice required by Prim. `Safe.add_light`
shows that this choice preserves extendibility to a minimum spanning forest.
`Growth.minimum_spanning_tree` packages the complete mathematical argument;
an implementation proof only supplies the chosen cuts and final coverage.
-/

namespace Algo2Lean.Prim

open Algo2Lean.Kruskal

/-- An edge has one endpoint inside the cut and the other outside. -/
def Crosses (inside : Int → Prop) (edge : Edge) : Prop :=
  (inside edge.source ∧ ¬ inside edge.target) ∨
  (inside edge.target ∧ ¬ inside edge.source)

/-- An input edge has minimum weight among all edges crossing the given cut. -/
structure LightEdge (input : List Edge) (inside : Int → Prop) (edge : Edge) : Prop where
  member : edge ∈ input
  crosses : Crosses inside edge
  least : ∀ candidate ∈ input, Crosses inside candidate → edge.weight ≤ candidate.weight

/-- A cut respects the chosen edges when no chosen edge crosses it. -/
def Respects (inside : Int → Prop) (selected : List Edge) : Prop :=
  ∀ edge ∈ selected, ¬ Crosses inside edge

/-- A walk along edges that respect a cut cannot leave the side where it starts. -/
theorem stays_inside {edges : List Edge} {u v : Int} {inside : Int → Prop}
    (respects : Respects inside edges) (path : Connected edges u v)
    (start : inside u) : inside v := by
  classical
  induction path with
  | refl => exact start
  | @step u next v adjacent rest ih =>
    apply ih
    apply Classical.byContradiction
    intro outside
    obtain ⟨edge, member, forward | backward⟩ := adjacent
    · obtain ⟨rfl, rfl⟩ := forward
      exact respects edge member (Or.inl ⟨start, outside⟩)
    · obtain ⟨rfl, rfl⟩ := backward
      exact respects edge member (Or.inr ⟨start, outside⟩)

/-- Crossing endpoints cannot already be connected using edges respecting the cut. -/
theorem crossing_disconnected {edges : List Edge} {edge : Edge} {inside : Int → Prop}
    (respects : Respects inside edges) (crossing : Crosses inside edge) :
    ¬ Connected edges edge.source edge.target := by
  intro path
  rcases crossing with forward | backward
  · exact forward.2 (stays_inside respects path forward.1)
  · exact backward.2 (stays_inside respects path.symm backward.1)

/-- An edge crossing a cut can replace a crossing edge of a connecting forest.
The replacement preserves the forest's connected components exactly. -/
theorem exchange_across_cut {edges : List Edge} {added : Edge} {inside : Int → Prop}
    (forest : Forest edges) (linked : Connected edges added.source added.target)
    (crossing : Crosses inside added) :
    ∃ removed ∈ edges, Crosses inside removed ∧
      Forest (added :: edges.erase removed) ∧
      (∀ u v, Connected (added :: edges.erase removed) u v ↔ Connected edges u v) := by
  classical
  let internal := edges.filter (fun edge => decide (¬ Crosses inside edge))
  have respects : Respects inside internal := by
    intro edge member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  obtain ⟨removed, member, outside, necessary⟩ :=
    forest.missing_bridge linked (crossing_disconnected respects crossing)
  have removedCrossing : Crosses inside removed := by
    apply Classical.byContradiction
    intro absent
    exact outside (List.mem_filter.mpr ⟨member, by simp [absent]⟩)
  exact ⟨removed, member, removedCrossing, ⟨forest.erase removed, necessary⟩,
    exchange_connectivity member linked necessary⟩

/-- Chosen edges are safe if every competing spanning forest can be replaced by
one containing them without increasing its weight. This definition does not
assume beforehand that a minimum spanning forest has been constructed. -/
def Safe (input selected : List Edge) : Prop :=
  ∀ other, Forest other → Spans input other →
    ∃ completion, Forest completion ∧ Spans input completion ∧
      (∀ edge ∈ selected, edge ∈ completion) ∧ weight completion ≤ weight other

theorem safe_nil (input : List Edge) : Safe input [] := by
  intro other forest spanning
  exact ⟨other, forest, spanning, by simp, Int.le_refl _⟩

/-- The light-edge theorem used by Prim: adding a least-weight edge across a
cut that respects all chosen edges preserves safety. -/
theorem Safe.add_light {input selected : List Edge} {edge : Edge} {inside : Int → Prop}
    (safe : Safe input selected) (light : LightEdge input inside edge)
    (respects : Respects inside selected) : Safe input (edge :: selected) := by
  classical
  intro other otherForest otherSpans
  obtain ⟨completion, forest, spanning, retains, bound⟩ := safe other otherForest otherSpans
  obtain ⟨removed, member, crossing, exchanged, connectivity⟩ :=
    exchange_across_cut forest
      (spanning.connected _ _ (edge_connected light.member)) light.crosses
  have missing : removed ∉ selected := fun present => respects removed present crossing
  have cheap := light.least removed (spanning.subset removed member) crossing
  refine ⟨edge :: completion.erase removed, exchanged, ?_, ?_, ?_⟩
  · constructor
    · intro candidate present
      rcases List.mem_cons.mp present with rfl | present
      · exact light.member
      · exact spanning.subset candidate (List.mem_of_mem_erase present)
    · intro u v path
      exact (connectivity u v).mpr (spanning.connected u v path)
  · intro candidate present
    rcases List.mem_cons.mp present with rfl | present
    · simp
    · have different : candidate ≠ removed := by
        intro same
        exact missing (same ▸ present)
      exact List.mem_cons_of_mem edge
        ((List.mem_erase_of_ne different).mpr (retains candidate present))
  · have cost : weight (edge :: completion.erase removed) ≤ weight completion := by
      rw [weight_cons, weight_erase member]
      omega
    exact Int.le_trans cost bound

/-- Once safe chosen edges span the input, they have minimum possible weight. -/
theorem Safe.minimum_spanning_forest {input selected : List Edge}
    (safe : Safe input selected) (forest : Forest selected) (spanning : Spans input selected) :
    MinimumSpanningForest input selected := by
  classical
  refine ⟨forest, spanning, ?_⟩
  intro other otherForest otherSpans
  obtain ⟨completion, completeForest, completeSpans, retains, bound⟩ :=
    safe other otherForest otherSpans
  have same : ∀ edge, edge ∈ selected ↔ edge ∈ completion := by
    intro edge
    refine ⟨retains edge, ?_⟩
    intro member
    apply Classical.byContradiction
    intro missing
    exact completeForest.outside_disconnected retains member missing
      (spanning.connected _ _ (edge_connected (completeSpans.subset edge member)))
  rw [forest.weight_eq completeForest same]
  exact bound

/-- A finite sequence of Prim choices. Each cut may be chosen freely provided
it respects the accumulated forest and the next edge is light across it. -/
inductive Growth (input : List Edge) : List Edge → List Edge → Prop where
  | done (selected : List Edge) : Growth input selected selected
  | add {inside : Int → Prop} {edge : Edge} {selected result : List Edge} :
      LightEdge input inside edge → Respects inside selected →
      Growth input (edge :: selected) result → Growth input selected result

theorem Growth.forest {input selected result : List Edge}
    (growth : Growth input selected result) (forest : Forest selected) : Forest result := by
  induction growth with
  | done => exact forest
  | add light respects rest ih =>
    exact ih ⟨forest, crossing_disconnected respects light.crosses⟩

theorem Growth.safe {input selected result : List Edge}
    (growth : Growth input selected result) (safe : Safe input selected) : Safe input result := by
  induction growth with
  | done => exact safe
  | add light respects rest ih => exact ih (safe.add_light light respects)

theorem Growth.subset {input selected result : List Edge}
    (growth : Growth input selected result) :
    ∀ edge ∈ result, edge ∈ input ∨ edge ∈ selected := by
  induction growth with
  | done => exact fun _ member => Or.inr member
  | add light respects rest ih =>
    intro edge member
    rcases ih edge member with inputMember | selectedMember
    · exact Or.inl inputMember
    · rcases List.mem_cons.mp selectedMember with rfl | selectedMember
      · exact Or.inl light.member
      · exact Or.inr selectedMember

/-- Any completed light-edge growth that spans the input is a minimum spanning
forest. No positivity or strict ordering of edge weights is required. -/
theorem Growth.minimum_spanning_forest {input result : List Edge}
    (growth : Growth input [] result)
    (covers : ∀ u v, Connected input u v → Connected result u v) :
    MinimumSpanningForest input result := by
  apply (growth.safe (safe_nil input)).minimum_spanning_forest (growth.forest trivial)
  exact ⟨fun edge member => by simpa using growth.subset edge member, covers⟩

-- Main result: Correctness
/-- On a connected, nonempty finite graph, completed Prim growth returns a
minimum spanning tree, compared against every competing spanning forest. -/
theorem Growth.minimum_spanning_tree {size : Nat} {input result : List Edge}
    (growth : Growth input [] result) (nonempty : 0 < size)
    (valid : ValidInput size input) (connected : ConnectedOn size input)
    (covers : ∀ u v, Connected input u v → Connected result u v) :
    MinimumSpanningTree size input result :=
  (growth.minimum_spanning_forest covers).tree nonempty valid connected

/-- The mathematical loop invariant after the root has been selected. Chosen
edges form a safe tree connecting precisely the currently visited vertices.
The representation of the visited predicate is left to the implementation. -/
structure TreeState (input : List Edge) (root : Int) (visited : Int → Prop)
    (selected : List Edge) : Prop where
  root_visited : visited root
  subset : ∀ edge ∈ selected, edge ∈ input
  endpoints : ∀ edge ∈ selected, visited edge.source ∧ visited edge.target
  reaches : ∀ vertex, visited vertex → Connected selected root vertex
  forest : Forest selected
  safe : Safe input selected

/-- The single visited root and no selected edges satisfy Prim's tree invariant. -/
theorem TreeState.initial (input : List Edge) (root : Int) :
    TreeState input root (fun vertex => vertex = root) [] := by
  refine ⟨rfl, by simp, by simp, ?_, trivial, safe_nil input⟩
  intro vertex same
  subst vertex
  exact .refl root

theorem TreeState.respects {input selected : List Edge} {root : Int} {visited : Int → Prop}
    (state : TreeState input root visited selected) : Respects visited selected := by
  intro edge member crossing
  obtain ⟨sourceInside, targetInside⟩ := state.endpoints edge member
  rcases crossing with forward | backward
  · exact forward.2 targetInside
  · exact backward.2 sourceInside

/-- Selecting a light outgoing edge extends the current tree to its unvisited
target. This is the complete mathematical invariant step of Prim's main loop. -/
theorem TreeState.extend {input selected : List Edge} {root : Int} {visited : Int → Prop}
    (state : TreeState input root visited selected) {edge : Edge}
    (light : LightEdge input visited edge) (sourceInside : visited edge.source)
    (targetOutside : ¬ visited edge.target) :
    TreeState input root (fun vertex => visited vertex ∨ vertex = edge.target)
      (edge :: selected) := by
  have lift {u v : Int} (path : Connected selected u v) : Connected (edge :: selected) u v :=
    path.mono (fun _ member => List.mem_cons_of_mem edge member)
  refine ⟨Or.inl state.root_visited, ?_, ?_, ?_, ?_, state.safe.add_light light state.respects⟩
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact light.member
    · exact state.subset candidate member
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨Or.inl sourceInside, Or.inr rfl⟩
    · exact ⟨Or.inl (state.endpoints candidate member).1,
        Or.inl (state.endpoints candidate member).2⟩
  · intro vertex inside
    rcases inside with old | rfl
    · exact lift (state.reaches vertex old)
    · exact (lift (state.reaches edge.source sourceInside)).trans
        (edge_connected (by simp))
  · exact ⟨state.forest, fun path => targetOutside (stays_inside state.respects path sourceInside)⟩

/-- Changing only the representation of the visited set preserves the invariant. -/
theorem TreeState.congr_visited {input selected : List Edge} {root : Int}
    {before after : Int → Prop} (state : TreeState input root before selected)
    (same : ∀ vertex, before vertex ↔ after vertex) : TreeState input root after selected := by
  refine ⟨(same root).mp state.root_visited, state.subset, ?_, ?_, state.forest, state.safe⟩
  · intro edge member
    exact ⟨(same edge.source).mp (state.endpoints edge member).1,
      (same edge.target).mp (state.endpoints edge member).2⟩
  · intro vertex member
    exact state.reaches vertex ((same vertex).mpr member)

/-- Visiting every endpoint makes the selected tree span the whole input. -/
theorem TreeState.spans {input selected : List Edge} {root : Int} {visited : Int → Prop}
    (state : TreeState input root visited selected)
    (covered : ∀ edge ∈ input, visited edge.source ∧ visited edge.target) :
    Spans input selected := by
  refine ⟨state.subset, ?_⟩
  intro u v path
  apply path.replace
  intro edge member
  exact (state.reaches edge.source (covered edge member).1).symm.trans
    (state.reaches edge.target (covered edge member).2)

/-- Prim's completed tree has minimum weight among all spanning forests. -/
theorem TreeState.minimum_spanning_forest {input selected : List Edge} {root : Int}
    {visited : Int → Prop} (state : TreeState input root visited selected)
    (covered : ∀ edge ∈ input, visited edge.source ∧ visited edge.target) :
    MinimumSpanningForest input selected :=
  state.safe.minimum_spanning_forest state.forest (state.spans covered)

/-- Finishing the loop on a connected finite graph yields a genuine MST. The
only implementation-specific obligation is that every declared vertex was visited. -/
theorem TreeState.minimum_spanning_tree {size : Nat} {input selected : List Edge} {root : Int}
    {visited : Int → Prop} (state : TreeState input root visited selected)
    (nonempty : 0 < size) (valid : ValidInput size input) (connected : ConnectedOn size input)
    (covered : ∀ vertex : Int, 0 ≤ vertex → vertex < size → visited vertex) :
    MinimumSpanningTree size input selected := by
  apply MinimumSpanningForest.tree (state.minimum_spanning_forest ?_) nonempty valid connected
  intro edge member
  exact ⟨covered edge.source (valid.source edge member).1 (valid.source edge member).2,
    covered edge.target (valid.target edge member).1 (valid.target edge member).2⟩

/-- Queue keys bound every edge entering an unvisited endpoint from the visited
tree. Both orientations are included because the mathematical graph is undirected. -/
def BoundaryKeys (input : List Edge) (visited : Int → Prop) (key : Int → Int) : Prop :=
  ∀ edge ∈ input,
    (visited edge.source → ¬ visited edge.target → key edge.target ≤ edge.weight) ∧
    (visited edge.target → ¬ visited edge.source → key edge.source ≤ edge.weight)

/-- Extracting a minimum key produces a light cut edge when keys satisfy their
usual Prim invariant. Ties are allowed and the keys may be negative. -/
theorem light_of_minimum_key {input : List Edge} {visited : Int → Prop} {key : Int → Int}
    (keys : BoundaryKeys input visited key) {edge : Edge}
    (member : edge ∈ input) (sourceInside : visited edge.source)
    (targetOutside : ¬ visited edge.target) (chosenKey : key edge.target = edge.weight)
    (least : ∀ vertex, ¬ visited vertex → key edge.target ≤ key vertex) :
    LightEdge input visited edge := by
  refine ⟨member, Or.inl ⟨sourceInside, targetOutside⟩, ?_⟩
  intro candidate candidateMember crossing
  rw [← chosenKey]
  rcases crossing with forward | backward
  · exact Int.le_trans (least candidate.target forward.2)
      ((keys candidate candidateMember).1 forward.1 forward.2)
  · exact Int.le_trans (least candidate.source backward.2)
      ((keys candidate candidateMember).2 backward.1 backward.2)

/-- A finite adjacency scan keeps the best known incoming edge at each unvisited
vertex. A negative parent means that no scanned edge reaches that vertex.
`processed` describes exactly the edges whose relaxations have been performed. -/
structure Frontier (processed : Edge → Prop) (visited : Int → Prop)
    (key parent : Int → Int) : Prop where
  witness : ∀ vertex, ¬ visited vertex → 0 ≤ parent vertex →
    ∃ edge, processed edge ∧ edge.source = parent vertex ∧
      edge.target = vertex ∧ edge.weight = key vertex
  complete : ∀ edge, processed edge → ¬ visited edge.target → 0 ≤ parent edge.target
  least : ∀ edge, processed edge → ¬ visited edge.target → key edge.target ≤ edge.weight

/-- Functional notation for one sequence assignment. -/
def assign (values : Int → Int) (index value : Int) : Int → Int :=
  fun vertex => if vertex = index then value else values vertex

theorem Frontier.initial (visited : Int → Prop) (key : Int → Int) :
    Frontier (fun _ => False) visited key (fun _ => -1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    omega
  · intro edge impossible
    exact False.elim impossible
  · intro edge impossible
    exact False.elim impossible

/-- Removing a vertex from the queue preserves every remaining key invariant. -/
theorem Frontier.grow_visited {processed : Edge → Prop} {before after : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed before key parent)
    (grows : ∀ vertex, before vertex → after vertex) : Frontier processed after key parent := by
  have outside {vertex} (h : ¬ after vertex) : ¬ before vertex := fun old => h (grows vertex old)
  exact ⟨fun vertex h => frontier.witness vertex (outside h),
    fun edge member h => frontier.complete edge member (outside h),
    fun edge member h => frontier.least edge member (outside h)⟩

/-- An edge to an already selected vertex does not affect the frontier. -/
theorem Frontier.add_visited {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed visited key parent)
    (edge : Edge) (inside : visited edge.target) :
    Frontier (fun candidate => candidate = edge ∨ processed candidate) visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨candidate, member, source, target, cost⟩ := frontier.witness vertex outside known
    exact ⟨candidate, Or.inr member, source, target, cost⟩
  · intro candidate member outside
    rcases member with rfl | member
    · exact False.elim (outside inside)
    · exact frontier.complete candidate member outside
  · intro candidate member outside
    rcases member with rfl | member
    · exact False.elim (outside inside)
    · exact frontier.least candidate member outside

/-- An equally expensive or heavier edge leaves a known key and its parent unchanged. -/
theorem Frontier.add_keep {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed visited key parent)
    (edge : Edge) (known : 0 ≤ parent edge.target) (expensive : key edge.target ≤ edge.weight) :
    Frontier (fun candidate => candidate = edge ∨ processed candidate) visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside present
    obtain ⟨candidate, member, source, target, cost⟩ := frontier.witness vertex outside present
    exact ⟨candidate, Or.inr member, source, target, cost⟩
  · intro candidate member outside
    rcases member with rfl | member
    · exact known
    · exact frontier.complete candidate member outside
  · intro candidate member outside
    rcases member with rfl | member
    · exact expensive
    · exact frontier.least candidate member outside

/-- A newly discovered or cheaper edge replaces exactly its target's key and
parent. This local lemma matches the two assignments in Prim's relaxation branch. -/
theorem Frontier.add_improve {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed visited key parent)
    (edge : Edge) (sourceNonnegative : 0 ≤ edge.source)
    (better : parent edge.target < 0 ∨ edge.weight ≤ key edge.target) :
    Frontier (fun candidate => candidate = edge ∨ processed candidate) visited
      (assign key edge.target edge.weight) (assign parent edge.target edge.source) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    by_cases same : vertex = edge.target
    · subst vertex
      exact ⟨edge, Or.inl rfl, by simp [assign], rfl, by simp [assign]⟩
    · simp only [assign, same, ↓reduceIte] at known ⊢
      obtain ⟨candidate, member, source, target, cost⟩ := frontier.witness vertex outside known
      exact ⟨candidate, Or.inr member, source, target, cost⟩
  · intro candidate member outside
    by_cases same : candidate.target = edge.target
    · simpa [assign, same] using sourceNonnegative
    · simp only [assign, same, ↓reduceIte]
      rcases member with rfl | member
      · exact False.elim (same rfl)
      · exact frontier.complete candidate member outside
  · intro candidate member outside
    by_cases same : candidate.target = edge.target
    · simp only [assign, same, ↓reduceIte]
      rcases member with rfl | member
      · exact Int.le_refl _
      · have bound := frontier.least candidate member outside
        have known := frontier.complete candidate member outside
        rw [same] at bound known
        rcases better with absent | cheaper
        · omega
        · exact Int.le_trans cheaper bound
    · simp only [assign, same, ↓reduceIte]
      rcases member with rfl | member
      · exact False.elim (same rfl)
      · exact frontier.least candidate member outside

/-- Equivalent descriptions of processed edges give the same frontier invariant. -/
theorem Frontier.congr_processed {before after : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier before visited key parent)
    (same : ∀ edge, before edge ↔ after edge) : Frontier after visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨edge, member, source, target, cost⟩ := frontier.witness vertex outside known
    exact ⟨edge, (same edge).mp member, source, target, cost⟩
  · intro edge member outside
    exact frontier.complete edge ((same edge).mpr member) outside
  · intro edge member outside
    exact frontier.least edge ((same edge).mpr member) outside

/-- The main-loop key invariant after all adjacency lists of visited vertices
have been scanned. Vertices are discovered exactly when the cut reaches them. -/
abbrev Keys (input : List Edge) (visited : Int → Prop) (key parent : Int → Int) : Prop :=
  Frontier (fun edge => edge ∈ input ∧ visited edge.source) visited key parent

/-- An undirected adjacency representation contains a reverse occurrence of
the same weight for every directed input occurrence. -/
def Symmetric (input : List Edge) : Prop :=
  ∀ edge ∈ input, ∃ reverse ∈ input,
    reverse.source = edge.target ∧ reverse.target = edge.source ∧ reverse.weight = edge.weight

/-- The directed adjacency-list key invariant also bounds undirected cut edges. -/
theorem Keys.boundary {input : List Edge} {visited : Int → Prop} {key parent : Int → Int}
    (keys : Keys input visited key parent) (symmetric : Symmetric input) :
    BoundaryKeys input visited key := by
  intro edge member
  constructor
  · intro sourceInside targetOutside
    exact keys.least edge ⟨member, sourceInside⟩ targetOutside
  · intro targetInside sourceOutside
    obtain ⟨reverse, reverseMember, source, target, cost⟩ := symmetric edge member
    have sourceInside : visited reverse.source := source ▸ targetInside
    have targetOutside : ¬ visited reverse.target := target ▸ sourceOutside
    have bound := keys.least reverse ⟨reverseMember, sourceInside⟩ targetOutside
    simpa [target, cost] using bound

/-- A queue that stores the discovered unvisited vertices extracts a light edge.
The queue's minimum requirement ranges only over discovered vertices, so no
artificial infinity value is needed for undiscovered keys. -/
theorem Keys.extract {input : List Edge} {visited : Int → Prop} {key parent : Int → Int}
    (keys : Keys input visited key parent) (symmetric : Symmetric input)
    (vertex : Int) (outside : ¬ visited vertex) (known : 0 ≤ parent vertex)
    (least : ∀ other, ¬ visited other → 0 ≤ parent other → key vertex ≤ key other) :
    ∃ edge, LightEdge input visited edge ∧ edge.source = parent vertex ∧
      edge.target = vertex ∧ edge.weight = key vertex ∧ visited edge.source := by
  obtain ⟨edge, ⟨member, sourceInside⟩, source, target, cost⟩ := keys.witness vertex outside known
  refine ⟨edge, ⟨member, Or.inl ⟨sourceInside, target ▸ outside⟩, ?_⟩,
    source, target, cost, sourceInside⟩
  intro candidate candidateMember crossing
  rw [cost]
  rcases crossing with forward | backward
  · exact Int.le_trans (least candidate.target forward.2
      (keys.complete candidate ⟨candidateMember, forward.1⟩ forward.2))
      (keys.least candidate ⟨candidateMember, forward.1⟩ forward.2)
  · obtain ⟨reverse, reverseMember, reverseSource, reverseTarget, reverseCost⟩ :=
      symmetric candidate candidateMember
    have inside : visited reverse.source := reverseSource ▸ backward.1
    have unvisited : ¬ visited reverse.target := reverseTarget ▸ backward.2
    have bound := Int.le_trans (least reverse.target unvisited
      (keys.complete reverse ⟨reverseMember, inside⟩ unvisited))
      (keys.least reverse ⟨reverseMember, inside⟩ unvisited)
    simpa [reverseCost] using bound

/-- An empty frontier has already reached every vertex connected to its visited root. -/
theorem Keys.reachable_of_empty {input : List Edge} {visited : Int → Prop}
    {key parent : Int → Int} (keys : Keys input visited key parent)
    (symmetric : Symmetric input) {root vertex : Int} (rootInside : visited root)
    (path : Connected input root vertex)
    (empty : ∀ other, ¬ visited other → parent other < 0) : visited vertex := by
  classical
  apply Classical.byContradiction
  intro outside
  obtain ⟨edge, member, crossing⟩ := path.crosses_cut visited rootInside outside
  rcases crossing with forward | backward
  · have known := keys.complete edge ⟨member, forward.1⟩ forward.2
    have absent := empty edge.target forward.2
    omega
  · obtain ⟨reverse, reverseMember, source, target, cost⟩ := symmetric edge member
    have inside : visited reverse.source := source ▸ backward.1
    have unvisited : ¬ visited reverse.target := target ▸ backward.2
    have known := keys.complete reverse ⟨reverseMember, inside⟩ unvisited
    have absent := empty reverse.target unvisited
    omega

/-- The pure effect of scanning one adjacency list. The four constructors match
the empty list, visited-target, unchanged-key, and improved-key branches. -/
inductive KeyScan (visited : Int → Prop) (source : Int) :
    List (Int × Int) → (Int → Int) → (Int → Int) → (Int → Int) → (Int → Int) → Prop where
  | done (key parent : Int → Int) : KeyScan visited source [] key parent key parent
  | skip {vertex cost : Int} {rest : List (Int × Int)} {key parent finalKey finalParent : Int → Int} :
      visited vertex → KeyScan visited source rest key parent finalKey finalParent →
      KeyScan visited source ((vertex, cost) :: rest) key parent finalKey finalParent
  | keep {vertex cost : Int} {rest : List (Int × Int)} {key parent finalKey finalParent : Int → Int} :
      ¬ visited vertex → 0 ≤ parent vertex → key vertex ≤ cost →
      KeyScan visited source rest key parent finalKey finalParent →
      KeyScan visited source ((vertex, cost) :: rest) key parent finalKey finalParent
  | improve {vertex cost : Int} {rest : List (Int × Int)} {key parent finalKey finalParent : Int → Int} :
      ¬ visited vertex → (parent vertex < 0 ∨ cost < key vertex) →
      KeyScan visited source rest (assign key vertex cost) (assign parent vertex source)
        finalKey finalParent →
      KeyScan visited source ((vertex, cost) :: rest) key parent finalKey finalParent

theorem KeyScan.append {visited : Int → Prop} {source : Int} {first second : List (Int × Int)}
    {key parent middleKey middleParent finalKey finalParent : Int → Int}
    (one : KeyScan visited source first key parent middleKey middleParent)
    (two : KeyScan visited source second middleKey middleParent finalKey finalParent) :
    KeyScan visited source (first ++ second) key parent finalKey finalParent := by
  induction one with
  | done => exact two
  | skip inside rest ih => exact .skip inside (ih two)
  | keep outside known expensive rest ih => exact .keep outside known expensive (ih two)
  | improve outside better rest ih => exact .improve outside better (ih two)

/-- Scanning never changes the key or parent of an already visited vertex. -/
theorem KeyScan.visited_unchanged {visited : Int → Prop} {source : Int} {edges : List (Int × Int)}
    {key parent finalKey finalParent : Int → Int}
    (scan : KeyScan visited source edges key parent finalKey finalParent)
    (vertex : Int) (inside : visited vertex) :
    finalKey vertex = key vertex ∧ finalParent vertex = parent vertex := by
  induction scan with
  | done => exact ⟨rfl, rfl⟩
  | skip _ _ ih => exact ih
  | keep _ _ _ _ ih => exact ih
  | @improve other cost rest key parent finalKey finalParent outside better scan ih =>
    have different : vertex ≠ other := fun same => outside (same ▸ inside)
    simpa [assign, different] using ih

/-- Edge identity does not affect a relaxation: parallel occurrences with the
same endpoints and weight provide the same frontier guarantees. -/
theorem Frontier.add_payload {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} {edge : Edge} {input : List Edge}
    (frontier : Frontier (fun candidate => candidate = edge ∨ processed candidate)
      visited key parent) (member : edge ∈ input) :
    Frontier (fun candidate => processed candidate ∨
      candidate ∈ input ∧ candidate.source = edge.source ∧
        candidate.target = edge.target ∧ candidate.weight = edge.weight) visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨candidate, candidateMember, source, target, cost⟩ := frontier.witness vertex outside known
    refine ⟨candidate, ?_, source, target, cost⟩
    rcases candidateMember with rfl | old
    · exact Or.inr ⟨member, rfl, rfl, rfl⟩
    · exact Or.inl old
  · intro candidate candidateMember outside
    rcases candidateMember with old | ⟨_, _, target, _⟩
    · exact frontier.complete candidate (Or.inr old) outside
    · rw [target] at outside ⊢
      exact frontier.complete edge (Or.inl rfl) outside
  · intro candidate candidateMember outside
    rcases candidateMember with old | ⟨_, _, target, cost⟩
    · exact frontier.least candidate (Or.inr old) outside
    · rw [target] at outside ⊢
      rw [cost]
      exact frontier.least edge (Or.inl rfl) outside

/-- A completed adjacency scan incorporates all of that list's edge occurrences
into the frontier, while retaining every earlier scanned edge. -/
theorem KeyScan.frontier {visited : Int → Prop} {source : Int} {edges : List (Int × Int)}
    {key parent finalKey finalParent : Int → Int}
    (scan : KeyScan visited source edges key parent finalKey finalParent)
    (input : List Edge) (sourceNonnegative : 0 ≤ source)
    (members : ∀ pair ∈ edges, ∃ edge ∈ input,
      edge.source = source ∧ edge.target = pair.1 ∧ edge.weight = pair.2)
    {processed : Edge → Prop} (frontier : Frontier processed visited key parent) :
    Frontier (fun edge => processed edge ∨ edge ∈ input ∧ edge.source = source ∧
      (edge.target, edge.weight) ∈ edges) visited finalKey finalParent := by
  induction scan generalizing processed with
  | done key parent =>
    exact frontier.congr_processed (by simp)
  | @skip vertex cost rest key parent finalKey finalParent inside scan ih =>
    obtain ⟨edge, member, sourceEq, targetEq, weightEq⟩ := members (vertex, cost) (by simp)
    have next := (frontier.add_visited edge (targetEq ▸ inside)).add_payload member
    have result := ih (fun pair present => members pair (by simp [present])) next
    apply result.congr_processed
    intro candidate
    simp only [sourceEq, targetEq, weightEq, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((old | ⟨inInput, source, target, cost⟩) | ⟨inInput, source, tail⟩)
      · exact Or.inl old
      · exact Or.inr ⟨inInput, source, Or.inl ⟨target, cost⟩⟩
      · exact Or.inr ⟨inInput, source, Or.inr tail⟩
    · rintro (old | ⟨inInput, source, (⟨target, cost⟩ | tail)⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨inInput, source, target, cost⟩)
      · exact Or.inr ⟨inInput, source, tail⟩
  | @keep vertex cost rest key parent finalKey finalParent outside known expensive scan ih =>
    obtain ⟨edge, member, sourceEq, targetEq, weightEq⟩ := members (vertex, cost) (by simp)
    have next := (frontier.add_keep edge (targetEq ▸ known)
      (by simpa [targetEq, weightEq] using expensive)).add_payload member
    have result := ih (fun pair present => members pair (by simp [present])) next
    apply result.congr_processed
    intro candidate
    simp only [sourceEq, targetEq, weightEq, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((old | ⟨inInput, source, target, cost⟩) | ⟨inInput, source, tail⟩)
      · exact Or.inl old
      · exact Or.inr ⟨inInput, source, Or.inl ⟨target, cost⟩⟩
      · exact Or.inr ⟨inInput, source, Or.inr tail⟩
    · rintro (old | ⟨inInput, source, (⟨target, cost⟩ | tail)⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨inInput, source, target, cost⟩)
      · exact Or.inr ⟨inInput, source, tail⟩
  | @improve vertex cost rest key parent finalKey finalParent outside better scan ih =>
    obtain ⟨edge, member, sourceEq, targetEq, weightEq⟩ := members (vertex, cost) (by simp)
    have sourceValid : 0 ≤ edge.source := by simpa [sourceEq] using sourceNonnegative
    have betterEdge : parent edge.target < 0 ∨ edge.weight ≤ key edge.target := by
      rw [targetEq, weightEq]
      rcases better with absent | cheaper
      · exact Or.inl absent
      · exact Or.inr (Int.le_of_lt cheaper)
    have next := (frontier.add_improve edge sourceValid betterEdge).add_payload member
    rw [targetEq, weightEq, sourceEq] at next
    have result := ih (fun pair present => members pair (by simp [present])) next
    apply result.congr_processed
    intro candidate
    simp only [List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((old | ⟨inInput, source, target, cost⟩) | ⟨inInput, source, tail⟩)
      · exact Or.inl old
      · exact Or.inr ⟨inInput, source, Or.inl ⟨target, cost⟩⟩
      · exact Or.inr ⟨inInput, source, Or.inr tail⟩
    · rintro (old | ⟨inInput, source, (⟨target, cost⟩ | tail)⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨inInput, source, target, cost⟩)
      · exact Or.inr ⟨inInput, source, tail⟩

/-- Before selecting the root, every vertex is undiscovered and no key is constrained. -/
theorem Keys.initial (input : List Edge) (key : Int → Int) :
    Keys input (fun _ => False) key (fun _ => -1) :=
  (Frontier.initial (fun _ => False) key).congr_processed (by simp)

/-- One complete main-loop iteration extends the visited set by its extracted
vertex and scans exactly that vertex's adjacency list. All resulting keys again
describe the full boundary of the enlarged tree. -/
theorem KeyScan.keys_after_selection {input : List Edge} {visited : Int → Prop}
    {source : Int} {edges : List (Int × Int)} {key parent finalKey finalParent : Int → Int}
    (keys : Keys input visited key parent)
    (scan : KeyScan (fun vertex => visited vertex ∨ vertex = source) source
      edges key parent finalKey finalParent)
    (sourceNonnegative : 0 ≤ source)
    (members : ∀ pair ∈ edges, ∃ edge ∈ input,
      edge.source = source ∧ edge.target = pair.1 ∧ edge.weight = pair.2)
    (complete : ∀ edge ∈ input, edge.source = source → (edge.target, edge.weight) ∈ edges) :
    Keys input (fun vertex => visited vertex ∨ vertex = source) finalKey finalParent := by
  have next := keys.grow_visited (after := fun vertex => visited vertex ∨ vertex = source)
    (fun _ old => Or.inl old)
  have scanned := scan.frontier input sourceNonnegative members next
  apply scanned.congr_processed
  intro edge
  constructor
  · rintro (⟨member, old⟩ | ⟨member, source, _⟩)
    · exact ⟨member, Or.inl old⟩
    · exact ⟨member, Or.inr source⟩
  · rintro ⟨member, old | source⟩
    · exact Or.inl ⟨member, old⟩
    · exact Or.inr ⟨member, source, complete edge member source⟩

/-- Replacing the representation of the visited predicate preserves all key facts. -/
theorem Keys.congr_visited {input : List Edge} {before after : Int → Prop}
    {key parent : Int → Int} (keys : Keys input before key parent)
    (same : ∀ vertex, before vertex ↔ after vertex) : Keys input after key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨edge, ⟨member, inside⟩, source, target, cost⟩ :=
      keys.witness vertex (fun old => outside ((same vertex).mp old)) known
    exact ⟨edge, ⟨member, (same edge.source).mp inside⟩, source, target, cost⟩
  · intro edge member outside
    exact keys.complete edge ⟨member.1, (same edge.source).mpr member.2⟩
      (fun old => outside ((same edge.target).mp old))
  · intro edge member outside
    exact keys.least edge ⟨member.1, (same edge.source).mpr member.2⟩
      (fun old => outside ((same edge.target).mp old))

end Algo2Lean.Prim
