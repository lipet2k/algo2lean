import Std

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Reusable shortest-path mathematics for Dijkstra implementations.

This module imports neither a compiled algorithm nor the Algo2Lean runtime.
Distance sequences are ordinary functions `Int → Int`. A queue backend only
needs to supply minimum selection, the relaxation scan, and exhaustion; the
path, frontier, and shortest-distance proofs are shared across backends.
-/

namespace Algo2Lean.Dijkstra

/-- `edge u v weight` describes a directed edge; parallel edges are allowed. -/
abbrev Edges := Int → Int → Int → Prop

/-- A finite walk from `source`, recording its endpoint and total edge weight.
    Repeated vertices are allowed, so shortestness compares all finite walks. -/
inductive Path (edge : Edges) (source : Int) : Int → Int → Prop where
  | empty : Path edge source source 0
  | extend {vertex next cost weight : Int} :
      Path edge source vertex cost → edge vertex next weight →
      Path edge source next (cost + weight)

def NonnegativeEdges (edge : Edges) : Prop :=
  ∀ u v weight, edge u v weight → 0 ≤ weight

theorem path_nonnegative (edge : Edges) (source vertex cost : Int)
    (nonnegative : NonnegativeEdges edge) (path : Path edge source vertex cost) :
    0 ≤ cost := by
  induction path with
  | empty => omega
  | @extend vertex next cost weight route connection previous =>
    have weightNonnegative := nonnegative vertex next weight connection
    omega

/-- Every settled distance is a lower bound for every route to that vertex.
    With route witnesses, this says that settled distances are already exact. -/
def SettledOptimal (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) : Prop :=
  ∀ vertex, settled vertex → ∀ cost, Path edge source vertex cost → distance vertex ≤ cost

/-- All edges out of settled vertices have been relaxed. In particular, every
    edge crossing into the unsettled region gives that vertex a finite bound. -/
def FrontierBound (edge : Edges) (distance : Int → Int) (settled : Int → Prop) : Prop :=
  ∀ u v weight, settled u → ¬ settled v → edge u v weight →
    0 ≤ distance v ∧ distance v ≤ distance u + weight

/-- Every finite tentative distance comes from an actual route. -/
def DistanceWitnesses (edge : Edges) (source : Int) (distance : Int → Int) : Prop :=
  ∀ vertex, 0 ≤ distance vertex → Path edge source vertex (distance vertex)

def IsShortest (edge : Edges) (source vertex cost : Int) : Prop :=
  Path edge source vertex cost ∧
    ∀ otherCost, Path edge source vertex otherCost → cost ≤ otherCost

/-- The minimum unsettled tentative distance bounds every route ending in the
    unsettled region. Settled optimality establishes the bound at the first
    frontier crossing; nonnegative edge weights preserve it along the remaining route. -/
theorem unsettled_path_lower_bound (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (nonnegative : NonnegativeEdges edge)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (settledCorrect : SettledOptimal edge source distance settled)
    (frontier : FrontierBound edge distance settled)
    (minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex →
      distance selected ≤ distance vertex)
    (vertex cost : Int) (path : Path edge source vertex cost) (unsettled : ¬ settled vertex) :
    distance selected ≤ cost := by
  induction path with
  | empty =>
    have sourceZero := sourceInitialized unsettled
    have bound := minimum source unsettled (by omega)
    omega
  | @extend previous vertex prefixCost weight route connection inductionHypothesis =>
    by_cases previousSettled : settled previous
    · have previousBound := settledCorrect previous previousSettled prefixCost route
      obtain ⟨finite, relaxed⟩ := frontier previous vertex weight previousSettled unsettled connection
      have selectedBound := minimum vertex unsettled finite
      omega
    · have prefixBound := inductionHypothesis previousSettled
      have weightNonnegative := nonnegative previous vertex weight connection
      omega

/-- Greedy safety: choosing a minimum finite unsettled distance never settles
    a value larger than the weight of a route to the selected vertex. -/
theorem greedy_safe (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (nonnegative : NonnegativeEdges edge)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (settledCorrect : SettledOptimal edge source distance settled)
    (frontier : FrontierBound edge distance settled)
    (selectedUnsettled : ¬ settled selected)
    (minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex →
      distance selected ≤ distance vertex) :
    ∀ cost, Path edge source selected cost → distance selected ≤ cost := by
  intro cost path
  exact unsettled_path_lower_bound edge source selected distance settled nonnegative
    sourceInitialized settledCorrect frontier minimum selected cost path selectedUnsettled

/-- Together with the tentative route witness, the new settled value is an
    attained shortest distance, not merely a lower bound. -/
theorem greedy_shortest (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (nonnegative : NonnegativeEdges edge)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (settledCorrect : SettledOptimal edge source distance settled)
    (frontier : FrontierBound edge distance settled)
    (witnesses : DistanceWitnesses edge source distance)
    (selectedUnsettled : ¬ settled selected) (selectedFinite : 0 ≤ distance selected)
    (minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex →
      distance selected ≤ distance vertex) :
    IsShortest edge source selected (distance selected) := by
  exact ⟨witnesses selected selectedFinite,
    greedy_safe edge source selected distance settled nonnegative sourceInitialized
      settledCorrect frontier selectedUnsettled minimum⟩

/-- Settling the selected vertex preserves the settled-distance invariant.
    Restoring `FrontierBound` afterwards requires relaxing its outgoing edges. -/
theorem settle_preserves_optimality (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (settledCorrect : SettledOptimal edge source distance settled)
    (selectedCorrect : ∀ cost, Path edge source selected cost → distance selected ≤ cost) :
    SettledOptimal edge source distance (fun vertex => settled vertex ∨ vertex = selected) := by
  intro vertex newlySettled cost path
  rcases newlySettled with alreadySettled | rfl
  · exact settledCorrect vertex alreadySettled cost path
  · exact selectedCorrect cost path

/-- If no finite unsettled distance remains, every reachable vertex is settled.
    Only source initialization and the relaxed frontier are needed here. -/
theorem reachable_settled_of_exhausted (edge : Edges) (source : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (frontier : FrontierBound edge distance settled)
    (exhausted : ∀ vertex, ¬ settled vertex → distance vertex < 0)
    (vertex cost : Int) (path : Path edge source vertex cost) : settled vertex := by
  induction path with
  | empty =>
    by_cases sourceSettled : settled source
    · exact sourceSettled
    · have sourceZero := sourceInitialized sourceSettled
      have sourceAbsent := exhausted source sourceSettled
      omega
  | @extend previous vertex prefixCost weight route connection previousSettled =>
    by_cases vertexSettled : settled vertex
    · exact vertexSettled
    · have finite := (frontier previous vertex weight previousSettled vertexSettled connection).1
      have absent := exhausted vertex vertexSettled
      omega

/-- Unsettled vertices are unreachable when the finite priority queue is empty. -/
theorem exhausted_unreachable (edge : Edges) (source : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (sourceInitialized : ¬ settled source → distance source = 0)
    (frontier : FrontierBound edge distance settled)
    (exhausted : ∀ vertex, ¬ settled vertex → distance vertex < 0)
    (vertex : Int) (unsettled : ¬ settled vertex) :
    ∀ cost, ¬ Path edge source vertex cost := by
  intro cost path
  exact unsettled (reachable_settled_of_exhausted edge source distance settled
    sourceInitialized frontier exhausted vertex cost path)

abbrev Adjacency := Int → List (Int × Int)

/-- The mathematical graph used by the path lemmas, extracted from adjacency
    lists on the valid finite vertex range. -/
def representedEdges (size : Int) (adjacency : Adjacency) : Edges :=
  fun source target weight => 0 ≤ source ∧ source < size ∧ (target, weight) ∈ adjacency source

/-- The finite vertex range is used only by proofs, not by the source program. -/
def vertexRange (size : Int) : List Int := (List.range size.toNat).map Int.ofNat

@[simp] theorem vertexRange_length (size : Int) : (vertexRange size).length = size.toNat := by
  simp [vertexRange]

theorem vertexRange_nodup (size : Int) : (vertexRange size).Nodup := by
  exact List.Pairwise.map Int.ofNat (fun a b different same => different (Int.ofNat.inj same)) List.nodup_range

@[simp] theorem vertexRange_member (size vertex : Int) :
    vertex ∈ vertexRange size ↔ 0 ≤ vertex ∧ vertex < size := by
  simp only [vertexRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨index, bound, rfl⟩
    change 0 ≤ (index : Int) ∧ (index : Int) < size
    omega
  · rintro ⟨nonnegative, bound⟩
    exact ⟨vertex.toNat, by omega, Int.toNat_of_nonneg nonnegative⟩

/-- Removing the selected vertex matches the logical update of settledness. -/
theorem remaining_settle (size selected : Int) (settled : Int → Prop) (remaining : List Int)
    (unique : remaining.Nodup)
    (members : ∀ vertex, vertex ∈ remaining ↔ 0 ≤ vertex ∧ vertex < size ∧ ¬ settled vertex) :
    (remaining.erase selected).Nodup ∧
      ∀ vertex, vertex ∈ remaining.erase selected ↔
        0 ≤ vertex ∧ vertex < size ∧ ¬ (settled vertex ∨ vertex = selected) := by
  refine ⟨unique.erase selected, ?_⟩
  intro vertex
  rw [unique.mem_erase_iff, members]
  constructor
  · rintro ⟨different, nonnegative, bound, unsettled⟩
    exact ⟨nonnegative, bound, fun h => h.elim unsettled different⟩
  · rintro ⟨nonnegative, bound, notSettled⟩
    exact ⟨fun same => notSettled (Or.inr same), nonnegative, bound,
      fun old => notSettled (Or.inl old)⟩

/-- Each settlement consumes exactly one remaining vertex. -/
theorem remaining_length (remaining : List Int) (selected : Int) (member : selected ∈ remaining) :
    (remaining.erase selected).length + 1 = remaining.length := by
  have positive := List.length_pos_of_mem member
  rw [List.length_erase_of_mem member]
  omega

/-- A duplicate-free list cannot inject by membership into a shorter list. -/
theorem nodup_subset_length (first second : List Int) (unique : first.Nodup)
    (contained : ∀ vertex ∈ first, vertex ∈ second) : first.length ≤ second.length := by
  induction first generalizing second with
  | nil => simp
  | cons vertex rest ih =>
    obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
    have member := contained vertex (by simp)
    have remaining := ih (second.erase vertex) restUnique (by
      intro other inRest
      apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
      exact contained other (by simp [inRest]))
    have length := remaining_length second vertex member
    simp only [List.length_cons]
    omega

/-- An injectively indexed active prefix fits inside any finite list that
    contains its vertices. No assumptions about key values are needed. -/
theorem active_prefix_bound (vertices positions : Int → Int) (size : Int)
    (nonnegative : 0 ≤ size)
    (inverse : ∀ index, 0 ≤ index → index < size → positions (vertices index) = index)
    (remaining : List Int)
    (contained : ∀ index, 0 ≤ index → index < size → vertices index ∈ remaining) :
    size ≤ (remaining.length : Int) := by
  let active := (List.range size.toNat).map (fun index : Nat => vertices (index : Int))
  have unique : active.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (l := List.range size.toNat) _ List.nodup_range
    intro i j iMember jMember different same
    have iBound := List.mem_range.mp iMember
    have jBound := List.mem_range.mp jMember
    have left := inverse (i : Int) (by omega) (by omega)
    have right := inverse (j : Int) (by omega) (by omega)
    rw [same] at left
    exact different (by omega)
  have included : ∀ vertex ∈ active, vertex ∈ remaining := by
    intro vertex member
    obtain ⟨index, bound, rfl⟩ := List.mem_map.mp member
    have indexBound := List.mem_range.mp bound
    exact contained (index : Int) (by omega) (by omega)
  have bound := nodup_subset_length active remaining unique included
  simp only [active, List.length_map, List.length_range] at bound
  omega

/-- Number of adjacency entries still eligible to be visited. Parallel edges
    and shared linked suffixes are counted once for each source-list occurrence. -/
def edgeBudget (adjacency : Adjacency) (remaining : List Int) : Nat :=
  (remaining.map (fun vertex => (adjacency vertex).length)).sum

/-- Removing one list entry removes exactly its contribution to any natural
    weighted sum. This does not need a no-duplicates assumption. -/
theorem weighted_sum_erase (weight : Int → Nat) (remaining : List Int) (selected : Int)
    (member : selected ∈ remaining) :
    ((remaining.erase selected).map weight).sum + weight selected = (remaining.map weight).sum := by
  induction remaining with
  | nil => simp at member
  | cons vertex rest ih =>
    by_cases same : selected = vertex
    · subst selected
      simp [Nat.add_comm]
    · have inRest : selected ∈ rest := by simpa [same] using member
      have shorter := ih inRest
      simpa [List.erase_cons, same, Ne.symm same, Nat.add_assoc] using
        congrArg (fun total => weight vertex + total) shorter

theorem edgeBudget_erase (adjacency : Adjacency) (remaining : List Int) (selected : Int)
    (member : selected ∈ remaining) :
    edgeBudget adjacency (remaining.erase selected) + (adjacency selected).length =
      edgeBudget adjacency remaining :=
  weighted_sum_erase (fun vertex => (adjacency vertex).length) remaining selected member

/-- Finite nonnegative weights respect inclusion of duplicate-free vertices.
    The adjacency lists themselves may contain repeated edges. -/
theorem weighted_subset_bound (weight : Int → Nat) (first second : List Int)
    (unique : first.Nodup) (contained : ∀ vertex ∈ first, vertex ∈ second) :
    (first.map weight).sum ≤ (second.map weight).sum := by
  induction first generalizing second with
  | nil => simp
  | cons vertex rest ih =>
    obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
    have member := contained vertex (by simp)
    have remaining := ih (second.erase vertex) restUnique (by
      intro other inRest
      apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
      exact contained other (by simp [inRest]))
    have total := weighted_sum_erase weight second vertex member
    simp only [List.map_cons, List.sum_cons]
    omega

theorem edgeBudget_bound (adjacency : Adjacency) (size : Int) (remaining : List Int)
    (unique : remaining.Nodup)
    (bounded : ∀ vertex ∈ remaining, 0 ≤ vertex ∧ vertex < size) :
    edgeBudget adjacency remaining ≤ edgeBudget adjacency (vertexRange size) := by
  apply weighted_subset_bound _ _ _ unique
  intro vertex member
  exact (vertexRange_member size vertex).mpr (bounded vertex member)

/-- A single formula covers the comparison and swap budgets: choose the
    per-settlement and per-edge costs supplied by the queue contracts. -/
def weightedBudget (perVertex perEdge : Nat) (adjacency : Adjacency) (remaining : List Int) : Nat :=
  perVertex * remaining.length + perEdge * edgeBudget adjacency remaining

theorem weightedBudget_erase (perVertex perEdge : Nat) (adjacency : Adjacency)
    (remaining : List Int) (selected : Int) (member : selected ∈ remaining) :
    weightedBudget perVertex perEdge adjacency (remaining.erase selected) +
      perVertex + perEdge * (adjacency selected).length =
      weightedBudget perVertex perEdge adjacency remaining := by
  unfold weightedBudget
  rw [← remaining_length remaining selected member,
    ← edgeBudget_erase adjacency remaining selected member]
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]



/-! Pure invariants for every iteration of Dijkstra, independent of the queue
implementation, storage layout, and compiler-generated transition system. -/

def updateDistance (distance : Int → Int) (target value : Int) : Int → Int :=
  fun vertex => if vertex = target then value else distance vertex

def relaxDistance (distance : Int → Int) (target candidate : Int) : Int → Int :=
  if distance target < 0 ∨ candidate < distance target then updateDistance distance target candidate else distance

@[simp] theorem update_distance_same (distance : Int → Int) (target value : Int) :
    updateDistance distance target value target = value := by simp [updateDistance]

@[simp] theorem update_distance_other (distance : Int → Int) (target value vertex : Int)
    (different : vertex ≠ target) : updateDistance distance target value vertex = distance vertex := by
  simp [updateDistance, different]

theorem relax_distance_other (distance : Int → Int) (target candidate vertex : Int)
    (different : vertex ≠ target) : relaxDistance distance target candidate vertex = distance vertex := by
  by_cases better : distance target < 0 ∨ candidate < distance target
  <;> simp [relaxDistance, updateDistance, better, different]

/-- Relaxation creates a finite bound for the target, even if it was unknown. -/
theorem relax_distance_target (distance : Int → Int) (target candidate : Int) (nonnegative : 0 ≤ candidate) :
    0 ≤ relaxDistance distance target candidate target ∧
      relaxDistance distance target candidate target ≤ candidate := by
  by_cases better : distance target < 0 ∨ candidate < distance target
  · simp [relaxDistance, updateDistance, better, nonnegative]
  · simp only [relaxDistance, if_neg better]
    omega

/-- A finite distance never increases, and every earlier upper bound survives. -/
theorem relax_distance_preserves_bound (distance : Int → Int) (target candidate vertex bound : Int)
    (nonnegative : 0 ≤ candidate) (finite : 0 ≤ distance vertex) (bounded : distance vertex ≤ bound) :
    0 ≤ relaxDistance distance target candidate vertex ∧
      relaxDistance distance target candidate vertex ≤ bound := by
  by_cases same : vertex = target
  · subst vertex
    by_cases better : distance target < 0 ∨ candidate < distance target
    · simp only [relaxDistance, if_pos better, update_distance_same]
      exact ⟨nonnegative, by omega⟩
    · simp [relaxDistance, better, finite, bounded]
  · rw [relax_distance_other distance target candidate vertex same]
    exact ⟨finite, bounded⟩

theorem relax_distance_preserves_zero (distance : Int → Int) (target candidate vertex : Int)
    (nonnegative : 0 ≤ candidate) (zero : distance vertex = 0) :
    relaxDistance distance target candidate vertex = 0 := by
  have bounded := relax_distance_preserves_bound distance target candidate vertex 0 nonnegative
    (by omega) (by omega)
  omega

structure DistanceInvariant (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) : Prop where
  sourceZero : ¬ settled source → distance source = 0
  witnesses : DistanceWitnesses edge source distance
  settledOptimal : SettledOptimal edge source distance settled
  settledFinite : ∀ vertex, settled vertex → 0 ≤ distance vertex
  unknown : ∀ vertex, distance vertex < 0 → distance vertex = -1

structure SearchInvariant (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) : Prop extends DistanceInvariant edge source distance settled where
  frontier : FrontierBound edge distance settled

/-- During one adjacency scan the selected vertex has just been settled.
    All older settled vertices retain their complete frontier bounds, while
    `processed` records the selected vertex's edges already handled. -/
structure RelaxationInvariant (edge : Edges) (source : Int) (distance : Int → Int)
    (settled : Int → Prop) (selected : Int) (processed : List (Int × Int))
    : Prop extends DistanceInvariant edge source distance settled where
  selectedSettled : settled selected
  oldFrontier : ∀ u v weight, settled u → u ≠ selected → ¬ settled v → edge u v weight →
    0 ≤ distance v ∧ distance v ≤ distance u + weight
  processedFrontier : ∀ v weight, (v, weight) ∈ processed → ¬ settled v →
    0 ≤ distance v ∧ distance v ≤ distance selected + weight

def settleVertex (settled : Int → Prop) (selected : Int) : Int → Prop :=
  fun vertex => settled vertex ∨ vertex = selected

/-- Greedy minimum selection permits settling exactly one vertex. The edge
    scan starts with an empty processed list and retains all older bounds. -/
theorem start_relaxation (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (nonnegative : NonnegativeEdges edge) (invariant : SearchInvariant edge source distance settled)
    (unsettled : ¬ settled selected) (finite : 0 ≤ distance selected)
    (minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex → distance selected ≤ distance vertex) :
    RelaxationInvariant edge source distance (settleVertex settled selected) selected [] := by
  refine ⟨⟨?_, invariant.witnesses, ?_, ?_, invariant.unknown⟩, Or.inr rfl, ?_, ?_⟩
  · intro sourceUnsettled
    exact invariant.sourceZero (fun present => sourceUnsettled (Or.inl present))
  · exact settle_preserves_optimality edge source selected distance settled invariant.settledOptimal
      (greedy_safe edge source selected distance settled nonnegative invariant.sourceZero
        invariant.settledOptimal invariant.frontier unsettled minimum)
  · intro vertex present
    rcases present with old | rfl
    · exact invariant.settledFinite vertex old
    · exact finite
  · intro u v weight present different notSettled connection
    rcases present with old | same
    · exact invariant.frontier u v weight old (fun yes => notSettled (Or.inl yes)) connection
    · exact False.elim (different same)
  · intro v weight member
    simp at member

theorem DistanceInvariant.relax (edge : Edges) (source selected target weight : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (invariant : DistanceInvariant edge source distance settled)
    (connection : edge selected target weight) (selectedFinite : 0 ≤ distance selected)
    (weightNonnegative : 0 ≤ weight) (targetUnsettled : ¬ settled target) :
    DistanceInvariant edge source (relaxDistance distance target (distance selected + weight)) settled := by
  have candidateNonnegative : 0 ≤ distance selected + weight := by omega
  have candidateRoute : Path edge source target (distance selected + weight) :=
    Path.extend (invariant.witnesses selected selectedFinite) connection
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sourceUnsettled
    exact relax_distance_preserves_zero distance target _ source candidateNonnegative
      (invariant.sourceZero sourceUnsettled)
  · intro vertex finite
    by_cases better : distance target < 0 ∨ distance selected + weight < distance target
    · by_cases same : vertex = target
      · subst vertex
        simpa [relaxDistance, better] using candidateRoute
      · rw [relax_distance_other distance target _ vertex same] at finite ⊢
        exact invariant.witnesses vertex finite
    · simpa [relaxDistance, better] using invariant.witnesses vertex (by simpa [relaxDistance, better] using finite)
  · intro vertex present cost path
    have different : vertex ≠ target := by intro same; exact targetUnsettled (same ▸ present)
    rw [relax_distance_other distance target _ vertex different]
    exact invariant.settledOptimal vertex present cost path
  · intro vertex present
    have different : vertex ≠ target := by intro same; exact targetUnsettled (same ▸ present)
    rw [relax_distance_other distance target _ vertex different]
    exact invariant.settledFinite vertex present
  · intro vertex negative
    by_cases same : vertex = target
    · subst vertex
      have finite := (relax_distance_target distance target _ candidateNonnegative).1
      omega
    · rw [relax_distance_other distance target _ vertex same] at negative ⊢
      exact invariant.unknown vertex negative

/-- Processing an unsettled target preserves every earlier relaxation and
    establishes the new edge's bound. The `relaxDistance` branch covers both
    actual improvements and unsuccessful comparisons. -/
theorem relax_unsettled_edge (edge : Edges) (source selected target weight : Int)
    (distance : Int → Int) (settled : Int → Prop) (processed : List (Int × Int))
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (connection : edge selected target weight) (weightNonnegative : 0 ≤ weight)
    (targetUnsettled : ¬ settled target) :
    RelaxationInvariant edge source (relaxDistance distance target (distance selected + weight))
      settled selected ((target, weight) :: processed) := by
  have selectedFinite := invariant.settledFinite selected invariant.selectedSettled
  have candidateNonnegative : 0 ≤ distance selected + weight := by omega
  have selectedDifferent : selected ≠ target := by
    intro same; exact targetUnsettled (same ▸ invariant.selectedSettled)
  refine ⟨DistanceInvariant.relax edge source selected target weight distance settled
    invariant.toDistanceInvariant connection selectedFinite weightNonnegative targetUnsettled,
    invariant.selectedSettled, ?_, ?_⟩
  · intro u v edgeWeight uSettled different vUnsettled edgeExists
    have uDifferent : u ≠ target := by intro same; exact targetUnsettled (same ▸ uSettled)
    rw [relax_distance_other distance target _ u uDifferent]
    obtain ⟨finite, bound⟩ := invariant.oldFrontier u v edgeWeight uSettled different vUnsettled edgeExists
    exact relax_distance_preserves_bound distance target _ v _ candidateNonnegative finite bound
  · intro v edgeWeight member vUnsettled
    rw [relax_distance_other distance target _ selected selectedDifferent]
    simp only [List.mem_cons] at member
    rcases member with same | earlier
    · cases same
      exact relax_distance_target distance target _ candidateNonnegative
    · obtain ⟨finite, bound⟩ := invariant.processedFrontier v edgeWeight earlier vUnsettled
      exact relax_distance_preserves_bound distance target _ v _ candidateNonnegative finite bound

theorem skip_settled_edge (edge : Edges) (source selected target weight : Int)
    (distance : Int → Int) (settled : Int → Prop) (processed : List (Int × Int))
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (targetSettled : settled target) :
    RelaxationInvariant edge source distance settled selected ((target, weight) :: processed) := by
  refine ⟨invariant.toDistanceInvariant, invariant.selectedSettled, invariant.oldFrontier, ?_⟩
  intro v edgeWeight member vUnsettled
  simp only [List.mem_cons] at member
  rcases member with same | earlier
  · cases same
    exact False.elim (vUnsettled targetSettled)
  · exact invariant.processedFrontier v edgeWeight earlier vUnsettled

/-- Once the whole outgoing list is processed, the ordinary outer-loop
    invariant has been restored for every settled vertex. -/
theorem finish_relaxation (edge : Edges) (source selected : Int)
    (distance : Int → Int) (settled : Int → Prop) (processed : List (Int × Int))
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (complete : ∀ target weight, edge selected target weight → (target, weight) ∈ processed) :
    SearchInvariant edge source distance settled := by
  refine ⟨invariant.toDistanceInvariant, ?_⟩
  intro u v weight present notSettled connection
  by_cases selectedVertex : u = selected
  · subst u
    exact invariant.processedFrontier v weight (complete v weight connection) notSettled
  · exact invariant.oldFrontier u v weight present selectedVertex notSettled connection

def initialDistances (source : Int) : Int → Int := fun vertex => if vertex = source then 0 else -1

theorem initial_search_invariant (edge : Edges) (source : Int) :
    SearchInvariant edge source (initialDistances source) (fun _ => False) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro _; simp [initialDistances]
  · intro vertex finite
    by_cases same : vertex = source
    · subst vertex
      simpa [initialDistances] using (Path.empty (edge := edge) (source := source))
    · simp [initialDistances, same] at finite
  · intro _ impossible; contradiction
  · intro _ impossible; contradiction
  · intro vertex negative
    by_cases same : vertex = source
    · simp [initialDistances, same] at negative
    · simp [initialDistances, same]
  · intro _ _ _ impossible; contradiction

/-- Queue exhaustion gives the final shortest-path specification. Negative
    results are exactly the canonical `-1` value and exactly the unreachable
    vertices; every finite result is an attained shortest path weight. -/
theorem exhausted_distances_correct (edge : Edges) (source : Int)
    (distance : Int → Int) (settled : Int → Prop)
    (invariant : SearchInvariant edge source distance settled)
    (exhausted : ∀ vertex, ¬ settled vertex → distance vertex < 0) :
    ∀ vertex, (distance vertex = -1 ↔ ∀ cost, ¬ Path edge source vertex cost) ∧
      (0 ≤ distance vertex → IsShortest edge source vertex (distance vertex)) := by
  intro vertex
  refine ⟨?_, ?_⟩
  · constructor
    · intro unknown
      have notSettled : ¬ settled vertex := by
        intro present
        have finite := invariant.settledFinite vertex present
        omega
      exact exhausted_unreachable edge source distance settled invariant.sourceZero invariant.frontier exhausted vertex notSettled
    · intro unreachable
      by_cases finite : 0 ≤ distance vertex
      · exact False.elim (unreachable _ (invariant.witnesses vertex finite))
      · exact invariant.unknown vertex (by omega)
  · intro finite
    have present : settled vertex := by
      by_cases yes : settled vertex
      · exact yes
      · have unknown := exhausted vertex yes
        omega
    exact ⟨invariant.witnesses vertex finite, invariant.settledOptimal vertex present⟩

/-- The two source branches select the expected distance function. -/
theorem relax_distance_improves (distance : Int → Int) (target candidate : Int)
    (better : distance target < 0 ∨ candidate < distance target) :
    relaxDistance distance target candidate = updateDistance distance target candidate := by
  simp [relaxDistance, better]

theorem relax_distance_unchanged (distance : Int → Int) (target candidate : Int)
    (known : 0 ≤ distance target) (bounded : distance target ≤ candidate) :
    relaxDistance distance target candidate = distance := by
  have notBetter : ¬ (distance target < 0 ∨ candidate < distance target) := by omega
  simp [relaxDistance, notBetter]

/-- Pure description of a complete adjacency scan. The execution proof supplies
    its settled/unsettled branches; comparison and update are `relaxDistance`. -/
inductive RelaxScan (settled : Int → Prop) (selected : Int) :
    List (Int × Int) → (Int → Int) → (Int → Int) → Prop where
  | empty (distance : Int → Int) : RelaxScan settled selected [] distance distance
  | skip {target weight : Int} {rest : List (Int × Int)}
      {distance result : Int → Int} : settled target →
      RelaxScan settled selected rest distance result →
      RelaxScan settled selected ((target, weight) :: rest) distance result
  | relax {target weight : Int} {rest : List (Int × Int)}
      {distance result : Int → Int} : ¬ settled target →
      RelaxScan settled selected rest
        (relaxDistance distance target (distance selected + weight)) result →
      RelaxScan settled selected ((target, weight) :: rest) distance result

/-- Settling the selected vertex freezes its own distance throughout the scan. -/
theorem RelaxScan.selected_unchanged (settled : Int → Prop) (selected : Int)
    (edges : List (Int × Int)) (distance result : Int → Int)
    (selectedSettled : settled selected) (scan : RelaxScan settled selected edges distance result) :
    result selected = distance selected := by
  induction scan with
  | empty => rfl
  | skip _ _ tail => exact tail
  | @relax target weight rest distance result unsettled _ tail =>
    rw [tail]
    exact relax_distance_other distance target (distance selected + weight) selected
      (fun same => unsettled (same ▸ selectedSettled))

/-- An entire scan preserves the same local invariant; its processed list gains
    exactly the scanned edges. This theorem is independent of storage layout. -/
theorem RelaxScan.preserves_invariant (edge : Edges) (source selected : Int)
    (settled : Int → Prop) (edges processed : List (Int × Int)) (distance result : Int → Int)
    (nonnegative : NonnegativeEdges edge)
    (actual : ∀ target weight, (target, weight) ∈ edges → edge selected target weight)
    (invariant : RelaxationInvariant edge source distance settled selected processed)
    (scan : RelaxScan settled selected edges distance result) :
    RelaxationInvariant edge source result settled selected (edges.reverse ++ processed) := by
  induction scan generalizing processed with
  | empty => simpa using invariant
  | @skip target weight rest distance result targetSettled tail ih =>
    have next := skip_settled_edge edge source selected target weight distance settled processed
      invariant targetSettled
    have done := ih ((target, weight) :: processed)
      (fun v w member => actual v w (by simp [member])) next
    simpa [List.reverse_cons, List.append_assoc] using done
  | @relax target weight rest distance result targetUnsettled tail ih =>
    have connection := actual target weight (by simp)
    have next := relax_unsettled_edge edge source selected target weight distance settled processed
      invariant connection (nonnegative selected target weight connection) targetUnsettled
    have done := ih ((target, weight) :: processed)
      (fun v w member => actual v w (by simp [member])) next
    simpa [List.reverse_cons, List.append_assoc] using done

/-- Processing the whole outgoing adjacency list restores the ordinary
    outer-loop invariant, ready for the next minimum extraction. -/
theorem RelaxScan.restores_frontier (edge : Edges) (source selected : Int)
    (settled : Int → Prop) (edges : List (Int × Int)) (distance result : Int → Int)
    (nonnegative : NonnegativeEdges edge)
    (represents : ∀ target weight, (target, weight) ∈ edges ↔ edge selected target weight)
    (invariant : RelaxationInvariant edge source distance settled selected [])
    (scan : RelaxScan settled selected edges distance result) :
    SearchInvariant edge source result settled := by
  have done := scan.preserves_invariant edge source selected settled edges [] distance result
    nonnegative (fun target weight member => (represents target weight).mp member) invariant
  apply finish_relaxation edge source selected result settled (edges.reverse ++ []) done
  intro target weight connection
  simpa using (represents target weight).mpr connection

/-- Mathematical scan summaries compose in the same order as source execution. -/
theorem RelaxScan.append {settled : Int → Prop} {selected : Int}
    {first second : List (Int × Int)} {before middle after : Int → Int}
    (one : RelaxScan settled selected first before middle)
    (two : RelaxScan settled selected second middle after) :
    RelaxScan settled selected (first ++ second) before after := by
  induction one with
  | empty => exact two
  | skip already _ rest => exact .skip already (rest two)
  | relax unsettled _ rest => exact .relax unsettled (rest two)

/-- Each result entry is either the unreachable sentinel `-1` or the exact
    weight of a shortest path. Callers need no heap or transcript in this predicate. -/
def ShortestDistances (edge : Edges) (source : Int) (distance : Int → Int) : Prop :=
  ∀ vertex,
    (distance vertex = -1 ↔ ∀ cost, ¬ Path edge source vertex cost) ∧
    (distance vertex ≠ -1 → IsShortest edge source vertex (distance vertex))

/-- A reachable vertex can be used directly as a shortest-path conclusion. -/
theorem ShortestDistances.shortest {edge : Edges} {source vertex : Int} {distance : Int → Int}
    (correct : ShortestDistances edge source distance)
    (reachable : ∃ cost, Path edge source vertex cost) :
    IsShortest edge source vertex (distance vertex) := by
  apply (correct vertex).2
  intro unknown
  obtain ⟨cost, path⟩ := reachable
  exact (correct vertex).1.mp unknown cost path

theorem ShortestDistances.source_zero {edge : Edges} {source : Int} {distance : Int → Int}
    (correct : ShortestDistances edge source distance) (nonnegative : NonnegativeEdges edge) :
    distance source = 0 := by
  have shortest := correct.shortest (vertex := source) ⟨0, Path.empty⟩
  have lower := path_nonnegative edge source source (distance source) nonnegative shortest.1
  have upper := shortest.2 0 Path.empty
  omega

/-- The mathematical specification uniquely determines every output entry. -/
theorem ShortestDistances.unique {edge : Edges} {source : Int} {first second : Int → Int}
    (one : ShortestDistances edge source first) (two : ShortestDistances edge source second) :
    first = second := by
  funext vertex
  by_cases absent : first vertex = -1
  · exact absent.trans ((two vertex).1.mpr ((one vertex).1.mp absent)).symm
  · have firstShortest := (one vertex).2 absent
    have secondShortest := two.shortest ⟨first vertex, firstShortest.1⟩
    have lower := firstShortest.2 _ secondShortest.1
    have upper := secondShortest.2 _ firstShortest.1
    omega

/-- The completed invariant's canonical sentinel removes the nonnegativity
    side condition from the shortest-path interface. -/
theorem shortest_distances_of_canonical (edge : Edges) (source : Int) (distance : Int → Int)
    (canonical : ∀ vertex, distance vertex < 0 → distance vertex = -1)
    (correct : ∀ vertex,
      (distance vertex = -1 ↔ ∀ cost, ¬ Path edge source vertex cost) ∧
      (0 ≤ distance vertex → IsShortest edge source vertex (distance vertex))) :
    ShortestDistances edge source distance := by
  intro vertex
  refine ⟨(correct vertex).1, ?_⟩
  intro known
  apply (correct vertex).2
  by_cases nonnegative : 0 ≤ distance vertex
  · exact nonnegative
  · exact False.elim (known (canonical vertex (by omega)))

/-! Backend-independent queue and complete-loop contracts. -/

/-- The observable queue contains exactly the finite unsettled vertices, with
    their current tentative distances as keys. The backend chooses its storage. -/
def QueueContents (entries : Int → Option Int) (distance : Int → Int)
    (settled : Int → Prop) : Prop :=
  ∀ vertex key, entries vertex = some key ↔
    ¬ settled vertex ∧ distance vertex = key ∧ 0 ≤ key

/-- The selected vertex is unsettled and has a minimum finite tentative distance. -/
structure MinimumSelection (distance : Int → Int) (settled : Int → Prop)
    (selected : Int) : Prop where
  unsettled : ¬ settled selected
  finite : 0 ≤ distance selected
  minimum : ∀ vertex, ¬ settled vertex → 0 ≤ distance vertex →
    distance selected ≤ distance vertex

def Exhausted (distance : Int → Int) (settled : Int → Prop) : Prop :=
  ∀ vertex, ¬ settled vertex → distance vertex < 0

/-- A backend's ordinary minimum-key contract supplies the greedy hypothesis. -/
theorem QueueContents.minimum {entries : Int → Option Int} {distance : Int → Int}
    {settled : Int → Prop} {selected key : Int}
    (contents : QueueContents entries distance settled)
    (present : entries selected = some key)
    (least : ∀ vertex other, entries vertex = some other → key ≤ other) :
    MinimumSelection distance settled selected := by
  obtain ⟨unsettled, selectedKey, finite⟩ := (contents selected key).mp present
  refine ⟨unsettled, by omega, ?_⟩
  intro vertex notSettled nonnegative
  have inQueue := (contents vertex (distance vertex)).mpr ⟨notSettled, rfl, nonnegative⟩
  simpa [selectedKey] using least vertex (distance vertex) inQueue

/-- An empty backend queue supplies the logical stopping condition. -/
theorem QueueContents.exhausted {entries : Int → Option Int} {distance : Int → Int}
    {settled : Int → Prop} (contents : QueueContents entries distance settled)
    (empty : ∀ vertex, entries vertex = none) : Exhausted distance settled := by
  intro vertex unsettled
  by_cases finite : 0 ≤ distance vertex
  · have present := (contents vertex (distance vertex)).mpr ⟨unsettled, rfl, finite⟩
    rw [empty vertex] at present
    contradiction
  · omega

/-- Decreasing or inserting one key matches the corresponding distance update.
    The storage proof supplies the two pointwise update equations. -/
theorem QueueContents.update {entries : Int → Option Int} {distance : Int → Int}
    {settled : Int → Prop} {target candidate : Int}
    (contents : QueueContents entries distance settled)
    (unsettled : ¬ settled target) (nonnegative : 0 ≤ candidate) :
    QueueContents (fun vertex => if vertex = target then some candidate else entries vertex)
      (updateDistance distance target candidate) settled := by
  intro vertex key
  by_cases same : vertex = target
  · subst vertex
    simp [updateDistance, unsettled]
    intro equal
    simpa [equal] using nonnegative
  · simpa [same, updateDistance] using contents vertex key

/-- Deleting the selected key matches settling that vertex; other bindings
    and all distance values are unchanged. -/
theorem QueueContents.remove {entries : Int → Option Int} {distance : Int → Int}
    {settled : Int → Prop} {selected : Int}
    (contents : QueueContents entries distance settled) :
    QueueContents (fun vertex => if vertex = selected then none else entries vertex)
      distance (settleVertex settled selected) := by
  intro vertex key
  by_cases same : vertex = selected
  · subst vertex
    simp [settleVertex]
  · simpa [same, settleVertex] using contents vertex key

/-- A finite logical account of the outer loop, independent of its queue,
    heap, compiler, and transition labels. The list records selected vertices;
    each selection scans its entire adjacency list, then the queue is exhausted.
    A compiled execution must establish this relation before using its theorems. -/
inductive SearchRun (edge : Edges) (adjacency : Adjacency) :
    (Int → Int) → (Int → Prop) → (Int → Int) → List Int → Prop where
  | done (distance : Int → Int) (settled : Int → Prop)
      (exhausted : Exhausted distance settled) :
      SearchRun edge adjacency distance settled distance []
  | select {distance next output : Int → Int} {settled : Int → Prop}
      {selected : Int} {vertices : List Int}
      (minimum : MinimumSelection distance settled selected)
      (represents : ∀ target weight,
        (target, weight) ∈ adjacency selected ↔ edge selected target weight)
      (scan : RelaxScan (settleVertex settled selected) selected
        (adjacency selected) distance next)
      (rest : SearchRun edge adjacency next (settleVertex settled selected) output vertices) :
      SearchRun edge adjacency distance settled output (selected :: vertices)

/-- Queue implementations share the whole greedy correctness argument, not
    only individual path lemmas. Only the execution-to-`SearchRun` proof changes. -/
theorem SearchRun.correct {edge : Edges} {adjacency : Adjacency}
    {distance output : Int → Int} {settled : Int → Prop} {vertices : List Int} {source : Int}
    (execution : SearchRun edge adjacency distance settled output vertices)
    (nonnegative : NonnegativeEdges edge)
    (invariant : SearchInvariant edge source distance settled) :
    ShortestDistances edge source output := by
  induction execution with
  | done distance settled exhausted =>
    exact shortest_distances_of_canonical edge source distance invariant.unknown
      (exhausted_distances_correct edge source distance settled invariant exhausted)
  | @select distance next output settled selected vertices minimum represents scan rest ih =>
    have started := start_relaxation edge source selected distance settled nonnegative invariant
      minimum.unsettled minimum.finite minimum.minimum
    exact ih (scan.restores_frontier edge source selected _ (adjacency selected) distance next
      nonnegative represents started)

/-- Ordinary initialization is sufficient for every conforming queue backend. -/
theorem SearchRun.initial_correct {edge : Edges} {adjacency : Adjacency} {source : Int}
    {output : Int → Int} {vertices : List Int}
    (execution : SearchRun edge adjacency (initialDistances source) (fun _ => False) output vertices)
    (nonnegative : NonnegativeEdges edge) : ShortestDistances edge source output :=
  execution.correct nonnegative (initial_search_invariant edge source)

/-- Later selections never include a vertex already settled at the start. -/
theorem SearchRun.unsettled {edge : Edges} {adjacency : Adjacency}
    {distance output : Int → Int} {settled : Int → Prop} {vertices : List Int}
    (execution : SearchRun edge adjacency distance settled output vertices) :
    ∀ vertex ∈ vertices, ¬ settled vertex := by
  induction execution with
  | done => simp
  | @select distance next output settled selected vertices minimum represents scan rest ih =>
    intro vertex member
    rcases List.mem_cons.mp member with rfl | later
    · exact minimum.unsettled
    · intro already
      exact ih vertex later (Or.inl already)

/-- Every vertex is selected at most once, independently of tie-breaking. -/
theorem SearchRun.distinct {edge : Edges} {adjacency : Adjacency}
    {distance output : Int → Int} {settled : Int → Prop} {vertices : List Int}
    (execution : SearchRun edge adjacency distance settled output vertices) : vertices.Nodup := by
  induction execution with
  | done => exact List.nodup_nil
  | @select distance next output settled selected vertices minimum represents scan rest ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro repeated
    exact rest.unsettled selected repeated (Or.inr rfl)

/-- Backend-independent operation counts: at most one extraction per vertex
    and one scan per adjacency entry, including parallel edges. -/
theorem SearchRun.operation_bounds {edge : Edges} {adjacency : Adjacency}
    {distance output : Int → Int} {settled : Int → Prop} {vertices : List Int} {size : Int}
    (execution : SearchRun edge adjacency distance settled output vertices)
    (bounded : ∀ vertex ∈ vertices, 0 ≤ vertex ∧ vertex < size) :
    vertices.length ≤ size.toNat ∧
      edgeBudget adjacency vertices ≤ edgeBudget adjacency (vertexRange size) := by
  refine ⟨?_, edgeBudget_bound adjacency size vertices execution.distinct bounded⟩
  have included : ∀ vertex ∈ vertices, vertex ∈ vertexRange size := by
    intro vertex member
    exact (vertexRange_member size vertex).mpr (bounded vertex member)
  simpa using nodup_subset_length vertices (vertexRange size) execution.distinct included

end Algo2Lean.Dijkstra
