import Std

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite undirected graph mathematics for Kruskal's algorithm. Edge identities
separate parallel input occurrences. Endpoints and weights are integers; weights
may be negative. This module does not depend on a union-find implementation or
on generated algorithm definitions.
-/

namespace Algo2Lean.Kruskal

structure Edge where
  id : Nat
  source : Int
  target : Int
  weight : Int
  deriving DecidableEq, Repr

/-- One undirected traversal of an edge present in the finite edge list. -/
def Adjacent (edges : List Edge) (u v : Int) : Prop :=
  ∃ edge ∈ edges, (edge.source = u ∧ edge.target = v) ∨
    (edge.source = v ∧ edge.target = u)

/-- Connectivity means existence of a finite undirected walk. -/
inductive Connected (edges : List Edge) : Int → Int → Prop where
  | refl (vertex : Int) : Connected edges vertex vertex
  | step {u v w : Int} : Adjacent edges u v → Connected edges v w → Connected edges u w

theorem Adjacent.symm {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Adjacent edges v u := by
  obtain ⟨e, member, forward | backward⟩ := edge
  · exact ⟨e, member, Or.inr forward⟩
  · exact ⟨e, member, Or.inl backward⟩

theorem Adjacent.connected {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Connected edges u v := .step edge (.refl _)

theorem Connected.trans {edges : List Edge} {u v w : Int}
    (first : Connected edges u v) (second : Connected edges v w) : Connected edges u w := by
  induction first with
  | refl => exact second
  | step edge path ih => exact .step edge (ih second)

theorem Connected.symm {edges : List Edge} {u v : Int} (path : Connected edges u v) :
    Connected edges v u := by
  induction path with
  | refl => exact .refl _
  | step edge path ih => exact ih.trans edge.symm.connected

theorem Connected.mono {before after : List Edge} {u v : Int}
    (subset : ∀ edge ∈ before, edge ∈ after) (path : Connected before u v) :
    Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step edge path ih =>
    obtain ⟨e, member, direction⟩ := edge
    exact .step ⟨e, subset e member, direction⟩ ih

theorem Connected.replace {before after : List Edge} {u v : Int}
    (edges : ∀ edge ∈ before, Connected after edge.source edge.target)
    (path : Connected before u v) : Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step adjacent path ih =>
    obtain ⟨edge, member, forward | backward⟩ := adjacent
    · obtain ⟨rfl, rfl⟩ := forward
      exact (edges edge member).trans ih
    · obtain ⟨rfl, rfl⟩ := backward
      exact (edges edge member).symm.trans ih

@[simp] theorem connected_nil {u v : Int} : Connected [] u v ↔ u = v := by
  constructor
  · intro path
    cases path with
    | refl => rfl
    | step edge _ => obtain ⟨e, member, _⟩ := edge; simp at member
  · intro same; subst v; exact .refl _

theorem edge_connected {edges : List Edge} {edge : Edge} (member : edge ∈ edges) :
    Connected edges edge.source edge.target :=
  Adjacent.connected ⟨edge, member, Or.inl ⟨rfl, rfl⟩⟩

/-- A walk between opposite sides of a cut contains a crossing edge. -/
theorem Connected.crosses_cut {edges : List Edge} {u v : Int} (side : Int → Prop)
    (path : Connected edges u v) (inside : side u) (outside : ¬ side v) :
    ∃ edge ∈ edges,
      (side edge.source ∧ ¬ side edge.target) ∨
      (side edge.target ∧ ¬ side edge.source) := by
  classical
  induction path with
  | refl => exact False.elim (outside inside)
  | @step u next v adjacent rest ih =>
    by_cases same : side next
    · exact ih same outside
    · obtain ⟨edge, member, forward | backward⟩ := adjacent
      · obtain ⟨rfl, rfl⟩ := forward
        exact ⟨edge, member, Or.inl ⟨inside, same⟩⟩
      · obtain ⟨rfl, rfl⟩ := backward
        exact ⟨edge, member, Or.inr ⟨inside, same⟩⟩

/-- An undirected forest is constructed by joining disconnected components.
    List order records an insertion order; no edge joins vertices already linked
    by the remaining edges. Loops and repeated input occurrences are excluded. -/
def Forest : List Edge → Prop
  | [] => True
  | edge :: rest => Forest rest ∧ ¬ Connected rest edge.source edge.target

/-- All selected edges come from the input and preserve exactly its connectivity. -/
structure Spans (input selected : List Edge) : Prop where
  subset : ∀ edge ∈ selected, edge ∈ input
  connected : ∀ u v, Connected input u v → Connected selected u v

/-- Total mathematical weight counts each selected occurrence once. -/
def weight (edges : List Edge) : Int := (edges.map Edge.weight).sum

/-- Minimum weight is compared against every spanning forest of the same input. -/
def MinimumSpanningForest (input selected : List Edge) : Prop :=
  Forest selected ∧ Spans input selected ∧
    ∀ other, Forest other → Spans input other → weight selected ≤ weight other

/-- Input edges may be parallel, looped, or negatively weighted. Distinct ids
    identify occurrences independently of endpoint and weight equality. -/
structure ValidInput (size : Nat) (edges : List Edge) : Prop where
  identities : (edges.map Edge.id).Nodup
  source : ∀ edge ∈ edges, 0 ≤ edge.source ∧ edge.source < size
  target : ∀ edge ∈ edges, 0 ≤ edge.target ∧ edge.target < size

/-- Edges are scanned in nondecreasing weight order. Equal weights are allowed. -/
def Sorted (edges : List Edge) : Prop :=
  edges.Pairwise (fun before after => before.weight ≤ after.weight)

/-- The mathematical scan keeps an edge exactly when it joins two current
    components. A union-find implementation only needs to realize this test. -/
inductive Scan : List Edge → List Edge → List Edge → Prop where
  | done (selected : List Edge) : Scan [] selected selected
  | reject {edge : Edge} {pending selected result : List Edge} :
      Connected selected edge.source edge.target → Scan pending selected result →
      Scan (edge :: pending) selected result
  | accept {edge : Edge} {pending selected result : List Edge} :
      ¬ Connected selected edge.source edge.target → Scan pending (edge :: selected) result →
      Scan (edge :: pending) selected result

theorem Scan.forest {pending selected result : List Edge} (scan : Scan pending selected result)
    (forest : Forest selected) : Forest result := by
  induction scan with
  | done => exact forest
  | reject linked rest ih => exact ih forest
  | accept unlinked rest ih => exact ih ⟨forest, unlinked⟩

theorem Scan.retains {pending selected result : List Edge} (scan : Scan pending selected result) :
    ∀ edge ∈ selected, edge ∈ result := by
  induction scan with
  | done => exact fun _ member => member
  | reject linked rest ih => exact ih
  | accept unlinked rest ih => exact fun edge member => ih edge (by simp [member])

theorem Scan.subset {pending selected result : List Edge} (scan : Scan pending selected result) :
    ∀ edge ∈ result, edge ∈ pending ∨ edge ∈ selected := by
  induction scan with
  | done => exact fun edge member => Or.inr member
  | @reject edge pending selected result linked rest ih =>
    intro candidate member
    rcases ih candidate member with scanned | old
    · exact Or.inl (by simp [scanned])
    · exact Or.inr old
  | @accept edge pending selected result unlinked rest ih =>
    intro candidate member
    rcases ih candidate member with scanned | old
    · exact Or.inl (by simp [scanned])
    · rcases List.mem_cons.mp old with same | old
      · exact Or.inl (by simp [same])
      · exact Or.inr old

theorem Scan.covers {pending selected result : List Edge} (scan : Scan pending selected result) :
    ∀ edge ∈ pending, Connected result edge.source edge.target := by
  induction scan with
  | done => simp
  | @reject edge pending selected result linked rest ih =>
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact linked.mono rest.retains
    · exact ih candidate member
  | @accept edge pending selected result unlinked rest ih =>
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge_connected (rest.retains candidate (by simp))
    · exact ih candidate member

/-- Even without the weight-order hypothesis, the completed scan produces a
    forest with exactly the input's connected components. -/
theorem Scan.spanning_forest {input result : List Edge} (scan : Scan input [] result) :
    Forest result ∧ Spans input result := by
  refine ⟨scan.forest trivial, ?_⟩
  constructor
  · intro edge member
    simpa using scan.subset edge member
  · intro u v path
    exact path.replace scan.covers

/-- There is one component test per scanned occurrence, and at most one
    successful union per occurrence. Union-find and sorting costs are separate. -/
theorem Scan.length_bound {pending selected result : List Edge}
    (scan : Scan pending selected result) : result.length ≤ selected.length + pending.length := by
  induction scan with
  | done => simp
  | reject linked rest ih => simp at *; omega
  | accept unlinked rest ih => simp at *; omega


/-- Adding one edge merges its two components and changes no other component. -/
def Joined (edges : List Edge) (a b u v : Int) : Prop :=
  Connected edges u v ∨
    (Connected edges u a ∧ Connected edges b v) ∨
    (Connected edges u b ∧ Connected edges a v)

theorem Joined.trans {edges : List Edge} {a b u v w : Int}
    (one : Joined edges a b u v) (two : Joined edges a b v w) :
    Joined edges a b u w := by
  rcases one with old | forward | backward
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inl (old.trans oldTwo)
    · exact Or.inr (Or.inl ⟨old.trans forwardTwo.1, forwardTwo.2⟩)
    · exact Or.inr (Or.inr ⟨old.trans backwardTwo.1, backwardTwo.2⟩)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inl ⟨forward.1, forward.2.trans oldTwo⟩)
    · exact Or.inr (Or.inl ⟨forward.1, forwardTwo.2⟩)
    · exact Or.inl (forward.1.trans backwardTwo.2)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inr ⟨backward.1, backward.2.trans oldTwo⟩)
    · exact Or.inl (backward.1.trans forwardTwo.2)
    · exact Or.inr (Or.inr ⟨backward.1, backwardTwo.2⟩)

theorem connected_cons {edge : Edge} {edges : List Edge} {u v : Int} :
    Connected (edge :: edges) u v ↔ Joined edges edge.source edge.target u v := by
  constructor
  · intro path
    induction path with
    | refl => exact Or.inl (.refl _)
    | @step u next v adjacent rest ih =>
      apply Joined.trans (v := next) ?_ ih
      obtain ⟨candidate, member, direction⟩ := adjacent
      rcases List.mem_cons.mp member with rfl | member
      · rcases direction with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _, .refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _, .refl _⟩)
      · exact Or.inl (Adjacent.connected ⟨candidate, member, direction⟩)
  · intro joined
    have lift {x y} (path : Connected edges x y) : Connected (edge :: edges) x y :=
      path.mono (fun _ member => List.mem_cons_of_mem edge member)
    rcases joined with old | forward | backward
    · exact lift old
    · exact (lift forward.1).trans ((edge_connected (by simp)).trans (lift forward.2))
    · exact (lift backward.1).trans ((edge_connected (by simp)).symm.trans (lift backward.2))

/-- An inserted forest edge cannot already occur in the remaining list. -/
theorem Forest.fresh {edge : Edge} {edges : List Edge} (forest : Forest (edge :: edges)) :
    edge ∉ edges := by
  intro member
  exact forest.2 (edge_connected member)

theorem Forest.nodup {edges : List Edge} (forest : Forest edges) : edges.Nodup := by
  induction edges with
  | nil => simp
  | cons edge rest ih => exact List.nodup_cons.mpr ⟨forest.fresh, ih forest.1⟩

/-- Joining different components cannot create an alternate route inside an
    existing component, even after some of that component's edges are removed. -/
theorem disconnected_extension {edge : Edge} {before after : List Edge} {u v : Int}
    (subset : ∀ candidate ∈ after, candidate ∈ before)
    (separate : ¬ Connected before edge.source edge.target)
    (old : Connected before u v) (path : Connected (edge :: after) u v) :
    Connected after u v := by
  rcases connected_cons.mp path with unchanged | forward | backward
  · exact unchanged
  · exact False.elim (separate ((forward.1.mono subset).symm.trans
      (old.trans (forward.2.mono subset).symm)))
  · exact False.elim (separate ((backward.2.mono subset).trans
      (old.symm.trans (backward.1.mono subset))))


/-- Deleting an edge preserves acyclicity. -/
theorem Forest.erase {edges : List Edge} (forest : Forest edges) (removed : Edge) :
    Forest (edges.erase removed) := by
  induction edges with
  | nil => trivial
  | cons edge rest ih =>
    by_cases same : edge = removed
    · subst edge; simpa using forest.1
    · simp only [List.erase_cons, beq_iff_eq, same, ↓reduceIte]
      exact ⟨ih forest.1, fun path => forest.2
        (path.mono (fun _ member => List.mem_of_mem_erase member))⟩

/-- Every edge of a forest is a bridge. -/
theorem Forest.bridge {edges : List Edge} (forest : Forest edges)
    {edge : Edge} (member : edge ∈ edges) :
    ¬ Connected (edges.erase edge) edge.source edge.target := by
  induction edges with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simpa using forest.2
    · have different : first ≠ edge := by intro same; exact forest.fresh (same.symm ▸ member)
      simp only [List.erase_cons, beq_iff_eq, different, ↓reduceIte]
      intro path
      exact ih forest.1 member (disconnected_extension
        (fun _ included => List.mem_of_mem_erase included) forest.2
        (edge_connected member) path)

/-- A forest path can be reconstructed from the edges whose deletion separates
    its endpoints. This avoids choosing a particular list representation of a path. -/
theorem Forest.essential_cover {edges selected : List Edge} (forest : Forest edges)
    {u v : Int} (path : Connected edges u v)
    (contains : ∀ edge ∈ edges, ¬ Connected (edges.erase edge) u v → edge ∈ selected) :
    Connected selected u v := by
  classical
  induction edges generalizing u v with
  | nil => exact connected_nil.mp path ▸ Connected.refl u
  | cons first rest ih =>
    have removed {edge : Edge} (member : edge ∈ rest) :
        (first :: rest).erase edge = first :: rest.erase edge := by
      have different : first ≠ edge := by intro same; exact forest.fresh (same.symm ▸ member)
      simp [different]
    by_cases old : Connected rest u v
    · apply ih forest.1 old
      intro edge member necessary
      apply contains edge (by simp [member])
      rw [removed member]
      intro alternative
      exact necessary (disconnected_extension
        (fun _ included => List.mem_of_mem_erase included) forest.2 old alternative)
    · have join (x y : Int) (left : Connected rest x first.source)
          (right : Connected rest first.target y) (separate : ¬ Connected rest x y)
          (covered : ∀ edge ∈ first :: rest,
            ¬ Connected ((first :: rest).erase edge) x y → edge ∈ selected) :
          Connected selected x y := by
        have selectedFirst : first ∈ selected := covered first (by simp) (by simpa)
        have selectedLeft : Connected selected x first.source := by
          apply ih forest.1 left
          intro edge member necessary
          apply covered edge (by simp [member])
          rw [removed member]
          intro alternative
          rcases connected_cons.mp alternative with unchanged | forward | backward
          · exact separate (unchanged.mono (fun _ included => List.mem_of_mem_erase included))
          · exact necessary forward.1
          · exact forest.2 (left.symm.trans
              (backward.1.mono (fun _ included => List.mem_of_mem_erase included)))
        have selectedRight : Connected selected first.target y := by
          apply ih forest.1 right
          intro edge member necessary
          apply covered edge (by simp [member])
          rw [removed member]
          intro alternative
          rcases connected_cons.mp alternative with unchanged | forward | backward
          · exact separate (unchanged.mono (fun _ included => List.mem_of_mem_erase included))
          · exact necessary forward.2
          · exact forest.2 ((backward.2.mono
              (fun _ included => List.mem_of_mem_erase included)).trans right.symm)
        exact selectedLeft.trans ((edge_connected selectedFirst).trans selectedRight)
      rcases connected_cons.mp path with impossible | forward | backward
      · exact False.elim (old impossible)
      · exact join u v forward.1 forward.2 old contains
      · apply Connected.symm
        apply join v u backward.2.symm backward.1.symm (fun p => old p.symm)
        intro edge member necessary
        exact contains edge member (fun p => necessary p.symm)

/-- If a smaller edge set fails to connect a pair, some essential edge of a
    connecting forest is missing from that set. -/
theorem Forest.missing_bridge {edges selected : List Edge} (forest : Forest edges)
    {u v : Int} (path : Connected edges u v) (separate : ¬ Connected selected u v) :
    ∃ edge ∈ edges, edge ∉ selected ∧ ¬ Connected (edges.erase edge) u v := by
  classical
  apply Classical.byContradiction
  intro absent
  apply separate
  apply forest.essential_cover path
  intro edge member necessary
  apply Classical.byContradiction
  intro missing
  exact absent ⟨edge, member, missing, necessary⟩

/-- Exchanging a bridge on the new edge's path preserves all connected components. -/
theorem exchange_connectivity {edges : List Edge} {added removed : Edge}
    (member : removed ∈ edges) (linked : Connected edges added.source added.target)
    (separate : ¬ Connected (edges.erase removed) added.source added.target) :
    ∀ u v, Connected (added :: edges.erase removed) u v ↔ Connected edges u v := by
  have permutation := List.perm_cons_erase member
  have existing : Connected (removed :: edges.erase removed) added.source added.target :=
    linked.mono (fun _ present => permutation.mem_iff.mp present)
  have removedLinked : Connected (added :: edges.erase removed) removed.source removed.target := by
    have lift {x y} (path : Connected (edges.erase removed) x y) :
        Connected (added :: edges.erase removed) x y :=
      path.mono (fun _ present => List.mem_cons_of_mem added present)
    have addedLinked : Connected (added :: edges.erase removed) added.source added.target :=
      edge_connected (by simp)
    rcases connected_cons.mp existing with impossible | forward | backward
    · exact False.elim (separate impossible)
    · exact (lift forward.1).symm.trans (addedLinked.trans (lift forward.2).symm)
    · exact (lift backward.2).trans (addedLinked.symm.trans (lift backward.1))
  intro u v
  constructor
  · intro path
    apply path.replace
    intro edge present
    rcases List.mem_cons.mp present with rfl | present
    · exact linked
    · exact edge_connected (List.mem_of_mem_erase present)
  · intro path
    apply path.replace
    intro edge present
    by_cases same : edge = removed
    · subst edge; exact removedLinked
    · exact edge_connected (by simp [((List.mem_erase_of_ne same).mpr present)])

/-- The forest exchange lemma: add an edge between different selected
    components and remove a forest-path edge outside the selected set. -/
theorem Forest.exchange {edges selected : List Edge} (forest : Forest edges)
    {added : Edge} (linked : Connected edges added.source added.target)
    (separate : ¬ Connected selected added.source added.target) :
    ∃ removed ∈ edges, removed ∉ selected ∧
      Forest (added :: edges.erase removed) ∧
      (∀ u v, Connected (added :: edges.erase removed) u v ↔ Connected edges u v) := by
  obtain ⟨removed, member, missing, necessary⟩ := forest.missing_bridge linked separate
  exact ⟨removed, member, missing, ⟨forest.erase removed, necessary⟩,
    exchange_connectivity member linked necessary⟩


@[simp] theorem weight_nil : weight [] = 0 := rfl
@[simp] theorem weight_cons (edge : Edge) (edges : List Edge) :
    weight (edge :: edges) = edge.weight + weight edges := by simp [weight]

theorem weight_perm {one two : List Edge} (same : one.Perm two) : weight one = weight two := by
  induction same with
  | nil => rfl
  | cons edge same ih => simp [ih]
  | swap first second rest => simp [Int.add_left_comm]
  | trans first second ihOne ihTwo => exact ihOne.trans ihTwo

theorem weight_erase {edges : List Edge} {edge : Edge} (member : edge ∈ edges) :
    weight edges = edge.weight + weight (edges.erase edge) :=
  (weight_perm (List.perm_cons_erase member)).trans (weight_cons edge _)

/-- A forest edge not in a selected subgraph cannot have its endpoints already
    connected by that subgraph: otherwise it would not be a bridge. -/
theorem Forest.outside_disconnected {edges selected : List Edge} (forest : Forest edges)
    (subset : ∀ edge ∈ selected, edge ∈ edges) {edge : Edge}
    (member : edge ∈ edges) (missing : edge ∉ selected) :
    ¬ Connected selected edge.source edge.target := by
  intro path
  apply forest.bridge member
  apply path.mono
  intro candidate present
  have different : candidate ≠ edge := by intro same; exact missing (same ▸ present)
  exact (List.mem_erase_of_ne different).mpr (subset candidate present)

/-- Forests with exactly the same edge occurrences have the same total weight. -/
theorem Forest.weight_eq {one two : List Edge} (first : Forest one) (second : Forest two)
    (same : ∀ edge, edge ∈ one ↔ edge ∈ two) : weight one = weight two := by
  induction one generalizing two with
  | nil =>
    cases two with
    | nil => rfl
    | cons edge rest => have absent := (same edge).mpr (by simp); simp at absent
  | cons edge rest ih =>
    have present : edge ∈ two := (same edge).mp (by simp)
    have deleted : edge ∉ two.erase edge := by
      intro member
      exact second.bridge present (edge_connected member)
    have remaining : ∀ candidate, candidate ∈ rest ↔ candidate ∈ two.erase edge := by
      intro candidate
      constructor
      · intro member
        have different : candidate ≠ edge := by intro equal; exact first.fresh (equal ▸ member)
        exact (List.mem_erase_of_ne different).mpr ((same candidate).mp (by simp [member]))
      · intro member
        rcases List.mem_cons.mp ((same candidate).mpr (List.mem_of_mem_erase member)) with equal | present
        · exact False.elim (deleted (equal ▸ member))
        · exact present
    rw [weight_cons, weight_erase present, ih first.1 (second.erase edge) remaining]

/-- The exchange argument maintains an arbitrary competitor forest. Its edges
    are either already selected or still pending. Each accepted edge can replace
    an equally heavy or heavier competitor edge, preserving all connectivity. -/
theorem Scan.weight_le {pending selected result : List Edge} (scan : Scan pending selected result)
    (ordered : Sorted pending) (selectedForest : Forest selected)
    (other : List Edge) (otherForest : Forest other)
    (retains : ∀ edge ∈ selected, edge ∈ other)
    (remaining : ∀ edge ∈ other, edge ∈ pending ∨ edge ∈ selected)
    (covers : ∀ edge ∈ pending, Connected other edge.source edge.target) :
    weight result ≤ weight other := by
  classical
  induction scan generalizing other with
  | done selected =>
    have same : ∀ edge, edge ∈ selected ↔ edge ∈ other := by
      intro edge
      exact ⟨retains edge, fun member => by simpa using remaining edge member⟩
    exact Int.le_of_eq (selectedForest.weight_eq otherForest same)
  | @reject edge pending selected result linked rest ih =>
    apply ih (List.pairwise_cons.mp ordered).2 selectedForest other otherForest retains
    · intro candidate member
      rcases remaining candidate member with pendingMember | selectedMember
      · rcases List.mem_cons.mp pendingMember with same | pendingMember
        · by_cases selectedMember : candidate ∈ selected
          · exact Or.inr selectedMember
          · exact False.elim (otherForest.outside_disconnected retains member selectedMember
              (same.symm ▸ linked))
        · exact Or.inl pendingMember
      · exact Or.inr selectedMember
    · exact fun candidate member => covers candidate (by simp [member])
  | @accept edge pending selected result separate rest ih =>
    have selectedNext : Forest (edge :: selected) := ⟨selectedForest, separate⟩
    have tailOrdered : Sorted pending := (List.pairwise_cons.mp ordered).2
    by_cases present : edge ∈ other
    · apply ih tailOrdered selectedNext other otherForest
      · intro candidate member
        rcases List.mem_cons.mp member with same | old
        · exact same ▸ present
        · exact retains candidate old
      · intro candidate member
        rcases remaining candidate member with pendingMember | selectedMember
        · rcases List.mem_cons.mp pendingMember with same | pendingMember
          · exact Or.inr (by simp [same])
          · exact Or.inl pendingMember
        · exact Or.inr (by simp [selectedMember])
      · exact fun candidate member => covers candidate (by simp [member])
    · obtain ⟨removed, removedMember, removedOutside, exchangedForest, connectivity⟩ :=
        otherForest.exchange (covers edge (by simp)) separate
      have removedPending : removed ∈ pending := by
        rcases remaining removed removedMember with waiting | old
        · rcases List.mem_cons.mp waiting with same | waiting
          · exact False.elim (present (same ▸ removedMember))
          · exact waiting
        · exact False.elim (removedOutside old)
      have cheap : edge.weight ≤ removed.weight := (List.pairwise_cons.mp ordered).1 removed removedPending
      have exchangeBound : weight (edge :: other.erase removed) ≤ weight other := by
        rw [weight_cons, weight_erase removedMember]
        omega
      apply Int.le_trans (b := weight (edge :: other.erase removed)) ?_ exchangeBound
      apply ih tailOrdered selectedNext (edge :: other.erase removed) exchangedForest
      · intro candidate member
        rcases List.mem_cons.mp member with same | old
        · exact by simp [same]
        · have different : candidate ≠ removed := by intro same; exact removedOutside (same ▸ old)
          exact List.mem_cons_of_mem edge ((List.mem_erase_of_ne different).mpr (retains candidate old))
      · intro candidate member
        rcases List.mem_cons.mp member with same | old
        · exact Or.inr (by simp [same])
        · rcases remaining candidate (List.mem_of_mem_erase old) with waiting | already
          · rcases List.mem_cons.mp waiting with same | waiting
            · exact Or.inr (by simp [same])
            · exact Or.inl waiting
          · exact Or.inr (by simp [already])
      · intro candidate member
        exact (connectivity _ _).mpr (covers candidate (by simp [member]))

/-- Kruskal's sorted-edge scan returns a minimum spanning forest. The comparison
    is against every spanning forest, and edge weights may be arbitrary integers. -/
theorem Scan.minimum_spanning_forest {input result : List Edge}
    (scan : Scan input [] result) (ordered : Sorted input) :
    MinimumSpanningForest input result := by
  obtain ⟨forest, spanning⟩ := scan.spanning_forest
  refine ⟨forest, spanning, ?_⟩
  intro other otherForest otherSpanning
  apply scan.weight_le ordered trivial other otherForest
  · simp
  · exact fun edge member => Or.inl (otherSpanning.subset edge member)
  · exact fun edge member => otherSpanning.connected _ _ (edge_connected member)


/-- The bridge characterization makes foresthood independent of list order. -/
theorem Forest.of_bridges {edges : List Edge}
    (bridges : ∀ edge ∈ edges, ¬ Connected (edges.erase edge) edge.source edge.target) :
    Forest edges := by
  induction edges with
  | nil => trivial
  | cons first rest ih =>
    have separate : ¬ Connected rest first.source first.target := by
      simpa using bridges first (by simp)
    refine ⟨ih ?_, separate⟩
    intro edge member path
    have different : first ≠ edge := by
      intro same
      exact separate (same.symm ▸ edge_connected member)
    apply bridges edge (by simp [member])
    simp only [List.erase_cons, beq_iff_eq, different, ↓reduceIte]
    exact path.mono (fun _ present => List.mem_cons_of_mem first present)

theorem Forest.perm {before after : List Edge} (forest : Forest before)
    (same : before.Perm after) : Forest after := by
  apply Forest.of_bridges
  intro edge member path
  apply forest.bridge (same.mem_iff.mpr member)
  exact path.mono (fun _ present => (same.erase edge).mem_iff.mpr present)

/-- Reordering input occurrences changes neither connectivity nor spanning. -/
theorem Spans.perm_input {before after selected : List Edge} (spanning : Spans before selected)
    (same : before.Perm after) : Spans after selected := by
  constructor
  · exact fun edge member => same.mem_iff.mp (spanning.subset edge member)
  · exact fun u v path => spanning.connected u v
      (path.mono (fun _ member => same.mem_iff.mpr member))

theorem MinimumSpanningForest.perm_input {before after selected : List Edge}
    (minimum : MinimumSpanningForest before selected) (same : before.Perm after) :
    MinimumSpanningForest after selected :=
  ⟨minimum.1, minimum.2.1.perm_input same,
    fun other forest spanning => minimum.2.2 other forest (spanning.perm_input same.symm)⟩

/-- Sorting may permute edge occurrences freely, including equal-weight edges.
    The result remains a minimum spanning forest of the original input. -/
theorem Scan.minimum_of_perm {input sorted result : List Edge}
    (permutation : input.Perm sorted) (ordered : Sorted sorted)
    (scan : Scan sorted [] result) : MinimumSpanningForest input result :=
  (scan.minimum_spanning_forest ordered).perm_input permutation.symm

/-- A forest may be presented in output order rather than reverse insertion order. -/
theorem MinimumSpanningForest.perm_result {input before after : List Edge}
    (minimum : MinimumSpanningForest input before) (same : before.Perm after) :
    MinimumSpanningForest input after := by
  refine ⟨minimum.1.perm same, ⟨?_, ?_⟩, ?_⟩
  · exact fun edge member => minimum.2.1.subset edge (same.mem_iff.mpr member)
  · exact fun u v path => (minimum.2.1.connected u v path).mono
      (fun _ member => same.mem_iff.mp member)
  · intro other forest spanning
    rw [← weight_perm same]
    exact minimum.2.2 other forest spanning

/-- Every finite input admits a completed mathematical scan. No assumption of
    successful termination is hidden inside the minimum-forest statement. -/
theorem scan_exists (input selected : List Edge) : ∃ result, Scan input selected result := by
  classical
  induction input generalizing selected with
  | nil => exact ⟨selected, .done selected⟩
  | cons edge rest ih =>
    by_cases linked : Connected selected edge.source edge.target
    · obtain ⟨result, scan⟩ := ih selected
      exact ⟨result, .reject linked scan⟩
    · obtain ⟨result, scan⟩ := ih (edge :: selected)
      exact ⟨result, .accept linked scan⟩

theorem minimum_spanning_forest_exists {input : List Edge} (ordered : Sorted input) :
    ∃ result, Scan input [] result ∧ MinimumSpanningForest input result := by
  obtain ⟨result, scan⟩ := scan_exists input []
  exact ⟨result, scan, scan.minimum_spanning_forest ordered⟩

/-- Connectivity includes all declared vertices, including isolated vertices. -/
def ConnectedOn (size : Nat) (edges : List Edge) : Prop :=
  ∀ u v, 0 ≤ u → u < size → 0 ≤ v → v < size → Connected edges u v

/-- On a nonempty connected input graph, a minimum spanning forest is a minimum
    spanning tree. The vertex range is explicit so isolated vertices are not lost. -/
def MinimumSpanningTree (size : Nat) (input selected : List Edge) : Prop :=
  0 < size ∧ ValidInput size input ∧
    MinimumSpanningForest input selected ∧ ConnectedOn size selected

theorem MinimumSpanningForest.tree {size : Nat} {input selected : List Edge}
    (minimum : MinimumSpanningForest input selected) (nonempty : 0 < size)
    (valid : ValidInput size input) (connected : ConnectedOn size input) :
    MinimumSpanningTree size input selected := by
  refine ⟨nonempty, valid, minimum, ?_⟩
  intro u v uLower uUpper vLower vUpper
  exact minimum.2.1.connected u v (connected u v uLower uUpper vLower vUpper)

theorem Scan.minimum_spanning_tree {size : Nat} {input sorted result : List Edge}
    (nonempty : 0 < size) (valid : ValidInput size input) (connected : ConnectedOn size input)
    (permutation : input.Perm sorted) (ordered : Sorted sorted) (scan : Scan sorted [] result) :
    MinimumSpanningTree size input result :=
  (scan.minimum_of_perm permutation ordered).tree nonempty valid connected

end Algo2Lean.Kruskal
