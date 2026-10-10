import Algo2LeanLib.FibonacciStorage

namespace Algo2Lean.Fibonacci

/-- Detach the cursor root, keeping the remaining root ring as pending work. -/
def Snapshot.detachMinimum (state : Snapshot) : Snapshot :=
  {state with
    left := Rings.removeLeft state.left state.right state.minimum
    right := Rings.removeRight state.left state.right state.minimum
    minimum := if state.right state.minimum = state.minimum then -1 else state.right state.minimum}

theorem SplitRepresented.pending_parent {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {vertex : Int}
    (member : vertex ∈ pending.map Node.vertex) : state.parents vertex = -1 := by
  obtain ⟨root, inPending, same⟩ := List.mem_map.mp member
  exact same ▸ (represented.stored root (by simp [inPending])).root_parent

theorem SplitRepresented.detach_stored {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (root : Node) (member : root ∈ pending ++ detached)
    (cursor : state.minimum ∈ pending.map Node.vertex) :
    Stored state.detachMinimum (-1) root := by
  have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
    rcases represented.pendingRing with empty | ring
    · simp [empty] at cursor
    · exact ring
  obtain ⟨leftMember, rightMember⟩ := ring.neighbors cursor
  apply (represented.stored root member).frame_roots
  · intro vertex key inside
    exact represented.nonnegative vertex key (List.mem_flatMap.mpr ⟨root, member, inside⟩)
  · intro vertex key inside
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro vertex present nonroot
    have different (other : Int) (inside : other ∈ pending.map Node.vertex) : vertex ≠ other := by
      intro same
      have rootParent := represented.pending_parent inside
      rw [same, rootParent] at nonroot
      omega
    constructor
    · simp only [Snapshot.detachMinimum, Rings.removeLeft, Rings.write]
      rw [if_neg (different _ cursor), if_neg (different _ rightMember)]
    · simp only [Snapshot.detachMinimum, Rings.removeRight, Rings.write]
      rw [if_neg (different _ cursor), if_neg (different _ leftMember)]

/-- Detachment preserves every other detached root's self-ring. -/
theorem SplitRepresented.detach_singletons {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached)
    (cursor : state.minimum ∈ pending.map Node.vertex) (root : Node) (member : root ∈ detached) :
    state.detachMinimum.left root.vertex = root.vertex ∧
      state.detachMinimum.right root.vertex = root.vertex := by
  have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
    rcases represented.pendingRing with empty | ring
    · simp [empty] at cursor
    · exact ring
  obtain ⟨leftMember, rightMember⟩ := ring.neighbors cursor
  have separate (vertex : Int) (inside : vertex ∈ pending.map Node.vertex) : root.vertex ≠ vertex := by
    intro same
    apply represented.valid.1.roots_disjoint vertex inside
    apply List.mem_map.mpr
    exact ⟨(root.vertex, root.key), List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩, same⟩
  constructor
  · simpa only [Snapshot.detachMinimum, Rings.removeLeft, Rings.write,
      if_neg (separate _ cursor), if_neg (separate _ rightMember)] using
      (represented.detachedRings root member).1
  · simpa only [Snapshot.detachMinimum, Rings.removeRight, Rings.write,
      if_neg (separate _ cursor), if_neg (separate _ leftMember)] using
      (represented.detachedRings root member).2

/-- Moving the displayed cursor root to detached storage strictly shrinks
    the finite pending list without changing contents or tree invariants. -/
theorem SplitRepresented.detach_head {state : Snapshot} {root : Node} {pending detached : Forest}
    (represented : SplitRepresented state (root :: pending) detached) (cursor : state.minimum = root.vertex) :
    SplitRepresented state.detachMinimum pending (root :: detached) := by
  have permutation : (pending ++ root :: detached).Perm ((root :: pending) ++ detached) := by
    simpa only [List.cons_append] using (List.perm_middle (a := root) (l₁ := pending) (l₂ := detached))
  have contents := permutation.flatMap_right Node.entries
  have ring : Rings.Ring state.left state.right (root.vertex :: pending.map Node.vertex) := by
    rcases represented.pendingRing with empty | ring
    · simp at empty
    · exact ring
  have member : state.minimum ∈ (root :: pending).map Node.vertex := by simp [cursor]
  refine ⟨represented.valid.perm permutation, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro other inForest
    exact represented.detach_stored other (permutation.mem_iff.mp inForest) member
  · simpa only [Snapshot.detachMinimum, cursor] using ring.remove_head
  · intro other inDetached
    rcases List.mem_cons.mp inDetached with rfl | old
    · simp [Snapshot.detachMinimum, cursor, Rings.removeLeft, Rings.removeRight]
    · exact represented.detach_singletons member other old
  · intro vertex key inside
    exact represented.nonnegative vertex key (contents.mem_iff.mp inside)
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · cases pending with
    | nil =>
      left
      refine ⟨rfl, ?_⟩
      have self : state.right root.vertex = root.vertex := by
        obtain ⟨last, chain, forward, backward⟩ := ring.open_head
        cases chain with
        | singleton => exact forward
        | cons _ _ _ rest =>
          have impossible := rest.first_mem
          simp at impossible
      simp [Snapshot.detachMinimum, cursor, self]
    | cons first rest =>
      right
      refine ⟨first, by simp, ?_⟩
      have next : state.right root.vertex = first.vertex := by
        obtain ⟨last, chain, forward, backward⟩ := ring.open_head
        cases chain with
        | cons _ edge _ chain =>
          obtain ⟨tail, equal⟩ := chain.head
          simp only [List.map_cons, List.cons.injEq] at equal
          exact edge.trans equal.1.symm
      have different : first.vertex ≠ root.vertex := by
        intro same
        exact (List.nodup_cons.mp ring.unique).1 (by simp [same])
      simp [Snapshot.detachMinimum, cursor, next, different]

/-- The detached list is ghost bookkeeping: all its roots have self-rings. -/
theorem SplitRepresented.perm_detached {state : Snapshot} {pending before after : Forest}
    (represented : SplitRepresented state pending before) (permutation : after.Perm before) :
    SplitRepresented state pending after := by
  have whole := permutation.append_left pending
  have contents := whole.flatMap_right Node.entries
  refine ⟨represented.valid.perm whole, ?_, represented.pendingRing, ?_, ?_, ?_, ?_, represented.cursor⟩
  · intro root member
    exact represented.stored root (whole.mem_iff.mp member)
  · intro root member
    exact represented.detachedRings root (permutation.mem_iff.mp member)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)

/-- Pending root lists may be rotated to expose the actual cursor. -/
theorem SplitRepresented.rotate_pending {state : Snapshot} {front back detached : Forest}
    (represented : SplitRepresented state (front ++ back) detached) :
    SplitRepresented state (back ++ front) detached := by
  have rotation : (back ++ front).Perm (front ++ back) := List.perm_append_comm
  have whole := rotation.append_right detached
  have contents := whole.flatMap_right Node.entries
  refine ⟨represented.valid.perm whole, ?_, ?_, represented.detachedRings, ?_, ?_, ?_, ?_⟩
  · intro root member
    exact represented.stored root (whole.mem_iff.mp member)
  · simpa only [List.map_append] using Rings.RingOrEmpty.rotate_append
      (front.map Node.vertex) (back.map Node.vertex) (by simpa only [List.map_append] using represented.pendingRing)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · rcases represented.cursor with ⟨empty, pointer⟩ | ⟨root, member, pointer⟩
    · left
      exact ⟨by simpa only [List.append_eq_nil_iff, and_comm] using empty, pointer⟩
    · exact Or.inr ⟨root, rotation.mem_iff.mpr member, pointer⟩

/-- Updating scratch buckets changes no represented node or pending pointer. -/
theorem SplitRepresented.table_write {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (degree vertex : Int) :
    SplitRepresented {state with table := Rings.write state.table degree vertex} pending detached := by
  refine ⟨represented.valid, ?_, represented.pendingRing, represented.detachedRings,
    represented.nonnegative, represented.presence, represented.size, represented.cursor⟩
  intro root member
  apply (represented.stored root member).frame
  · intros; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩


/-- Finite ghost contents of the scratch table, with exactly one root per degree. -/
structure Buckets (state : Snapshot) (roots : Forest) : Prop where
  unique : (roots.map Node.degree).Nodup
  read : ∀ root ∈ roots, state.table root.degree = root.vertex
  complete : ∀ degree, 0 ≤ state.table degree →
    ∃ root ∈ roots, (root.degree : Int) = degree ∧ root.vertex = state.table degree
  nonnegative : ∀ root ∈ roots, 0 ≤ root.vertex

theorem Buckets.empty {state : Snapshot} (empty : ∀ degree, state.table degree < 0) :
    Buckets state [] := by
  refine ⟨by simp, by simp, ?_, by simp⟩
  intro degree occupied
  have negative := empty degree
  omega

theorem Buckets.perm {state : Snapshot} {before after : Forest} (buckets : Buckets state before)
    (permutation : after.Perm before) : Buckets state after := by
  refine ⟨(permutation.map Node.degree).nodup_iff.mpr buckets.unique, ?_, ?_, ?_⟩
  · intro root member
    exact buckets.read root (permutation.mem_iff.mp member)
  · intro degree occupied
    obtain ⟨root, member, same, read⟩ := buckets.complete degree occupied
    exact ⟨root, permutation.mem_iff.mpr member, same, read⟩
  · intro root member
    exact buckets.nonnegative root (permutation.mem_iff.mp member)

theorem Buckets.congr {before after : Snapshot} {roots : Forest} (buckets : Buckets before roots)
    (same : after.table = before.table) : Buckets after roots := by
  refine ⟨buckets.unique, ?_, ?_, buckets.nonnegative⟩
  · intro root member
    simpa only [same] using buckets.read root member
  · intro degree occupied
    simpa only [same] using buckets.complete degree (same ▸ occupied)

/-- Clearing the selected bucket removes exactly its root from scratch storage. -/
theorem Buckets.remove_head {state : Snapshot} {root : Node} {rest : Forest}
    (buckets : Buckets state (root :: rest)) :
    Buckets {state with table := Rings.write state.table root.degree (-1)} rest := by
  have separate := (List.nodup_cons.mp buckets.unique).1
  refine ⟨(List.nodup_cons.mp buckets.unique).2, ?_, ?_, ?_⟩
  · intro other member
    have different : (other.degree : Int) ≠ root.degree := by
      intro same
      have equal : other.degree = root.degree := by omega
      exact separate (List.mem_map.mpr ⟨other, member, equal⟩)
    simpa only [Rings.write, if_neg different] using buckets.read other (by simp [member])
  · intro degree occupied
    have different : degree ≠ root.degree := by
      intro same
      simp [Rings.write, same] at occupied
    change 0 ≤ Rings.write state.table root.degree (-1) degree at occupied
    rw [Rings.write, if_neg different] at occupied
    obtain ⟨other, member, readDegree, readVertex⟩ := buckets.complete degree occupied
    rcases List.mem_cons.mp member with rfl | tail
    · exact False.elim (different readDegree.symm)
    · exact ⟨other, tail, readDegree, by simpa only [Rings.write, if_neg different] using readVertex⟩
  · intro other member
    exact buckets.nonnegative other (by simp [member])

/-- An empty bucket accepts a root and preserves degree uniqueness. -/
theorem Buckets.insert {state : Snapshot} {roots : Forest} (buckets : Buckets state roots)
    (root : Node) (nonnegative : 0 ≤ root.vertex) (empty : state.table root.degree < 0) :
    Buckets {state with table := Rings.write state.table root.degree root.vertex} (root :: roots) := by
  have fresh : root.degree ∉ roots.map Node.degree := by
    rintro member
    obtain ⟨other, member, same⟩ := List.mem_map.mp member
    have read := buckets.read other member
    have positive := buckets.nonnegative other member
    rw [same] at read
    omega
  refine ⟨List.nodup_cons.mpr ⟨fresh, buckets.unique⟩, ?_, ?_, ?_⟩
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · simp [Rings.write]
    · have different : (other.degree : Int) ≠ root.degree := by
        intro same
        have equal : other.degree = root.degree := by omega
        exact fresh (List.mem_map.mpr ⟨other, member, equal⟩)
      simpa only [Rings.write, if_neg different] using buckets.read other member
  · intro degree occupied
    by_cases same : degree = root.degree
    · refine ⟨root, by simp, same.symm, ?_⟩
      simp [Rings.write, same]
    · change 0 ≤ Rings.write state.table root.degree root.vertex degree at occupied
      rw [Rings.write, if_neg same] at occupied
      obtain ⟨other, member, readDegree, readVertex⟩ := buckets.complete degree occupied
      exact ⟨other, by simp [member], readDegree, by simpa only [Rings.write, if_neg same] using readVertex⟩
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact nonnegative
    · exact buckets.nonnegative other member

/-- An occupied degree identifies a root that can be moved to the head of the
    detached list without affecting the physical forest. -/
theorem Buckets.find {state : Snapshot} {roots : Forest} (buckets : Buckets state roots)
    (degree : Int) (occupied : 0 ≤ state.table degree) :
    ∃ root rest, (root :: rest).Perm roots ∧ (root.degree : Int) = degree ∧
      root.vertex = state.table degree ∧ roots.length = rest.length + 1 := by
  obtain ⟨root, member, same, pointer⟩ := buckets.complete degree occupied
  obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
  refine ⟨root, front ++ back, ?_, same, pointer, ?_⟩
  · rw [located]
    exact List.perm_middle.symm
  · simp [located, Nat.add_assoc]

/-- All occupied buckets have degrees of actual finite ranked trees. -/
theorem Buckets.degree_bound {state : Snapshot} {pending roots : Forest}
    (represented : SplitRepresented state pending roots) (buckets : Buckets state roots)
    (degree : Int) (occupied : 0 ≤ state.table degree) :
    degree ≤ 2 * (Forest.entries (pending ++ roots)).length.log2 + 1 := by
  obtain ⟨root, member, same, _⟩ := buckets.complete degree occupied
  have included : root.entries.length ≤ (Forest.entries (pending ++ roots)).length := by
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp (show root ∈ pending ++ roots by simp [member])
    rw [located]
    simp [Forest.entries, List.flatMap_append]
    omega
  have ranked := represented.valid.2.2.1 root (by simp [member])
  have bound := ranked.shape_ranked.degree_bound_of_size
    (by simpa only [Node.shape_size] using included)
  simp only [Node.shape_degree] at bound
  omega



theorem Forest.marks_perm {before after : Forest} (permutation : after.Perm before) :
    after.marks = before.marks := by
  unfold Forest.marks
  exact (permutation.map Node.marks).sum_nat

theorem Forest.link_marks {pending rest : Forest} {parent child : Node}
    (unmarked : child.marked = false) :
    (pending ++ parent.link child :: rest).marks = (pending ++ parent :: child :: rest).marks := by
  have linked : (parent.link child).marks = parent.marks + child.marks := by
    simpa only [unmarked, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using parent.link_marks child
  simp only [Forest.marks, List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, linked]
  omega
theorem Forest.entries_perm {before after : Forest} (permutation : after.Perm before) :
    after.entries.Perm before.entries := by
  exact List.Perm.flatMap_right Node.entries permutation

theorem Forest.link_entries {pending rest : Forest} {parent child : Node} :
    (pending ++ parent.link child :: rest).entries.Perm
      (pending ++ parent :: child :: rest).entries := by
  simpa only [Forest.entries, List.flatMap_append, List.flatMap_cons, List.append_assoc] using
    (parent.link_entries child).append_right rest.entries |>.append_left pending.entries

/-- The exact array operation for a degree-table collision; clocks are separate. -/
def Snapshot.collision (state : Snapshot) (vertex degree : Int) : Snapshot :=
  let other := state.table degree
  let cleared := {state with table := Rings.write state.table degree (-1)}
  if state.keys other < state.keys vertex then cleared.link vertex other
  else cleared.link other vertex

def Snapshot.collisionParent (state : Snapshot) (vertex degree : Int) : Int :=
  if state.keys (state.table degree) < state.keys vertex then state.table degree else vertex

@[simp] theorem Node.link_vertex (parent child : Node) : (parent.link child).vertex = parent.vertex := rfl
@[simp] theorem Node.link_degree (parent child : Node) : (parent.link child).degree = parent.degree + 1 := rfl

/-- One occupied bucket is consumed and one tree degree increases. The pending
    root ring and complete ranked forest are preserved by the actual writes. -/
theorem SplitRepresented.collide {state : Snapshot} {pending buckets : Forest} {current : Node}
    (represented : SplitRepresented state pending (current :: buckets))
    (table : Buckets state buckets) (occupied : 0 ≤ state.table current.degree) :
    ∃ result remaining,
      SplitRepresented (state.collision current.vertex current.degree) pending (result :: remaining) ∧
      Buckets (state.collision current.vertex current.degree) remaining ∧
      result.vertex = state.collisionParent current.vertex current.degree ∧
      result.degree = current.degree + 1 ∧ buckets.length = remaining.length + 1 ∧
      (pending ++ result :: remaining).entries.Perm (pending ++ current :: buckets).entries ∧
      (pending ++ result :: remaining).marks = (pending ++ current :: buckets).marks := by
  obtain ⟨other, remaining, permutation, equalDegree, pointer, shorter⟩ := table.find current.degree occupied
  have degrees : other.degree = current.degree := by omega
  have arranged := (permutation.cons current).append_left pending
  have ordered := represented.perm_detached (permutation.cons current)
  have otherTable := table.perm permutation
  have cleared := ordered.table_write current.degree (-1)
  have currentStored := ordered.stored current (by simp)
  have otherStored := ordered.stored other (by simp)
  have currentKey := currentStored.root_key
  have otherKey := otherStored.root_key
  have reduced : Buckets {state with table := Rings.write state.table current.degree (-1)} remaining := by
    simpa only [degrees] using otherTable.remove_head
  by_cases smaller : other.key < current.key
  · have switched := cleared.perm_detached (List.Perm.swap current other remaining)
    have linked := switched.link (Int.le_of_lt smaller) degrees
    refine ⟨other.link current, remaining, ?_, ?_, ?_, ?_, shorter, ?_, ?_⟩
    · simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using linked
    · have carried := reduced.congr (after :=
        ({state with table := Rings.write state.table current.degree (-1)} : Snapshot).link current.vertex other.vertex) rfl
      simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using carried
    · simp only [Node.link_vertex, Snapshot.collisionParent, ← pointer, currentKey, otherKey, smaller, ↓reduceIte]
    · simp [degrees]
    · exact Forest.link_entries.trans (Forest.entries_perm
        (((List.Perm.swap current other remaining).append_left pending).trans arranged))
    · exact (Forest.link_marks (ordered.valid.2.2.2 current (by simp))).trans
        (Forest.marks_perm (((List.Perm.swap current other remaining).append_left pending).trans arranged))
  · have winner : current.key ≤ other.key := by omega
    have linked := cleared.link winner degrees.symm
    refine ⟨current.link other, remaining, ?_, ?_, ?_, by simp, shorter, ?_, ?_⟩
    · simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using linked
    · have carried := reduced.congr (after :=
        ({state with table := Rings.write state.table current.degree (-1)} : Snapshot).link other.vertex current.vertex) rfl
      simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using carried
    · simp only [Node.link_vertex, Snapshot.collisionParent, ← pointer, currentKey, otherKey, smaller, ↓reduceIte]
    · exact Forest.link_entries.trans (Forest.entries_perm arranged)
    · exact (Forest.link_marks (ordered.valid.2.2.2 other (by simp))).trans (Forest.marks_perm arranged)

/-- A trace of scratch-table collisions records only exact local array effects. -/
inductive BucketCollisions : Snapshot → Int → Int → Snapshot → Int → Int → Nat → Prop where
  | done (state : Snapshot) (vertex degree : Int) (empty : state.table degree < 0) :
      BucketCollisions state vertex degree state vertex degree 0
  | step {state after : Snapshot} {vertex degree result finalDegree : Int} {links : Nat}
      (occupied : 0 ≤ state.table degree)
      (rest : BucketCollisions (state.collision vertex degree) (state.collisionParent vertex degree)
        (degree + 1) after result finalDegree links) :
      BucketCollisions state vertex degree after result finalDegree (links + 1)


/-- The actual collision loop terminates because every link consumes one
    occupied bucket. No external bound or pre-supplied collision trace is needed. -/
theorem SplitRepresented.resolve_collisions {state : Snapshot} {pending buckets : Forest} {current : Node}
    (represented : SplitRepresented state pending (current :: buckets))
    (table : Buckets state buckets) :
    ∃ after result remaining links,
      BucketCollisions state current.vertex current.degree after result.vertex result.degree links ∧
      SplitRepresented after pending (result :: remaining) ∧ Buckets after remaining ∧
      after.table result.degree < 0 ∧ links + remaining.length = buckets.length ∧
      (pending ++ result :: remaining).entries.Perm (pending ++ current :: buckets).entries ∧
      (pending ++ result :: remaining).marks = (pending ++ current :: buckets).marks := by
  have terminate : ∀ count : Nat, ∀ state current buckets,
      buckets.length = count → SplitRepresented state pending (current :: buckets) → Buckets state buckets →
      ∃ after result remaining links,
        BucketCollisions state current.vertex current.degree after result.vertex result.degree links ∧
        SplitRepresented after pending (result :: remaining) ∧ Buckets after remaining ∧
        after.table result.degree < 0 ∧ links + remaining.length = buckets.length ∧
        (pending ++ result :: remaining).entries.Perm (pending ++ current :: buckets).entries ∧
        (pending ++ result :: remaining).marks = (pending ++ current :: buckets).marks := by
    intro count
    induction count using Nat.strongRecOn with
    | ind count ih =>
      intro before root entries size valid table
      by_cases empty : before.table root.degree < 0
      · exact ⟨before, root, entries, 0, .done _ _ _ empty, valid, table, empty, by simp, .refl _, rfl⟩
      have occupied : 0 ≤ before.table root.degree := by omega
      obtain ⟨next, rest, represented, nextTable, vertex, degree, shorter, stepEntries, stepMarks⟩ := valid.collide table occupied
      have smaller : rest.length < count := by omega
      obtain ⟨after, result, remaining, links, execution, finalValid, finalTable, unused, accounted, tailEntries, tailMarks⟩ :=
        ih rest.length smaller (before.collision root.vertex root.degree) next rest rfl represented nextTable
      refine ⟨after, result, remaining, links + 1, ?_, finalValid, finalTable, unused, by omega, tailEntries.trans stepEntries, tailMarks.trans stepMarks⟩
      apply BucketCollisions.step occupied
      simpa only [vertex, degree, Int.natCast_add, Int.natCast_one] using execution
  exact terminate buckets.length state current buckets rfl represented table



/-- The highest encountered degree bounds all occupied scratch buckets. -/
def ScratchBound (state : Snapshot) (maximum : Int) : Prop :=
  ∀ degree, maximum < degree → state.table degree < 0

@[simp] theorem Snapshot.collision_table (state : Snapshot) (vertex degree : Int) :
    (state.collision vertex degree).table = Rings.write state.table degree (-1) := by
  unfold Snapshot.collision
  dsimp only
  split <;> rfl

@[simp] theorem Snapshot.collision_size (state : Snapshot) (vertex degree : Int) :
    (state.collision vertex degree).size = state.size := by
  unfold Snapshot.collision
  dsimp only
  split <;> rfl

theorem ScratchBound.collision {state : Snapshot} {maximum : Int} (bound : ScratchBound state maximum)
    (vertex degree : Int) : ScratchBound (state.collision vertex degree) maximum := by
  intro index above
  rw [Snapshot.collision_table]
  unfold Rings.write
  split
  · omega
  · exact bound index above

theorem BucketCollisions.size {before after : Snapshot} {vertex degree result finalDegree : Int} {links : Nat}
    (execution : BucketCollisions before vertex degree after result finalDegree links) : after.size = before.size := by
  induction execution with
  | done => rfl
  | step occupied rest ih => exact ih.trans (Snapshot.collision_size _ _ _)

theorem BucketCollisions.scratch_bound {before after : Snapshot} {vertex degree result finalDegree maximum : Int} {links : Nat}
    (execution : BucketCollisions before vertex degree after result finalDegree links)
    (bound : ScratchBound before maximum) : ScratchBound after maximum := by
  induction execution with
  | done => exact bound
  | step occupied rest ih => exact ih (bound.collision _ _)

theorem ScratchBound.store {state : Snapshot} {maximum : Int} (bound : ScratchBound state maximum)
    (vertex degree : Int) :
    ScratchBound {state with table := Rings.write state.table degree vertex} (max maximum degree) := by
  intro index above
  have different : index ≠ degree := by omega
  simpa only [Rings.write, if_neg different] using bound index (by omega)

/-- A common finite size bounds every current tree, including trees produced
    during consolidation rather than only the final degree buckets. -/
theorem SplitRepresented.degree_bound {state : Snapshot} {pending detached : Forest} {root : Node}
    (represented : SplitRepresented state pending detached) (member : root ∈ pending ++ detached)
    (size : Nat) (readSize : state.size = size) : root.degree ≤ 2 * size.log2 + 1 := by
  have included : root.entries.length ≤ (Forest.entries (pending ++ detached)).length := by
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    rw [located]
    simp [Forest.entries, List.flatMap_append]
    omega
  have length : (Forest.entries (pending ++ detached)).length = size := by
    have storedSize := represented.size
    omega
  have ranked := represented.valid.2.2.1 root member
  have bound := ranked.shape_ranked.degree_bound_of_size
    (by simpa only [Node.shape_size, length] using included)
  simpa only [Node.shape_degree] using bound

/-- Finite execution of the pending-root phase, expressed through the exact
    snapshot mutations and the independently verified collision phase. -/
inductive RootConsumption : Snapshot → Int → Snapshot → Int → Nat → Nat → Prop where
  | done (state : Snapshot) (maximum : Int) (empty : state.minimum < 0) :
      RootConsumption state maximum state maximum 0 0
  | step {before merged after : Snapshot} {maximum vertex degree finalMaximum : Int}
      {links roots tailLinks : Nat} (nonempty : 0 ≤ before.minimum)
      (collisions : BucketCollisions before.detachMinimum before.minimum
        (before.detachMinimum.degrees before.minimum) merged vertex degree links)
      (rest : RootConsumption {merged with table := Rings.write merged.table degree vertex}
        (max maximum degree) after finalMaximum roots tailLinks) :
      RootConsumption before maximum after finalMaximum (roots + 1) (links + tailLinks)

/-- Starting from a finite represented pending forest and exact scratch table,
    every pending root is consumed once. All final roots have distinct degrees,
    the largest encountered degree is logarithmic, and links reduce root count. -/
theorem SplitRepresented.consume_roots {state : Snapshot} {pending buckets : Forest}
    (represented : SplitRepresented state pending buckets) (table : Buckets state buckets)
    (maximum : Int) (bound : ScratchBound state maximum) (size : Nat) (readSize : state.size = size)
    (maximumBound : maximum ≤ 2 * size.log2 + 1) :
    ∃ after finalBuckets finalMaximum links,
      RootConsumption state maximum after finalMaximum pending.length links ∧
      SplitRepresented after [] finalBuckets ∧ Buckets after finalBuckets ∧
      ScratchBound after finalMaximum ∧ finalMaximum ≤ 2 * size.log2 + 1 ∧
      links + finalBuckets.length = pending.length + buckets.length ∧ after.size = size ∧
      finalBuckets.entries.Perm (pending ++ buckets).entries ∧
      finalBuckets.marks = (pending ++ buckets).marks := by
  have terminate : ∀ count : Nat, ∀ before pending buckets maximum,
      pending.length = count → SplitRepresented before pending buckets → Buckets before buckets →
      ScratchBound before maximum → before.size = size → maximum ≤ 2 * size.log2 + 1 →
      ∃ after finalBuckets finalMaximum links,
        RootConsumption before maximum after finalMaximum pending.length links ∧
        SplitRepresented after [] finalBuckets ∧ Buckets after finalBuckets ∧
        ScratchBound after finalMaximum ∧ finalMaximum ≤ 2 * size.log2 + 1 ∧
        links + finalBuckets.length = pending.length + buckets.length ∧ after.size = size ∧
        finalBuckets.entries.Perm (pending ++ buckets).entries ∧
        finalBuckets.marks = (pending ++ buckets).marks := by
    intro count
    induction count using Nat.strongRecOn with
    | ind count ih =>
      intro before pending buckets maximum length valid table bound readSize maximumBound
      rcases valid.cursor with ⟨empty, pointer⟩ | ⟨root, member, pointer⟩
      · subst pending
        exact ⟨before, buckets, maximum, 0, .done _ _ (by omega), valid, table, bound,
          maximumBound, by simp, readSize, .refl _, rfl⟩
      · obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
        have rotated : SplitRepresented before (root :: (back ++ front)) buckets := by
          have rotate := (located ▸ valid).rotate_pending
          simpa only [List.cons_append] using rotate
        have smaller : (back ++ front).length < count := by
          simp only [located, List.length_append, List.length_cons] at length
          simp only [List.length_append]
          omega
        have rearranged : ((back ++ front) ++ root :: buckets).Perm (pending ++ buckets) := by
          have rotate : (root :: (back ++ front)).Perm pending := by
            rw [located]
            simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
          exact List.perm_middle.trans (by simpa only [List.cons_append] using rotate.append_right buckets)
        have detached := rotated.detach_head pointer
        have detachedTable : Buckets before.detachMinimum buckets := table.congr rfl
        obtain ⟨merged, result, remaining, links, collisions, mergedValid, mergedTable, emptyBucket, linkCount, collisionEntries, collisionMarks⟩ :=
          detached.resolve_collisions detachedTable
        have initialDegree : before.detachMinimum.degrees root.vertex = root.degree :=
          (rotated.stored root (by simp)).root_degree
        have collisionRun : BucketCollisions before.detachMinimum before.minimum
            (before.detachMinimum.degrees before.minimum) merged result.vertex result.degree links := by
          simpa only [pointer, initialDegree] using collisions
        have inputNonnegative := rotated.nonnegative root.vertex root.key
          (List.mem_flatMap.mpr ⟨root, by simp, root.root_entry⟩)
        have nodeNonnegative := mergedValid.nonnegative result.vertex result.key
          (List.mem_flatMap.mpr ⟨result, by simp, result.root_entry⟩)
        have prepared := mergedValid.table_write result.degree result.vertex
        have preparedTable := mergedTable.insert result nodeNonnegative emptyBucket
        have sizeSame : merged.size = size := collisions.size.trans readSize
        have currentDegree := mergedValid.degree_bound (root := result) (by simp) size sizeSame
        have beforeBound : ScratchBound before.detachMinimum maximum := bound
        have preparedBound := (collisions.scratch_bound beforeBound).store result.vertex result.degree
        have preparedMaximum : max maximum (result.degree : Int) ≤ 2 * size.log2 + 1 := by omega
        obtain ⟨after, finalBuckets, finalMaximum, tailLinks, rest, finalValid, finalTable, finalBound,
            finalMaximumBound, accounting, finalSize, tailEntries, tailMarks⟩ :=
          ih _ smaller {merged with table := Rings.write merged.table result.degree result.vertex}
            (back ++ front) (result :: remaining) (max maximum result.degree) rfl prepared preparedTable
            preparedBound sizeSame preparedMaximum
        refine ⟨after, finalBuckets, finalMaximum, links + tailLinks, ?_, finalValid, finalTable,
          finalBound, finalMaximumBound, ?_, finalSize,
          tailEntries.trans (collisionEntries.trans (Forest.entries_perm rearranged)),
          tailMarks.trans (collisionMarks.trans (Forest.marks_perm rearranged))⟩
        · have run := RootConsumption.step (before := before) (by omega : 0 ≤ before.minimum) collisionRun rest
          have number : (back ++ front).length + 1 = pending.length := by
            simp only [located, List.length_append, List.length_cons]
            omega
          simpa only [number] using run
        · simp only [List.length_cons, List.length_append] at accounting
          have number : pending.length = back.length + front.length + 1 := by
            simp only [located, List.length_append, List.length_cons]
            omega
          omega
  exact terminate pending.length state pending buckets maximum rfl represented table bound readSize maximumBound


end Algo2Lean.Fibonacci
