import Algo2LeanLib.FibonacciMutableCascade

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- Exact key write in the strict-decrease branch. -/
def Snapshot.lowerKey (state : Snapshot) (vertex key : Int) : Snapshot :=
  { state with keys := Rings.write state.keys vertex key }

/-- The final minimum comparison performed after every strict decrease. -/
def Snapshot.finishDecrease (state : Snapshot) (vertex : Int) : Snapshot :=
  { state with minimum := if state.keys vertex < state.keys state.minimum then vertex else state.minimum }

/-- A permutation of mapped addresses can be realized by reordering the
    original nodes. No globally injective address function is required. -/
theorem lift_map_permutation {α β : Type} (f : α → β) {nodes : List α} {values : List β}
    (permutation : values.Perm (nodes.map f)) :
    ∃ ordered : List α, ordered.Perm nodes ∧ ordered.map f = values := by
  induction values generalizing nodes with
  | nil =>
    have empty := permutation.length_eq
    simp only [List.length_nil, List.length_map, Eq.comm, List.length_eq_zero_iff] at empty
    subst nodes
    exact ⟨[], List.Perm.refl [], rfl⟩
  | cons value tail ih =>
    have member : value ∈ nodes.map f := permutation.mem_iff.mp (by simp)
    obtain ⟨node, inNodes, address⟩ := List.mem_map.mp member
    obtain ⟨before, after, located⟩ := List.mem_iff_append.mp inNodes
    subst nodes
    have move : (before ++ node :: after).Perm (node :: (before ++ after)) := List.perm_middle
    have rest : tail.Perm ((before ++ after).map f) := by
      have moved := permutation.trans (move.map f)
      rw [List.map_cons, address] at moved
      exact moved.cons_inv
    obtain ⟨ordered, order, mapped⟩ := ih rest
    exact ⟨node :: ordered, (order.cons node).trans move.symm, by simp [mapped, address]⟩

/-- Internal representation without rank/order assumptions. Physical root
    traversal order is kept separate from the logical forest order during cuts. -/
structure RootBoundary (state : Snapshot) (forest : Forest) : Prop where
  trees : StoredForest state forest
  roots : ∃ order : List Int, order.Perm (forest.map Node.vertex) ∧ Rings.RingOrEmpty state.left state.right order
  presence : ∀ vertex, state.present vertex ≠ 0 ↔ Forest.Has forest vertex
  size : state.size = forest.entries.length
  minimum : (forest = [] ∧ state.minimum = -1) ∨
    ∃ root ∈ forest, state.minimum = root.vertex ∧
      ∀ other ∈ forest, state.keys state.minimum ≤ state.keys other.vertex
  scratch : ∀ degree, state.table degree < 0

theorem Represented.boundary {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) : RootBoundary state forest := by
  refine ⟨represented.stored_forest, ⟨forest.map Node.vertex, .refl _, represented.roots⟩,
    represented.presence, represented.size, ?_, represented.scratch⟩
  rcases represented.minimum with empty | ⟨root, member, pointer, least⟩
  · exact Or.inl empty
  · right
    refine ⟨root, member, pointer, ?_⟩
    intro other inForest
    rw [pointer, (represented.stored root member).root_key, (represented.stored other inForest).root_key]
    exact least other inForest

/-- Restoring semantic invariants turns the temporary boundary relation back
    into the original public representation, with a harmless root permutation. -/
theorem RootBoundary.close {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    (valid : forest.Valid) : ∃ ordered, ordered.Perm forest ∧ Represented state ordered := by
  obtain ⟨addresses, permutation, ring⟩ := boundary.roots
  obtain ⟨ordered, order, mapped⟩ := lift_map_permutation Node.vertex permutation
  have entries := order.flatMap_right Node.entries
  refine ⟨ordered, order, valid.perm order, ?_, ?_, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · simpa only [mapped] using ring
  · intro root member
    exact boundary.trees.stored root (order.mem_iff.mp member)
  · intro vertex key member
    exact boundary.trees.nonnegative vertex key (entries.mem_iff.mp member)
  · intro vertex
    rw [boundary.presence]
    exact exists_congr (fun _ => entries.mem_iff.symm)
  · exact boundary.size.trans (congrArg Int.ofNat entries.length_eq.symm)
  · rcases boundary.minimum with ⟨empty, pointer⟩ | ⟨root, rootMember, pointer, least⟩
    · exact Or.inl ⟨by have length := order.length_eq; simp [empty] at length; exact length, pointer⟩
    · right
      refine ⟨root, order.mem_iff.mpr rootMember, pointer, ?_⟩
      intro other member
      have old := order.mem_iff.mp member
      have bound := least other old
      rw [pointer, (boundary.trees.stored root rootMember).root_key, (boundary.trees.stored other old).root_key] at bound
      exact bound


theorem Ancestors.root_vertex (context : List Ancestor) {before after : Node}
    (same : before.vertex = after.vertex) :
    (Ancestors.plug context before).vertex = (Ancestors.plug context after).vertex := by
  induction context generalizing before after with
  | nil => exact same
  | cons frame rest ih => exact ih rfl

theorem RootBoundary.root_parent {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    {vertex : Int} (member : vertex ∈ forest.map Node.vertex) : state.parents vertex = -1 := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  rw [← same]
  exact (boundary.trees.stored root inForest).root_parent

theorem RootBoundary.root_nonnegative {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    {vertex : Int} (member : vertex ∈ forest.map Node.vertex) : 0 ≤ vertex := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  rw [← same]
  exact boundary.trees.nonnegative _ _ (List.mem_flatMap.mpr ⟨root, inForest, root.root_entry⟩)

theorem RootBoundary.minimum_addresses {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    (nonempty : forest ≠ []) : state.minimum ∈ forest.map Node.vertex ∧
      ∀ vertex ∈ forest.map Node.vertex, state.keys state.minimum ≤ state.keys vertex := by
  obtain ⟨root, member, pointer, least⟩ := boundary.minimum.resolve_left (fun empty => nonempty empty.1)
  constructor
  · rw [pointer]; exact List.mem_map.mpr ⟨root, member, rfl⟩
  · intro vertex member
    obtain ⟨other, member, same⟩ := List.mem_map.mp member
    rw [← same]
    exact least other member

theorem RootBoundary.root_endpoints {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest) :
    state.RootEndpoints := by
  intro nonnegative
  obtain ⟨root, member, pointer, _⟩ := boundary.minimum.resolve_left (by rintro ⟨_, same⟩; omega)
  have rootMember : state.minimum ∈ forest.map Node.vertex := by rw [pointer]; exact List.mem_map.mpr ⟨root, member, rfl⟩
  obtain ⟨addresses, permutation, ring⟩ := boundary.roots
  have cursor := permutation.mem_iff.mpr rootMember
  have actual : Rings.Ring state.left state.right addresses := by
    rcases ring with empty | ring
    · rw [empty] at cursor; simp at cursor
    · exact ring
  exact ⟨boundary.root_parent rootMember, boundary.root_parent (permutation.mem_iff.mp (actual.neighbors cursor).2)⟩

/-- A physical cut preserves all boundary observations while moving exactly
    one child tree into the root ring. No rank assumption is made mid-cascade. -/
theorem RootBoundary.cut {state : Snapshot} {context : List Ancestor} {parent child : Node} {rest : Forest}
    (boundary : RootBoundary state (Ancestors.plug context parent :: rest))
    (before after : List Node) (located : parent.children = before ++ child :: after) :
    RootBoundary (state.cut child.vertex parent.vertex)
      (Ancestors.plug context (parent.withChildren (before ++ after)) :: child.withMark false :: rest) := by
  let oldRoot := Ancestors.plug context parent
  let newRoot := Ancestors.plug context (parent.withChildren (before ++ after))
  have rootAddress : newRoot.vertex = oldRoot.vertex := Ancestors.root_vertex context rfl
  have contents := (Ancestors.entries_replace (context := context) (parent.cut_entries before after child located)).symm.append_right rest.entries
  have changed := boundary.trees.cut boundary.root_endpoints before after located
  have parentStored := (boundary.trees.stored oldRoot (by simp [oldRoot])).focus_context
  have childMember : child ∈ parent.children := by rw [located]; simp
  have childStored : Stored state parent.vertex child := by
    cases parentStored with | node _ _ _ _ _ _ _ children => exact children child childMember
  have parentNonnegative := boundary.trees.nonnegative parent.vertex parent.key
    (List.mem_flatMap.mpr ⟨oldRoot, by simp [oldRoot], (Ancestors.entries_sublist context parent).subset parent.root_entry⟩)
  have oldMinimum := boundary.minimum_addresses (by simp)
  have minimumNonnegative := boundary.root_nonnegative oldMinimum.1
  have fresh : child.vertex ∉ (oldRoot :: rest).map Node.vertex := by
    intro member
    have rootParent := boundary.root_parent member
    have childParent := childStored.root_parent
    omega
  have afterAddresses : (newRoot :: child.withMark false :: rest).map Node.vertex =
      oldRoot.vertex :: child.vertex :: rest.map Node.vertex := by
    change newRoot.vertex :: child.vertex :: rest.map Node.vertex = oldRoot.vertex :: child.vertex :: rest.map Node.vertex
    rw [rootAddress]
  refine ⟨changed.1, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, roots⟩ := boundary.roots
    have cursor := permutation.mem_iff.mpr oldMinimum.1
    have actual : Rings.Ring state.left state.right addresses := by
      rcases roots with empty | ring
      · rw [empty] at cursor; simp at cursor
      · exact ring
    have removal : Rings.Ring (state.removeChild child.vertex parent.vertex).left
        (state.removeChild child.vertex parent.vertex).right addresses := by
      have pointers (vertex : Int) (member : vertex ∈ addresses) :
          (state.removeChild child.vertex parent.vertex).left vertex = state.left vertex ∧
            (state.removeChild child.vertex parent.vertex).right vertex = state.right vertex := by
        have root := boundary.root_parent (permutation.mem_iff.mp member)
        apply parentStored.removeChild_links childMember
        · intro same
          have childParent := childStored.root_parent
          rw [same] at root
          omega
        · omega
      exact actual.frame (fun vertex member => (pointers vertex member).1)
        (fun vertex member => (pointers vertex member).2)
    obtain ⟨front, back, order⟩ := List.mem_iff_append.mp cursor
    have rotated : Rings.Ring (state.removeChild child.vertex parent.vertex).left
        (state.removeChild child.vertex parent.vertex).right (state.minimum :: (back ++ front)) := by
      rw [order] at removal
      exact removal.rotate_append front (state.minimum :: back)
    have rotatedPermutation : (state.minimum :: (back ++ front)).Perm ((oldRoot :: rest).map Node.vertex) := by
      have rotation : (state.minimum :: (back ++ front)).Perm addresses := by
        rw [order]
        simpa only [List.cons_append] using (List.perm_append_comm (l₁ := state.minimum :: back) (l₂ := front))
      exact rotation.trans permutation
    have freshRotated := fun member => fresh (rotatedPermutation.mem_iff.mp member)
    refine ⟨state.minimum :: child.vertex :: (back ++ front), ?_, Or.inr ?_⟩
    · rw [afterAddresses]
      exact ((List.Perm.swap child.vertex state.minimum (back ++ front)).trans
        (rotatedPermutation.cons child.vertex)).trans (List.Perm.swap oldRoot.vertex child.vertex (rest.map Node.vertex))
    · have inserted := rotated.insert_after freshRotated
      simpa only [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, if_neg (by omega : ¬state.minimum < 0)] using inserted
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence]
    apply exists_congr
    intro key
    simpa [Forest.entries, newRoot, oldRoot, List.append_assoc] using (contents.mem_iff (a := (vertex, key))).symm
  · change state.size = _
    rw [boundary.size]
    exact congrArg Int.ofNat (by simpa [Forest.entries, List.append_assoc] using contents.length_eq.symm)
  · right
    have presentAfter (vertex : Int) (member : vertex ∈ (oldRoot :: rest).map Node.vertex) :
        vertex ∈ (newRoot :: child.withMark false :: rest).map Node.vertex := by
      rw [afterAddresses]
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · simp [member]
    by_cases better : state.keys child.vertex < state.keys state.minimum
    · refine ⟨child.withMark false, by simp, ?_, ?_⟩
      · change (if state.minimum < 0 then child.vertex else if state.keys child.vertex < state.keys state.minimum then child.vertex else state.minimum) = child.vertex
        rw [if_neg (by omega), if_pos better]
      · intro other member
        have memberAddr : other.vertex ∈ (newRoot :: child.withMark false :: rest).map Node.vertex := List.mem_map.mpr ⟨other, member, rfl⟩
        rw [afterAddresses] at memberAddr
        have bound : state.keys child.vertex ≤ state.keys other.vertex := by
          simp only [List.mem_cons] at memberAddr
          rcases memberAddr with same | same | old
          · have oldBound := oldMinimum.2 oldRoot.vertex (by simp [oldRoot])
            rw [same]; omega
          · rw [same]
            exact Int.le_refl _
          · have oldBound := oldMinimum.2 other.vertex (by simp [old]); omega
        simpa [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, better, Int.not_lt.mpr minimumNonnegative] using bound
    · obtain ⟨root, member, pointer⟩ := List.mem_map.mp (presentAfter state.minimum oldMinimum.1)
      refine ⟨root, member, ?_, ?_⟩
      · simpa [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, better, Int.not_lt.mpr minimumNonnegative] using pointer.symm
      · intro other member
        have memberAddr : other.vertex ∈ (newRoot :: child.withMark false :: rest).map Node.vertex := List.mem_map.mpr ⟨other, member, rfl⟩
        rw [afterAddresses] at memberAddr
        have bound : state.keys state.minimum ≤ state.keys other.vertex := by
          simp only [List.mem_cons] at memberAddr
          rcases memberAddr with same | same | old
          · exact oldMinimum.2 other.vertex (by simp [same, oldRoot])
          · rw [same]; omega
          · exact oldMinimum.2 other.vertex (by simp [old])
        simpa [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, better, Int.not_lt.mpr minimumNonnegative] using bound


/-- Existing-handle push_or_decrease follows the source's exact key, parent,
    cut/cascade, and final-minimum branches; insertion is a separate contract. -/
inductive DecreaseRun : Snapshot → Snapshot → Int → Int → Nat → Prop where
  | unchanged {state : Snapshot} {vertex key : Int} (noDecrease : state.keys vertex ≤ key) :
      DecreaseRun state state vertex key 0
  | root {state : Snapshot} {vertex key : Int} (decreased : key < state.keys vertex)
      (root : state.parents vertex < 0) :
      DecreaseRun state ((state.lowerKey vertex key).finishDecrease vertex) vertex key 0
  | ordered {state : Snapshot} {vertex key : Int} (decreased : key < state.keys vertex)
      (nonroot : 0 ≤ state.parents vertex)
      (ordered : (state.lowerKey vertex key).keys (state.parents vertex) ≤ key) :
      DecreaseRun state ((state.lowerKey vertex key).finishDecrease vertex) vertex key 0
  | cascading {state middle : Snapshot} {vertex key : Int} {cuts : Nat}
      (decreased : key < state.keys vertex) (nonroot : 0 ≤ state.parents vertex)
      (violates : key < (state.lowerKey vertex key).keys (state.parents vertex))
      (cascade : CascadeRun ((state.lowerKey vertex key).cut vertex (state.parents vertex)) middle
        (state.parents vertex) cuts) :
      DecreaseRun state (middle.finishDecrease vertex) vertex key (cuts + 1)


theorem RootBoundary.perm {state : Snapshot} {before after : Forest}
    (boundary : RootBoundary state before) (order : after.Perm before) : RootBoundary state after := by
  have entries := order.flatMap_right Node.entries
  refine ⟨boundary.trees.perm order, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, permutation.trans (order.map Node.vertex).symm, ring⟩
  · intro vertex
    rw [boundary.presence]
    exact exists_congr (fun _ => entries.mem_iff.symm)
  · exact boundary.size.trans (congrArg Int.ofNat entries.length_eq.symm)
  · rcases boundary.minimum with ⟨empty, pointer⟩ | ⟨root, member, pointer, least⟩
    · exact Or.inl ⟨by have length := order.length_eq; simp [empty] at length; exact length, pointer⟩
    · exact Or.inr ⟨root, order.mem_iff.mpr member, pointer,
        fun other member => least other (order.mem_iff.mp member)⟩

/-- The marking branch preserves the whole physical boundary, with only the
    focused logical node's mark changed. -/
theorem RootBoundary.mark {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (boundary : RootBoundary state (Ancestors.plug context node :: rest)) (marked : Bool) :
    RootBoundary (state.setMark node.vertex marked) (Ancestors.plug context (node.withMark marked) :: rest) := by
  have address := Ancestors.root_vertex context (before := node.withMark marked) (after := node) rfl
  have rootMap : (Ancestors.plug context (node.withMark marked) :: rest).map Node.vertex =
      (Ancestors.plug context node :: rest).map Node.vertex := by simp only [List.map_cons, address]
  have contents : (Ancestors.plug context (node.withMark marked)).entries.Perm (Ancestors.plug context node).entries := by
    have lifted := Ancestors.entries_replace (context := context) (before := node.withMark marked)
      (after := node) (removed := []) (by simp)
    simpa using lifted
  have entries : (Forest.entries (Ancestors.plug context (node.withMark marked) :: rest)).Perm
      (Forest.entries (Ancestors.plug context node :: rest)) := by
    simpa [Forest.entries] using contents.append_right rest.entries
  refine ⟨boundary.trees.mark marked, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, by simpa only [rootMap] using permutation, ring⟩
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence]
    exact exists_congr (fun _ => entries.mem_iff.symm)
  · exact boundary.size.trans (congrArg Int.ofNat entries.length_eq.symm)
  · have least := boundary.minimum_addresses (by simp)
    have member : state.minimum ∈ (Ancestors.plug context (node.withMark marked) :: rest).map Node.vertex := by
      rw [rootMap]; exact least.1
    obtain ⟨root, member, pointer⟩ := List.mem_map.mp member
    right
    refine ⟨root, member, pointer.symm, ?_⟩
    intro other member
    have present : other.vertex ∈ (Ancestors.plug context node :: rest).map Node.vertex := by
      rw [← rootMap]
      exact List.mem_map.mpr ⟨other, member, rfl⟩
    exact least.2 other.vertex present

/-- Actual cascades preserve root rings, minimum, exact membership, size and
    scratch storage, in addition to the finite stored trees. -/
theorem cascade_boundary_exists (context : List Ancestor) (node : Node) (kept : List Node)
    (state : Snapshot) (rest : Forest)
    (boundary : RootBoundary state (Ancestors.plug context (node.withChildren kept) :: rest)) :
    ∃ final, CascadeRun state final node.vertex (cascadeCuts node context) ∧
      RootBoundary final (cascadeForest node kept context ++ rest) := by
  induction context generalizing node kept state rest with
  | nil =>
    have stored := boundary.trees.stored (node.withChildren kept) (by simp [Ancestors.plug])
    have parent := stored.root_parent
    change state.parents node.vertex = -1 at parent
    exact ⟨state, .root (by omega), boundary⟩
  | cons frame ancestors ih =>
    have mainStored := boundary.trees.stored (Ancestors.plug (frame :: ancestors) (node.withChildren kept)) (by simp)
    have focus := mainStored.focus_context
    have parent : state.parents node.vertex = frame.vertex := focus.root_parent
    have readMark : state.marks node.vertex = if node.marked then 1 else 0 := focus.root_mark
    have frameMember : (frame.vertex, frame.key) ∈ (Ancestors.plug (frame :: ancestors) (node.withChildren kept)).entries :=
      (Ancestors.entries_sublist ancestors (frame.plug (node.withChildren kept))).subset (by simp [Ancestor.plug, Node.entries])
    have frameNonnegative := boundary.trees.nonnegative frame.vertex frame.key (List.mem_flatMap.mpr ⟨_, by simp, frameMember⟩)
    by_cases marked : node.marked = true
    · have cut := boundary.cut (context := ancestors) (parent := frame.plug (node.withChildren kept))
        (child := node.withChildren kept) frame.before frame.after rfl
      obtain ⟨final, run, repaired⟩ := ih (frame.plug node) (frame.before ++ frame.after)
        (state.cut node.vertex frame.vertex) ((node.withChildren kept).withMark false :: rest) cut
      refine ⟨final, ?_, ?_⟩
      · have sourceRun : CascadeRun state final node.vertex (cascadeCuts (frame.plug node) ancestors + 1) :=
          CascadeRun.cut (by omega) (by simp [marked] at readMark; omega) (by simpa only [parent] using! run)
        simpa only [cascadeCuts, marked, ↓reduceIte] using sourceRun
      · apply repaired.perm
        simp only [cascadeForest, marked, ↓reduceIte, List.cons_append]
        exact List.perm_middle.symm
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      refine ⟨state.setMark node.vertex true, ?_, ?_⟩
      · simpa [cascadeCuts, unmarked] using CascadeRun.mark (by omega : 0 ≤ state.parents node.vertex)
          (by simpa [unmarked] using readMark)
      · simpa [cascadeForest, unmarked] using! boundary.mark true

theorem Forest.counts_perm {before after : Forest} (order : after.Perm before) : after.counts = before.counts := by
  unfold Forest.counts Forest.marks
  rw [order.length_eq, (order.map Node.marks).sum_nat]

/-- Cascade validity is stable under arbitrary untouched roots. -/
theorem Forest.Valid.cascade {context : List Ancestor} {parent child : Node} {rest : Forest}
    (valid : Forest.Valid (Ancestors.plug context parent :: rest)) (before after : List Node)
    (located : parent.children = before ++ child :: after) :
    Forest.Valid (child.withMark false :: cascadeForest parent (before ++ after) context ++ rest) := by
  let root := Ancestors.plug context parent
  have single : Forest.Valid [root] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Forest.Unique, Forest.entries, root] using valid.1.head
    · intro node member
      have same := List.mem_singleton.mp member
      subst node
      exact valid.2.1 _ (by simp [root])
    · intro node member
      have same := List.mem_singleton.mp member
      subst node
      exact valid.2.2.1 _ (by simp [root])
    · intro node member
      have same := List.mem_singleton.mp member
      subst node
      exact valid.2.2.2 _ (by simp [root])
  have localValid := cascadeForest_valid context parent child before after located single
  have contents := cascadeForest_entries context parent (before ++ after) child.entries
    (parent.cut_entries before after child located)
  have permutation : (Forest.entries (child.withMark false :: cascadeForest parent (before ++ after) context ++ rest)).Perm
      (Forest.entries (Ancestors.plug context parent :: rest)) := by
    have reordered := (List.perm_append_comm (l₁ := child.entries)
      (l₂ := (cascadeForest parent (before ++ after) context).entries)).trans contents.symm
    simpa [Forest.entries, List.flatMap_append, List.append_assoc] using reordered.append_right rest.entries
  refine ⟨valid.1.of_entries_perm permutation, ?_, ?_, ?_⟩
  all_goals
    intro node member
    change node ∈ (child.withMark false :: cascadeForest parent (before ++ after) context) ++ rest at member
    rcases List.mem_append.mp member with repaired | old
    first | exact localValid.2.1 node repaired | exact localValid.2.2.1 node repaired | exact localValid.2.2.2 node repaired
    first | exact valid.2.1 node (by simp [old]) | exact valid.2.2.1 node (by simp [old]) | exact valid.2.2.2 node (by simp [old])

/-- Full represented cut-and-cascade: exact root ring and minimum are restored,
    every entry is preserved, and the concrete forest satisfies Decrease accounting. -/
theorem represented_cut_and_cascade {state : Snapshot} {context : List Ancestor} {parent child : Node} {rest : Forest}
    (represented : Represented state (Ancestors.plug context parent :: rest))
    (before after : List Node) (located : parent.children = before ++ child :: after) :
    ∃ final outputForest,
      CascadeRun (state.cut child.vertex parent.vertex) final parent.vertex (cascadeCuts parent context) ∧
      Represented final outputForest ∧
      outputForest.entries.Perm (Forest.entries (Ancestors.plug context parent :: rest)) ∧
      Decrease (Forest.counts (Ancestors.plug context parent :: rest)) outputForest.counts
        (cascadeCuts parent context + 1) := by
  have cut := represented.boundary.cut before after located
  obtain ⟨final, run, boundary⟩ := cascade_boundary_exists context parent (before ++ after)
    (state.cut child.vertex parent.vertex) (child.withMark false :: rest) cut
  have canonical := boundary.perm List.perm_middle.symm
  obtain ⟨outputForest, order, output⟩ := canonical.close (represented.valid.cascade before after located)
  have content := cascadeForest_entries context parent (before ++ after) child.entries
    (parent.cut_entries before after child located)
  have canonicalContent : (Forest.entries (child.withMark false :: cascadeForest parent (before ++ after) context ++ rest)).Perm
      (Forest.entries (Ancestors.plug context parent :: rest)) := by
    have rearranged := (List.perm_append_comm (l₁ := child.entries)
      (l₂ := (cascadeForest parent (before ++ after) context).entries)).trans content.symm
    simpa [Forest.entries, List.flatMap_append, List.append_assoc] using rearranged.append_right rest.entries
  refine ⟨final, outputForest, run, output, (order.flatMap_right Node.entries).trans canonicalContent, ?_⟩
  rw [Forest.counts_perm order]
  exact cascadeForest_decrease_accounting context parent child before after rest located

end Algo2Lean.Fibonacci
