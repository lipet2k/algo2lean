import Algo2LeanLib.FibonacciStorage

namespace Algo2Lean.Fibonacci

/-- Insert an existing detached tree into the root ring without changing its
    entries or its children. This is the exact non-clock effect of `add_root`. -/
def Snapshot.addRoot (state : Snapshot) (vertex : Int) : Snapshot :=
  { state with
    parents := Rings.write state.parents vertex (-1)
    marks := Rings.write state.marks vertex 0
    left := if state.minimum < 0 then Rings.write state.left vertex vertex
      else Rings.insertAfterLeft state.left state.right state.minimum vertex
    right := if state.minimum < 0 then Rings.write state.right vertex vertex
      else Rings.insertAfterRight state.right state.minimum vertex
    minimum := if state.minimum < 0 then vertex
      else if state.keys vertex < state.keys state.minimum then vertex else state.minimum }

theorem Snapshot.addRoot_fields (state : Snapshot) (vertex : Int)
    (root : state.parents vertex = -1) (unmarked : state.marks vertex = 0) (index : Int) :
    SameFields state (state.addRoot vertex) index := by
  constructor <;> simp [Snapshot.addRoot, Rings.write]
  · rintro rfl; exact root.symm
  · rintro rfl; exact unmarked.symm

theorem SplitRepresented.root_parent {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {vertex : Int}
    (member : vertex ∈ (pending ++ detached).map Node.vertex) : state.parents vertex = -1 := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  exact same ▸ (represented.stored root inForest).root_parent

theorem SplitRepresented.root_unmarked {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {node : Node}
    (member : node ∈ pending ++ detached) : state.marks node.vertex = 0 := by
  have unmarked := represented.valid.2.2.2 node member
  have stored := represented.stored node member
  cases stored with
  | node _ _ mark _ _ _ _ _ =>
    simp only [Node.marked] at unmarked
    simpa [Node.vertex, unmarked] using mark

/-- Only root pointers are changed, so every tree retains all its internal data. -/
theorem SplitRepresented.add_root_stored {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {added : Node}
    (member : added ∈ detached) (root : Node) (inside : root ∈ pending ++ detached) :
    Stored (state.addRoot added.vertex) (-1) root := by
  have addedStored := represented.stored added (by simp [member])
  have unmarked := represented.root_unmarked (by simp [member] : added ∈ pending ++ detached)
  apply (represented.stored root inside).frame_roots
  · intro vertex key active
    exact represented.nonnegative vertex key (List.mem_flatMap.mpr ⟨root, inside, active⟩)
  · intro vertex key active
    exact state.addRoot_fields added.vertex addedStored.root_parent unmarked vertex
  · intro vertex _ nonroot
    have notAdded : vertex ≠ added.vertex := by
      intro same
      rw [same, addedStored.root_parent] at nonroot
      omega
    by_cases empty : state.minimum < 0
    · simp [Snapshot.addRoot, empty, Rings.write, notAdded]
    · obtain ⟨cursor, inPending, pointer⟩ := represented.cursor.resolve_left
        (by rintro ⟨_, minimum⟩; omega)
      have cursorMember : state.minimum ∈ pending.map Node.vertex := by
        rw [pointer]
        exact List.mem_map.mpr ⟨cursor, inPending, rfl⟩
      have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
        rcases represented.pendingRing with impossible | ring
        · simp [impossible] at cursorMember
        · exact ring
      have nextMember := (ring.neighbors cursorMember).2
      have parentCursor := represented.root_parent (by simp only [List.map_append, List.mem_append]; exact Or.inl cursorMember)
      have parentNext := represented.root_parent (by simp only [List.map_append, List.mem_append]; exact Or.inl nextMember)
      have notCursor : vertex ≠ state.minimum := by intro same; rw [same, parentCursor] at nonroot; omega
      have notNext : vertex ≠ state.right state.minimum := by intro same; rw [same, parentNext] at nonroot; omega
      simp [Snapshot.addRoot, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
        Rings.write, notAdded, notCursor, notNext]


/-- Existing detached singleton rings are disjoint from the new root-ring links. -/
theorem SplitRepresented.add_root_singletons {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (added : Node)
    (root : Node) (member : root ∈ detached) (different : root.vertex ≠ added.vertex) :
    (state.addRoot added.vertex).left root.vertex = root.vertex ∧
      (state.addRoot added.vertex).right root.vertex = root.vertex := by
  have original := represented.detachedRings root member
  by_cases empty : state.minimum < 0
  · simpa [Snapshot.addRoot, empty, Rings.write, different] using original
  · obtain ⟨cursor, inPending, pointer⟩ := represented.cursor.resolve_left
      (by rintro ⟨_, minimum⟩; omega)
    have cursorMember : state.minimum ∈ pending.map Node.vertex := by
      rw [pointer]
      exact List.mem_map.mpr ⟨cursor, inPending, rfl⟩
    have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
      rcases represented.pendingRing with impossible | ring
      · simp [impossible] at cursorMember
      · exact ring
    have distinct (vertex : Int) (inside : vertex ∈ pending.map Node.vertex) : root.vertex ≠ vertex := by
      intro same
      apply represented.valid.1.roots_disjoint vertex inside
      apply List.mem_map.mpr
      exact ⟨(root.vertex, root.key), List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩, same⟩
    have notCursor := distinct _ cursorMember
    have notNext := distinct _ (ring.neighbors cursorMember).2
    simpa [Snapshot.addRoot, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
      Rings.write, different, notCursor, notNext] using original

/-- Rebuilding an empty pending ring moves one whole tree from detached roots. -/
theorem SplitRepresented.add_detached_empty {state : Snapshot} {added : Node} {rest : Forest}
    (represented : SplitRepresented state [] (added :: rest)) :
    SplitRepresented (state.addRoot added.vertex) [added] rest := by
  have minimum : state.minimum = -1 := by
    rcases represented.cursor with empty | ⟨root, impossible, _⟩
    · exact empty.2
    · simp at impossible
  refine ⟨represented.valid, ?_, ?_, ?_, represented.nonnegative,
    represented.presence, represented.size, ?_⟩
  · intro root member
    exact represented.add_root_stored (by simp) root member
  · apply Or.inr
    apply Rings.singleton_ring <;> simp [Snapshot.addRoot, minimum, Rings.write]
  · intro root member
    apply represented.add_root_singletons added root (by simp [member])
    intro same
    have separate := represented.valid.1.disjoint (front := [added]) (back := rest)
    apply separate added.vertex
    · exact ⟨added.key, List.mem_flatMap.mpr ⟨added, by simp, added.root_entry⟩⟩
    · exact ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
  · exact Or.inr ⟨added, by simp, by simp [Snapshot.addRoot, minimum]⟩

/-- With the cursor at the head, a detached tree is inserted immediately after
    it. The concatenated forest changes only by root permutation. -/
theorem SplitRepresented.add_detached_after_head {state : Snapshot} {head added : Node}
    {pending detached : Forest} (represented : SplitRepresented state (head :: pending) (added :: detached))
    (minimum : state.minimum = head.vertex) :
    SplitRepresented (state.addRoot added.vertex) (head :: added :: pending) detached := by
  have permutation : ((head :: added :: pending) ++ detached).Perm
      ((head :: pending) ++ added :: detached) := by
    simpa only [List.cons_append] using
      (List.perm_middle (a := added) (l₁ := pending) (l₂ := detached)).symm.cons head
  have contents := permutation.flatMap_right Node.entries
  have valid := represented.valid.perm permutation
  have nonnegative := represented.nonnegative head.vertex head.key
    (List.mem_flatMap.mpr ⟨head, by simp, head.root_entry⟩)
  have nonempty : ¬state.minimum < 0 := by omega
  have headNonnegative : ¬head.vertex < 0 := by omega
  have ring : Rings.Ring state.left state.right ((head :: pending).map Node.vertex) := by
    rcases represented.pendingRing with impossible | ring
    · simp at impossible
    · exact ring
  have fresh : added.vertex ∉ (head :: pending).map Node.vertex := by
    intro inside
    apply represented.valid.1.roots_disjoint added.vertex inside
    exact List.mem_map.mpr ⟨(added.vertex, added.key), List.mem_flatMap.mpr ⟨added, by simp, added.root_entry⟩, rfl⟩
  refine ⟨valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro root member
    exact represented.add_root_stored (by simp) root (permutation.mem_iff.mp member)
  · apply Or.inr
    simpa [Snapshot.addRoot, minimum, headNonnegative] using ring.insert_after fresh
  · intro root member
    apply represented.add_root_singletons added root (by simp [member])
    intro same
    have separate := valid.1.disjoint
    apply separate added.vertex
    · exact ⟨added.key, List.mem_flatMap.mpr ⟨added, by simp, added.root_entry⟩⟩
    · exact ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    exact (represented.presence vertex).trans
      ⟨fun ⟨key, member⟩ => ⟨key, contents.mem_iff.mpr member⟩,
        fun ⟨key, member⟩ => ⟨key, contents.mem_iff.mp member⟩⟩
  · change state.size = _
    rw [represented.size]
    exact congrArg Int.ofNat contents.length_eq.symm
  · by_cases better : state.keys added.vertex < state.keys state.minimum
    · exact Or.inr ⟨added, by simp, by simp [Snapshot.addRoot, nonempty, better]⟩
    · have notBetter : ¬state.keys added.vertex < state.keys head.vertex := by simpa only [minimum] using better
      exact Or.inr ⟨head, by simp, by simp [Snapshot.addRoot, minimum, headNonnegative, notBetter]⟩


/-- Metadata at every other vertex is unaffected, even when the inserted tree
    still has an old parent or a mark that the helper will clear. -/
theorem Snapshot.addRoot_other_fields (state : Snapshot) (vertex index : Int)
    (different : index ≠ vertex) : SameFields state (state.addRoot vertex) index := by
  constructor <;> simp [Snapshot.addRoot, Rings.write, different]

/-- The only rewritten ring addresses are the new root, the cursor, and the
    cursor's old successor. -/
theorem Snapshot.addRoot_other_links (state : Snapshot) (vertex index : Int)
    (different : index ≠ vertex)
    (outside : 0 ≤ state.minimum → index ≠ state.minimum ∧ index ≠ state.right state.minimum) :
    (state.addRoot vertex).left index = state.left index ∧
      (state.addRoot vertex).right index = state.right index := by
  by_cases empty : state.minimum < 0
  · simp [Snapshot.addRoot, empty, Rings.write, different]
  · have separate := outside (by omega)
    simp [Snapshot.addRoot, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
      Rings.write, different, separate.1, separate.2]

end Algo2Lean.Fibonacci
