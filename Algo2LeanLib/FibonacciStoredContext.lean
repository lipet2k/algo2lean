import Algo2LeanLib.FibonacciStorage
import Algo2LeanLib.FibonacciCascade

namespace Algo2Lean.Fibonacci

/-- A stored ancestor with one subtree left open. The hole is identified only
    by its address, so proofs about the descendant can be replaced locally. -/
structure StoredAncestor (state : Snapshot) (parent : Int) (frame : Ancestor) (address : Int) : Prop where
  key : state.keys frame.vertex = frame.key
  parent : state.parents frame.vertex = parent
  mark : state.marks frame.vertex = if frame.marked then 1 else 0
  degree : state.degrees frame.vertex = frame.before.length + 1 + frame.after.length
  present : state.present frame.vertex = 1
  childHead : state.children frame.vertex =
    match frame.before with | [] => address | first :: _ => first.vertex
  ring : Rings.Ring state.left state.right
    (frame.before.map Node.vertex ++ address :: frame.after.map Node.vertex)
  siblings : ∀ sibling ∈ frame.before ++ frame.after, Stored state frame.vertex sibling

/-- Filling a stored hole requires a subtree contract and its address, rather
    than reopening every ancestor's fields and siblings. -/
theorem StoredAncestor.fill {state : Snapshot} {parent address : Int} {frame : Ancestor} {node : Node}
    (ancestor : StoredAncestor state parent frame address) (sameAddress : node.vertex = address)
    (stored : Stored state frame.vertex node) : Stored state parent (frame.plug node) := by
  cases frame with
  | mk vertex key marked before after =>
    refine Stored.node ancestor.key ancestor.parent ancestor.mark ?_ ancestor.present ?_ ?_ ?_
    · simpa [Ancestor.plug, List.length_append, List.length_cons, Nat.add_assoc, Int.natCast_add,
        Int.add_assoc, Int.add_comm, Int.add_left_comm] using ancestor.degree
    · cases before with
      | nil => exact ancestor.childHead.trans sameAddress.symm
      | cons first rest => exact ancestor.childHead
    · apply Or.inr
      simpa only [List.map_append, List.map_cons, sameAddress] using ancestor.ring
    · intro child member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inBefore | rfl | inAfter
      · exact ancestor.siblings child (by simp [inBefore])
      · exact stored
      · exact ancestor.siblings child (by simp [inAfter])

/-- Opening an existing stored ancestor produces its reusable hole contract. -/
theorem Stored.ancestor {state : Snapshot} {parent : Int} {frame : Ancestor} {node : Node}
    (stored : Stored state parent (frame.plug node)) : StoredAncestor state parent frame node.vertex := by
  cases frame with
  | mk vertex key marked before after =>
    cases stored with
    | node readKey readParent readMark degree present head ring children =>
      refine ⟨readKey, readParent, readMark, ?_, present, ?_, ?_, ?_⟩
      · simpa [List.length_append, List.length_cons, Nat.add_assoc, Int.natCast_add,
          Int.add_assoc, Int.add_comm, Int.add_left_comm] using degree
      · cases before <;> exact head
      · rcases ring with impossible | ring
        · simp at impossible
        · simpa only [List.map_append, List.map_cons] using ring
      · intro sibling member
        apply children sibling
        simp only [List.mem_append] at member
        rcases member with inBefore | inAfter
        · simp [inBefore]
        · simp [inAfter]

/-- A finite chain of open ancestors. It contains no proof of the focused
    subtree, allowing the local cut/mark proof to be supplied independently. -/
inductive StoredContext (state : Snapshot) (rootParent : Int) : List Ancestor → Int → Int → Prop where
  | nil (address : Int) : StoredContext state rootParent [] address rootParent
  | cons {frame : Ancestor} {rest : List Ancestor} {address frameParent : Int}
      (outer : StoredContext state rootParent rest frame.vertex frameParent)
      (ancestor : StoredAncestor state frameParent frame address) :
      StoredContext state rootParent (frame :: rest) address frame.vertex

theorem StoredContext.fill {state : Snapshot} {rootParent focusParent address : Int}
    {context : List Ancestor} {node : Node}
    (surrounding : StoredContext state rootParent context address focusParent)
    (sameAddress : node.vertex = address) (stored : Stored state focusParent node) :
    Stored state rootParent (Ancestors.plug context node) := by
  induction surrounding generalizing node with
  | nil => exact stored
  | cons outer ancestor ih =>
    apply ih rfl
    exact ancestor.fill sameAddress stored

/-- Any finite stored tree can be opened along a chosen logical ancestor path. -/
theorem Stored.open_context {state : Snapshot} {rootParent : Int} {context : List Ancestor} {node : Node}
    (stored : Stored state rootParent (Ancestors.plug context node)) :
    ∃ focusParent, StoredContext state rootParent context node.vertex focusParent ∧ Stored state focusParent node := by
  induction context generalizing node with
  | nil => exact ⟨rootParent, .nil _, stored⟩
  | cons frame rest ih =>
    obtain ⟨frameParent, surrounding, frameStored⟩ := ih stored
    have focus : Stored state frame.vertex node := by
      cases frameStored with | node _ _ _ _ _ _ _ children => exact children node (by simp)
    exact ⟨frame.vertex, .cons surrounding frameStored.ancestor, focus⟩

theorem Ancestors.plug_append (first second : List Ancestor) (node : Node) :
    Ancestors.plug (first ++ second) node = Ancestors.plug second (Ancestors.plug first node) := by
  induction first generalizing node with
  | nil => rfl
  | cons frame rest ih => exact ih (frame.plug node)

/-- Every stored entry has a finite path of ancestors and a complete local
    subtree. This supplies a proof context for arbitrary active vertex handles. -/
theorem Stored.locate {state : Snapshot} {parent : Int} {tree : Node}
    (stored : Stored state parent tree) :
    ∀ vertex key, (vertex, key) ∈ tree.entries →
      ∃ context node, tree = Ancestors.plug context node ∧ node.vertex = vertex ∧ node.key = key := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro value weight member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, inside⟩
    · exact ⟨[], .make value weight marked children, rfl, rfl, rfl⟩
    · obtain ⟨context, focus, located, address, valueKey⟩ := ih child inChildren value weight inside
      obtain ⟨before, after, childrenEq⟩ := List.mem_iff_append.mp inChildren
      let frame : Ancestor := ⟨vertex, key, marked, before, after⟩
      refine ⟨context ++ [frame], focus, ?_, address, valueKey⟩
      simp only [Ancestors.plug_append, Ancestors.plug, Ancestor.plug, frame, childrenEq, ← located]

/-- An active nonroot is a child in an actual finite ancestor frame. Thus
    parent-pointer traversal corresponds to a structural ancestor path. -/
theorem Represented.locate_nonroot {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int}
    (active : state.present vertex ≠ 0) (nonroot : 0 ≤ state.parents vertex) :
    ∃ root ∈ forest, ∃ (context : List Ancestor) (frame : Ancestor) (node : Node),
      root = Ancestors.plug context (frame.plug node) ∧ node.vertex = vertex ∧
      frame.vertex = state.parents vertex ∧ Stored state frame.vertex node := by
  obtain ⟨key, member⟩ := (represented.presence vertex).mp active
  obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
  have rootStored := represented.stored root inForest
  obtain ⟨context, node, located, address, _⟩ := rootStored.locate vertex key inside
  rw [located] at rootStored
  cases context with
  | nil =>
    have parent := rootStored.root_parent
    change state.parents node.vertex = -1 at parent
    rw [address] at parent
    omega
  | cons frame rest =>
    obtain ⟨_, surrounding, focus⟩ := rootStored.open_context
    cases surrounding with
    | cons outer ancestor =>
      have parent := focus.root_parent
      rw [address] at parent
      exact ⟨root, inForest, rest, frame, node, located, address, parent.symm, focus⟩


/-- A local subtree edit may also rewire the global root ring. Metadata outside
    the subtree and nonroot pointers outside its strict descendants are framed. -/
structure Snapshot.LocalChange (before after : Snapshot) (node : Node) : Prop where
  fields : ∀ vertex, ¬node.Has vertex → Snapshot.SameFields before after vertex
  links : ∀ vertex, 0 ≤ before.parents vertex → ¬Forest.Has node.children vertex →
    after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex

/-- The focused subtree and its siblings occupy disjoint addresses. -/
theorem Ancestor.unique_parts {frame : Ancestor} {node : Node}
    (unique : ((frame.plug node).entries.map Prod.fst).Nodup) :
    (node.entries.map Prod.fst).Nodup ∧ ¬node.Has frame.vertex ∧
      (∀ vertex, Forest.Has (frame.before ++ frame.after) vertex → ¬node.Has vertex) := by
  have childrenUnique : Forest.Unique (frame.before ++ node :: frame.after) := by
    have expanded := unique
    simp only [Ancestor.plug, Node.entries, List.map_cons] at expanded
    exact (List.nodup_cons.mp expanded).2
  have reordered : Forest.Unique (node :: (frame.before ++ frame.after)) :=
    childrenUnique.of_entries_perm (List.perm_middle.symm.flatMap_right Node.entries)
  refine ⟨reordered.head, ?_, ?_⟩
  · intro present
    exact (frame.plug node).unique_root unique
      (by obtain ⟨key, member⟩ := present
          exact ⟨key, List.mem_flatMap.mpr ⟨node, by simp [Ancestor.plug, Node.children], member⟩⟩)
  · intro vertex siblings focus
    apply (Forest.Unique.disjoint (front := [node]) (back := frame.before ++ frame.after) reordered) vertex
    · simpa [Forest.Has, Forest.entries] using focus
    · exact siblings

/-- All unrelated stored subtrees survive a local edit. -/
theorem Stored.frame_local {before after : Snapshot} {parent : Int} {focus other : Node}
    (stored : Stored before parent other) (change : Snapshot.LocalChange before after focus)
    (separate : ∀ vertex, other.Has vertex → ¬focus.Has vertex)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ other.entries → 0 ≤ vertex) :
    Stored after parent other := by
  apply stored.frame
  · intro vertex key member
    exact change.fields vertex (separate vertex ⟨key, member⟩)
  · intro vertex key member
    apply change.links vertex
    · obtain ⟨parentKey, parentMember⟩ := stored.descendant_parent vertex key member
      exact nonnegative _ _ parentMember
    · intro inside
      exact separate vertex ⟨key, Node.descendant_entries member⟩
        (by obtain ⟨key, member⟩ := inside; exact ⟨key, Node.descendant_entries member⟩)

/-- A local edit preserves the stored open ancestor around its focused node. -/
theorem StoredAncestor.frame_local {before after : Snapshot} {parent : Int} {frame : Ancestor} {node : Node}
    (ancestor : StoredAncestor before parent frame node.vertex)
    (focusStored : Stored before frame.vertex node)
    (unique : ((frame.plug node).entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ (frame.plug node).entries → 0 ≤ vertex)
    (change : Snapshot.LocalChange before after node) : StoredAncestor after parent frame node.vertex := by
  have parts := Ancestor.unique_parts unique
  have rootFields := change.fields frame.vertex parts.2.1
  refine ⟨rootFields.key.trans ancestor.key, rootFields.parent.trans ancestor.parent,
    rootFields.mark.trans ancestor.mark, rootFields.degree.trans ancestor.degree,
    rootFields.present.trans ancestor.present, rootFields.child.trans ancestor.childHead, ?_, ?_⟩
  · apply ancestor.ring.frame
    all_goals
      intro vertex member
      have pointer : before.parents vertex = frame.vertex := by
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inBefore | rfl | inAfter
        · obtain ⟨sibling, inBefore, same⟩ := List.mem_map.mp inBefore
          rw [← same]
          exact (ancestor.siblings sibling (by simp [inBefore])).root_parent
        · exact focusStored.root_parent
        · obtain ⟨sibling, inAfter, same⟩ := List.mem_map.mp inAfter
          rw [← same]
          exact (ancestor.siblings sibling (by simp [inAfter])).root_parent
      have bound : 0 ≤ before.parents vertex := by
        rw [pointer]
        exact nonnegative frame.vertex frame.key (by simp [Ancestor.plug, Node.entries])
      have outside : ¬Forest.Has node.children vertex := by
        intro inside
        have inFocus : node.Has vertex := by
          obtain ⟨key, member⟩ := inside
          exact ⟨key, Node.descendant_entries member⟩
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inBefore | rfl | inAfter
        · obtain ⟨sibling, inBefore, same⟩ := List.mem_map.mp inBefore
          exact parts.2.2 vertex ⟨sibling.key, same ▸ List.mem_flatMap.mpr
            ⟨sibling, by simp [inBefore], sibling.root_entry⟩⟩ inFocus
        · exact node.unique_root parts.1 inside
        · obtain ⟨sibling, inAfter, same⟩ := List.mem_map.mp inAfter
          exact parts.2.2 vertex ⟨sibling.key, same ▸ List.mem_flatMap.mpr
            ⟨sibling, by simp [inAfter], sibling.root_entry⟩⟩ inFocus
      first | exact (change.links vertex bound outside).1 | exact (change.links vertex bound outside).2
  · intro sibling member
    apply (ancestor.siblings sibling member).frame_local change
    · intro vertex inside
      exact parts.2.2 vertex (by obtain ⟨key, inside⟩ := inside; exact ⟨key, List.mem_flatMap.mpr ⟨sibling, member, inside⟩⟩)
    · intro vertex key inside
      apply nonnegative vertex key
      apply Node.child_entries _ inside
      simp only [Ancestor.plug, Node.children, List.mem_append, List.mem_cons]
      simp only [List.mem_append] at member
      rcases member with first | last
      · exact Or.inl first
      · exact Or.inr (Or.inr last)

theorem Snapshot.LocalChange.enclose {before after : Snapshot} {node : Node}
    (change : LocalChange before after node) (frame : Ancestor) :
    LocalChange before after (frame.plug node) := by
  constructor
  · intro vertex outside
    apply change.fields vertex
    rintro ⟨key, member⟩
    exact outside ⟨key, Node.child_entries (by simp [Ancestor.plug, Node.children]) member⟩
  · intro vertex nonroot outside
    apply change.links vertex nonroot
    rintro ⟨key, member⟩
    exact outside ⟨key, List.mem_flatMap.mpr
      ⟨node, by simp [Ancestor.plug, Node.children], Node.descendant_entries member⟩⟩

theorem Ancestor.entries_sublist (frame : Ancestor) (node : Node) :
    node.entries.Sublist (frame.plug node).entries := by
  have first := List.sublist_append_left node.entries (frame.after.flatMap Node.entries)
  have second := List.sublist_append_right (frame.before.flatMap Node.entries)
    (node.entries ++ frame.after.flatMap Node.entries)
  simpa only [Ancestor.plug, Node.entries, List.flatMap_append, List.flatMap_cons] using
    (first.trans second).cons (frame.vertex, frame.key)

theorem Ancestors.entries_sublist (context : List Ancestor) (node : Node) :
    node.entries.Sublist (Ancestors.plug context node).entries := by
  induction context generalizing node with
  | nil => exact List.Sublist.refl _
  | cons frame rest ih => exact (frame.entries_sublist node).trans (ih (frame.plug node))

def Ancestors.parent (context : List Ancestor) (rootParent : Int) : Int :=
  match context with | [] => rootParent | frame :: _ => frame.vertex

theorem StoredContext.focus_parent {state : Snapshot} {rootParent focusParent address : Int}
    {context : List Ancestor} (surrounding : StoredContext state rootParent context address focusParent) :
    focusParent = Ancestors.parent context rootParent := by cases surrounding <;> rfl

theorem Stored.focus_context {state : Snapshot} {rootParent : Int} {context : List Ancestor} {node : Node}
    (stored : Stored state rootParent (Ancestors.plug context node)) :
    Stored state (Ancestors.parent context rootParent) node := by
  obtain ⟨_, surrounding, focus⟩ := stored.open_context
  simpa only [surrounding.focus_parent] using focus

/-- A local subtree proof lifts through every stored ancestor. Root-list
    rewiring is allowed because ancestor child rings contain only nonroots. -/
theorem Stored.lift_context {before after : Snapshot} {rootParent : Int} {context : List Ancestor}
    {node replacement : Node} (stored : Stored before rootParent (Ancestors.plug context node))
    (unique : ((Ancestors.plug context node).entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context node).entries → 0 ≤ vertex)
    (change : Snapshot.LocalChange before after node)
    (sameAddress : replacement.vertex = node.vertex)
    (replacementStored : Stored after (Ancestors.parent context rootParent) replacement) :
    Stored after rootParent (Ancestors.plug context replacement) := by
  induction context generalizing node replacement with
  | nil => exact replacementStored
  | cons frame rest ih =>
    have frameStored := stored.focus_context (context := rest)
    have focusStored : Stored before frame.vertex node := by
      cases frameStored with | node _ _ _ _ _ _ _ children => exact children node (by simp)
    have included := Ancestors.entries_sublist rest (frame.plug node)
    have frameUnique := (included.map Prod.fst).nodup unique
    have frameNonnegative : ∀ vertex key, (vertex, key) ∈ (frame.plug node).entries → 0 ≤ vertex :=
      fun vertex key member => nonnegative vertex key (included.subset member)
    have ancestor := frameStored.ancestor.frame_local focusStored frameUnique frameNonnegative change
    have next := ancestor.fill sameAddress replacementStored
    exact ih stored unique nonnegative (change.enclose frame) rfl next

/-- Ring neighbors are concrete entries in the same finite child list. -/
theorem Stored.child_neighbors_inside {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) :
    Forest.Has parent.children (state.left child.vertex) ∧
      Forest.Has parent.children (state.right child.vertex) := by
  cases stored with
  | @node vertex key outer marked children _ _ _ _ _ _ ring subtrees =>
    have childMember : child.vertex ∈ children.map Node.vertex := List.mem_map.mpr ⟨child, member, rfl⟩
    have actual : Rings.Ring state.left state.right (children.map Node.vertex) := by
      rcases ring with impossible | ring
      · rw [impossible] at childMember; simp at childMember
      · exact ring
    have neighbors := actual.neighbors childMember
    constructor
    · obtain ⟨left, inChildren, same⟩ := List.mem_map.mp neighbors.1
      exact ⟨left.key, same ▸ List.mem_flatMap.mpr ⟨left, inChildren, left.root_entry⟩⟩
    · obtain ⟨right, inChildren, same⟩ := List.mem_map.mp neighbors.2
      exact ⟨right.key, same ▸ List.mem_flatMap.mpr ⟨right, inChildren, right.root_entry⟩⟩

theorem Stored.removeChild_local {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) :
    Snapshot.LocalChange state (state.removeChild child.vertex parent.vertex) parent := by
  constructor
  · intro vertex outside
    apply Snapshot.removeChild_fields
    intro same
    exact outside (same ▸ ⟨parent.key, parent.root_entry⟩)
  · intro vertex _ outside
    have neighbors := stored.child_neighbors_inside member
    have notChild : vertex ≠ child.vertex := by
      intro same
      exact outside (same ▸ ⟨child.key, List.mem_flatMap.mpr ⟨child, member, child.root_entry⟩⟩)
    have notLeft : vertex ≠ state.left child.vertex := fun same => outside (same ▸ neighbors.1)
    have notRight : vertex ≠ state.right child.vertex := fun same => outside (same ▸ neighbors.2)
    simp [Snapshot.removeChild, Rings.removeLeft, Rings.removeRight, Rings.write, notChild, notLeft, notRight]

/-- Marking the focused node preserves a preceding local-change guarantee. -/
theorem Snapshot.LocalChange.setMark {before after : Snapshot} {node : Node}
    (change : LocalChange before after node) (marked : Bool) :
    LocalChange before (after.setMark node.vertex marked) node := by
  constructor
  · intro vertex outside
    have different : vertex ≠ node.vertex := by intro same; exact outside (same ▸ ⟨node.key, node.root_entry⟩)
    have fields := change.fields vertex outside
    exact ⟨fields.key, fields.parent, fields.child, fields.degree,
      by simpa [Snapshot.setMark, Rings.write, different] using fields.mark, fields.present⟩
  · exact change.links

/-- The actual first-loss child removal and mark writes lift through an
    arbitrary depth of ancestors without reopening unrelated subtrees. -/
theorem Stored.first_loss_context {state : Snapshot} {rootParent : Int} {context : List Ancestor}
    {parent child : Node} (stored : Stored state rootParent (Ancestors.plug context parent))
    (unique : ((Ancestors.plug context parent).entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context parent).entries → 0 ≤ vertex)
    (before after : List Node) (located : parent.children = before ++ child :: after) :
    Stored ((state.removeChild child.vertex parent.vertex).setMark parent.vertex true) rootParent
      (Ancestors.plug context ((parent.withChildren (before ++ after)).withMark true)) := by
  have parentStored := stored.focus_context
  have included := Ancestors.entries_sublist context parent
  have parentUnique := (included.map Prod.fst).nodup unique
  have member : child ∈ parent.children := by rw [located]; simp
  have removed := parentStored.removeChild before after located parentUnique
  have remainingUnique : ((parent.withChildren (before ++ after)).entries.map Prod.fst).Nodup := by
    have newUnique := ((parent.cut_entries before after child located).map Prod.fst).nodup_iff.mp parentUnique
    rw [List.map_append] at newUnique
    exact (List.nodup_append.mp newUnique).1
  have marked := removed.1.setMark remainingUnique true
  apply stored.lift_context (replacement := (parent.withChildren (before ++ after)).withMark true)
    unique nonnegative ((parentStored.removeChild_local member).setMark true) rfl
  exact marked

end Algo2Lean.Fibonacci
