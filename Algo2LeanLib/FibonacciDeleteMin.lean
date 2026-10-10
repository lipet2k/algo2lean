import Algo2LeanLib.FibonacciConsolidation
import Algo2LeanLib.FibonacciDecrease
import Algo2LeanLib.FibonacciRootInsertion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- Exact non-clock effect after the selected root has lost all children.
    Consolidation starts with its former successor as the traversal cursor. -/
def Snapshot.extractRoot (state : Snapshot) (vertex : Int) : Snapshot :=
  {state with
    left := Rings.removeLeft state.left state.right vertex
    right := Rings.removeRight state.left state.right vertex
    present := Rings.write state.present vertex 0
    size := state.size - 1
    minimum := if state.right vertex = vertex then -1 else state.right vertex}

/-- Deleting a childless selected root clears precisely its membership and
    leaves a represented pending ring ready for consolidation. -/
theorem Represented.extract_childless {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest))
    (minimum : state.minimum = root.vertex) (childless : root.children = []) :
    SplitRepresented (state.extractRoot root.vertex) rest [] ∧
      (∀ degree, (state.extractRoot root.vertex).table degree < 0) := by
  have detached := represented.split.detach_head minimum
  have entries : root.entries = [(root.vertex,root.key)] := by
    cases root with
    | make vertex key marked children =>
      change children = [] at childless
      simp [childless,Node.entries,Node.vertex,Node.key]
  have rootAbsent : ¬Forest.Has rest root.vertex := by
    have disjoint := represented.valid.1.disjoint (front := [root]) (back := rest)
    exact disjoint root.vertex ⟨root.key, by simp [Forest.entries,entries]⟩
  have unequal (vertex key : Int) (inside : (vertex,key) ∈ rest.entries) : vertex ≠ root.vertex := by
    intro same
    exact rootAbsent (same ▸ ⟨key,inside⟩)
  have valid : rest.Valid := by
    refine ⟨represented.valid.1.tail, ?_, ?_, ?_⟩ <;>
      intro node member
    · exact represented.valid.2.1 node (by simp [member])
    · exact represented.valid.2.2.1 node (by simp [member])
    · exact represented.valid.2.2.2 node (by simp [member])
  refine ⟨⟨by simpa using valid, ?_, ?_, by simp, ?_, ?_, ?_, ?_⟩, represented.scratch⟩
  · intro node member
    simp only [List.append_nil] at member
    apply (detached.stored node (by simp [member])).frame
    · intro vertex key inside
      have different := unequal vertex key (List.mem_flatMap.mpr ⟨node,member,inside⟩)
      constructor <;> simp [Snapshot.extractRoot,Snapshot.detachMinimum,Rings.write,different]
    · intro vertex key inside
      exact ⟨by simp [Snapshot.extractRoot,Snapshot.detachMinimum,minimum],
        by simp [Snapshot.extractRoot,Snapshot.detachMinimum,minimum]⟩
  · simpa only [Snapshot.extractRoot,Snapshot.detachMinimum,minimum] using detached.pendingRing
  · intro vertex key inside
    simp only [List.append_nil] at inside
    obtain ⟨node,member,inside⟩ := List.mem_flatMap.mp inside
    exact represented.nonnegative vertex key
      (List.mem_flatMap.mpr ⟨node,by simp [member],inside⟩)
  · intro vertex
    change Rings.write state.present root.vertex 0 vertex ≠ 0 ↔ Forest.Has (rest ++ []) vertex
    simp only [List.append_nil]
    by_cases same : vertex = root.vertex
    · subst vertex
      simp only [Rings.write_same,ne_self_iff_false,false_iff]
      exact rootAbsent
    · rw [Rings.write,if_neg same,represented.presence]
      simp only [Forest.entries,List.flatMap_cons,entries,List.singleton_append,List.mem_cons,
        Prod.mk.injEq, same,false_and,false_or,Forest.Has]
  · change state.size - 1 = (Forest.entries (rest ++ [])).length
    rw [represented.size]
    simp [Forest.entries,entries]
  · simpa only [Snapshot.extractRoot,Snapshot.detachMinimum,minimum] using detached.cursor

/-- A root boundary, valid forest, and matching physical ring establish the
    full representation in the supplied forest order. -/
theorem RootBoundary.close_with_ring {state : Snapshot} {forest : Forest}
    (boundary : RootBoundary state forest) (valid : forest.Valid)
    (ring : Rings.RingOrEmpty state.left state.right (forest.map Node.vertex)) :
    Represented state forest := by
  refine ⟨valid,ring,boundary.trees.stored,boundary.trees.nonnegative,
    boundary.presence,boundary.size,?_,boundary.scratch⟩
  rcases boundary.minimum with empty | ⟨root,member,pointer,least⟩
  · exact Or.inl empty
  · refine Or.inr ⟨root,member,pointer,?_⟩
    intro other inside
    have bound := least other inside
    rw [pointer,(boundary.trees.stored root member).root_key,
      (boundary.trees.stored other inside).root_key] at bound
    exact bound

/-- Promote the displayed first child; root pruning preserves rank, and heap
    order prevents the strict minimum comparison from changing the cursor. -/
theorem Represented.promote_child {state : Snapshot} {root child : Node} {tail rest : Forest}
    (represented : Represented state (root :: rest)) (minimum : state.minimum = root.vertex)
    (children : root.children = child :: tail) :
    Represented (state.cut child.vertex root.vertex)
      (root.withChildren tail :: child.withMark false :: rest) ∧
    (state.cut child.vertex root.vertex).minimum = root.vertex := by
  have changed := represented.boundary.cut (context := []) [] tail (child := child) children
  have valid := represented.valid.cut_root_child [] tail children
  have rootStored := represented.stored root (by simp)
  have childMember : child ∈ root.children := by rw [children]; simp
  have childStored : Stored state root.vertex child := by
    cases rootStored with | node _ _ _ _ _ _ _ subtrees => exact subtrees child childMember
  have rootNonnegative : 0 ≤ root.vertex :=
    represented.nonnegative root.vertex root.key (List.mem_flatMap.mpr ⟨root,by simp,root.root_entry⟩)
  have roots : Rings.Ring state.left state.right ((root :: rest).map Node.vertex) := by
    rcases represented.roots with impossible | ring
    · simp at impossible
    · exact ring
  have detachedRing : Rings.Ring (state.removeChild child.vertex root.vertex).left
      (state.removeChild child.vertex root.vertex).right ((root :: rest).map Node.vertex) := by
    have links (vertex : Int) (member : vertex ∈ (root :: rest).map Node.vertex) :
        (state.removeChild child.vertex root.vertex).left vertex = state.left vertex ∧
          (state.removeChild child.vertex root.vertex).right vertex = state.right vertex := by
      have parent := represented.root_parent member
      apply rootStored.removeChild_links childMember
      · intro same
        have otherParent := childStored.root_parent
        rw [same] at parent
        omega
      · omega
    exact roots.frame (fun vertex member => (links vertex member).1)
      (fun vertex member => (links vertex member).2)
  have fresh : child.vertex ∉ (root :: rest).map Node.vertex := by
    intro member
    have parent := represented.root_parent member
    have other := childStored.root_parent
    omega
  have rootLessChild : root.key ≤ child.key := by
    have ordered := represented.valid.2.1 root (by simp)
    cases ordered with | make least _ => exact least child childMember
  have noBetter : ¬state.keys child.vertex < state.keys root.vertex := by
    rw [childStored.root_key,rootStored.root_key]
    omega
  constructor
  · apply changed.close_with_ring valid
    apply Or.inr
    have inserted := detachedRing.insert_after fresh
    change Rings.Ring (state.cut child.vertex root.vertex).left
      (state.cut child.vertex root.vertex).right (root.vertex :: child.vertex :: rest.map Node.vertex)
    simpa only [Snapshot.cut,Snapshot.addRoot,Snapshot.removeChild,minimum,
      if_neg (by omega : ¬root.vertex < 0),List.map_cons] using inserted
  · simp [Snapshot.cut,Snapshot.addRoot,Snapshot.removeChild,minimum,
      show ¬root.vertex < 0 by omega,noBetter]

/-- One child-promotion iteration, before clock accounting. The selected child
    is the current header, exactly as read by the source loop. -/
def Snapshot.promoteChild (state : Snapshot) (vertex : Int) : Snapshot :=
  state.cut (state.children vertex) vertex

inductive PromotionRun (vertex : Int) : Snapshot → Snapshot → Nat → Prop where
  | done (state : Snapshot) (childless : state.children vertex < 0) :
      PromotionRun vertex state state 0
  | next {before after : Snapshot} {count : Nat}
      (hasChild : 0 ≤ before.children vertex)
      (rest : PromotionRun vertex (before.promoteChild vertex) after count) :
      PromotionRun vertex before after (count + 1)

/-- The child ring supplies the finite promotion count. Newly promoted roots
    appear after the minimum in reverse promotion order. -/
theorem promote_children_finite (children : List Node) :
    ∀ (state : Snapshot) (vertex key : Int) (marked : Bool) (rest : Forest),
      Represented state (Node.make vertex key marked children :: rest) → state.minimum = vertex →
      ∃ after pending,
        PromotionRun vertex state after children.length ∧
        Represented after (Node.make vertex key marked [] :: pending) ∧
        pending.Perm ((children.map (fun child => child.withMark false)).reverse ++ rest) ∧
        after.minimum = vertex := by
  induction children with
  | nil =>
    intro state vertex key marked rest represented minimum
    have read : state.children vertex = -1 := by
      have stored := represented.stored (.make vertex key marked []) (by simp)
      cases stored
      assumption
    exact ⟨state,rest,.done state (by omega),represented,by simp,minimum⟩
  | cons child children ih =>
    intro state vertex key marked rest represented minimum
    have childHead : state.children vertex = child.vertex := by
      have stored := represented.stored (.make vertex key marked (child :: children)) (by simp)
      cases stored
      assumption
    have nonnegative : 0 ≤ child.vertex := represented.nonnegative child.vertex child.key
      (List.mem_flatMap.mpr ⟨.make vertex key marked (child :: children),by simp,
        Node.child_entries (by simp [Node.children]) child.root_entry⟩)
    have promoted := represented.promote_child (child := child) minimum rfl
    obtain ⟨after,pending,run,representedAfter,permutation,minimumAfter⟩ :=
      ih (state.cut child.vertex vertex) vertex key marked (child.withMark false :: rest)
        promoted.1 promoted.2
    refine ⟨after,pending,?_,representedAfter,?_,minimumAfter⟩
    · apply PromotionRun.next (by omega)
      simpa only [Snapshot.promoteChild,childHead] using run
    · simpa [List.reverse_cons,List.append_assoc] using permutation

/-- All promotions keep the selected root's identity and exhaust its children. -/
theorem Represented.promote_all {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest)) (minimum : state.minimum = root.vertex) :
    ∃ after pending,
      PromotionRun root.vertex state after root.degree ∧
      Represented after (root.withChildren [] :: pending) ∧
      pending.Perm (Forest.promoteChildren root rest) ∧
      after.minimum = root.vertex := by
  cases root with
  | make vertex key marked children =>
    obtain ⟨after,pending,run,representedAfter,permutation,minimumAfter⟩ :=
      promote_children_finite children state vertex key marked rest represented minimum
    refine ⟨after,pending,run,representedAfter,?_,minimumAfter⟩
    exact permutation.trans ((List.reverse_perm _).append_right rest)

/-- The complete pre-consolidation deletion effect contains actual promotion
    steps followed by the source's membership/size/cursor updates. -/
inductive DeleteMinimum (vertex : Int) : Snapshot → Snapshot → Nat → Prop where
  | finish {before promoted : Snapshot} {count : Nat}
      (promotions : PromotionRun vertex before promoted count) :
      DeleteMinimum vertex before (promoted.extractRoot vertex) count

/-- Deletion removes exactly one minimum entry. The root and mark accounting
    is the interface consumed by the logarithmic consolidation cost proof. -/
theorem Represented.delete_minimum_head {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest)) (minimum : state.minimum = root.vertex) :
    ∃ after pending,
      DeleteMinimum root.vertex state after root.degree ∧
      SplitRepresented after pending [] ∧
      (∀ degree, after.table degree < 0) ∧
      ((root.vertex,root.key) :: pending.entries).Perm (Forest.entries (root :: rest)) ∧
      pending.length + 1 = (root :: rest).length + root.degree ∧
      pending.marks ≤ Forest.marks (root :: rest) ∧
      root.degree ≤ 2 * (Forest.entries (root :: rest)).length.log2 + 1 := by
  obtain ⟨promoted,pending,run,representedAfter,permutation,minimumAfter⟩ :=
    represented.promote_all minimum
  have extracted := representedAfter.extract_childless minimumAfter rfl
  have contents := permutation.flatMap_right Node.entries
  have accounting := Forest.promoteChildren_accounting root rest
  have marks : Forest.marks pending = (Forest.promoteChildren root rest).marks :=
    Forest.marks_perm permutation
  refine ⟨promoted.extractRoot root.vertex,pending,.finish run,extracted.1,extracted.2,?_,?_,?_,
    represented.root_degree_bound (by simp)⟩
  · rw [Forest.promoteChildren_entries]
    exact contents.cons _
  · have length := permutation.length_eq
    have roots := accounting.1
    change (Forest.promoteChildren root rest).length + 1 = (root :: rest).length + root.degree at roots
    omega
  · rw [marks]
    exact accounting.2

/-- Removing the current minimum works for every physical root rotation.
    The returned pending representation is exactly the input required by
    consolidation, with membership deletion and amortized accounting attached. -/
theorem Represented.delete_minimum {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (nonempty : forest ≠ []) :
    ∃ after pending promotions,
      DeleteMinimum state.minimum state after promotions ∧
      SplitRepresented after pending [] ∧
      (∀ degree, after.table degree < 0) ∧
      ((state.minimum,state.keys state.minimum) :: Forest.entries pending).Perm forest.entries ∧
      pending.length + 1 = forest.length + promotions ∧
      Forest.marks pending ≤ forest.marks ∧
      promotions ≤ 2 * forest.entries.length.log2 + 1 := by
  obtain ⟨root,member,pointer,least⟩ := represented.minimum.resolve_left (fun empty => nonempty empty.1)
  have readKey := (represented.stored root member).root_key
  obtain ⟨front,back,located⟩ := List.mem_iff_append.mp member
  have original : Represented state (front ++ root :: back) := located ▸ represented
  have rotated : Represented state (root :: (back ++ front)) := original.rotate
  have permutation : (root :: (back ++ front)).Perm forest := by
    rw [located]
    simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
  have lengths := permutation.length_eq
  have entryLengths := (permutation.flatMap_right Node.entries).length_eq
  have marks := Forest.marks_perm permutation
  obtain ⟨after,pending,run,split,scratch,entries,roots,marked,degree⟩ :=
    rotated.delete_minimum_head pointer
  refine ⟨after,pending,root.degree,?_,split,scratch,?_,?_,?_,?_⟩
  · simpa only [pointer] using run
  · rw [pointer,readKey]
    exact entries.trans (permutation.flatMap_right Node.entries)
  · omega
  · omega
  · simpa only [Forest.entries,entryLengths] using degree

@[simp] theorem DeleteMinimum.removed {vertex : Int} {before after : Snapshot} {count : Nat}
    (run : DeleteMinimum vertex before after count) : after.present vertex = 0 := by
  cases run
  simp [Snapshot.extractRoot]

end Algo2Lean.Fibonacci
