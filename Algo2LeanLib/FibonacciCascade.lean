import Algo2LeanLib.FibonacciForest

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- One ancestor records the siblings before and after the focused subtree.
    Contexts are ordered from the immediate parent towards the root. -/
structure Ancestor where
  vertex : Int
  key : Int
  marked : Bool
  before : List Node
  after : List Node

def Ancestor.plug (frame : Ancestor) (node : Node) : Node :=
  .make frame.vertex frame.key frame.marked (frame.before ++ node :: frame.after)

def Ancestors.plug (context : List Ancestor) (node : Node) : Node :=
  match context with
  | [] => node
  | frame :: rest => Ancestors.plug rest (frame.plug node)

/-- Logical cascade after the focused node loses one child. A marked nonroot
    is promoted and propagation continues; an unmarked nonroot is marked. -/
def cascadeForest (node : Node) (kept : List Node) : List Ancestor → Forest
  | [] => [node.withChildren kept]
  | frame :: rest =>
    if node.marked then
      (node.withChildren kept).withMark false ::
        cascadeForest (frame.plug node) (frame.before ++ frame.after) rest
    else
      [Ancestors.plug (frame :: rest) ((node.withChildren kept).withMark true)]

theorem Ancestor.focus_ranked {frame : Ancestor} {node : Node}
    (ranked : (frame.plug node).Ranked) : node.Ranked := by
  cases ranked with
  | make history children => exact children node (by simp)

theorem Ancestor.focus_ordered {frame : Ancestor} {node : Node}
    (ordered : (frame.plug node).Ordered) : node.Ordered := by
  cases ordered with
  | make bounds children => exact children node (by simp)

theorem Ancestors.focus_ranked {context : List Ancestor} {node : Node}
    (ranked : (Ancestors.plug context node).Ranked) : node.Ranked := by
  induction context generalizing node with
  | nil => exact ranked
  | cons frame rest ih => exact Ancestor.focus_ranked (ih ranked)

theorem Ancestors.focus_ordered {context : List Ancestor} {node : Node}
    (ordered : (Ancestors.plug context node).Ordered) : node.Ordered := by
  induction context generalizing node with
  | nil => exact ordered
  | cons frame rest ih => exact Ancestor.focus_ordered (ih ordered)

/-- An unchanged address/key with at least the old rank capacity can replace
    the focused subtree without changing any ancestor's rank-history clause. -/
theorem Ancestors.replace_ranked {context : List Ancestor} {before after : Node}
    (ranked : (Ancestors.plug context before).Ranked) (replacement : after.Ranked)
    (capacity : before.rankCapacity ≤ after.rankCapacity) : (Ancestors.plug context after).Ranked := by
  induction context generalizing before after with
  | nil => exact replacement
  | cons frame rest ih =>
    have old := Ancestors.focus_ranked (context := rest) ranked
    have next : (frame.plug after).Ranked :=
      old.replace_child frame.before frame.after rfl replacement capacity
    apply ih ranked next
    simp [Ancestor.plug, Node.rankCapacity, Node.degree, Node.children, Node.marked]

theorem Ancestors.replace_ordered {context : List Ancestor} {before after : Node}
    (ordered : (Ancestors.plug context before).Ordered) (replacement : after.Ordered)
    (sameKey : after.key = before.key) : (Ancestors.plug context after).Ordered := by
  induction context generalizing before after with
  | nil => exact replacement
  | cons frame rest ih =>
    have old := Ancestors.focus_ordered (context := rest) ordered
    have next : (frame.plug after).Ordered :=
      old.replace_child frame.before frame.after rfl replacement sameKey
    apply ih ordered next
    rfl

theorem Ancestors.plug_mark {context : List Ancestor} {before after : Node}
    (same : before.marked = after.marked) : (Ancestors.plug context before).marked = (Ancestors.plug context after).marked := by
  induction context generalizing before after with
  | nil => exact same
  | cons frame rest ih => exact ih rfl

theorem Ancestors.nonempty_mark (frame : Ancestor) (rest : List Ancestor) (before after : Node) :
    (Ancestors.plug (frame :: rest) before).marked = (Ancestors.plug (frame :: rest) after).marked := by
  exact Ancestors.plug_mark (context := rest) rfl

/-- Cascade repair restores heap order and the stronger marked-child rank
    history, for any number of consecutively marked ancestors. -/
theorem cascadeForest_invariants (context : List Ancestor) (node : Node) (kept : List Node)
    (remaining : kept.Sublist node.children) (oneLoss : kept.length + 1 = node.degree)
    (ordered : (Ancestors.plug context node).Ordered) (ranked : (Ancestors.plug context node).Ranked)
    (rootUnmarked : (Ancestors.plug context node).marked = false) :
    (cascadeForest node kept context).Ordered ∧ (cascadeForest node kept context).Ranked ∧
      (cascadeForest node kept context).RootsUnmarked := by
  induction context generalizing node kept with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro root member
      have same := List.mem_singleton.mp member
      subst root
      exact ordered.prune kept remaining
    · intro root member
      have same := List.mem_singleton.mp member
      subst root
      exact ranked.prune kept remaining
    · intro root member
      have same := List.mem_singleton.mp member
      subst root
      exact rootUnmarked
  | cons frame rest ih =>
    have nodeOrdered := Ancestors.focus_ordered ordered
    have nodeRanked := Ancestors.focus_ranked ranked
    by_cases marked : node.marked = true
    · have retained : (frame.before ++ frame.after).Sublist (frame.plug node).children :=
        (List.Sublist.refl frame.before).append ((List.Sublist.refl frame.after).cons node)
      have one : (frame.before ++ frame.after).length + 1 = (frame.plug node).degree := by
        simp [Ancestor.plug, Node.degree, Node.children, Nat.add_assoc]
      have tail := ih (frame.plug node) (frame.before ++ frame.after) retained one ordered ranked rootUnmarked
      refine ⟨?_, ?_, ?_⟩
      · intro root member
        simp only [cascadeForest, marked, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | old
        · exact (nodeOrdered.prune kept remaining).withMark false
        · exact tail.1 root old
      · intro root member
        simp only [cascadeForest, marked, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | old
        · exact (nodeRanked.prune kept remaining).withMark false
        · exact tail.2.1 root old
      · intro root member
        simp only [cascadeForest, marked, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | old
        · rfl
        · exact tail.2.2 root old
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      have capacity := node.first_loss_capacity kept unmarked oneLoss
      have newOrdered := Ancestors.replace_ordered ordered ((nodeOrdered.prune kept remaining).withMark true) rfl
      have newRanked := Ancestors.replace_ranked ranked ((nodeRanked.prune kept remaining).withMark true)
        (Nat.le_of_eq capacity.symm)
      refine ⟨?_, ?_, ?_⟩
      · intro root member
        simp [cascadeForest, unmarked] at member
        subst root
        exact newOrdered
      · intro root member
        simp [cascadeForest, unmarked] at member
        subst root
        exact newRanked
      · intro root member
        simp [cascadeForest, unmarked] at member
        subst root
        exact (Ancestors.nonempty_mark frame rest _ node).trans rootUnmarked

/-- Entry accounting can be propagated through any ancestor context. -/
theorem Ancestors.entries_replace {context : List Ancestor} {before after : Node} {removed : List (Int × Int)}
    (contents : before.entries.Perm (after.entries ++ removed)) :
    (Ancestors.plug context before).entries.Perm ((Ancestors.plug context after).entries ++ removed) := by
  induction context generalizing before after with
  | nil => exact contents
  | cons frame rest ih =>
    apply ih
    have first := ((contents.append_right (frame.after.flatMap Node.entries)).append_left
      (frame.before.flatMap Node.entries)).cons (frame.vertex, frame.key)
    have second := (List.perm_append_comm (l₁ := removed) (l₂ := frame.after.flatMap Node.entries)).append_left
      ((frame.vertex, frame.key) :: (frame.before.flatMap Node.entries ++ after.entries))
    simp only [List.append_assoc, List.cons_append] at first second
    exact (by simpa only [Ancestor.plug, Node.entries, List.flatMap_append,
      List.flatMap_cons, List.append_assoc, List.cons_append] using first.trans second)

/-- Cascade removes exactly the initially cut entries. Promoting marked
    ancestors neither loses nor duplicates any remaining vertex or key. -/
theorem cascadeForest_entries (context : List Ancestor) (node : Node) (kept : List Node)
    (removed : List (Int × Int))
    (contents : node.entries.Perm ((node.withChildren kept).entries ++ removed)) :
    (Ancestors.plug context node).entries.Perm ((cascadeForest node kept context).entries ++ removed) := by
  induction context generalizing node kept removed with
  | nil => simpa [cascadeForest, Forest.entries] using! contents
  | cons frame rest ih =>
    by_cases marked : node.marked = true
    · have cut := (frame.plug node).cut_entries frame.before frame.after node rfl
      have recursive := ih (frame.plug node) (frame.before ++ frame.after) node.entries cut
      have replace := contents.append_left (cascadeForest (frame.plug node) (frame.before ++ frame.after) rest).entries
      have reorder := (List.perm_append_comm
          (l₁ := (cascadeForest (frame.plug node) (frame.before ++ frame.after) rest).entries)
          (l₂ := (node.withChildren kept).entries)).append_right removed
      simp only [List.append_assoc] at replace reorder
      apply recursive.trans
      simpa only [cascadeForest, marked, ↓reduceIte, Forest.entries, List.flatMap_cons,
        Node.entries_withMark, List.append_assoc] using replace.trans reorder
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      have changed : node.entries.Perm (((node.withChildren kept).withMark true).entries ++ removed) := by
        simpa only [Node.entries_withMark] using contents
      have lifted := Ancestors.entries_replace (context := frame :: rest) changed
      simpa [cascadeForest, unmarked, Forest.entries] using lifted

/-- Cutting an arbitrary descendant and repairing its ancestors preserves the
    complete finite-forest invariant. The newly cut node is a separate root. -/
theorem cascadeForest_valid (context : List Ancestor) (node child : Node) (before after : List Node)
    (located : node.children = before ++ child :: after)
    (valid : Forest.Valid [Ancestors.plug context node]) :
    Forest.Valid (child.withMark false :: cascadeForest node (before ++ after) context) := by
  have rootMember : Ancestors.plug context node ∈ [Ancestors.plug context node] := by simp
  have ordered := valid.2.1 _ rootMember
  have ranked := valid.2.2.1 _ rootMember
  have unmarked := valid.2.2.2 _ rootMember
  have nodeOrdered := Ancestors.focus_ordered ordered
  have nodeRanked := Ancestors.focus_ranked ranked
  have member : child ∈ node.children := by rw [located]; simp
  have childOrdered : child.Ordered := by cases nodeOrdered with | make _ children => exact children child member
  have childRanked : child.Ranked := by cases nodeRanked with | make _ children => exact children child member
  have remaining : (before ++ after).Sublist node.children := by
    rw [located]
    exact (List.Sublist.refl before).append ((List.Sublist.refl after).cons child)
  have oneLoss : (before ++ after).length + 1 = node.degree := by
    unfold Node.degree
    rw [located]
    simp [Nat.add_assoc]
  have repaired := cascadeForest_invariants context node (before ++ after) remaining oneLoss ordered ranked unmarked
  have contents := cascadeForest_entries context node (before ++ after) child.entries
    (node.cut_entries before after child located)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply valid.1.of_entries_perm
    have permutation := List.perm_append_comm.trans contents.symm
    simpa [Forest.entries] using permutation
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact childOrdered.withMark false
    · exact repaired.1 root old
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact childRanked.withMark false
    · exact repaired.2.1 root old
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · rfl
    · exact repaired.2.2 root old

/-- Marks contributed by ancestors and siblings, excluding the focused subtree. -/
def Ancestor.marks (frame : Ancestor) : Nat :=
  (if frame.marked then 1 else 0) + Forest.marks frame.before + Forest.marks frame.after

def Ancestors.marks (context : List Ancestor) : Nat := (context.map Ancestor.marks).sum

theorem Ancestor.plug_marks (frame : Ancestor) (node : Node) :
    (frame.plug node).marks = node.marks + frame.marks := by
  simp [Ancestor.plug, Node.marks, Ancestor.marks, Forest.marks,
    List.sum_append_nat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Ancestors.plug_marks (context : List Ancestor) (node : Node) :
    (Ancestors.plug context node).marks = node.marks + Ancestors.marks context := by
  induction context generalizing node with
  | nil => simp [Ancestors.plug, Ancestors.marks]
  | cons frame rest ih => simp [Ancestors.plug, ih, Ancestor.plug_marks, Ancestors.marks, Nat.add_assoc]

/-- The number of additionally promoted ancestors; the initially requested
    child cut is accounted for separately. -/
def cascadeCuts (node : Node) : List Ancestor → Nat
  | [] => 0
  | frame :: rest => if node.marked then cascadeCuts (frame.plug node) rest + 1 else 0

/-- Concrete ancestor repair realizes the potential-accounting cascade,
    including arbitrary roots and marks elsewhere in the forest. -/
theorem cascadeForest_accounting (context : List Ancestor) (node : Node) (kept : List Node)
    (otherRoots otherMarks : Nat) :
    Cascade ⟨1 + otherRoots, (Ancestors.plug context (node.withChildren kept)).marks + otherMarks⟩
      ⟨(cascadeForest node kept context).length + otherRoots,
        (cascadeForest node kept context).marks + otherMarks⟩ (cascadeCuts node context) := by
  induction context generalizing node kept otherRoots otherMarks with
  | nil => simpa [cascadeForest, cascadeCuts, Ancestors.plug, Forest.marks] using (Cascade.root
      (Counts.mk (1 + otherRoots) ((node.withChildren kept).marks + otherMarks)))
  | cons frame rest ih =>
    by_cases marked : node.marked = true
    · let detached := (node.withChildren kept).withMark false
      have prunedMarked : (node.withChildren kept).marked = true := marked
      have clearing : detached.marks + 1 = (node.withChildren kept).marks := by
        simpa only [detached, prunedMarked, ↓reduceIte] using
          (node.withChildren kept).clear_mark_count
      have parentMarks : ((frame.plug node).withChildren (frame.before ++ frame.after)).marks = frame.marks := by
        simp [Ancestor.plug, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.marks,
          Ancestor.marks, Forest.marks, List.sum_append_nat, Nat.add_assoc]
      have next := ih (frame.plug node) (frame.before ++ frame.after) (otherRoots + 1)
        (detached.marks + otherMarks)
      simp only [Ancestors.plug_marks, parentMarks] at next
      have nextNormalized : Cascade
          ⟨(1 + otherRoots) + 1, detached.marks + frame.marks + Ancestors.marks rest + otherMarks⟩
          ⟨(cascadeForest node kept (frame :: rest)).length + otherRoots,
            (cascadeForest node kept (frame :: rest)).marks + otherMarks⟩
          (cascadeCuts (frame.plug node) rest) := by
        simpa only [cascadeForest, marked, ↓reduceIte, List.length_cons, Forest.marks,
          List.map_cons, List.sum_cons, detached, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
      have result := Cascade.cut nextNormalized
      simpa only [cascadeCuts, marked, ↓reduceIte, Ancestors.plug_marks, Ancestors.marks,
        List.map_cons, List.sum_cons, ← clearing, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      have changed : ((node.withChildren kept).withMark true).marks = (node.withChildren kept).marks + 1 := by
        cases node
        simp_all [Node.withChildren, Node.withMark, Node.marks, Node.vertex, Node.key, Node.marked, Node.children, Nat.add_comm]
      simpa [cascadeForest, cascadeCuts, unmarked, Forest.marks, Ancestors.plug_marks, changed, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Cascade.mark (1 + otherRoots) ((Ancestors.plug (frame :: rest) (node.withChildren kept)).marks + otherMarks)

/-- Full cut-and-cascade accounting agrees with the potential model, including
    marks in the cut subtree and any untouched roots. -/
theorem cascadeForest_decrease_accounting (context : List Ancestor) (node child : Node)
    (before after : List Node) (rest : Forest)
    (located : node.children = before ++ child :: after) :
    Decrease (Forest.counts (Ancestors.plug context node :: rest))
      (Forest.counts (child.withMark false :: cascadeForest node (before ++ after) context ++ rest))
      (cascadeCuts node context + 1) := by
  let final := Forest.counts (child.withMark false :: cascadeForest node (before ++ after) context ++ rest)
  let remainingMarks := (Ancestors.plug context (node.withChildren (before ++ after))).marks +
    (child.withMark false).marks + rest.marks
  have cascade : Cascade ⟨rest.length + 2, remainingMarks⟩ final (cascadeCuts node context) := by
    have result := cascadeForest_accounting context node (before ++ after) (rest.length + 1)
      ((child.withMark false).marks + rest.marks)
    simpa only [final, remainingMarks, Forest.counts, List.length_cons, List.length_append,
      Forest.marks, List.map_cons, List.map_append, List.sum_cons, List.sum_append_nat,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
  have originalMarks : (Ancestors.plug context node).marks + rest.marks =
      remainingMarks + (if child.marked then 1 else 0) := by
    have cut := node.cut_marks child before after located
    have clear := child.clear_mark_count
    simp only [remainingMarks, Ancestors.plug_marks]
    omega
  have originalCounts : Forest.counts (Ancestors.plug context node :: rest) =
      ⟨rest.length + 1, remainingMarks + (if child.marked then 1 else 0)⟩ := by
    simp only [Forest.counts, List.length_cons, Forest.marks, List.map_cons, List.sum_cons]
    simp only [Forest.marks] at originalMarks
    rw [originalMarks]
  rw [originalCounts]
  change Decrease _ final _
  cases marked : child.marked with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Decrease.unmarked cascade
  | true =>
    simp only [↓reduceIte]
    exact Decrease.marked cascade

end Algo2Lean.Fibonacci
