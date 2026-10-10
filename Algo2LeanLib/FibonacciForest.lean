import Algo2LeanLib.Fibonacci

/-!
Finite logical forests for the mutable Fibonacci heap.

Vertex handles and keys are mathematical integers. Child lists are newest-first
in link order, matching insertion before the physical child-ring head. A ring
representation still needs to prove that its traversal realizes this finite
forest, with unique handles and the observable parent/mark/degree fields.
-/

namespace Algo2Lean.Fibonacci

inductive Node where
  | make (vertex key : Int) (marked : Bool) (children : List Node) : Node

def Node.vertex : Node → Int
  | .make vertex _ _ _ => vertex

def Node.key : Node → Int
  | .make _ key _ _ => key

def Node.marked : Node → Bool
  | .make _ _ marked _ => marked

def Node.children : Node → List Node
  | .make _ _ _ children => children

def Node.degree (node : Node) : Nat := node.children.length

def Node.entries : Node → List (Int × Int)
  | .make vertex key _ children => (vertex, key) :: children.flatMap Node.entries

def Node.shape : Node → Tree
  | .make _ _ _ children => .node (children.map Node.shape)

def Node.withMark (node : Node) (marked : Bool) : Node :=
  .make node.vertex node.key marked node.children

def Node.withChildren (node : Node) (children : List Node) : Node :=
  .make node.vertex node.key node.marked children

def Node.withKey (node : Node) (key : Int) : Node :=
  .make node.vertex key node.marked node.children

abbrev Forest := List Node

def Forest.entries (forest : Forest) : List (Int × Int) := forest.flatMap Node.entries

def Forest.Unique (forest : Forest) : Prop := (forest.entries.map Prod.fst).Nodup

@[simp] theorem Node.entries_withMark (node : Node) (marked : Bool) :
    (node.withMark marked).entries = node.entries := by cases node; simp [Node.withMark, Node.entries, Node.vertex, Node.key, Node.children]

@[simp] theorem Node.degree_withMark (node : Node) (marked : Bool) :
    (node.withMark marked).degree = node.degree := by cases node; rfl

@[simp] theorem Node.shape_degree (node : Node) : node.shape.degree = node.degree := by
  cases node
  simp [Node.shape, Tree.degree, Node.degree, Node.children]

/-- Shape size counts the actual finite list of represented entries. -/
theorem Node.shape_size (node : Node) : node.shape.nodes = node.entries.length := by
  apply Node.rec
    (motive_1 := fun node => node.shape.nodes = node.entries.length)
    (motive_2 := fun children => (children.map (fun child => child.shape.nodes)).sum =
      (children.flatMap Node.entries).length) _ _ _ node
  · intro vertex key marked children ih
    simp only [Node.shape, Tree.nodes, Node.entries, List.map_map, Function.comp_def, List.length_cons]
    omega
  · simp
  · intro child children childSize tailSize
    simp [childSize, tailSize]

/-- Heap order is local along parent-child edges, recursively throughout each tree. -/
inductive Node.Ordered : Node → Prop where
  | make {vertex key : Int} {marked : Bool} {children : List Node} :
      (∀ child ∈ children, key ≤ child.key) →
      (∀ child ∈ children, child.Ordered) → Node.Ordered (.make vertex key marked children)

def Forest.Ordered (forest : Forest) : Prop := ∀ root ∈ forest, root.Ordered

def Forest.RootsUnmarked (forest : Forest) : Prop := ∀ root ∈ forest, root.marked = false

/-- Rank capacity is the degree plus one for a marked node. The extra unit
    accounts for the single child loss permitted before a cascading cut. -/
def Node.rankCapacity (node : Node) : Nat := node.degree + if node.marked then 1 else 0

def ChildOrder : List Node → Prop
  | [] => True
  | child :: older => older.length ≤ child.rankCapacity ∧ ChildOrder older

inductive Node.Ranked : Node → Prop where
  | make {vertex key : Int} {marked : Bool} {children : List Node} :
      ChildOrder children → (∀ child ∈ children, child.Ranked) →
      Node.Ranked (.make vertex key marked children)

def Forest.Ranked (forest : Forest) : Prop := ∀ root ∈ forest, root.Ranked

def Forest.Valid (forest : Forest) : Prop :=
  forest.Unique ∧ forest.Ordered ∧ forest.Ranked ∧ forest.RootsUnmarked

/-- Forgetting marks gives the weaker rank invariant used for the Fibonacci bound. -/
theorem ChildOrder.shape {children : List Node} (ordered : ChildOrder children) :
    RankOrder (children.map Node.shape) := by
  induction children with
  | nil => trivial
  | cons child older ih =>
    refine ⟨?_, ih ordered.2⟩
    have capacity := ordered.1
    simp only [List.length_map, Node.shape_degree]
    unfold Node.rankCapacity at capacity
    have allowance : (if child.marked then 1 else 0) ≤ (1 : Nat) := by split <;> decide
    omega

theorem Node.Ranked.shape_ranked {node : Node} (ranked : node.Ranked) : node.shape.Ranked := by
  induction ranked with
  | make ordered valid ih =>
    simp only [Node.shape]
    apply Tree.Ranked.node ordered.shape
    intro shape member
    obtain ⟨child, inChildren, rfl⟩ := List.mem_map.mp member
    exact ih child inChildren

theorem Node.Ranked.degree_bound {node : Node} (ranked : node.Ranked) :
    node.degree ≤ 2 * node.entries.length.log2 + 1 := by
  simpa only [Node.shape_degree, Node.shape_size] using ranked.shape_ranked.degree_bound

/-- Local parent-child order implies that the root is a lower bound for every
    key in its subtree, not merely its immediate children. -/
theorem Node.Ordered.root_minimum {node : Node} (ordered : node.Ordered) :
    ∀ vertex key, (vertex, key) ∈ node.entries → node.key ≤ key := by
  induction ordered with
  | make rootBound valid ih =>
    intro vertex key member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, inside⟩
    · exact Int.le_refl _
    · exact Int.le_trans (rootBound child inChildren) (ih child inChildren vertex key inside)

/-- A minimum among the roots is a minimum among all stored vertex/key pairs. -/
theorem Forest.minimum_of_roots {forest : Forest} {minimum : Node}
    (ordered : forest.Ordered) (present : minimum ∈ forest)
    (leastRoot : ∀ root ∈ forest, minimum.key ≤ root.key) :
    (minimum.vertex, minimum.key) ∈ forest.entries ∧
      ∀ vertex key, (vertex, key) ∈ forest.entries → minimum.key ≤ key := by
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨minimum, present, ?_⟩
    cases minimum
    simp [Node.entries, Node.vertex, Node.key]
  · intro vertex key member
    obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
    exact Int.le_trans (leastRoot root inForest) ((ordered root inForest).root_minimum vertex key inside)

/-- Changes to a root's mark do not alter its internal heap order or rank history. -/
theorem Node.Ordered.withMark {node : Node} (ordered : node.Ordered) (marked : Bool) :
    (node.withMark marked).Ordered := by
  cases ordered with
  | make bounds children => exact .make bounds children

theorem Node.Ranked.withMark {node : Node} (ranked : node.Ranked) (marked : Bool) :
    (node.withMark marked).Ranked := by
  cases ranked with
  | make ordered children => exact .make ordered children

/-- Decreasing a root key preserves all comparisons below that root. -/
theorem Node.Ordered.decrease_key {node : Node} (ordered : node.Ordered) (key : Int)
    (decreased : key ≤ node.key) : (node.withKey key).Ordered := by
  cases ordered with
  | make bounds children =>
    exact .make (fun child member => Int.le_trans decreased (bounds child member)) children

theorem Node.Ranked.withKey {node : Node} (ranked : node.Ranked) (key : Int) :
    (node.withKey key).Ranked := by
  cases ranked with
  | make ordered children => exact .make ordered children

/-- Surviving children retain their history order after cuts. -/
theorem ChildOrder.sublist {children kept : List Node} (ordered : ChildOrder children)
    (remaining : kept.Sublist children) : ChildOrder kept := by
  induction remaining with
  | slnil => trivial
  | cons child remaining ih => exact ih ordered.2
  | cons₂ child remaining ih => exact ⟨Nat.le_trans remaining.length_le ordered.1, ih ordered.2⟩

theorem Node.Ordered.prune {node : Node} (ordered : node.Ordered) (kept : List Node)
    (remaining : kept.Sublist node.children) : (node.withChildren kept).Ordered := by
  cases ordered with
  | make bounds children =>
    exact .make (fun child member => bounds child (remaining.subset member))
      (fun child member => children child (remaining.subset member))

theorem Node.Ranked.prune {node : Node} (ranked : node.Ranked) (kept : List Node)
    (remaining : kept.Sublist node.children) : (node.withChildren kept).Ranked := by
  cases ranked with
  | make ordered children =>
    exact .make (ordered.sublist remaining) (fun child member => children child (remaining.subset member))

/-- Equal-degree linking puts the losing root first in its parent's child list
    and clears the losing root's mark, exactly as a Fibonacci-heap link does. -/
def Node.link (parent child : Node) : Node :=
  parent.withChildren (child.withMark false :: parent.children)

theorem Node.Ordered.link {parent child : Node} (parentOrdered : parent.Ordered)
    (childOrdered : child.Ordered) (winner : parent.key ≤ child.key) :
    (parent.link child).Ordered := by
  cases parentOrdered with
  | make bounds children =>
    apply Node.Ordered.make
    · intro node member
      simp only [List.mem_cons] at member
      rcases member with rfl | old
      · exact winner
      · exact bounds node old
    · intro node member
      simp only [List.mem_cons] at member
      rcases member with rfl | old
      · exact childOrdered.withMark false
      · exact children node old

theorem Node.Ranked.link {parent child : Node} (parentRanked : parent.Ranked)
    (childRanked : child.Ranked) (equalDegree : parent.degree = child.degree) :
    (parent.link child).Ranked := by
  cases parentRanked with
  | @make vertex key marked children ordered valid =>
    apply Node.Ranked.make
    · refine ⟨?_, ordered⟩
      change children.length ≤ child.degree
      exact Nat.le_of_eq equalDegree
    · intro node member
      simp only [List.mem_cons] at member
      rcases member with rfl | old
      · exact childRanked.withMark false
      · exact valid node old

/-- Linking changes only the representation of the two trees, not their entries. -/
theorem Node.link_entries (parent child : Node) :
    (parent.link child).entries.Perm (parent.entries ++ child.entries) := by
  cases parent with
  | make vertex key marked children =>
    simpa only [Node.link, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.children,
      Node.entries, List.flatMap_cons, Node.entries_withMark, List.cons_append] using
      (List.perm_append_comm (l₁ := child.entries) (l₂ := children.flatMap Node.entries)).cons (vertex, key)

/-- Removing one child separates exactly that subtree from its parent. -/
theorem Node.cut_entries (parent : Node) (earlier suffix : List Node) (child : Node)
    (located : parent.children = earlier ++ child :: suffix) :
    parent.entries.Perm ((parent.withChildren (earlier ++ suffix)).entries ++ child.entries) := by
  cases parent with
  | make vertex key marked children =>
    change children = earlier ++ child :: suffix at located
    subst children
    simpa only [Node.entries, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.children,
      List.flatMap_append, List.flatMap_cons, List.cons_append, List.append_assoc] using
      ((List.perm_append_comm (l₁ := child.entries) (l₂ := suffix.flatMap Node.entries)).append_left
        (earlier.flatMap Node.entries)).cons (vertex, key)

/-- Cutting an unmarked child once and marking it preserves the capacity its
    parent used in the rank-history invariant. This is why one loss is allowed. -/
theorem Node.first_loss_capacity (node : Node) (kept : List Node)
    (unmarked : node.marked = false) (oneLoss : kept.length + 1 = node.degree) :
    ((node.withChildren kept).withMark true).rankCapacity = node.rankCapacity := by
  cases node with
  | make vertex key marked children =>
    change marked = false at unmarked
    subst marked
    simpa only [Node.rankCapacity, Node.withChildren, Node.withMark, Node.degree, Node.children,
      Node.marked, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using oneLoss

/-- Replacing a child by an equal-or-larger capacity preserves every history
    clause. Earlier siblings see the same number of older children. -/
theorem ChildOrder.replace (earlier suffix : List Node) (before after : Node)
    (ordered : ChildOrder (earlier ++ before :: suffix))
    (capacity : before.rankCapacity ≤ after.rankCapacity) :
    ChildOrder (earlier ++ after :: suffix) := by
  induction earlier with
  | nil => exact ⟨Nat.le_trans ordered.1 capacity, ordered.2⟩
  | cons child earlier ih =>
    exact ⟨by simpa using ordered.1, ih ordered.2⟩

/-- A child replacement with unchanged degree capacity can propagate up a
    tree without weakening any ancestor's rank-history invariant. -/
theorem Node.Ranked.replace_child {parent child replacement : Node}
    (ranked : parent.Ranked) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later)
    (replacementRanked : replacement.Ranked)
    (capacity : child.rankCapacity ≤ replacement.rankCapacity) :
    (parent.withChildren (earlier ++ replacement :: later)).Ranked := by
  cases ranked with
  | make ordered children =>
    simp only [Node.children] at located
    apply Node.Ranked.make
    · rw [located] at ordered
      exact ordered.replace earlier later child replacement capacity
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply children
        rw [located]
        simp [old]
      · exact replacementRanked
      · apply children
        rw [located]
        simp [old]

theorem Node.Ordered.replace_child {parent child replacement : Node}
    (ordered : parent.Ordered) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later)
    (replacementOrdered : replacement.Ordered) (sameKey : replacement.key = child.key) :
    (parent.withChildren (earlier ++ replacement :: later)).Ordered := by
  cases ordered with
  | @make vertex key marked originalChildren bounds children =>
    simp only [Node.children] at located
    have childMember : child ∈ originalChildren := by rw [located]; simp
    apply Node.Ordered.make
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply bounds; rw [located]; simp [old]
      · rw [sameKey]; exact bounds child childMember
      · apply bounds; rw [located]; simp [old]
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply children; rw [located]; simp [old]
      · exact replacementOrdered
      · apply children; rw [located]; simp [old]

def Forest.insertRoot (root : Node) (forest : Forest) : Forest := root.withMark false :: forest

def Forest.linkRoots (parent child : Node) (rest : Forest) : Forest := parent.link child :: rest

def Forest.cutRootChild (parent child : Node) (earlier later : List Node) (rest : Forest) : Forest :=
  parent.withChildren (earlier ++ later) :: child.withMark false :: rest

/-- Content permutations preserve handle uniqueness; no pointer or key
    identity is lost during structural forest operations. -/
theorem Forest.Unique.of_entries_perm {before after : Forest} (unique : before.Unique)
    (contents : after.entries.Perm before.entries) : after.Unique :=
  ((contents.map Prod.fst).nodup_iff).mpr unique

@[simp] theorem Forest.insertRoot_entries (root : Node) (forest : Forest) :
    (insertRoot root forest).entries = root.entries ++ forest.entries := by
  simp [Forest.insertRoot, Forest.entries]

theorem Forest.linkRoots_entries (parent child : Node) (rest : Forest) :
    (linkRoots parent child rest).entries.Perm (Forest.entries (parent :: child :: rest)) := by
  simpa [Forest.linkRoots, Forest.entries, List.append_assoc] using
    (parent.link_entries child).append_right rest.entries

theorem Forest.cutRootChild_entries (parent child : Node) (earlier later : List Node) (rest : Forest)
    (located : parent.children = earlier ++ child :: later) :
    (cutRootChild parent child earlier later rest).entries.Perm (Forest.entries (parent :: rest)) := by
  simpa [Forest.cutRootChild, Forest.entries, List.append_assoc] using
    (parent.cut_entries earlier later child located).symm.append_right rest.entries

/-- An unmarked root can be added when its handles are fresh for the forest. -/
theorem Forest.Valid.insert_root {forest : Forest} (valid : forest.Valid) (root : Node)
    (rootUnique : (root.entries.map Prod.fst).Nodup)
    (rootOrdered : root.Ordered) (rootRanked : root.Ranked)
    (fresh : ∀ vertex ∈ root.entries.map Prod.fst, vertex ∉ forest.entries.map Prod.fst) :
    (insertRoot root forest).Valid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Forest.Unique
    rw [Forest.insertRoot_entries, List.map_append]
    apply List.nodup_append.mpr
    refine ⟨rootUnique, valid.1, ?_⟩
    intro first inRoot second inForest same
    subst second
    exact fresh first inRoot inForest
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact rootOrdered.withMark false
    · exact valid.2.1 node old
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact rootRanked.withMark false
    · exact valid.2.2.1 node old
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · rfl
    · exact valid.2.2.2 node old

/-- Linking the larger-key root under an equal-degree smaller-key root
    preserves all semantic invariants and all represented entries. -/
theorem Forest.Valid.link_roots {parent child : Node} {rest : Forest}
    (valid : (Forest.Valid (parent :: child :: rest)))
    (winner : parent.key ≤ child.key) (equalDegree : parent.degree = child.degree) :
    (linkRoots parent child rest).Valid := by
  have parentMember : parent ∈ parent :: child :: rest := by simp
  have childMember : child ∈ parent :: child :: rest := by simp
  refine ⟨valid.1.of_entries_perm (Forest.linkRoots_entries parent child rest), ?_, ?_, ?_⟩
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.1 parent parentMember).link (valid.2.1 child childMember) winner
    · exact valid.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.2.1 parent parentMember).link (valid.2.2.1 child childMember) equalDegree
    · exact valid.2.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact valid.2.2.2 parent parentMember
    · exact valid.2.2.2 node (by simp [old])

/-- Cutting a child of a root preserves content, heap order, rank history and
    unique handles. The detached subtree becomes an unmarked root. -/
theorem Forest.Valid.cut_root_child {parent child : Node} {rest : Forest}
    (valid : (Forest.Valid (parent :: rest))) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later) :
    (cutRootChild parent child earlier later rest).Valid := by
  have parentMember : parent ∈ parent :: rest := by simp
  have childMember : child ∈ parent.children := by rw [located]; simp
  have remaining : (earlier ++ later).Sublist parent.children := by
    rw [located]
    exact (List.Sublist.refl earlier).append ((List.Sublist.refl later).cons child)
  have parentOrdered := valid.2.1 parent parentMember
  have parentRanked := valid.2.2.1 parent parentMember
  have childOrdered : child.Ordered := by cases parentOrdered with | make _ children => exact children child childMember
  have childRanked : child.Ranked := by cases parentRanked with | make _ children => exact children child childMember
  refine ⟨valid.1.of_entries_perm (Forest.cutRootChild_entries parent child earlier later rest located), ?_, ?_, ?_⟩
  · intro node member
    rcases List.mem_cons.mp member with rfl | tail
    · exact parentOrdered.prune _ remaining
    rcases List.mem_cons.mp tail with rfl | old
    · exact childOrdered.withMark false
    · exact valid.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | tail
    · exact parentRanked.prune _ remaining
    rcases List.mem_cons.mp tail with rfl | old
    · exact childRanked.withMark false
    · exact valid.2.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | tail
    · exact valid.2.2.2 parent parentMember
    rcases List.mem_cons.mp tail with rfl | old
    · rfl
    · exact valid.2.2.2 node (by simp [old])

/-- All marks in a subtree. Valid forests have unmarked roots, so their sum
    counts exactly the marked nonroots used by the potential function. -/
def Node.marks : Node → Nat
  | .make _ _ marked children => (if marked then 1 else 0) + (children.map Node.marks).sum

def Forest.marks (forest : Forest) : Nat := (forest.map Node.marks).sum

def Forest.counts (forest : Forest) : Counts := ⟨forest.length, forest.marks⟩

theorem Node.clear_mark_count (node : Node) :
    (node.withMark false).marks + (if node.marked then 1 else 0) = node.marks := by
  cases node
  simp [Node.withMark, Node.marks, Node.vertex, Node.key, Node.children, Node.marked, Nat.add_comm]

theorem Node.clear_mark_le (node : Node) : (node.withMark false).marks ≤ node.marks := by
  have count := node.clear_mark_count
  omega

theorem Node.link_marks (parent child : Node) :
    (parent.link child).marks + (if child.marked then 1 else 0) = parent.marks + child.marks := by
  cases parent
  simp only [Node.link, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.children,
    Node.marks, List.map_cons, List.sum_cons]
  have clear := child.clear_mark_count
  simp only [Node.marked] at clear
  omega

/-- Concrete forest linking realizes one step of the consolidation accounting relation. -/
theorem Forest.linkRoots_accounting (parent child : Node) (rest : Forest)
    (childUnmarked : child.marked = false) :
    Consolidation (Forest.counts (parent :: child :: rest))
      (Forest.counts (linkRoots parent child rest)) 1 := by
  have markCount : (parent.link child).marks = parent.marks + child.marks := by
    simpa [childUnmarked] using parent.link_marks child
  have before : Forest.counts (parent :: child :: rest) =
      ⟨rest.length + 2, parent.marks + child.marks + rest.marks⟩ := by
    simp [Forest.counts, Forest.marks, Nat.add_assoc]
  have after : Forest.counts (linkRoots parent child rest) =
      ⟨rest.length + 1, parent.marks + child.marks + rest.marks⟩ := by
    simp [Forest.counts, Forest.marks, Forest.linkRoots, markCount]
  rw [before, after]
  exact Consolidation.link (by omega) (.done _)

theorem Node.cut_marks (parent child : Node) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later) :
    (parent.withChildren (earlier ++ later)).marks + child.marks = parent.marks := by
  cases parent with
  | make vertex key marked children =>
    change children = earlier ++ child :: later at located
    subst children
    simp [Node.withChildren, Node.vertex, Node.key, Node.marked,
      Node.marks, List.map_append, List.sum_append_nat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A direct cut followed by stopping at a root matches the same decrease
    accounting rule whether the detached child was marked or unmarked. -/
theorem Forest.cutRootChild_accounting (parent child : Node) (earlier later : List Node) (rest : Forest)
    (located : parent.children = earlier ++ child :: later) :
    Decrease (Forest.counts (parent :: rest))
      (Forest.counts (cutRootChild parent child earlier later rest)) 1 := by
  have cut := parent.cut_marks child earlier later located
  have clear := child.clear_mark_count
  have roots : (Forest.counts (cutRootChild parent child earlier later rest)).roots =
      (Forest.counts (parent :: rest)).roots + 1 := by
    simp [Forest.counts, Forest.cutRootChild]
  have marks : (Forest.counts (cutRootChild parent child earlier later rest)).marks +
      (if child.marked then 1 else 0) = (Forest.counts (parent :: rest)).marks := by
    simp only [Forest.counts, Forest.cutRootChild, Forest.marks, List.map_cons, List.sum_cons]
    omega
  generalize old : Forest.counts (parent :: rest) = before at roots marks ⊢
  generalize new : Forest.counts (cutRootChild parent child earlier later rest) = after at roots marks ⊢
  cases before with
  | mk oldRoots oldMarks =>
    cases after with
    | mk newRoots newMarks =>
      simp only at roots marks
      subst newRoots
      cases mark : child.marked with
      | false =>
        simp only [mark, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at marks
        subst newMarks
        exact Decrease.unmarked (.root _)
      | true =>
        simp only [mark, ↓reduceIte] at marks
        subst oldMarks
        exact Decrease.marked (.root _)

/-- Removing the minimum root promotes its children without changing their keys. -/
def Forest.promoteChildren (minimum : Node) (rest : Forest) : Forest :=
  minimum.children.map (fun child => child.withMark false) ++ rest

theorem Forest.promoteChildren_entries (minimum : Node) (rest : Forest) :
    (Forest.entries (minimum :: rest)) =
      (minimum.vertex, minimum.key) :: (Forest.promoteChildren minimum rest).entries := by
  cases minimum
  simp [Forest.promoteChildren, Forest.entries, Node.entries, Node.children, Node.vertex, Node.key,
    List.flatMap_map]

/-- The forest after removing a root is valid before consolidation starts;
    the removed root's vertex is the only missing entry. -/
theorem Forest.Valid.promote_children {minimum : Node} {rest : Forest}
    (valid : Forest.Valid (minimum :: rest)) : (promoteChildren minimum rest).Valid := by
  have minimumMember : minimum ∈ minimum :: rest := by simp
  have minimumOrdered := valid.2.1 minimum minimumMember
  have minimumRanked := valid.2.2.1 minimum minimumMember
  have orderedChildren : ∀ child ∈ minimum.children, child.Ordered := by
    cases minimumOrdered with | make _ children => exact children
  have rankedChildren : ∀ child ∈ minimum.children, child.Ranked := by
    cases minimumRanked with | make _ children => exact children
  refine ⟨?_, ?_, ?_, ?_⟩
  · have unique := valid.1
    unfold Forest.Unique at *
    rw [Forest.promoteChildren_entries] at unique
    exact (List.nodup_cons.mp unique).2
  · intro root member
    rcases List.mem_append.mp member with promoted | old
    · obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp promoted
      exact (orderedChildren child childMember).withMark false
    · exact valid.2.1 root (by simp [old])
  · intro root member
    rcases List.mem_append.mp member with promoted | old
    · obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp promoted
      exact (rankedChildren child childMember).withMark false
    · exact valid.2.2.1 root (by simp [old])
  · intro root member
    rcases List.mem_append.mp member with promoted | old
    · obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp promoted
      rfl
    · exact valid.2.2.2 root (by simp [old])

/-- Promotion supplies the exact root-count equation and nonincreasing mark
    count used by the amortized extraction theorem. -/
theorem Forest.promoteChildren_accounting (minimum : Node) (rest : Forest) :
    (promoteChildren minimum rest).counts.roots + 1 =
      (Forest.counts (minimum :: rest)).roots + minimum.degree ∧
    (promoteChildren minimum rest).counts.marks ≤ (Forest.counts (minimum :: rest)).marks := by
  have clear : ∀ children : List Node,
      ((children.map (fun child => child.withMark false)).map Node.marks).sum ≤
        (children.map Node.marks).sum := by
    intro children
    induction children with
    | nil => simp
    | cons child children ih =>
      simp only [List.map_cons, List.sum_cons]
      have bound := child.clear_mark_le
      omega
  constructor
  · simp [Forest.counts, Forest.promoteChildren, Node.degree, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · have marks := clear minimum.children
    cases minimum
    simp only [Forest.counts, Forest.marks, Forest.promoteChildren, Node.children,
      List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, Node.marks]
    simp only [Node.children] at marks
    omega

/-- A first child loss inside a nonroot is absorbed by its mark. Replacing
    that child in its parent preserves the full stronger rank invariant. -/
theorem Node.Ranked.first_loss_in_parent {parent child : Node}
    (ranked : parent.Ranked) (earlier later kept : List Node)
    (located : parent.children = earlier ++ child :: later)
    (remaining : kept.Sublist child.children) (unmarked : child.marked = false)
    (oneLoss : kept.length + 1 = child.degree) :
    (parent.withChildren (earlier ++ (child.withChildren kept).withMark true :: later)).Ranked := by
  have childMember : child ∈ parent.children := by rw [located]; simp
  have childRanked : child.Ranked := by cases ranked with | make _ children => exact children child childMember
  apply ranked.replace_child earlier later located ((childRanked.prune kept remaining).withMark true)
  exact Nat.le_of_eq (child.first_loss_capacity kept unmarked oneLoss).symm

/-- The same first-loss replacement preserves key order: it changes only
    pointers, degree and mark, while the affected node's root key is unchanged. -/
theorem Node.Ordered.first_loss_in_parent {parent child : Node}
    (ordered : parent.Ordered) (earlier later kept : List Node)
    (located : parent.children = earlier ++ child :: later)
    (remaining : kept.Sublist child.children) :
    (parent.withChildren (earlier ++ (child.withChildren kept).withMark true :: later)).Ordered := by
  have childMember : child ∈ parent.children := by rw [located]; simp
  have childOrdered : child.Ordered := by cases ordered with | make _ children => exact children child childMember
  apply ordered.replace_child earlier later located ((childOrdered.prune kept remaining).withMark true)
  rfl

@[simp] theorem Node.withKey_vertices (node : Node) (key : Int) :
    ((node.withKey key).entries.map Prod.fst) = (node.entries.map Prod.fst) := by
  cases node
  simp [Node.withKey, Node.entries, Node.vertex, Node.marked, Node.children]

/-- Decreasing the key of a root needs no cut and preserves the forest invariants. -/
theorem Forest.Valid.decrease_root {root : Node} {rest : Forest}
    (valid : Forest.Valid (root :: rest)) (key : Int) (decreased : key ≤ root.key) :
    Forest.Valid (root.withKey key :: rest) := by
  have rootMember : root ∈ root :: rest := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have unique := valid.1
    simpa [Forest.Unique, Forest.entries] using unique
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.1 root rootMember).decrease_key key decreased
    · exact valid.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.2.1 root rootMember).withKey key
    · exact valid.2.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact valid.2.2.2 root rootMember
    · exact valid.2.2.2 node (by simp [old])

end Algo2Lean.Fibonacci
