import Algo2LeanLib.FibonacciForest
import Algo2LeanLib.FibonacciRings

/-!
The representation boundary between Fibonacci forests and mutable indexed storage.
Snapshots contain ordinary array observations, not a compiler configuration or a
transcript. A compiled operation must establish preservation of this relation.
-/

namespace Algo2Lean.Fibonacci

structure Snapshot where
  keys : Int → Int
  parents : Int → Int
  children : Int → Int
  left : Int → Int
  right : Int → Int
  degrees : Int → Int
  marks : Int → Int
  present : Int → Int
  table : Int → Int
  minimum : Int
  size : Int

/-- Every node has the observed key, parent, mark, degree, and child-ring head.
    The finite child list witnesses termination of a ring traversal. -/
inductive Stored (state : Snapshot) : Int → Node → Prop where
  | node {vertex key parent : Int} {marked : Bool} {children : List Node}
      (readKey : state.keys vertex = key)
      (readParent : state.parents vertex = parent)
      (readMark : state.marks vertex = if marked then 1 else 0)
      (readDegree : state.degrees vertex = children.length)
      (readPresent : state.present vertex = 1)
      (readChild : state.children vertex =
        match children with | [] => -1 | first :: _ => first.vertex)
      (childRing : Rings.RingOrEmpty state.left state.right (children.map Node.vertex))
      (subtrees : ∀ child ∈ children, Stored state vertex child) :
      Stored state parent (.make vertex key marked children)

theorem Stored.root_key {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.keys node.vertex = node.key := by
  cases stored
  assumption

theorem Stored.root_present {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.present node.vertex = 1 := by
  cases stored
  assumption

theorem Stored.root_degree {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.degrees node.vertex = node.degree := by
  cases stored
  assumption

/-- Storage reads agree with every logical entry, not only the root. -/
theorem Stored.entries {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) :
    ∀ vertex key, (vertex, key) ∈ node.entries →
      state.keys vertex = key ∧ state.present vertex = 1 := by
  induction stored with
  | node key parent mark degree present childHead ring children ih =>
    intro vertex value member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, member⟩
    · exact ⟨key, present⟩
    · exact ih child inChildren vertex value member

/-- A complete public queue invariant. Sentinel and exact-membership clauses
    are explicit; a class tag or valid forest alone is insufficient. -/
structure Represented (state : Snapshot) (forest : Forest) : Prop where
  valid : forest.Valid
  roots : Rings.RingOrEmpty state.left state.right (forest.map Node.vertex)
  stored : ∀ root ∈ forest, Stored state (-1) root
  nonnegative : ∀ vertex key, (vertex, key) ∈ forest.entries → 0 ≤ vertex
  presence : ∀ vertex, state.present vertex ≠ 0 ↔ ∃ key, (vertex, key) ∈ forest.entries
  size : state.size = forest.entries.length
  minimum : (forest = [] ∧ state.minimum = -1) ∨
    ∃ root ∈ forest, state.minimum = root.vertex ∧ ∀ other ∈ forest, root.key ≤ other.key
  /-- Any negative entry is an empty scratch bucket, exactly as tested by the source. -/
  scratch : ∀ degree, state.table degree < 0

theorem Represented.entry {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (member : (vertex, key) ∈ forest.entries) :
    state.keys vertex = key ∧ state.present vertex = 1 := by
  obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
  exact (represented.stored root inForest).entries vertex key inside

theorem Represented.present_nonnegative {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int}
    (present : state.present vertex ≠ 0) : 0 ≤ vertex := by
  obtain ⟨key, member⟩ := (represented.presence vertex).mp present
  exact represented.nonnegative vertex key member

/-- The public minimum pointer identifies a present globally minimum key. -/
theorem Represented.minimum_key {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (nonempty : forest ≠ []) :
    0 ≤ state.minimum ∧ state.present state.minimum = 1 ∧
      ∀ vertex, state.present vertex ≠ 0 → state.keys state.minimum ≤ state.keys vertex := by
  rcases represented.minimum with ⟨empty, _⟩ | ⟨root, inForest, pointer, least⟩
  · exact False.elim (nonempty empty)
  obtain ⟨rootEntry, minimum⟩ := Forest.minimum_of_roots represented.valid.2.1 inForest least
  have rootValues := represented.entry rootEntry
  rw [pointer]
  refine ⟨represented.nonnegative _ _ rootEntry, rootValues.2, ?_⟩
  intro vertex present
  obtain ⟨key, member⟩ := (represented.presence vertex).mp present
  rw [rootValues.1, (represented.entry member).1]
  exact minimum vertex key member

theorem Represented.empty_iff {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) : state.minimum < 0 ↔ forest = [] := by
  constructor
  · intro negative
    by_cases empty : forest = []
    · exact empty
    · have bound := represented.minimum_key empty
      omega
  · intro empty
    rcases represented.minimum with ⟨_, pointer⟩ | ⟨root, member, _⟩
    · omega
    · simp [empty] at member

theorem Represented.empty_presence {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (empty : forest = []) :
    ∀ vertex, state.present vertex = 0 := by
  intro vertex
  have absent := represented.presence vertex
  simp [empty, Forest.entries] at absent
  exact absent

/-- A represented root obeys the same logarithmic bound used in consolidation. -/
theorem Represented.root_degree_bound {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {root : Node} (member : root ∈ forest) :
    root.degree ≤ 2 * forest.entries.length.log2 + 1 := by
  have included : root.entries.length ≤ forest.entries.length := by
    obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp member
    rw [equal]
    simp [Forest.entries, List.flatMap_append]
    omega
  have contained : root.shape.nodes ≤ forest.entries.length := by
    simpa only [Node.shape_size] using included
  simpa only [Node.shape_degree] using
    (represented.valid.2.2.1 root member).shape_ranked.degree_bound_of_size contained

/-- The constructor's observable empty state establishes the invariant without
    any assumptions about unused sequence cells or pre-existing client data. -/
theorem Represented.empty (state : Snapshot)
    (absent : ∀ vertex, state.present vertex = 0)
    (emptySize : state.size = 0) (emptyMinimum : state.minimum = -1)
    (table : ∀ degree, state.table degree = -1) : Represented state [] := by
  refine ⟨?_, Or.inl rfl, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, emptyMinimum⟩, fun degree => by rw [table degree]; omega⟩
  · simp [Forest.Valid, Forest.Unique, Forest.entries, Forest.Ordered,
      Forest.Ranked, Forest.RootsUnmarked]
  · simp
  · simp [Forest.entries]
  · simp [absent, Forest.entries]
  · simpa [Forest.entries] using emptySize

/-- Observable node metadata; sibling pointers are framed separately because
    a subtree's root may move between rings without changing its descendants. -/
structure Snapshot.SameFields (before after : Snapshot) (vertex : Int) : Prop where
  key : after.keys vertex = before.keys vertex
  parent : after.parents vertex = before.parents vertex
  child : after.children vertex = before.children vertex
  degree : after.degrees vertex = before.degrees vertex
  mark : after.marks vertex = before.marks vertex
  present : after.present vertex = before.present vertex

@[simp] theorem Node.root_entry (node : Node) : (node.vertex, node.key) ∈ node.entries := by
  cases node
  simp [Node.vertex, Node.key, Node.entries]

theorem Node.child_entries {node child : Node} (childMember : child ∈ node.children)
    {vertex key : Int} (inside : (vertex, key) ∈ child.entries) : (vertex, key) ∈ node.entries := by
  cases node
  simp only [Node.children] at childMember
  simp only [Node.entries, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨child, childMember, inside⟩

theorem Node.descendant_entries {node : Node} {vertex key : Int}
    (member : (vertex, key) ∈ node.children.flatMap Node.entries) : (vertex, key) ∈ node.entries := by
  obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
  exact Node.child_entries childMember inside

theorem Stored.root_parent {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.parents node.vertex = parent := by
  cases stored
  assumption

/-- A stored subtree can be reused when its metadata and its descendants'
    sibling pointers are preserved. The root's own sibling pointers are irrelevant. -/
theorem Stored.frame {before after : Snapshot} {parent : Int} {node : Node}
    (stored : Stored before parent node)
    (fields : ∀ vertex key, (vertex, key) ∈ node.entries → Snapshot.SameFields before after vertex)
    (links : ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after parent node := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    have rootFields := fields vertex key (by simp [Node.entries])
    refine Stored.node (rootFields.key.trans readKey) (rootFields.parent.trans readParent)
      (rootFields.mark.trans readMark) (rootFields.degree.trans readDegree)
      (rootFields.present.trans readPresent)
      (by cases children <;> exact rootFields.child.trans readChild) ?_ ?_
    · rcases ring with empty | ring
      · exact Or.inl empty
      · apply Or.inr
        apply ring.frame
        · intro value member
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).1
        · intro value member
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).2
    · intro child member
      apply ih child member
      · intro vertex key inside
        apply fields vertex key
        exact Node.child_entries member inside
      · intro vertex key inside
        apply links vertex key
        exact List.mem_flatMap.mpr ⟨child, member, Node.descendant_entries inside⟩

/-- Nonroot entries have nonnegative parent handles. This lets root-ring
    rewiring be separated from every stored subtree's internal child rings. -/
theorem Stored.parents_nonnegative {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (parentNonnegative : 0 ≤ parent)
    (verticesNonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex) :
    ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ state.parents vertex := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro value weight member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, childMember, inside⟩
    · simpa only [readParent] using parentNonnegative
    · apply ih child childMember _ _ value weight inside
      · exact verticesNonnegative vertex key (by simp [Node.entries])
      · intro descendant descendantKey descendantMember
        exact verticesNonnegative descendant descendantKey (Node.child_entries childMember descendantMember)

/-- Preserving all active nonroot pointers suffices to preserve each old tree
    when only root-ring links and previously absent array cells are changed. -/
theorem Stored.frame_roots {before after : Snapshot} {parent : Int} {node : Node}
    (stored : Stored before parent node)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex)
    (fields : ∀ vertex key, (vertex, key) ∈ node.entries → Snapshot.SameFields before after vertex)
    (links : ∀ vertex, before.present vertex = 1 → 0 ≤ before.parents vertex →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after parent node := by
  apply stored.frame fields
  intro vertex key member
  obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
  have childrenStored : ∀ child ∈ node.children, Stored before node.vertex child := by
    cases stored with | node _ _ _ _ _ _ _ children => exact children
  have childStored := childrenStored child childMember
  apply links vertex ((childStored.entries vertex key inside).2)
  exact childStored.parents_nonnegative (nonnegative node.vertex node.key node.root_entry)
    (fun value weight inside => nonnegative value weight (Node.child_entries childMember inside)) vertex key inside


/-- Reordering roots changes neither heap order nor the rank history inside a tree. -/
theorem Forest.Valid.perm {before after : Forest} (valid : before.Valid)
    (permutation : after.Perm before) : after.Valid := by
  refine ⟨valid.1.of_entries_perm (permutation.flatMap_right Node.entries), ?_, ?_, ?_⟩
  · intro root member
    exact valid.2.1 root (permutation.mem_iff.mp member)
  · intro root member
    exact valid.2.2.1 root (permutation.mem_iff.mp member)
  · intro root member
    exact valid.2.2.2 root (permutation.mem_iff.mp member)

/-- A cyclic choice of the first root does not alter the represented snapshot. -/
theorem Represented.rotate {state : Snapshot} {front back : Forest}
    (represented : Represented state (front ++ back)) : Represented state (back ++ front) := by
  have permutation : (back ++ front).Perm (front ++ back) := List.perm_append_comm
  have contents := permutation.flatMap_right Node.entries
  refine ⟨represented.valid.perm permutation, ?_, ?_, ?_, ?_, ?_, ?_, represented.scratch⟩
  · simpa only [List.map_append] using (Rings.RingOrEmpty.rotate_append (front.map Node.vertex) (back.map Node.vertex) (by simpa only [List.map_append] using represented.roots))
  · intro root member
    exact represented.stored root (permutation.mem_iff.mp member)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · rcases represented.minimum with ⟨empty, pointer⟩ | ⟨root, member, pointer, least⟩
    · left
      exact ⟨by simpa only [List.append_eq_nil_iff, and_comm] using empty, pointer⟩
    · exact Or.inr ⟨root, permutation.mem_iff.mpr member, pointer,
        fun other member => least other (permutation.mem_iff.mp member)⟩

/-- Exact observable effect of inserting a previously absent singleton through
    `push_or_decrease` and `add_root`; clocks are handled independently. -/
def Snapshot.insertSingleton (state : Snapshot) (vertex key : Int) : Snapshot :=
  { state with
    keys := Rings.write state.keys vertex key
    parents := Rings.write state.parents vertex (-1)
    children := Rings.write state.children vertex (-1)
    degrees := Rings.write state.degrees vertex 0
    marks := Rings.write state.marks vertex 0
    present := Rings.write state.present vertex 1
    size := state.size + 1
    left := if state.minimum < 0 then Rings.write state.left vertex vertex
      else Rings.insertAfterLeft state.left state.right state.minimum vertex
    right := if state.minimum < 0 then Rings.write state.right vertex vertex
      else Rings.insertAfterRight state.right state.minimum vertex
    minimum := if state.minimum < 0 then vertex
      else if key < state.keys state.minimum then vertex else state.minimum }

private theorem singleton_valid (vertex key : Int) : Forest.Valid [Node.make vertex key false []] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Forest.Unique, Forest.entries, Node.entries]
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact Node.Ordered.make (by simp) (by simp)
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact Node.Ranked.make (by trivial) (by simp)
  · simp [Forest.RootsUnmarked, Node.marked]

private theorem singleton_stored (state : Snapshot) (vertex key : Int) :
    Stored (state.insertSingleton vertex key) (-1) (Node.make vertex key false []) := by
  apply Stored.node <;> simp [Snapshot.insertSingleton, Rings.write, Rings.RingOrEmpty]

/-- The first insertion works for arbitrary unused array cells. -/
theorem Represented.insert_empty {state : Snapshot} (represented : Represented state [])
    (vertex key : Int) (nonnegative : 0 ≤ vertex) :
    Represented (state.insertSingleton vertex key) [Node.make vertex key false []] := by
  have empty := represented.empty_iff.mpr rfl
  have absent := represented.empty_presence rfl
  refine ⟨singleton_valid vertex key, ?_, ?_, ?_, ?_, ?_, ?_, represented.scratch⟩
  · apply Or.inr
    apply Rings.singleton_ring <;> simp [Snapshot.insertSingleton, empty, Node.vertex]
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact singleton_stored state vertex key
  · intro value weight member
    simp [Forest.entries, Node.entries] at member
    exact member.1 ▸ nonnegative
  · intro value
    simp [Snapshot.insertSingleton, Rings.write, Forest.entries, Node.entries, absent]
  · have zero : state.size = 0 := by simpa [Forest.entries] using represented.size
    simp [Snapshot.insertSingleton, Forest.entries, Node.entries, zero]
  · right
    refine ⟨Node.make vertex key false [], by simp, ?_, ?_⟩
    · simp [Snapshot.insertSingleton, empty, Node.vertex]
    · simp [Node.key]

/-- An absent address cannot alias any active entry. -/
theorem Represented.fresh {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int} (absent : state.present vertex = 0) :
    vertex ∉ forest.entries.map Prod.fst := by
  intro member
  obtain ⟨⟨value, key⟩, inside, same⟩ := List.mem_map.mp member
  change value = vertex at same
  subst value
  have present := (represented.entry inside).2
  omega

theorem Represented.root_parent {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int} (member : vertex ∈ forest.map Node.vertex) :
    state.parents vertex = -1 := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  rw [← same]
  exact (represented.stored root inForest).root_parent

/-- Inserting at the minimum only rewires old root pointers. Metadata and all
    internal child rings are preserved for every existing tree. -/
theorem Represented.insert_stored {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (absent : state.present vertex = 0) {root : Node} (member : root ∈ forest) :
    Stored (state.insertSingleton vertex key) (-1) root := by
  have noAlias (value weight : Int) (inside : (value, weight) ∈ root.entries) : value ≠ vertex := by
    have present := (represented.stored root member).entries value weight inside
    intro same
    subst value
    omega
  apply (represented.stored root member).frame_roots
  · intro value weight inside
    exact represented.nonnegative value weight (List.mem_flatMap.mpr ⟨root, member, inside⟩)
  · intro value weight inside
    have different := noAlias value weight inside
    constructor <;> simp [Snapshot.insertSingleton, Rings.write, different]
  · intro value active nonroot
    have different : value ≠ vertex := by intro same; subst value; omega
    by_cases empty : state.minimum < 0
    · simp [Snapshot.insertSingleton, empty, Rings.write, different]
    · have nonempty : forest ≠ [] := fun same => empty (represented.empty_iff.mpr same)
      obtain ⟨least, leastMember, pointer, _⟩ := represented.minimum.resolve_left
        (fun same => nonempty same.1)
      have minimumMember : state.minimum ∈ forest.map Node.vertex := by
        rw [pointer]
        exact List.mem_map.mpr ⟨least, leastMember, rfl⟩
      have ring : Rings.Ring state.left state.right (forest.map Node.vertex) := by
        rcases represented.roots with impossible | ring
        · simp only [List.map_eq_nil_iff] at impossible
          exact False.elim (nonempty impossible)
        · exact ring
      have successorMember := (ring.neighbors minimumMember).2
      have minimumParent := represented.root_parent minimumMember
      have successorParent := represented.root_parent successorMember
      have notMinimum : value ≠ state.minimum := by intro same; subst value; omega
      have notSuccessor : value ≠ state.right state.minimum := by intro same; rw [same] at nonroot; omega
      simp [Snapshot.insertSingleton, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
        Rings.write, different, notMinimum, notSuccessor]

/-- If the abstract root list starts at the minimum, insertion has the exact
    logical order used by the source's `add_root`: old minimum, new node, rest. -/
theorem Represented.insert_after_minimum {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest)) {vertex key : Int}
    (nonnegative : 0 ≤ vertex) (absent : state.present vertex = 0)
    (minimum : state.minimum = root.vertex) :
    Represented (state.insertSingleton vertex key) (root :: Node.make vertex key false [] :: rest) := by
  let singleton := Node.make vertex key false []
  change Represented (state.insertSingleton vertex key) (root :: singleton :: rest)
  have contents : Forest.entries (root :: singleton :: rest) =
      root.entries ++ (vertex, key) :: rest.entries := by simp [Forest.entries, singleton, Node.entries]
  have oldNonempty : root :: rest ≠ [] := by simp
  have notEmpty : ¬state.minimum < 0 := fun negative => oldNonempty (represented.empty_iff.mp negative)
  have vertexFresh := represented.fresh absent
  have rootFresh : vertex ∉ (root :: rest).map Node.vertex := by
    intro member
    obtain ⟨node, member, same⟩ := List.mem_map.mp member
    apply vertexFresh
    exact List.mem_map.mpr ⟨(node.vertex, node.key), List.mem_flatMap.mpr ⟨node, member, node.root_entry⟩, same⟩
  have singletonValid := singleton_valid vertex key
  have insertedValid : Forest.Valid (singleton :: root :: rest) := by
    have result := represented.valid.insert_root singleton
      (by simp [singleton, Node.entries])
      (singletonValid.2.1 singleton (by simp [singleton]))
      (singletonValid.2.2.1 singleton (by simp [singleton]))
      (by
        intro value member
        have same : value = vertex := by simpa [singleton, Node.entries] using member
        simpa only [same] using vertexFresh)
    simpa [Forest.insertRoot, singleton, Node.withMark] using result
  have oldRing : Rings.Ring state.left state.right (root.vertex :: rest.map Node.vertex) := by
    rcases represented.roots with impossible | ring
    · simp at impossible
    · exact ring
  have minimumKey : state.keys state.minimum = root.key := minimum ▸ (represented.stored root (by simp)).root_key
  have least : ∀ other ∈ root :: rest, root.key ≤ other.key := by
    have global := (represented.minimum_key oldNonempty).2.2
    intro other member
    have active := (represented.stored other member).root_present
    have bound := global other.vertex (by omega)
    rw [minimumKey, (represented.stored other member).root_key] at bound
    exact bound
  refine ⟨insertedValid.perm (List.Perm.swap singleton root rest), ?_, ?_, ?_, ?_, ?_, ?_, represented.scratch⟩
  · apply Or.inr
    dsimp only [Snapshot.insertSingleton]
    rw [if_neg notEmpty, if_neg notEmpty]
    simpa only [minimum, List.map_cons, singleton, Node.vertex] using oldRing.insert_after rootFresh
  · intro node member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact represented.insert_stored absent (by simp)
    · exact singleton_stored state vertex key
    · exact represented.insert_stored absent (by simp [member])
  · intro value weight member
    simp only [contents, List.mem_append, List.mem_cons, Prod.mk.injEq] at member
    rcases member with member | ⟨rfl, rfl⟩ | member
    · exact represented.nonnegative value weight (by simpa [Forest.entries] using Or.inl member)
    · exact nonnegative
    · exact represented.nonnegative value weight (by simpa [Forest.entries] using Or.inr member)
  · intro value
    simp only [Snapshot.insertSingleton, Rings.write, contents, List.mem_append, List.mem_cons, Prod.mk.injEq]
    by_cases same : value = vertex
    · simp [same]
      exact ⟨key, Or.inr (Or.inl rfl)⟩
    · simp only [same, ↓reduceIte, false_and, false_or]
      simpa [Forest.entries, List.mem_append, exists_or] using represented.presence value
  · have size := represented.size
    simp only [Forest.entries, List.flatMap_cons, List.length_append] at size
    change state.size + 1 = Int.ofNat (Forest.entries (root :: singleton :: rest)).length
    rw [contents]
    simp only [List.length_append, List.length_cons, Forest.entries, Int.ofNat_eq_natCast]
    omega
  · right
    by_cases better : key < state.keys state.minimum
    · refine ⟨singleton, by simp, ?_, ?_⟩
      · simp only [Snapshot.insertSingleton, if_neg notEmpty, if_pos better, singleton, Node.vertex]
      · intro other member
        simp only [List.mem_cons] at member
        rcases member with same | same | member
        · subst other
          change key ≤ root.key
          rw [minimumKey] at better
          omega
        · subst other
          exact Int.le_refl _
        · have bound := least other (by simp [member])
          change key ≤ other.key
          rw [minimumKey] at better
          omega
    · refine ⟨root, by simp, ?_, ?_⟩
      · change (if state.minimum < 0 then vertex else if key < state.keys state.minimum then vertex else state.minimum) = root.vertex
        rw [if_neg notEmpty, if_neg better, minimum]
      · intro other member
        simp only [List.mem_cons] at member
        rcases member with same | same | member
        · subst other
          exact Int.le_refl _
        · subst other
          change root.key ≤ key
          rw [minimumKey] at better
          omega
        · exact least other (by simp [member])

/-- A fresh insertion preserves the complete representation, adds exactly the
    supplied entry, and increases the root count by one without adding marks. -/
theorem Represented.insert_singleton {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (nonnegative : 0 ≤ vertex) (absent : state.present vertex = 0) :
    ∃ afterForest, Represented (state.insertSingleton vertex key) afterForest ∧
      afterForest.entries.Perm ((vertex, key) :: forest.entries) ∧
      afterForest.length = forest.length + 1 ∧ afterForest.marks = forest.marks := by
  by_cases empty : forest = []
  · subst forest
    refine ⟨[Node.make vertex key false []], represented.insert_empty vertex key nonnegative, ?_, rfl, ?_⟩
    · simp [Forest.entries, Node.entries]
    · simp [Forest.marks, Node.marks]
  · obtain ⟨root, member, pointer, _⟩ := represented.minimum.resolve_left (fun impossible => empty impossible.1)
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    subst forest
    have rotated : Represented state (root :: (back ++ front)) := represented.rotate
    have after := rotated.insert_after_minimum (key := key) nonnegative absent pointer
    refine ⟨root :: Node.make vertex key false [] :: (back ++ front), after, ?_, ?_, ?_⟩
    · have reordered : (root :: (back ++ front)).Perm (front ++ root :: back) := by
        simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
      have entries := reordered.flatMap_right Node.entries
      apply List.Perm.trans _ (entries.cons (vertex, key))
      simp [Forest.entries, Node.entries]
    · simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · simp [Forest.marks, Node.marks, List.sum_append_nat, Nat.add_comm, Nat.add_assoc]


/-- Address membership ignores keys while retaining the finite tree witness. -/
def Node.Has (node : Node) (vertex : Int) : Prop := ∃ key, (vertex, key) ∈ node.entries

def Forest.Has (forest : Forest) (vertex : Int) : Prop := ∃ key, (vertex, key) ∈ forest.entries

@[simp] theorem Node.has_iff_map (node : Node) (vertex : Int) :
    node.Has vertex ↔ vertex ∈ node.entries.map Prod.fst := by
  constructor
  · rintro ⟨key, member⟩
    exact List.mem_map.mpr ⟨(vertex, key), member, rfl⟩
  · rintro member
    obtain ⟨⟨value, key⟩, member, same⟩ := List.mem_map.mp member
    change value = vertex at same
    subst value
    exact ⟨key, member⟩

@[simp] theorem Forest.has_iff_map (forest : Forest) (vertex : Int) :
    forest.Has vertex ↔ vertex ∈ forest.entries.map Prod.fst := by
  constructor
  · rintro ⟨key, member⟩
    exact List.mem_map.mpr ⟨(vertex, key), member, rfl⟩
  · rintro member
    obtain ⟨⟨value, key⟩, member, same⟩ := List.mem_map.mp member
    change value = vertex at same
    subst value
    exact ⟨key, member⟩

/-- The two parts of a unique forest have disjoint addresses. This is the
    separation fact needed when a root is detached and later linked. -/
theorem Forest.Unique.disjoint {front back : Forest} (unique : Forest.Unique (front ++ back)) :
    ∀ vertex, front.Has vertex → ¬back.Has vertex := by
  unfold Forest.Unique at unique
  simp only [Forest.entries, List.flatMap_append, List.map_append] at unique
  have separate := (List.nodup_append.mp unique).2.2
  intro vertex inFront inBack
  exact separate vertex ((front.has_iff_map vertex).mp inFront)
    vertex ((back.has_iff_map vertex).mp inBack) rfl

theorem Forest.Unique.left {front back : Forest} (unique : Forest.Unique (front ++ back)) :
    front.Unique := by
  unfold Forest.Unique at *
  simp only [Forest.entries, List.flatMap_append, List.map_append] at unique
  exact (List.nodup_append.mp unique).1

theorem Forest.Unique.right {front back : Forest} (unique : Forest.Unique (front ++ back)) :
    back.Unique := by
  unfold Forest.Unique at *
  simp only [Forest.entries, List.flatMap_append, List.map_append] at unique
  exact (List.nodup_append.mp unique).2.1

/-- Every root's own address is separate from its strict descendants. -/
theorem Node.unique_root {node : Node} (unique : (node.entries.map Prod.fst).Nodup) :
    ¬Forest.Has node.children node.vertex := by
  cases node with
  | make vertex key marked children =>
    simp only [Node.entries, List.map_cons] at unique
    simpa [Node.entries, Node.children, Node.vertex, Forest.has_iff_map, Forest.entries] using
      (List.nodup_cons.mp unique).1

/-- A root-ring vertex cannot be an entry in a separate forest component. -/
theorem Forest.Unique.roots_disjoint {front back : Forest}
    (unique : Forest.Unique (front ++ back)) :
    ∀ vertex ∈ front.map Node.vertex, vertex ∉ back.entries.map Prod.fst := by
  intro vertex member inside
  obtain ⟨root, member, same⟩ := List.mem_map.mp member
  exact unique.disjoint vertex
    ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
    ((back.has_iff_map vertex).mpr inside)

/-- Metadata of a subtree's root may be changed independently from all its
    strict descendants, including its parent pointer and mark. -/
theorem Stored.change_header {before after : Snapshot} {parent newParent : Int} {node : Node}
    (stored : Stored before parent node) (marked : Bool)
    (key : after.keys node.vertex = node.key)
    (readParent : after.parents node.vertex = newParent)
    (mark : after.marks node.vertex = if marked then 1 else 0)
    (degree : after.degrees node.vertex = node.degree)
    (present : after.present node.vertex = 1)
    (head : after.children node.vertex = before.children node.vertex)
    (fields : ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries →
      Snapshot.SameFields before after vertex)
    (links : ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after newParent (node.withMark marked) := by
  cases stored with
  | @node vertex value parent oldMark children oldKey oldParent oldMarked oldDegree oldPresent oldHead ring subtrees =>
    apply Stored.node key readParent mark degree present
      (by cases children <;> exact head.trans oldHead)
    · rcases ring with empty | ring
      · exact Or.inl empty
      · apply Or.inr
        apply ring.frame
        · intro value member
          obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
          subst value
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).1
        · intro value member
          obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
          subst value
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).2
    · intro child member
      apply (subtrees child member).frame
      · intro vertex key inside
        exact fields vertex key (List.mem_flatMap.mpr ⟨child, member, inside⟩)
      · intro vertex key inside
        exact links vertex key (List.mem_flatMap.mpr ⟨child, member, Node.descendant_entries inside⟩)

/-- The parent address of a strict descendant belongs to this finite tree. -/
theorem Stored.descendant_parent {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) :
    ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries → node.Has (state.parents vertex) := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro value weight member
    obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
    cases child with
    | make childVertex childKey childMark grandchildren =>
      simp only [Node.entries, List.mem_cons, Prod.mk.injEq] at inside
      rcases inside with ⟨rfl, rfl⟩ | deeper
      · have pointer := (subtrees _ childMember).root_parent
        change state.parents value = vertex at pointer
        rw [pointer]
        exact ⟨key, by simp [Node.entries]⟩
      · obtain ⟨parentKey, parentEntry⟩ := ih _ childMember value weight deeper
        exact ⟨parentKey, Node.child_entries childMember parentEntry⟩

/-- Exact non-clock effect of linking a detached child under a parent root. -/
def Snapshot.link (state : Snapshot) (child parent : Int) : Snapshot :=
  { state with
    parents := Rings.write state.parents child parent
    marks := Rings.write state.marks child 0
    children := Rings.write state.children parent child
    degrees := Rings.write state.degrees parent (state.degrees parent + 1)
    left := if state.children parent < 0 then Rings.write state.left child child
      else Rings.insertBeforeLeft state.left (state.children parent) child
    right := if state.children parent < 0 then Rings.write state.right child child
      else Rings.insertBeforeRight state.left state.right (state.children parent) child }

/-- Link updates only the metadata of its two supplied roots. -/
theorem Snapshot.link_fields {state : Snapshot} {child parent vertex : Int}
    (notChild : vertex ≠ child) (notParent : vertex ≠ parent) :
    SameFields state (state.link child parent) vertex := by
  constructor <;> simp [Snapshot.link, Rings.write, notChild, notParent]

/-- The child head and its predecessor have the supplied root as their parent. -/
theorem Stored.child_ring_parents {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (nonempty : ¬state.children node.vertex < 0) :
    state.parents (state.children node.vertex) = node.vertex ∧
      state.parents (state.left (state.children node.vertex)) = node.vertex := by
  cases stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
    cases children with
    | nil =>
      have negative : state.children vertex = -1 := readHead
      change ¬state.children vertex < 0 at nonempty
      omega
    | cons first rest =>
      change state.children vertex = first.vertex at readHead
      change state.parents (state.children vertex) = vertex ∧ state.parents (state.left (state.children vertex)) = vertex
      rw [readHead]
      have childRing : Rings.Ring state.left state.right (first.vertex :: rest.map Node.vertex) := by
        rcases ring with impossible | ring
        · simp at impossible
        · exact ring
      have predecessorMember := (childRing.neighbors (vertex := first.vertex) (by simp)).1
      change state.left first.vertex ∈ (first :: rest).map Node.vertex at predecessorMember
      obtain ⟨previous, member, same⟩ := List.mem_map.mp predecessorMember
      constructor
      · exact (subtrees first (by simp)).root_parent
      · rw [← same]
        exact (subtrees previous member).root_parent

/-- Rewiring one child ring leaves nodes with other parents untouched. -/
theorem Stored.link_links {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) {child vertex : Int}
    (notChild : vertex ≠ child) (otherParent : state.parents vertex ≠ node.vertex) :
    (state.link child node.vertex).left vertex = state.left vertex ∧
      (state.link child node.vertex).right vertex = state.right vertex := by
  by_cases empty : state.children node.vertex < 0
  · simp [Snapshot.link, empty, Rings.write, notChild]
  · obtain ⟨headParent, beforeParent⟩ := stored.child_ring_parents empty
    have notHead : vertex ≠ state.children node.vertex := by intro same; subst vertex; exact otherParent headParent
    have notBefore : vertex ≠ state.left (state.children node.vertex) := by intro same; subst vertex; exact otherParent beforeParent
    simp [Snapshot.link, empty, Rings.insertBeforeLeft, Rings.insertBeforeRight, Rings.write, notChild, notHead, notBefore]

/-- Linking two disjoint trees constructs exactly their logical parent/child
    combination. No global minimum, transcript, or degree table is needed. -/
theorem Stored.link {state : Snapshot} {outerParent : Int} {parent child : Node}
    (parentStored : Stored state outerParent parent) (childStored : Stored state (-1) child)
    (parentUnique : (parent.entries.map Prod.fst).Nodup)
    (childUnique : (child.entries.map Prod.fst).Nodup)
    (separate : ∀ vertex, parent.Has vertex → ¬child.Has vertex)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ parent.entries → 0 ≤ vertex) :
    Stored (state.link child.vertex parent.vertex) outerParent (parent.link child) := by
  have parentHas : parent.Has parent.vertex := ⟨parent.key, parent.root_entry⟩
  have childHas : child.Has child.vertex := ⟨child.key, child.root_entry⟩
  have different : child.vertex ≠ parent.vertex := by
    intro same
    exact separate parent.vertex parentHas (same ▸ childHas)
  have oldNotChild (vertex key : Int) (member : (vertex, key) ∈ parent.entries) : vertex ≠ child.vertex := by
    intro same
    exact separate child.vertex (same ▸ ⟨key, member⟩) childHas
  have descendantNotParent (vertex key : Int)
      (member : (vertex, key) ∈ parent.children.flatMap Node.entries) : vertex ≠ parent.vertex := by
    intro same
    exact parent.unique_root parentUnique ⟨key, same ▸ member⟩
  have childDescendantNotRoot (vertex key : Int)
      (member : (vertex, key) ∈ child.children.flatMap Node.entries) : vertex ≠ child.vertex := by
    intro same
    exact child.unique_root childUnique ⟨key, same ▸ member⟩
  have childNotParent (vertex key : Int) (member : (vertex, key) ∈ child.entries) : vertex ≠ parent.vertex := by
    intro same
    exact separate parent.vertex parentHas (same ▸ ⟨key, member⟩)
  have linkedChild : Stored (state.link child.vertex parent.vertex) parent.vertex (child.withMark false) := by
    apply childStored.change_header false
    · exact childStored.root_key
    · simp [Snapshot.link]
    · simp [Snapshot.link]
    · simpa [Snapshot.link, Rings.write, different] using childStored.root_degree
    · exact childStored.root_present
    · simp [Snapshot.link, Rings.write, different]
    · intro vertex key member
      exact Snapshot.link_fields (childDescendantNotRoot vertex key member)
        (childNotParent vertex key (Node.descendant_entries member))
    · intro vertex key member
      apply parentStored.link_links (childDescendantNotRoot vertex key member)
      intro same
      exact separate parent.vertex parentHas (same ▸ childStored.descendant_parent vertex key member)
  have oldChildren : ∀ old ∈ parent.children,
      Stored (state.link child.vertex parent.vertex) parent.vertex old := by
    have childrenStored : ∀ old ∈ parent.children, Stored state parent.vertex old := by
      cases parentStored with | node _ _ _ _ _ _ _ subtrees => exact subtrees
    intro old member
    apply (childrenStored old member).frame
    · intro vertex key inside
      exact Snapshot.link_fields (oldNotChild vertex key (Node.child_entries member inside))
        (descendantNotParent vertex key (List.mem_flatMap.mpr ⟨old, member, inside⟩))
    · intro vertex key inside
      apply parentStored.link_links (oldNotChild vertex key
        (Node.child_entries member (Node.descendant_entries inside)))
      intro same
      obtain ⟨parentKey, parentEntry⟩ := (childrenStored old member).descendant_parent vertex key inside
      exact parent.unique_root parentUnique ⟨parentKey,
        same ▸ List.mem_flatMap.mpr ⟨old, member, parentEntry⟩⟩
  cases parentStored with
  | @node vertex key outerParent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
    change child.vertex ≠ vertex at different
    change Stored _ outerParent (.make vertex key marked (child.withMark false :: children))
    refine Stored.node ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact readKey
    · simpa [Snapshot.link, Rings.write, Ne.symm different] using readParent
    · simpa [Snapshot.link, Rings.write, Ne.symm different] using readMark
    · simp [Snapshot.link, Node.vertex, readDegree, Int.natCast_add]
    · exact readPresent
    · simp [Snapshot.link, Node.vertex, Node.withMark]
    · cases children with
      | nil =>
        have empty : state.children vertex = -1 := readHead
        apply Or.inr
        apply Rings.singleton_ring <;>
          simp [Snapshot.link, Node.vertex, Node.withMark, empty]
      | cons first rest =>
        have head : state.children vertex = first.vertex := readHead
        have headNonnegative : 0 ≤ first.vertex :=
          nonnegative first.vertex first.key (Node.child_entries (by simp [Node.children]) first.root_entry)
        have notEmpty : ¬state.children vertex < 0 := by rw [head]; omega
        have original : Rings.Ring state.left state.right (first.vertex :: rest.map Node.vertex) := by
          rcases ring with impossible | ring
          · simp at impossible
          · exact ring
        have fresh : child.vertex ∉ first.vertex :: rest.map Node.vertex := by
          intro member
          change child.vertex ∈ (first :: rest).map Node.vertex at member
          obtain ⟨old, member, same⟩ := List.mem_map.mp member
          exact oldNotChild old.vertex old.key (Node.child_entries member old.root_entry) same
        apply Or.inr
        dsimp only [Snapshot.link]
        change Rings.Ring
          (if state.children vertex < 0 then _ else _)
          (if state.children vertex < 0 then _ else _)
          ((child.withMark false).vertex :: first.vertex :: rest.map Node.vertex)
        rw [if_neg notEmpty, if_neg notEmpty]
        simpa only [Node.vertex, Node.withMark, head] using original.insert_before fresh
    · intro node member
      rcases List.mem_cons.mp member with rfl | old
      · exact linkedChild
      · exact oldChildren node old

/-- Unrelated stored trees survive a link, including all their child rings. -/
theorem Stored.link_frame {state : Snapshot} {outerParent otherParent : Int} {parent other : Node}
    (parentStored : Stored state outerParent parent) (otherStored : Stored state otherParent other)
    {child : Int} (notParent : ¬other.Has parent.vertex) (notChild : ¬other.Has child) :
    Stored (state.link child parent.vertex) otherParent other := by
  have different (vertex key : Int) (member : (vertex, key) ∈ other.entries) :
      vertex ≠ child ∧ vertex ≠ parent.vertex := by
    constructor
    · intro same
      exact notChild (same ▸ ⟨key, member⟩)
    · intro same
      exact notParent (same ▸ ⟨key, member⟩)
  apply otherStored.frame
  · intro vertex key member
    exact Snapshot.link_fields (different vertex key member).1 (different vertex key member).2
  · intro vertex key member
    apply parentStored.link_links (different vertex key (Node.descendant_entries member)).1
    intro same
    exact notParent (same ▸ otherStored.descendant_parent vertex key member)

/-- A temporary consolidation state separates the untouched pending root ring
    from detached roots held in degree buckets or the current collision. The
    minimum is a traversal cursor and need not be a global minimum yet. -/
structure SplitRepresented (state : Snapshot) (pending detached : Forest) : Prop where
  valid : Forest.Valid (pending ++ detached)
  stored : ∀ root ∈ pending ++ detached, Stored state (-1) root
  pendingRing : Rings.RingOrEmpty state.left state.right (pending.map Node.vertex)
  detachedRings : ∀ root ∈ detached, state.left root.vertex = root.vertex ∧ state.right root.vertex = root.vertex
  nonnegative : ∀ vertex key, (vertex, key) ∈ Forest.entries (pending ++ detached) → 0 ≤ vertex
  presence : ∀ vertex, state.present vertex ≠ 0 ↔ Forest.Has (pending ++ detached) vertex
  size : state.size = (Forest.entries (pending ++ detached)).length
  cursor : (pending = [] ∧ state.minimum = -1) ∨ ∃ root ∈ pending, state.minimum = root.vertex

/-- Whole-heap representation starts consolidation with no detached roots. -/
theorem Represented.split {state : Snapshot} {forest : Forest} (represented : Represented state forest) :
    SplitRepresented state forest [] := by
  refine ⟨?_, ?_, represented.roots, by simp, ?_, ?_, ?_, ?_⟩
  · simpa using represented.valid
  · simpa using represented.stored
  · simpa using represented.nonnegative
  · simpa [Forest.Has] using represented.presence
  · simpa using represented.size
  · rcases represented.minimum with empty | ⟨root, member, pointer, _⟩
    · exact Or.inl empty
    · exact Or.inr ⟨root, member, pointer⟩

/-- One equal-degree collision preserves the abstract invariants wherever its
    two roots occur after a prefix of roots awaiting processing. -/
theorem Forest.Valid.link_after {pending rest : Forest} {parent child : Node}
    (valid : Forest.Valid (pending ++ parent :: child :: rest))
    (winner : parent.key ≤ child.key) (equalDegree : parent.degree = child.degree) :
    Forest.Valid (pending ++ parent.link child :: rest) := by
  have reordered : Forest.Valid (parent :: child :: (rest ++ pending)) := by
    apply valid.perm
    simpa only [List.cons_append] using
      (List.perm_append_comm (l₁ := parent :: child :: rest) (l₂ := pending))
  have linked := reordered.link_roots winner equalDegree
  apply linked.perm
  simpa only [Forest.linkRoots, List.cons_append] using
    (List.perm_append_comm (l₁ := pending) (l₂ := parent.link child :: rest))

/-- The concrete pointer change of a collision leaves every pending root
    pointer intact, so traversal can continue over the same finite list. -/
theorem SplitRepresented.link_pending_ring {state : Snapshot} {pending rest : Forest} {parent child : Node}
    (represented : SplitRepresented state pending (parent :: child :: rest)) :
    Rings.RingOrEmpty (state.link child.vertex parent.vertex).left
      (state.link child.vertex parent.vertex).right (pending.map Node.vertex) := by
  have parentStored := represented.stored parent (by simp)
  have childStored := represented.stored child (by simp)
  have parentNonnegative := represented.nonnegative parent.vertex parent.key
    (List.mem_flatMap.mpr ⟨parent, by simp, parent.root_entry⟩)
  have childAbsent := represented.valid.1.disjoint
  rcases represented.pendingRing with empty | ring
  · exact Or.inl empty
  · apply Or.inr
    have pointers (vertex : Int) (member : vertex ∈ pending.map Node.vertex) :
        (state.link child.vertex parent.vertex).left vertex = state.left vertex ∧
          (state.link child.vertex parent.vertex).right vertex = state.right vertex := by
      obtain ⟨root, member, same⟩ := List.mem_map.mp member
      have stored := represented.stored root (by simp [member])
      apply parentStored.link_links
      · intro equal
        have inPending : Forest.Has pending child.vertex :=
          ⟨root.key, equal ▸ same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
        exact childAbsent child.vertex inPending ⟨child.key,
          List.mem_flatMap.mpr ⟨child, by simp, child.root_entry⟩⟩
      · have parent := stored.root_parent
        rw [same] at parent
        omega
    exact ring.frame (fun vertex member => (pointers vertex member).1)
      (fun vertex member => (pointers vertex member).2)

theorem Forest.Unique.head {root : Node} {rest : Forest} (unique : Forest.Unique (root :: rest)) :
    (root.entries.map Prod.fst).Nodup := by
  unfold Forest.Unique at unique
  simp only [Forest.entries, List.flatMap_cons, List.map_append] at unique
  exact (List.nodup_append.mp unique).1

theorem Forest.Unique.tail {root : Node} {rest : Forest} (unique : Forest.Unique (root :: rest)) :
    rest.Unique := by
  unfold Forest.Unique at *
  simp only [Forest.entries, List.flatMap_cons, List.map_append] at unique
  exact (List.nodup_append.mp unique).2.1

/-- Linking two detached roots preserves pending traversal, exact membership,
    size, heap order, rank history, and all remaining detached singleton rings. -/
theorem SplitRepresented.link {state : Snapshot} {pending rest : Forest} {parent child : Node}
    (represented : SplitRepresented state pending (parent :: child :: rest))
    (winner : parent.key ≤ child.key) (equalDegree : parent.degree = child.degree) :
    SplitRepresented (state.link child.vertex parent.vertex) pending (parent.link child :: rest) := by
  have reordered : Forest.Valid ([parent, child] ++ (pending ++ rest)) := by
    apply represented.valid.perm
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using
      (List.perm_append_comm (l₁ := [parent, child]) (l₂ := pending)).append_right rest
  have separated := reordered.1.disjoint
  have pairUnique := reordered.1.left
  have parentStored := represented.stored parent (by simp)
  have childStored := represented.stored child (by simp)
  have parentNonnegative := represented.nonnegative parent.vertex parent.key
    (List.mem_flatMap.mpr ⟨parent, by simp, parent.root_entry⟩)
  have parentChildSeparate : ∀ vertex, parent.Has vertex → ¬child.Has vertex := by
    intro vertex parentMember childMember
    apply (Forest.Unique.disjoint (front := [parent]) (back := [child]) pairUnique) vertex
    · simpa [Forest.Has, Forest.entries] using parentMember
    · simpa [Forest.Has, Forest.entries] using childMember
  have linked := parentStored.link childStored pairUnique.head pairUnique.tail.head parentChildSeparate
    (fun vertex key member => represented.nonnegative vertex key
      (List.mem_flatMap.mpr ⟨parent, by simp, member⟩))
  have different : parent.vertex ≠ child.vertex := by
    intro same
    exact parentChildSeparate child.vertex (same ▸ ⟨parent.key, parent.root_entry⟩) ⟨child.key, child.root_entry⟩
  have otherNotRoot (other : Node) (member : other ∈ pending ++ rest) :
      ¬other.Has parent.vertex ∧ ¬other.Has child.vertex := by
    constructor
    · rintro ⟨key, inside⟩
      exact separated parent.vertex
        ⟨parent.key, List.mem_flatMap.mpr ⟨parent, by simp, parent.root_entry⟩⟩
        ⟨key, List.mem_flatMap.mpr ⟨other, member, inside⟩⟩
    · rintro ⟨key, inside⟩
      exact separated child.vertex
        ⟨child.key, List.mem_flatMap.mpr ⟨child, by simp, child.root_entry⟩⟩
        ⟨key, List.mem_flatMap.mpr ⟨other, member, inside⟩⟩
  have contents : (Forest.entries (pending ++ parent.link child :: rest)).Perm
      (Forest.entries (pending ++ parent :: child :: rest)) := by
    simpa only [Forest.entries, List.flatMap_append, List.flatMap_cons, List.append_assoc] using
      ((parent.link_entries child).append_right rest.entries).append_left pending.entries
  refine ⟨represented.valid.link_after winner equalDegree, ?_, represented.link_pending_ring, ?_, ?_, ?_, ?_, represented.cursor⟩
  · intro root member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with inPending | rfl | inRest
    · exact parentStored.link_frame (represented.stored root (by simp [inPending]))
        (otherNotRoot root (by simp [inPending])).1 (otherNotRoot root (by simp [inPending])).2
    · exact linked
    · exact parentStored.link_frame (represented.stored root (by simp [inRest]))
        (otherNotRoot root (by simp [inRest])).1 (otherNotRoot root (by simp [inRest])).2
  · intro root member
    rcases List.mem_cons.mp member with rfl | inRest
    · have unchanged := parentStored.link_links (child := child.vertex) different
        (by have pointer := parentStored.root_parent; omega)
      exact ⟨unchanged.1.trans (represented.detachedRings parent (by simp)).1,
        unchanged.2.trans (represented.detachedRings parent (by simp)).2⟩
    · have rootStored := represented.stored root (by simp [inRest])
      have rootNotChild : root.vertex ≠ child.vertex := by
        intro same
        exact (otherNotRoot root (by simp [inRest])).2 (same ▸ ⟨root.key, root.root_entry⟩)
      have unchanged := parentStored.link_links rootNotChild
        (by have pointer := rootStored.root_parent; omega)
      exact ⟨unchanged.1.trans (represented.detachedRings root (by simp [inRest])).1,
        unchanged.2.trans (represented.detachedRings root (by simp [inRest])).2⟩
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)


/-- A finite preorder witness places an ancestor strictly before its child. -/
def Precedes (vertices : List Int) (parent child : Int) : Prop :=
  ∃ before middle after, vertices = before ++ parent :: (middle ++ child :: after)

theorem Precedes.frame {vertices : List Int} {parent child : Int}
    (precedes : Precedes vertices parent child) (before after : List Int) :
    Precedes (before ++ vertices ++ after) parent child := by
  obtain ⟨front, middle, back, rfl⟩ := precedes
  refine ⟨before ++ front, middle, back ++ after, ?_⟩
  simp only [List.append_assoc, List.cons_append]

theorem Precedes.parent_mem {vertices : List Int} {parent child : Int}
    (precedes : Precedes vertices parent child) : parent ∈ vertices := by
  obtain ⟨before, middle, after, rfl⟩ := precedes
  simp

/-- Distinct preorder addresses turn structural precedence into a decreasing
    natural rank along parent pointers. -/
theorem Precedes.rank {vertices : List Int} {parent child : Int}
    (precedes : Precedes vertices parent child) (unique : vertices.Nodup) :
    vertices.idxOf parent < vertices.idxOf child := by
  obtain ⟨before, middle, after, rfl⟩ := precedes
  have separated := (List.nodup_append.mp unique).2.2
  have noParent : parent ∉ before := by
    intro member
    exact separated parent member parent (by simp) rfl
  have noChild : child ∉ before := by
    intro member
    exact separated child member child (by simp) rfl
  have uniqueTail := (List.nodup_append.mp unique).2.1
  have different : parent ≠ child := by
    intro same
    exact (List.nodup_cons.mp uniqueTail).1 (by simp [same])
  simp only [List.idxOf_append, noParent, noChild, ↓reduceIte, List.idxOf_cons_self,
    List.idxOf_cons, cond_eq_ite, beq_iff_eq, different, ↓reduceIte]
  omega

/-- Every nonroot parent precedes its child in the tree's finite preorder. -/
theorem Stored.parent_precedes {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) :
    ∀ vertex key, (vertex, key) ∈ node.entries →
      state.parents vertex = parent ∨ Precedes (node.entries.map Prod.fst) (state.parents vertex) vertex := by
  induction stored with
  | @node root key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro vertex weight member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, childMember, inside⟩
    · exact Or.inl readParent
    · right
      rcases ih child childMember vertex weight inside with atRoot | deeper
      · have descendantMember : vertex ∈ (children.flatMap Node.entries).map Prod.fst :=
          List.mem_map.mpr ⟨(vertex, weight), List.mem_flatMap.mpr ⟨child, childMember, inside⟩, rfl⟩
        obtain ⟨front, back, located⟩ := List.mem_iff_append.mp descendantMember
        refine ⟨[], front, back, ?_⟩
        simp only [Node.entries, List.map_cons, List.nil_append, atRoot, located]
      · obtain ⟨front, back, located⟩ := List.mem_iff_append.mp childMember
        have embedded := deeper.frame (root :: (front.flatMap Node.entries).map Prod.fst)
          ((back.flatMap Node.entries).map Prod.fst)
        simpa only [Node.entries, List.map_cons, Prod.fst, located, List.flatMap_append,
          List.flatMap_cons, List.map_append, List.cons_append, List.append_assoc] using embedded

/-- Rank is ordinary preorder position; values outside the active finite
    forest may have arbitrary parents and play no role in this measure. -/
def Forest.parentRank (forest : Forest) (vertex : Int) : Nat :=
  (forest.entries.map Prod.fst).idxOf vertex

theorem Represented.parent_rank {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int}
    (active : state.present vertex ≠ 0) (nonroot : 0 ≤ state.parents vertex) :
    state.present (state.parents vertex) ≠ 0 ∧
      forest.parentRank (state.parents vertex) < forest.parentRank vertex := by
  obtain ⟨key, member⟩ := (represented.presence vertex).mp active
  obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
  rcases (represented.stored root inForest).parent_precedes vertex key inside with isRoot | precedes
  · omega
  · obtain ⟨front, back, located⟩ := List.mem_iff_append.mp inForest
    have full : Precedes (forest.entries.map Prod.fst) (state.parents vertex) vertex := by
      have embedded := precedes.frame ((front.flatMap Node.entries).map Prod.fst)
        ((back.flatMap Node.entries).map Prod.fst)
      simpa only [Forest.entries, located, List.flatMap_append, List.flatMap_cons,
        List.map_append, List.append_assoc] using embedded
    constructor
    · apply (represented.presence _).mpr
      exact (forest.has_iff_map _).mpr full.parent_mem
    · exact full.rank represented.valid.1


/-- Exact child-ring removal before the source's `add_root` call. The child's
    parent and mark are intentionally left for that following operation. -/
def Snapshot.removeChild (state : Snapshot) (child parent : Int) : Snapshot :=
  { state with
    children := Rings.write state.children parent
      (if state.children parent = child then
        if state.right child = child then -1 else state.right child
       else state.children parent)
    degrees := Rings.write state.degrees parent (state.degrees parent - 1)
    left := Rings.removeLeft state.left state.right child
    right := Rings.removeRight state.left state.right child }

theorem Snapshot.removeChild_fields {state : Snapshot} {child parent vertex : Int}
    (notParent : vertex ≠ parent) : SameFields state (state.removeChild child parent) vertex := by
  constructor <;> simp [Snapshot.removeChild, Rings.write, notParent]

/-- A finite child ring identifies both neighbors as children of the same parent. -/
theorem Stored.child_neighbors {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) :
    state.parents (state.left child.vertex) = parent.vertex ∧
      state.parents (state.right child.vertex) = parent.vertex := by
  cases stored with
  | @node vertex key outer marked childList _ _ _ _ _ _ ring children =>
    have childRing : Rings.Ring state.left state.right (childList.map Node.vertex) := by
      rcases ring with impossible | ring
      · have childMember : child.vertex ∈ childList.map Node.vertex := List.mem_map.mpr ⟨child, member, rfl⟩
        rw [impossible] at childMember
        simp at childMember
      · exact ring
    have neighbors := childRing.neighbors (List.mem_map.mpr ⟨child, member, rfl⟩)
    constructor
    · obtain ⟨previous, inChildren, same⟩ := List.mem_map.mp neighbors.1
      rw [← same]
      exact (children previous inChildren).root_parent
    · obtain ⟨next, inChildren, same⟩ := List.mem_map.mp neighbors.2
      rw [← same]
      exact (children next inChildren).root_parent

/-- Removing a child only changes the pointers of that child's two neighbors. -/
theorem Stored.removeChild_links {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) {vertex : Int}
    (notChild : vertex ≠ child.vertex) (otherParent : state.parents vertex ≠ parent.vertex) :
    (state.removeChild child.vertex parent.vertex).left vertex = state.left vertex ∧
      (state.removeChild child.vertex parent.vertex).right vertex = state.right vertex := by
  obtain ⟨leftParent, rightParent⟩ := stored.child_neighbors member
  have notLeft : vertex ≠ state.left child.vertex := by intro same; subst vertex; exact otherParent leftParent
  have notRight : vertex ≠ state.right child.vertex := by intro same; subst vertex; exact otherParent rightParent
  simp [Snapshot.removeChild, Rings.removeLeft, Rings.removeRight, Rings.write, notChild, notLeft, notRight]

/-- The child-head update performed by `cut` selects the first remaining child. -/
theorem Rings.Ring.remove_head_pointer {left right : Int → Int} {head child : Int}
    {front back : List Int} (ring : Rings.Ring left right (front ++ child :: back))
    (readHead : head = (front ++ child :: back).head!) :
    (if head = child then if right child = child then -1 else right child else head) =
      match front ++ back with | [] => -1 | first :: _ => first := by
  cases front with
  | nil =>
    have same : head = child := by simpa using readHead
    rw [same, if_pos rfl]
    cases back with
    | nil => simp [ring.singleton_pointers.2]
    | cons next rest =>
      have pointers := ring.head_next
      have different : next ≠ child := by
        intro same
        exact (List.nodup_cons.mp ring.unique).1 (by simp [same])
      simp [pointers.1, different]
  | cons first rest =>
    have same : head = first := by simpa using readHead
    have different : first ≠ child := by
      intro same
      exact (List.nodup_cons.mp ring.unique).1 (by simp [same])
    simp [same, different]

/-- Every original child subtree survives sibling removal. Only its root's
    own sibling pointers change; the subtree remains reusable as a unit. -/
theorem Stored.removeChild_subtrees {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (childMember : child ∈ parent.children)
    (unique : (parent.entries.map Prod.fst).Nodup) :
    ∀ old ∈ parent.children, Stored (state.removeChild child.vertex parent.vertex) parent.vertex old := by
  have childrenStored : ∀ old ∈ parent.children, Stored state parent.vertex old := by
    cases stored with | node _ _ _ _ _ _ _ children => exact children
  have different (old : Node) (member : old ∈ parent.children) (vertex key : Int)
      (inside : (vertex, key) ∈ old.entries) : vertex ≠ parent.vertex := by
    intro same
    exact parent.unique_root unique ⟨key, same ▸ List.mem_flatMap.mpr ⟨old, member, inside⟩⟩
  intro old member
  apply (childrenStored old member).frame
  · intro vertex key inside
    exact Snapshot.removeChild_fields (different old member vertex key inside)
  · intro vertex key inside
    have otherParent : state.parents vertex ≠ parent.vertex := by
      obtain ⟨parentKey, parentInside⟩ := (childrenStored old member).descendant_parent vertex key inside
      exact different old member (state.parents vertex) parentKey parentInside
    apply stored.removeChild_links childMember _ otherParent
    intro same
    have pointer := (childrenStored child childMember).root_parent
    exact otherParent (same ▸ pointer)

/-- Removing one selected child realizes list deletion, keeps the removed
    subtree intact, and produces a detached singleton sibling ring. Rank
    restoration (marking or cascading) is deliberately a later operation. -/
theorem Stored.removeChild {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (before after : List Node)
    (located : parent.children = before ++ child :: after)
    (unique : (parent.entries.map Prod.fst).Nodup) :
    Stored (state.removeChild child.vertex parent.vertex) outerParent (parent.withChildren (before ++ after)) ∧
      Stored (state.removeChild child.vertex parent.vertex) parent.vertex child ∧
      (state.removeChild child.vertex parent.vertex).left child.vertex = child.vertex ∧
      (state.removeChild child.vertex parent.vertex).right child.vertex = child.vertex := by
  have childMember : child ∈ parent.children := by rw [located]; simp
  have preserved := stored.removeChild_subtrees childMember unique
  refine ⟨?_, preserved child childMember, ?_, ?_⟩
  · cases stored with
    | @node vertex key outerParent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
      change children = before ++ child :: after at located
      have original : Rings.Ring state.left state.right ((before ++ child :: after).map Node.vertex) := by
        rcases ring with impossible | ring
        · simp only [List.map_eq_nil_iff] at impossible
          rw [located] at impossible
          simp at impossible
        · simpa only [located] using ring
      have readOriginal : state.children vertex = ((before ++ child :: after).map Node.vertex).head! := by
        rw [← located]
        cases children with
        | nil => simp [Node.children] at childMember
        | cons first rest => exact readHead
      change Stored _ outerParent (.make vertex key marked (before ++ after))
      refine Stored.node readKey readParent readMark ?_ readPresent ?_ ?_ ?_
      · simp only [Snapshot.removeChild, Node.vertex, Rings.write_same, readDegree,
          located, List.length_append, List.length_cons, Int.natCast_add, Int.natCast_one]
        omega
      · have result := Rings.Ring.remove_head_pointer
          (front := before.map Node.vertex) (back := after.map Node.vertex)
          (by simpa only [List.map_append, List.map_cons] using original)
          (by simpa only [List.map_append, List.map_cons] using readOriginal)
        change (Rings.write state.children vertex _ vertex) = _
        rw [Rings.write_same]
        cases before <;> cases after <;> simpa using result
      · have remaining := Rings.Ring.remove_from_decomposition
          (front := before.map Node.vertex) (back := after.map Node.vertex) child.vertex
          (by simpa only [List.map_append, List.map_cons] using original)
        simpa only [Snapshot.removeChild, Node.vertex, List.map_append] using remaining
      · intro old member
        apply preserved old
        change old ∈ children
        rw [located]
        simp only [List.mem_append, List.mem_cons]
        simp only [List.mem_append] at member
        rcases member with first | last
        · exact Or.inl first
        · exact Or.inr (Or.inr last)
  · simp [Snapshot.removeChild, Rings.removeLeft]
  · simp [Snapshot.removeChild, Rings.removeRight]

/-- A mark update has no effect on allocation, membership, pointers or keys. -/
def Snapshot.setMark (state : Snapshot) (vertex : Int) (marked : Bool) : Snapshot :=
  { state with marks := Rings.write state.marks vertex (if marked then 1 else 0) }

/-- Marking a node preserves its entire stored subtree. Unique addresses make
    the single changed cell separate from every strict descendant. -/
theorem Stored.setMark {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (unique : (node.entries.map Prod.fst).Nodup) (marked : Bool) :
    Stored (state.setMark node.vertex marked) parent (node.withMark marked) := by
  apply stored.change_header (after := state.setMark node.vertex marked) marked stored.root_key stored.root_parent
  · simp [Snapshot.setMark]
  · exact stored.root_degree
  · exact stored.root_present
  · rfl
  · intro vertex key member
    have different : vertex ≠ node.vertex := by
      intro same
      exact node.unique_root unique ⟨key, same ▸ member⟩
    constructor <;> simp [Snapshot.setMark, Rings.write, different]
  · intro vertex key member
    exact ⟨rfl, rfl⟩

/-- A mark update can be framed through any disjoint stored subtree. -/
theorem Stored.setMark_frame {state : Snapshot} {parent vertex : Int} {node : Node}
    (stored : Stored state parent node) (absent : ¬node.Has vertex) (marked : Bool) :
    Stored (state.setMark vertex marked) parent node := by
  apply stored.frame
  · intro value key member
    have different : value ≠ vertex := by intro same; exact absent (same ▸ ⟨key, member⟩)
    constructor <;> simp [Snapshot.setMark, Rings.write, different]
  · intro value key member
    exact ⟨rfl, rfl⟩

/-- Replacing one child descriptor is local: the enclosing node's interface
    only needs the same child address, its own metadata, and preserved siblings. -/
theorem Stored.replace_child {beforeState afterState : Snapshot} {outerParent : Int}
    {parent child replacement : Node} (stored : Stored beforeState outerParent parent)
    (before after : List Node) (located : parent.children = before ++ child :: after)
    (sameAddress : replacement.vertex = child.vertex)
    (fields : Snapshot.SameFields beforeState afterState parent.vertex)
    (pointers : ∀ vertex ∈ parent.children.map Node.vertex,
      afterState.left vertex = beforeState.left vertex ∧ afterState.right vertex = beforeState.right vertex)
    (replacementStored : Stored afterState parent.vertex replacement)
    (siblingsStored : ∀ sibling ∈ before ++ after, Stored afterState parent.vertex sibling) :
    Stored afterState outerParent (parent.withChildren (before ++ replacement :: after)) := by
  cases stored with
  | @node vertex key outerParent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
    change children = before ++ child :: after at located
    change Stored _ outerParent (.make vertex key marked (before ++ replacement :: after))
    refine Stored.node (fields.key.trans readKey) (fields.parent.trans readParent)
      (fields.mark.trans readMark) ?_ (fields.present.trans readPresent) ?_ ?_ ?_
    · have sameDegree : afterState.degrees vertex = beforeState.degrees vertex := fields.degree
      rw [sameDegree, readDegree, located]
      simp
    · have head := fields.child.trans readHead
      cases before with
      | nil =>
        change afterState.children vertex = replacement.vertex
        change children = child :: after at located
        cases children with
        | nil => simp at located
        | cons first rest =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj located
          exact head.trans sameAddress.symm
      | cons first rest =>
        change afterState.children vertex = first.vertex
        change children = first :: (rest ++ child :: after) at located
        cases children with
        | nil => simp at located
        | cons old tail =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj located
          exact head
    · have sameVertices : (before ++ replacement :: after).map Node.vertex = children.map Node.vertex := by
        simp [located, sameAddress]
      rw [sameVertices]
      rcases ring with empty | ring
      · exact Or.inl empty
      · exact Or.inr (ring.frame (fun vertex member => (pointers vertex member).1)
          (fun vertex member => (pointers vertex member).2))
    · intro sibling member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inBefore | rfl | inAfter
      · exact siblingsStored sibling (by simp [inBefore])
      · exact replacementStored
      · exact siblingsStored sibling (by simp [inAfter])

end Algo2Lean.Fibonacci
