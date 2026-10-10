import Algo2LeanLib.FibonacciDecrease

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Algo2Lean.Fibonacci

/-- Exact replacement of one queue entry; all other entries are unchanged. -/
def EntryChange (before after : List (Int × Int)) (vertex oldKey newKey : Int) : Prop :=
  ∃ unchanged, before.Perm ((vertex, oldKey) :: unchanged) ∧
    after.Perm ((vertex, newKey) :: unchanged)

theorem Node.entries_head (node : Node) : node.entries = (node.vertex, node.key) :: node.children.flatMap Node.entries := by cases node; simp [Node.entries, Node.vertex, Node.key, Node.children]

/-- Entries surrounding a focused subtree in its ancestor context. -/
def Ancestors.surrounding : List Ancestor → List (Int × Int)
  | [] => []
  | frame :: rest => (frame.vertex, frame.key) ::
      (Forest.entries frame.before ++ Forest.entries frame.after ++ Ancestors.surrounding rest)

theorem Ancestors.entries_surrounding (context : List Ancestor) (node : Node) :
    (Ancestors.plug context node).entries.Perm (node.entries ++ Ancestors.surrounding context) := by
  induction context generalizing node with
  | nil => simp [Ancestors.plug, Ancestors.surrounding]
  | cons frame rest ih =>
    apply (ih (frame.plug node)).trans
    simp only [Ancestor.plug, Node.entries, List.flatMap_append, List.flatMap_cons]
    simpa [Ancestors.surrounding, Forest.entries, List.append_assoc] using
      (List.perm_append_comm (l₁ := (frame.vertex, frame.key) :: frame.before.flatMap Node.entries)
        (l₂ := node.entries)).append_right (frame.after.flatMap Node.entries ++ Ancestors.surrounding rest)

theorem Ancestors.key_change (context : List Ancestor) (node : Node) (rest : Forest) (key : Int) :
    EntryChange (Forest.entries (Ancestors.plug context node :: rest))
      (Forest.entries (Ancestors.plug context (node.withKey key) :: rest)) node.vertex node.key key := by
  refine ⟨node.children.flatMap Node.entries ++ Ancestors.surrounding context ++ rest.entries, ?_, ?_⟩
  · simpa [Forest.entries, Node.entries_head, List.append_assoc] using
      (Ancestors.entries_surrounding context node).append_right rest.entries
  · simpa [Forest.entries, Node.entries_head, List.append_assoc] using!
      (Ancestors.entries_surrounding context (node.withKey key)).append_right rest.entries

theorem EntryChange.vertices {before after : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) :
    (after.map Prod.fst).Perm (before.map Prod.fst) := by
  obtain ⟨unchanged, old, new⟩ := changed
  exact (new.map Prod.fst).trans (old.map Prod.fst).symm

theorem Stored.lowerKey_frame {state : Snapshot} {parent vertex : Int} {node : Node}
    (stored : Stored state parent node) (absent : ¬node.Has vertex) (key : Int) :
    Stored (state.lowerKey vertex key) parent node := by
  apply stored.frame
  · intro value old member
    have different : value ≠ vertex := by intro same; exact absent (same ▸ ⟨old, member⟩)
    constructor <;> simp [Snapshot.lowerKey, Rings.write, different]
  · intro value old member
    exact ⟨rfl, rfl⟩

theorem Stored.lowerKey {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (unique : (node.entries.map Prod.fst).Nodup) (key : Int) :
    Stored (state.lowerKey node.vertex key) parent (node.withKey key) := by
  have outside := node.unique_root unique
  cases stored with
  | @node vertex value parent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
    refine Stored.node ?_ readParent readMark readDegree readPresent ?_ ring ?_
    · simp [Snapshot.lowerKey, Node.vertex]
    · cases children <;> exact readHead
    · intro child member
      apply (subtrees child member).lowerKey_frame (key := key)
      rintro ⟨old, inside⟩
      exact outside ⟨old, List.mem_flatMap.mpr ⟨child, member, inside⟩⟩

theorem Snapshot.LocalChange.lowerKey (state : Snapshot) (node : Node) (key : Int) :
    Snapshot.LocalChange state (state.lowerKey node.vertex key) node := by
  constructor
  · intro vertex outside
    have different : vertex ≠ node.vertex := by intro same; exact outside (same ▸ ⟨node.key, node.root_entry⟩)
    constructor <;> simp [Snapshot.lowerKey, Rings.write, different]
  · intro vertex parent outside
    exact ⟨rfl, rfl⟩

theorem StoredForest.lowerKey {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (forest : StoredForest state (Ancestors.plug context node :: rest)) (key : Int) :
    StoredForest (state.lowerKey node.vertex key) (Ancestors.plug context (node.withKey key) :: rest) := by
  have mainStored := forest.stored (Ancestors.plug context node) (by simp)
  have included := Ancestors.entries_sublist context node
  have nodeUnique := (included.map Prod.fst).nodup forest.unique.head
  have mainNonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context node).entries → 0 ≤ vertex :=
    fun vertex key member => forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨_, by simp, member⟩)
  have vertices := (Ancestors.key_change context node rest key).vertices
  refine ⟨vertices.nodup_iff.mpr forest.unique, ?_, ?_⟩
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact mainStored.lift_context forest.unique.head mainNonnegative (Snapshot.LocalChange.lowerKey state node key) rfl
        (mainStored.focus_context.lowerKey nodeUnique key)
    · apply (forest.stored root (by simp [old])).lowerKey_frame
      intro inside
      apply (Forest.Unique.disjoint (front := [Ancestors.plug context node]) (back := rest) forest.unique) node.vertex
      · exact ⟨node.key, by simpa [Forest.entries] using included.subset node.root_entry⟩
      · obtain ⟨oldKey, inside⟩ := inside
        exact ⟨oldKey, List.mem_flatMap.mpr ⟨root, old, inside⟩⟩
  · intro vertex value member
    have old := vertices.mem_iff.mp (List.mem_map.mpr ⟨(vertex, value), member, rfl⟩)
    obtain ⟨⟨oldVertex, oldKey⟩, member, same⟩ := List.mem_map.mp old
    change oldVertex = vertex at same
    subst oldVertex
    exact forest.nonnegative vertex oldKey member

/-- Lowering a nonroot key leaves the root boundary intact; the parent-edge
    order may temporarily fail and is repaired by the following cut. -/
theorem RootBoundary.lower_nonroot {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (boundary : RootBoundary state (Ancestors.plug context node :: rest)) (key : Int)
    (nonroot : 0 ≤ state.parents node.vertex) :
    RootBoundary (state.lowerKey node.vertex key) (Ancestors.plug context (node.withKey key) :: rest) := by
  have vertices := (Ancestors.key_change context node rest key).vertices
  have address := Ancestors.root_vertex context (before := node.withKey key) (after := node) rfl
  have rootMap : (Ancestors.plug context (node.withKey key) :: rest).map Node.vertex =
      (Ancestors.plug context node :: rest).map Node.vertex := by simp only [List.map_cons, address]
  have different (vertex : Int) (member : vertex ∈ (Ancestors.plug context node :: rest).map Node.vertex) :
      vertex ≠ node.vertex := by
    intro same
    have parent := boundary.root_parent member
    rw [same] at parent
    omega
  have least := boundary.minimum_addresses (by simp)
  refine ⟨boundary.trees.lowerKey key, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, by simpa only [rootMap] using permutation, ring⟩
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence, Forest.has_iff_map, Forest.has_iff_map]
    exact vertices.mem_iff.symm
  · change state.size = _
    rw [boundary.size]
    have length := vertices.length_eq
    simp only [List.length_map] at length
    exact congrArg Int.ofNat length.symm
  · have member : state.minimum ∈ (Ancestors.plug context (node.withKey key) :: rest).map Node.vertex := by rw [rootMap]; exact least.1
    obtain ⟨root, member, pointer⟩ := List.mem_map.mp member
    refine Or.inr ⟨root, member, pointer.symm, ?_⟩
    intro other member
    have old : other.vertex ∈ (Ancestors.plug context node :: rest).map Node.vertex := by
      rw [← rootMap]; exact List.mem_map.mpr ⟨other, member, rfl⟩
    simpa [Snapshot.lowerKey, Rings.write, different state.minimum least.1, different other.vertex old]
      using least.2 other.vertex old

theorem RootBoundary.finish_root {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    {vertex : Int} (member : vertex ∈ forest.map Node.vertex) : state.finishDecrease vertex = state := by
  have nonempty : forest ≠ [] := by rintro rfl; simp at member
  have least := (boundary.minimum_addresses nonempty).2 vertex member
  simp [Snapshot.finishDecrease, Int.not_lt.mpr least]

theorem Ancestors.root_key (context : List Ancestor) {before after : Node}
    (same : before.key = after.key) : (Ancestors.plug context before).key = (Ancestors.plug context after).key := by
  induction context generalizing before after with
  | nil => exact same
  | cons frame rest ih => exact ih rfl

@[simp] theorem Node.withKey_marks (node : Node) (key : Int) : (node.withKey key).marks = node.marks := by
  cases node
  simp [Node.marks, Node.withKey, Node.vertex, Node.marked, Node.children]

/-- Changing a focused key changes neither roots nor marks. -/
theorem Ancestors.key_counts (context : List Ancestor) (node : Node) (rest : Forest) (key : Int) :
    Forest.counts (Ancestors.plug context (node.withKey key) :: rest) =
      Forest.counts (Ancestors.plug context node :: rest) := by
  simp [Forest.counts, Forest.marks, Ancestors.plug_marks]

theorem Node.Ordered.replace_child_bound {parent child replacement : Node}
    (ordered : parent.Ordered) (before after : List Node)
    (located : parent.children = before ++ child :: after)
    (replacementOrdered : replacement.Ordered) (bound : parent.key ≤ replacement.key) :
    (parent.withChildren (before ++ replacement :: after)).Ordered := by
  cases ordered with
  | @make vertex key marked children bounds subtrees =>
    change children = before ++ child :: after at located
    apply Node.Ordered.make
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply bounds; rw [located]; simp [old]
      · exact bound
      · apply bounds; rw [located]; simp [old]
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply subtrees; rw [located]; simp [old]
      · exact replacementOrdered
      · apply subtrees; rw [located]; simp [old]

/-- A decreased root needs only the final minimum comparison. -/
theorem RootBoundary.lower_root {state : Snapshot} {node : Node} {rest : Forest}
    (boundary : RootBoundary state (node :: rest)) (key : Int) (decreased : key ≤ node.key) :
    RootBoundary ((state.lowerKey node.vertex key).finishDecrease node.vertex) (node.withKey key :: rest) := by
  let lowered := state.lowerKey node.vertex key
  have vertices := (Ancestors.key_change [] node rest key).vertices
  have rootMap : (node.withKey key :: rest).map Node.vertex = (node :: rest).map Node.vertex := rfl
  have least := boundary.minimum_addresses (by simp)
  have oldKey := (boundary.trees.stored node (by simp)).root_key
  have keyAt : lowered.keys node.vertex = key := by simp [lowered, Snapshot.lowerKey]
  have keyElse (vertex : Int) (different : vertex ≠ node.vertex) : lowered.keys vertex = state.keys vertex := by
    simp [lowered, Snapshot.lowerKey, Rings.write, different]
  have keyMonotone (vertex : Int) : lowered.keys vertex ≤ state.keys vertex := by
    by_cases same : vertex = node.vertex
    · rw [same, keyAt, oldKey]; exact decreased
    · rw [keyElse vertex same]; exact Int.le_refl _
  have others (vertex : Int) (member : vertex ∈ (node :: rest).map Node.vertex) (different : vertex ≠ node.vertex) :
      lowered.keys state.minimum ≤ lowered.keys vertex := by
    rw [keyElse vertex different]
    exact Int.le_trans (keyMonotone state.minimum) (least.2 vertex member)
  have stored : StoredForest (lowered.finishDecrease node.vertex) (node.withKey key :: rest) := by
    have base := boundary.trees.lowerKey (context := []) key
    refine ⟨base.unique, ?_, base.nonnegative⟩
    intro root member
    apply (base.stored root member).frame
    · intro vertex key inside; constructor <;> rfl
    · intro vertex key inside; exact ⟨rfl, rfl⟩
  refine ⟨stored, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, permutation, ring⟩
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence, Forest.has_iff_map, Forest.has_iff_map]
    exact vertices.mem_iff.symm
  · change state.size = _
    rw [boundary.size]
    have length := vertices.length_eq
    simp only [List.length_map] at length
    exact congrArg Int.ofNat length.symm
  · by_cases better : lowered.keys node.vertex < lowered.keys state.minimum
    · refine Or.inr ⟨node.withKey key, by simp, ?_, ?_⟩
      · change (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) = node.vertex
        rw [if_pos better]
      · intro other member
        have old : other.vertex ∈ (node :: rest).map Node.vertex := by
          rw [← rootMap]; exact List.mem_map.mpr ⟨other, member, rfl⟩
        change lowered.keys (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) ≤ lowered.keys other.vertex
        rw [if_pos better]
        by_cases same : other.vertex = node.vertex
        · rw [same]; exact Int.le_refl _
        · exact Int.le_trans (Int.le_of_lt better) (others other.vertex old same)
    · have member : state.minimum ∈ (node.withKey key :: rest).map Node.vertex := by rw [rootMap]; exact least.1
      obtain ⟨root, member, pointer⟩ := List.mem_map.mp member
      refine Or.inr ⟨root, member, ?_, ?_⟩
      · change (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) = root.vertex
        rw [if_neg better, pointer]
      · intro other member
        have old : other.vertex ∈ (node :: rest).map Node.vertex := by
          rw [← rootMap]; exact List.mem_map.mpr ⟨other, member, rfl⟩
        change lowered.keys (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) ≤ lowered.keys other.vertex
        rw [if_neg better]
        by_cases same : other.vertex = node.vertex
        · rw [same]; omega
        · exact others other.vertex old same

/-- An unchanged minimum comparison is a no-op after the queue invariant has
    already established that the chosen root is globally least. -/
theorem Represented.finishDecrease {state : Snapshot} {forest : Forest} (represented : Represented state forest)
    {vertex key : Int} (member : (vertex, key) ∈ forest.entries) : state.finishDecrease vertex = state := by
  have read := represented.entry member
  have nonempty : forest ≠ [] := by rintro rfl; simp [Forest.entries] at member
  have least := (represented.minimum_key nonempty).2.2 vertex (by omega)
  simp [Snapshot.finishDecrease, Int.not_lt.mpr least]

theorem Forest.Valid.lower_ordered {frame : Ancestor} {context : List Ancestor} {node : Node} {rest : Forest}
    (valid : Forest.Valid (Ancestors.plug (frame :: context) node :: rest))
    (key : Int) (decreased : key ≤ node.key) (bound : frame.key ≤ key) :
    Forest.Valid (Ancestors.plug (frame :: context) (node.withKey key) :: rest) := by
  have rootOrdered := valid.2.1 (Ancestors.plug (frame :: context) node) (by simp)
  have rootRanked := valid.2.2.1 (Ancestors.plug (frame :: context) node) (by simp)
  have nodeOrdered := Ancestors.focus_ordered rootOrdered
  have nodeRanked := Ancestors.focus_ranked rootRanked
  refine ⟨(Ancestors.key_change (frame :: context) node rest key).vertices.nodup_iff.mpr valid.1, ?_, ?_, ?_⟩
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · have frameOrdered := Ancestors.focus_ordered (context := context) rootOrdered
      have repaired : (frame.plug (node.withKey key)).Ordered :=
        frameOrdered.replace_child_bound frame.before frame.after rfl (nodeOrdered.decrease_key key decreased) bound
      exact Ancestors.replace_ordered (context := context) (before := frame.plug node) rootOrdered repaired rfl
    · exact valid.2.1 root (by simp [old])
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact Ancestors.replace_ranked rootRanked (nodeRanked.withKey key) (Nat.le_refl _)
    · exact valid.2.2.1 root (by simp [old])
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · rw [← Ancestors.plug_mark (context := frame :: context) (before := node) (after := node.withKey key) rfl]
      exact valid.2.2.2 _ (by simp)
    · exact valid.2.2.2 root (by simp [old])

theorem cascadeForest_same_header (context : List Ancestor) {before after : Node} (kept : List Node)
    (vertex : before.vertex = after.vertex) (key : before.key = after.key) (marked : before.marked = after.marked) :
    cascadeForest before kept context = cascadeForest after kept context := by
  have same : before.withChildren kept = after.withChildren kept := by
    simp only [Node.withChildren, vertex, key, marked]
  induction context generalizing before after kept with
  | nil => simp only [cascadeForest, same]
  | cons frame rest ih =>
    simp only [cascadeForest, marked, same]
    split
    · rw [ih (before := frame.plug before) (after := frame.plug after) (frame.before ++ frame.after) rfl rfl rfl rfl]
    · rfl

theorem cascadeCuts_same_header (context : List Ancestor) {before after : Node}
    (marked : before.marked = after.marked) : cascadeCuts before context = cascadeCuts after context := by
  induction context generalizing before after with
  | nil => rfl
  | cons frame rest ih =>
    simp only [cascadeCuts, marked]
    split
    · rw [ih (before := frame.plug before) (after := frame.plug after) rfl]
    · rfl

theorem EntryChange.perm_after {before after result : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) (permutation : result.Perm after) :
    EntryChange before result vertex oldKey newKey := by
  obtain ⟨unchanged, old, new⟩ := changed
  exact ⟨unchanged, old, permutation.trans new⟩

theorem EntryChange.perm_before {before after initial : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) (permutation : initial.Perm before) :
    EntryChange initial after vertex oldKey newKey := by
  obtain ⟨unchanged, old, new⟩ := changed
  exact ⟨unchanged, permutation.trans old, new⟩

/-- Lowering and cutting a selected nonroot, followed by the actual cascade,
    restores the full finite forest and its amortized potential invariant. -/
theorem represented_lower_cut {state : Snapshot} {context : List Ancestor} {frame : Ancestor}
    {node : Node} {rest : Forest}
    (represented : Represented state (Ancestors.plug (frame :: context) node :: rest))
    (key : Int) (decreased : key ≤ node.key) :
    ∃ middle outputForest,
      CascadeRun ((state.lowerKey node.vertex key).cut node.vertex frame.vertex) middle
        frame.vertex (cascadeCuts (frame.plug node) context) ∧
      Represented middle outputForest ∧
      EntryChange (Forest.entries (Ancestors.plug (frame :: context) node :: rest))
        outputForest.entries node.vertex node.key key ∧
      Decrease (Forest.counts (Ancestors.plug (frame :: context) node :: rest)) outputForest.counts
        (cascadeCuts (frame.plug node) context + 1) := by
  have rootStored := represented.stored (Ancestors.plug (frame :: context) node) (by simp)
  have parent : state.parents node.vertex = frame.vertex := rootStored.focus_context.root_parent
  have frameStored := rootStored.focus_context (context := context)
  have framePresent : state.present frame.vertex = 1 := frameStored.root_present
  have nonnegative := represented.present_nonnegative (by omega : state.present frame.vertex ≠ 0)
  have lowered := represented.boundary.lower_nonroot key (by omega)
  have cut := lowered.cut (context := context) (parent := frame.plug (node.withKey key))
    (child := node.withKey key) frame.before frame.after rfl
  obtain ⟨middle, run, boundary⟩ := cascade_boundary_exists context (frame.plug node)
    (frame.before ++ frame.after) ((state.lowerKey node.vertex key).cut node.vertex frame.vertex)
    ((node.withKey key).withMark false :: rest) cut
  have canonical := boundary.perm List.perm_middle.symm
  have oldValid := represented.valid.cascade (context := context) (parent := frame.plug node)
    (child := node) frame.before frame.after rfl
  have valid : Forest.Valid ((node.withKey key).withMark false ::
      cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest) := by
    simpa only [Node.withMark, Node.withKey, Node.vertex, Node.key, Node.marked, Node.children]
      using! oldValid.decrease_root key decreased
  obtain ⟨outputForest, order, output⟩ := canonical.close valid
  have content := cascadeForest_entries context (frame.plug (node.withKey key))
    (frame.before ++ frame.after) (node.withKey key).entries
    ((frame.plug (node.withKey key)).cut_entries frame.before frame.after (node.withKey key) rfl)
  have cascadeSame := cascadeForest_same_header context (before := frame.plug (node.withKey key))
    (after := frame.plug node) (frame.before ++ frame.after) rfl rfl rfl
  rw [cascadeSame] at content
  have canonicalContent : (Forest.entries ((node.withKey key).withMark false ::
      cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest)).Perm
      (Forest.entries (Ancestors.plug (frame :: context) (node.withKey key) :: rest)) := by
    have rearranged := (List.perm_append_comm (l₁ := (node.withKey key).entries)
      (l₂ := (cascadeForest (frame.plug node) (frame.before ++ frame.after) context).entries)).trans content.symm
    simpa [Forest.entries, List.flatMap_append, List.append_assoc, Ancestors.plug] using rearranged.append_right rest.entries
  refine ⟨middle, outputForest, run, output,
    (Ancestors.key_change (frame :: context) node rest key).perm_after ((order.flatMap_right Node.entries).trans canonicalContent), ?_⟩
  rw [Forest.counts_perm order]
  have countsSame : Forest.counts ((node.withKey key).withMark false ::
      cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest) =
      Forest.counts (node.withMark false :: cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest) := by
    have markCommute : (node.withKey key).withMark false = (node.withMark false).withKey key := rfl
    simp [Forest.counts, Forest.marks, markCommute]
  simp only [List.cons_append] at countsSame
  rw [countsSame]
  exact cascadeForest_decrease_accounting context (frame.plug node) node frame.before frame.after rest rfl

theorem EntryChange.new_member {before after : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) : (vertex, newKey) ∈ after := by
  obtain ⟨unchanged, _, content⟩ := changed
  exact content.mem_iff.mpr (by simp)

/-- Strict decrease-key at an arbitrary finite ancestor context. The result
    exposes only the exact execution, represented queue, entry replacement,
    and reusable potential accounting. -/
theorem represented_decrease_focused {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (represented : Represented state (Ancestors.plug context node :: rest))
    (key : Int) (decreased : key < node.key) :
    ∃ final outputForest cuts,
      DecreaseRun state final node.vertex key cuts ∧ Represented final outputForest ∧
      EntryChange (Forest.entries (Ancestors.plug context node :: rest)) outputForest.entries node.vertex node.key key ∧
      Decrease (Forest.counts (Ancestors.plug context node :: rest)) outputForest.counts cuts := by
  have rootStored := represented.stored (Ancestors.plug context node) (by simp)
  have nodeStored := rootStored.focus_context
  have readKey := nodeStored.root_key
  have strict : key < state.keys node.vertex := by rw [readKey]; exact decreased
  cases context with
  | nil =>
    have rootParent : state.parents node.vertex = -1 := nodeStored.root_parent
    have boundary := represented.boundary.lower_root key (Int.le_of_lt decreased)
    obtain ⟨outputForest, order, output⟩ := boundary.close (represented.valid.decrease_root key (Int.le_of_lt decreased))
    refine ⟨(state.lowerKey node.vertex key).finishDecrease node.vertex, outputForest, 0,
      .root strict (by omega), output,
      (Ancestors.key_change [] node rest key).perm_after (order.flatMap_right Node.entries), ?_⟩
    rw [Forest.counts_perm order]
    change Decrease (Forest.counts (node :: rest)) (Forest.counts (node.withKey key :: rest)) 0
    rw [show Forest.counts (node.withKey key :: rest) = Forest.counts (node :: rest) from Ancestors.key_counts [] node rest key]
    exact .unchanged _
  | cons frame context =>
    have parent : state.parents node.vertex = frame.vertex := nodeStored.root_parent
    have parentStored := rootStored.focus_context (context := context)
    have parentKey : state.keys frame.vertex = frame.key := parentStored.root_key
    have parentPresent : state.present frame.vertex = 1 := parentStored.root_present
    have parentNonnegative := represented.present_nonnegative (by omega : state.present frame.vertex ≠ 0)
    have unique := ((Ancestors.entries_sublist context (frame.plug node)).map Prod.fst).nodup represented.valid.1.head
    have different : frame.vertex ≠ node.vertex := by
      intro same
      exact (Ancestor.unique_parts unique).2.1 (same ▸ ⟨node.key, node.root_entry⟩)
    have loweredParent : (state.lowerKey node.vertex key).keys (state.parents node.vertex) = frame.key := by
      simp [Snapshot.lowerKey, Rings.write, parent, different, parentKey]
    by_cases ordered : frame.key ≤ key
    · have boundary := represented.boundary.lower_nonroot key (by omega)
      obtain ⟨outputForest, order, output⟩ := boundary.close
        (represented.valid.lower_ordered key (Int.le_of_lt decreased) ordered)
      have content := (Ancestors.key_change (frame :: context) node rest key).perm_after
        (order.flatMap_right Node.entries)
      have finish := output.finishDecrease content.new_member
      refine ⟨state.lowerKey node.vertex key, outputForest, 0, ?_, output, content, ?_⟩
      · have run := DecreaseRun.ordered strict (by omega : 0 ≤ state.parents node.vertex)
          (by rw [loweredParent]; exact ordered)
        simpa only [finish] using run
      · rw [Forest.counts_perm order, Ancestors.key_counts (frame :: context) node rest key]
        exact .unchanged _
    · obtain ⟨middle, outputForest, cascade, output, content, accounting⟩ :=
        represented_lower_cut represented key (Int.le_of_lt decreased)
      have finish := output.finishDecrease content.new_member
      refine ⟨middle, outputForest, cascadeCuts (frame.plug node) context + 1, ?_, output, content, accounting⟩
      have run := DecreaseRun.cascading strict (by omega : 0 ≤ state.parents node.vertex)
        (by rw [loweredParent]; omega) (by simpa only [parent] using cascade)
      simpa only [finish] using run

/-- Every strict decrease of an existing handle terminates, preserves the
    represented Fibonacci heap, changes exactly that key, and satisfies the
    constant-amortized decrease accounting relation. -/
theorem Represented.decrease {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (vertex key : Int)
    (active : state.present vertex ≠ 0) (decreased : key < state.keys vertex) :
    ∃ final outputForest cuts,
      DecreaseRun state final vertex key cuts ∧ Represented final outputForest ∧
      EntryChange forest.entries outputForest.entries vertex (state.keys vertex) key ∧
      Decrease forest.counts outputForest.counts cuts := by
  obtain ⟨oldKey, entry⟩ := (represented.presence vertex).mp active
  have readKey := (represented.entry entry).1
  obtain ⟨root, member, inside⟩ := List.mem_flatMap.mp entry
  obtain ⟨context, node, located, address, value⟩ := (represented.stored root member).locate vertex oldKey inside
  obtain ⟨front, back, position⟩ := List.mem_iff_append.mp member
  subst forest
  have rotated := represented.rotate (front := front) (back := root :: back)
  have permutation : (root :: (back ++ front)).Perm (front ++ root :: back) := by
    simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
  rw [located] at rotated
  obtain ⟨final, outputForest, cuts, run, output, changed, accounting⟩ :=
    represented_decrease_focused (by simpa only [List.cons_append] using rotated) key
      (by rw [value, ← readKey]; exact decreased)
  refine ⟨final, outputForest, cuts, ?_, output, ?_, ?_⟩
  · simpa only [address] using run
  · have entryPermutation := permutation.flatMap_right Node.entries
    rw [located] at entryPermutation
    have complete := changed.perm_before entryPermutation.symm
    simpa only [address, value, readKey, located] using! complete
  · have counts := Forest.counts_perm permutation
    rw [located] at counts
    rw [located, ← counts]
    exact accounting

end Algo2Lean.Fibonacci
