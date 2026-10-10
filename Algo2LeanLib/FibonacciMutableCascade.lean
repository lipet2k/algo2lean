import Algo2LeanLib.FibonacciStoredContext
import Algo2LeanLib.FibonacciRootInsertion

namespace Algo2Lean.Fibonacci

/-- The two existing root addresses touched by `add_root` are actual roots. -/
def Snapshot.RootEndpoints (state : Snapshot) : Prop :=
  0 ≤ state.minimum → state.parents state.minimum = -1 ∧ state.parents (state.right state.minimum) = -1

theorem Represented.root_endpoints {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) : state.RootEndpoints := by
  intro nonempty
  obtain ⟨root, member, pointer, _⟩ := represented.minimum.resolve_left (by rintro ⟨_, negative⟩; omega)
  have head : state.minimum ∈ forest.map Node.vertex := by rw [pointer]; exact List.mem_map.mpr ⟨root, member, rfl⟩
  have ring : Rings.Ring state.left state.right (forest.map Node.vertex) := by
    rcases represented.roots with empty | ring
    · rw [empty] at head; simp at head
    · exact ring
  exact ⟨represented.root_parent head, represented.root_parent (ring.neighbors head).2⟩

/-- Adding a separate subtree only changes its own header and root pointers. -/
theorem Stored.addRoot_frame {state : Snapshot} {parent vertex : Int} {node : Node}
    (stored : Stored state parent node) (absent : ¬node.Has vertex)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex)
    (endpoints : state.RootEndpoints) : Stored (state.addRoot vertex) parent node := by
  apply stored.frame
  · intro value key member
    apply state.addRoot_other_fields
    intro same
    exact absent (same ▸ ⟨key, member⟩)
  · intro value key member
    have active : node.Has value := ⟨key, Node.descendant_entries member⟩
    have different : value ≠ vertex := fun same => absent (same ▸ active)
    obtain ⟨parentKey, parentInside⟩ := stored.descendant_parent value key member
    have nonroot := nonnegative _ _ parentInside
    apply state.addRoot_other_links _ _ different
    intro existsRoot
    obtain ⟨first, next⟩ := endpoints existsRoot
    constructor
    · intro same; rw [same, first] at nonroot; omega
    · intro same; rw [same, next] at nonroot; omega

/-- A detached subtree becomes an unmarked root with its internal structure intact. -/
theorem Stored.addRoot_self {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (unique : (node.entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex)
    (endpoints : state.RootEndpoints) : Stored (state.addRoot node.vertex) (-1) (node.withMark false) := by
  apply stored.change_header (after := state.addRoot node.vertex) false
  · exact stored.root_key
  · simp [Snapshot.addRoot]
  · simp [Snapshot.addRoot]
  · exact stored.root_degree
  · exact stored.root_present
  · rfl
  · intro vertex key member
    apply state.addRoot_other_fields
    intro same
    exact node.unique_root unique ⟨key, same ▸ member⟩
  · intro vertex key member
    have different : vertex ≠ node.vertex := by
      intro same
      exact node.unique_root unique ⟨key, same ▸ member⟩
    obtain ⟨parentKey, parentInside⟩ := stored.descendant_parent vertex key member
    have nonroot := nonnegative _ _ parentInside
    apply state.addRoot_other_links _ _ different
    intro existsRoot
    obtain ⟨first, next⟩ := endpoints existsRoot
    constructor
    · intro same; rw [same, first] at nonroot; omega
    · intro same; rw [same, next] at nonroot; omega

/-- A child-ring removal cannot change the existing root-ring endpoints. -/
theorem Stored.removeChild_endpoints {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children)
    (parentNonnegative : 0 ≤ parent.vertex) (endpoints : state.RootEndpoints) :
    (state.removeChild child.vertex parent.vertex).RootEndpoints := by
  intro nonempty
  change 0 ≤ state.minimum at nonempty
  obtain ⟨head, next⟩ := endpoints nonempty
  have childStored : Stored state parent.vertex child := by
    cases stored with | node _ _ _ _ _ _ _ children => exact children child member
  have different : state.minimum ≠ child.vertex := by
    intro same
    have childParent := childStored.root_parent
    rw [same] at head
    omega
  have unchanged := stored.removeChild_links member different (by omega)
  change state.parents state.minimum = -1 ∧
    state.parents ((state.removeChild child.vertex parent.vertex).right state.minimum) = -1
  rw [unchanged.2]
  exact ⟨head, next⟩

/-- The exact local mutation performed by the source `cut` helper. -/
def Snapshot.cut (state : Snapshot) (child parent : Int) : Snapshot :=
  (state.removeChild child parent).addRoot child

/-- Root insertion after a child removal remains a local edit of its old
    parent's subtree, with the permitted global root-ring rewiring. -/
theorem Stored.cut_local {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children)
    (parentNonnegative : 0 ≤ parent.vertex) (endpoints : state.RootEndpoints) :
    Snapshot.LocalChange state (state.cut child.vertex parent.vertex) parent := by
  have removal := stored.removeChild_local member
  have removedEndpoints := stored.removeChild_endpoints member parentNonnegative endpoints
  constructor
  · intro vertex outside
    have different : vertex ≠ child.vertex := by
      intro same
      exact outside (same ▸ ⟨child.key, Node.child_entries member child.root_entry⟩)
    have first := removal.fields vertex outside
    have second := (state.removeChild child.vertex parent.vertex).addRoot_other_fields child.vertex vertex different
    exact ⟨second.key.trans first.key, second.parent.trans first.parent, second.child.trans first.child,
      second.degree.trans first.degree, second.mark.trans first.mark, second.present.trans first.present⟩
  · intro vertex nonroot outside
    have different : vertex ≠ child.vertex := by
      intro same
      exact outside (same ▸ ⟨child.key, List.mem_flatMap.mpr ⟨child, member, child.root_entry⟩⟩)
    have first := removal.links vertex nonroot outside
    have second := (state.removeChild child.vertex parent.vertex).addRoot_other_links child.vertex vertex different
      (by intro present
          obtain ⟨head, next⟩ := removedEndpoints present
          change state.parents _ = -1 at head next
          constructor
          · intro same; rw [same] at nonroot; omega
          · intro same; rw [same] at nonroot; omega)
    exact ⟨second.1.trans first.1, second.2.trans first.2⟩

/-- Inserting a node which was not a root preserves the root-endpoint invariant. -/
theorem Snapshot.addRoot_endpoints {state : Snapshot} {vertex : Int}
    (endpoints : state.RootEndpoints) (nonroot : 0 ≤ state.parents vertex) :
    (state.addRoot vertex).RootEndpoints := by
  intro _
  by_cases empty : state.minimum < 0
  · simp [Snapshot.addRoot, empty, Rings.write]
  · obtain ⟨head, next⟩ := endpoints (by omega)
    have notHead : vertex ≠ state.minimum := by intro same; rw [same, head] at nonroot; omega
    have notNext : vertex ≠ state.right state.minimum := by intro same; rw [same, next] at nonroot; omega
    by_cases better : state.keys vertex < state.keys state.minimum
    · simp [Snapshot.addRoot, empty, better, Rings.insertAfterRight, Rings.write,
        notHead, Ne.symm notNext, next]
    · simp [Snapshot.addRoot, empty, better, Rings.insertAfterRight, Rings.write,
        Ne.symm notHead, head]

/-- A complete `cut` preserves the finite main tree with the child removed and
    establishes a separate unmarked stored root, at arbitrary ancestor depth. -/
theorem Stored.cut_context {state : Snapshot} {rootParent : Int} {context : List Ancestor}
    {parent child : Node} (stored : Stored state rootParent (Ancestors.plug context parent))
    (unique : ((Ancestors.plug context parent).entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context parent).entries → 0 ≤ vertex)
    (endpoints : state.RootEndpoints) (before after : List Node)
    (located : parent.children = before ++ child :: after) :
    Stored (state.cut child.vertex parent.vertex) rootParent
      (Ancestors.plug context (parent.withChildren (before ++ after))) ∧
      Stored (state.cut child.vertex parent.vertex) (-1) (child.withMark false) ∧
      (state.cut child.vertex parent.vertex).RootEndpoints := by
  have parentStored := stored.focus_context
  have included := Ancestors.entries_sublist context parent
  have parentUnique := (included.map Prod.fst).nodup unique
  have parentNonnegative : 0 ≤ parent.vertex := nonnegative parent.vertex parent.key
    (included.subset parent.root_entry)
  have childMember : child ∈ parent.children := by rw [located]; simp
  have removed := parentStored.removeChild before after located parentUnique
  have newUnique := ((parent.cut_entries before after child located).map Prod.fst).nodup_iff.mp parentUnique
  rw [List.map_append] at newUnique
  have parts := List.nodup_append.mp newUnique
  have removedEndpoints := parentStored.removeChild_endpoints childMember parentNonnegative endpoints
  have prunedContained : ∀ vertex key, (vertex, key) ∈ (parent.withChildren (before ++ after)).entries →
      (vertex, key) ∈ parent.entries := by
    intro vertex key member
    exact (parent.cut_entries before after child located).mem_iff.mpr (List.mem_append_left _ member)
  have childContained : ∀ vertex key, (vertex, key) ∈ child.entries → (vertex, key) ∈ parent.entries :=
    fun _ _ member => Node.child_entries childMember member
  have childNow := removed.2.1.addRoot_self parts.2.1
    (fun vertex key member => nonnegative vertex key (included.subset (childContained vertex key member))) removedEndpoints
  have childAbsent : ¬(parent.withChildren (before ++ after)).Has child.vertex := by
    intro inside
    exact parts.2.2 child.vertex ((Node.has_iff_map _ _).mp inside) child.vertex
      ((Node.has_iff_map _ _).mp ⟨child.key, child.root_entry⟩) rfl
  have parentNow := removed.1.addRoot_frame childAbsent
    (fun vertex key member => nonnegative vertex key (included.subset (prunedContained vertex key member))) removedEndpoints
  refine ⟨?_, childNow, ?_⟩
  · exact stored.lift_context unique nonnegative
      (parentStored.cut_local childMember parentNonnegative endpoints) rfl parentNow
  · apply Snapshot.addRoot_endpoints removedEndpoints
    have pointer := removed.2.1.root_parent
    rw [pointer]
    exact parentNonnegative

/-- Finite structural storage during a cascade. Rank and heap-order restoration
    are proved at the boundary; transient child-loss states need not satisfy them. -/
structure StoredForest (state : Snapshot) (forest : Forest) : Prop where
  unique : forest.Unique
  stored : ∀ root ∈ forest, Stored state (-1) root
  nonnegative : ∀ vertex key, (vertex, key) ∈ forest.entries → 0 ≤ vertex

theorem Represented.stored_forest {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) : StoredForest state forest :=
  ⟨represented.valid.1, represented.stored, represented.nonnegative⟩

theorem StoredForest.perm {state : Snapshot} {before after : Forest}
    (stored : StoredForest state before) (permutation : after.Perm before) : StoredForest state after := by
  have entries := permutation.flatMap_right Node.entries
  exact ⟨stored.unique.of_entries_perm entries,
    fun root member => stored.stored root (permutation.mem_iff.mp member),
    fun vertex key member => stored.nonnegative vertex key (entries.mem_iff.mp member)⟩

/-- A complete cut preserves all other roots, including previously promoted
    ancestors accumulated by the same cascading operation. -/
theorem StoredForest.cut {state : Snapshot} {context : List Ancestor} {parent child : Node} {rest : Forest}
    (forest : StoredForest state (Ancestors.plug context parent :: rest))
    (endpoints : state.RootEndpoints) (before after : List Node)
    (located : parent.children = before ++ child :: after) :
    StoredForest (state.cut child.vertex parent.vertex)
      (Ancestors.plug context (parent.withChildren (before ++ after)) :: child.withMark false :: rest) ∧
      (state.cut child.vertex parent.vertex).RootEndpoints := by
  let main := Ancestors.plug context parent
  have mainStored := forest.stored main (by simp [main])
  have mainUnique := forest.unique.head
  have mainNonnegative : ∀ vertex key, (vertex, key) ∈ main.entries → 0 ≤ vertex :=
    fun vertex key member => forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨main, by simp [main], member⟩)
  have cut := mainStored.cut_context mainUnique mainNonnegative endpoints before after located
  have parentStored := mainStored.focus_context
  have included := Ancestors.entries_sublist context parent
  have parentNonnegative := mainNonnegative parent.vertex parent.key (included.subset parent.root_entry)
  have member : child ∈ parent.children := by rw [located]; simp
  have change :=  parentStored.cut_local member parentNonnegative endpoints
  have contents := Ancestors.entries_replace (context := context) (parent.cut_entries before after child located)
  refine ⟨⟨?_, ?_, ?_⟩, cut.2.2⟩
  · apply forest.unique.of_entries_perm
    simpa [Forest.entries, List.append_assoc] using (contents.symm.append_right rest.entries)
  · intro root inForest
    rcases List.mem_cons.mp inForest with rfl | tail
    · exact cut.1
    rcases List.mem_cons.mp tail with rfl | old
    · exact cut.2.1
    · apply (forest.stored root (by simp [old])).frame_local change
      · intro vertex rootHas parentHas
        apply (Forest.Unique.disjoint (front := [main]) (back := rest) forest.unique) vertex
        · obtain ⟨key, inside⟩ := parentHas
          exact ⟨key, by simpa [Forest.entries] using included.subset inside⟩
        · obtain ⟨key, inside⟩ := rootHas
          exact ⟨key, List.mem_flatMap.mpr ⟨root, old, inside⟩⟩
      · intro vertex key inside
        exact forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨root, by simp [old], inside⟩)
  · intro vertex key inForest
    have all : (Forest.entries (Ancestors.plug context (parent.withChildren (before ++ after)) :: child.withMark false :: rest)).Perm
        (Forest.entries (main :: rest)) := by
      simpa [Forest.entries, main, List.append_assoc] using contents.symm.append_right rest.entries
    exact forest.nonnegative vertex key (all.mem_iff.mp inForest)

theorem Stored.root_mark {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.marks node.vertex = if node.marked then 1 else 0 := by
  cases stored
  assumption

theorem StoredForest.mark {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (forest : StoredForest state (Ancestors.plug context node :: rest)) (marked : Bool) :
    StoredForest (state.setMark node.vertex marked) (Ancestors.plug context (node.withMark marked) :: rest) := by
  have mainStored := forest.stored (Ancestors.plug context node) (by simp)
  have included := Ancestors.entries_sublist context node
  have nodeUnique := (included.map Prod.fst).nodup forest.unique.head
  have mainNonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context node).entries → 0 ≤ vertex :=
    fun vertex key member => forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨_, by simp, member⟩)
  have change : Snapshot.LocalChange state (state.setMark node.vertex marked) node := by
    apply Snapshot.LocalChange.setMark (after := state)
    constructor
    · intro vertex _; constructor <;> rfl
    · intro vertex _ _; exact ⟨rfl, rfl⟩
  have contents : (Ancestors.plug context (node.withMark marked)).entries.Perm
      (Ancestors.plug context node).entries := by
    have lifted := Ancestors.entries_replace (context := context) (before := node.withMark marked)
      (after := node) (removed := []) (by simp)
    simpa using lifted
  refine ⟨forest.unique.of_entries_perm ?_, ?_, ?_⟩
  · simpa [Forest.entries] using contents.append_right rest.entries
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact mainStored.lift_context forest.unique.head mainNonnegative change rfl
        (mainStored.focus_context.setMark nodeUnique marked)
    · apply (forest.stored root (by simp [old])).setMark_frame
      intro inside
      apply (Forest.Unique.disjoint (front := [Ancestors.plug context node]) (back := rest) forest.unique) node.vertex
      · exact ⟨node.key, by simpa [Forest.entries] using included.subset node.root_entry⟩
      · obtain ⟨key, inside⟩ := inside
        exact ⟨key, List.mem_flatMap.mpr ⟨root, old, inside⟩⟩
  · intro vertex key member
    have all := contents.append_right rest.entries
    exact forest.nonnegative vertex key (all.mem_iff.mp member)

/-- The actual parent/mark control flow of cascading_cut, abstracted only from
    sequence references and clock increments. Each cut is the exact Snapshot effect. -/
inductive CascadeRun : Snapshot → Snapshot → Int → Nat → Prop where
  | root {state : Snapshot} {vertex : Int} (root : state.parents vertex < 0) :
      CascadeRun state state vertex 0
  | mark {state : Snapshot} {vertex : Int} (nonroot : 0 ≤ state.parents vertex)
      (unmarked : state.marks vertex = 0) :
      CascadeRun state (state.setMark vertex true) vertex 0
  | cut {state final : Snapshot} {vertex : Int} {cuts : Nat}
      (nonroot : 0 ≤ state.parents vertex) (marked : state.marks vertex ≠ 0)
      (next : CascadeRun (state.cut vertex (state.parents vertex)) final (state.parents vertex) cuts) :
      CascadeRun state final vertex (cuts + 1)

/-- Actual pointer-based cascade execution follows the finite ancestor repair,
    preserving every stored subtree and producing exactly its promoted roots. -/
theorem cascade_run_exists (context : List Ancestor) (node : Node) (kept : List Node)
    (state : Snapshot) (rest : Forest)
    (forest : StoredForest state (Ancestors.plug context (node.withChildren kept) :: rest))
    (endpoints : state.RootEndpoints) :
    ∃ final, CascadeRun state final node.vertex (cascadeCuts node context) ∧
      StoredForest final (cascadeForest node kept context ++ rest) ∧ final.RootEndpoints := by
  induction context generalizing node kept state rest with
  | nil =>
    have stored := forest.stored (node.withChildren kept) (by simp [Ancestors.plug])
    have parent := stored.root_parent
    change state.parents node.vertex = -1 at parent
    exact ⟨state, .root (by omega), forest, endpoints⟩
  | cons frame ancestors ih =>
    have mainStored := forest.stored (Ancestors.plug (frame :: ancestors) (node.withChildren kept)) (by simp)
    have focus := mainStored.focus_context
    have parent : state.parents node.vertex = frame.vertex := focus.root_parent
    have readMark : state.marks node.vertex = if node.marked then 1 else 0 := focus.root_mark
    have frameMember : (frame.vertex, frame.key) ∈ (Ancestors.plug (frame :: ancestors) (node.withChildren kept)).entries :=
      (Ancestors.entries_sublist ancestors (frame.plug (node.withChildren kept))).subset (by simp [Ancestor.plug, Node.entries])
    have frameNonnegative := forest.nonnegative frame.vertex frame.key (List.mem_flatMap.mpr ⟨_, by simp, frameMember⟩)
    by_cases marked : node.marked = true
    · have cut := forest.cut (context := ancestors) (parent := frame.plug (node.withChildren kept))
        (child := node.withChildren kept) endpoints frame.before frame.after rfl
      obtain ⟨final, run, repaired, finalEndpoints⟩ := ih (frame.plug node) (frame.before ++ frame.after)
        (state.cut node.vertex frame.vertex) ((node.withChildren kept).withMark false :: rest) cut.1 cut.2
      refine ⟨final, ?_, ?_, finalEndpoints⟩
      · have sourceRun : CascadeRun state final node.vertex (cascadeCuts (frame.plug node) ancestors + 1) :=
          CascadeRun.cut (by omega) (by simp [marked] at readMark; omega) (by simpa only [parent] using run)
        simpa only [cascadeCuts, marked, ↓reduceIte] using sourceRun
      · apply repaired.perm
        simp only [cascadeForest, marked, ↓reduceIte, List.cons_append]
        exact List.perm_middle.symm
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      refine ⟨state.setMark node.vertex true, ?_, ?_, ?_⟩
      · simpa [cascadeCuts, unmarked] using CascadeRun.mark (by omega : 0 ≤ state.parents node.vertex)
          (by simpa [unmarked] using readMark)
      · simpa [cascadeForest, unmarked] using forest.mark true
      · exact endpoints

/-- One requested cut followed by its actual cascade produces the same finite
    forest whose potential accounting was proved in the mathematical layer. -/
theorem cut_and_cascade_exists (context : List Ancestor) (parent child : Node)
    (before after : List Node) (state : Snapshot) (rest : Forest)
    (located : parent.children = before ++ child :: after)
    (forest : StoredForest state (Ancestors.plug context parent :: rest)) (endpoints : state.RootEndpoints) :
    ∃ final, CascadeRun (state.cut child.vertex parent.vertex) final parent.vertex (cascadeCuts parent context) ∧
      StoredForest final (child.withMark false :: cascadeForest parent (before ++ after) context ++ rest) ∧
      final.RootEndpoints ∧
      Decrease (Forest.counts (Ancestors.plug context parent :: rest))
        (Forest.counts (child.withMark false :: cascadeForest parent (before ++ after) context ++ rest))
        (cascadeCuts parent context + 1) := by
  have cut := forest.cut endpoints before after located
  obtain ⟨final, run, result, finalEndpoints⟩ := cascade_run_exists context parent (before ++ after)
    (state.cut child.vertex parent.vertex) (child.withMark false :: rest) cut.1 cut.2
  exact ⟨final, run, result.perm List.perm_middle.symm, finalEndpoints,
    cascadeForest_decrease_accounting context parent child before after rest located⟩

end Algo2Lean.Fibonacci
