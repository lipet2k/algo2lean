import Algo2LeanLib.FibonacciConsolidation
import Algo2LeanLib.FibonacciRootInsertion

namespace Algo2Lean.Fibonacci

/-- Move one detached tree into the pending root ring at its actual cursor. -/
theorem SplitRepresented.add_detached {state : Snapshot} {pending detached : Forest} {added : Node}
    (represented : SplitRepresented state pending (added :: detached)) :
    ∃ afterPending,
      SplitRepresented (state.addRoot added.vertex) afterPending detached ∧
      afterPending.Perm (added :: pending) := by
  cases pending with
  | nil => exact ⟨[added], represented.add_detached_empty, List.Perm.refl _⟩
  | cons head tail =>
    obtain ⟨cursor, member, pointer⟩ := represented.cursor.resolve_left (by simp)
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    have represented' : SplitRepresented state (front ++ cursor :: back) (added :: detached) := located ▸ represented
    have rotated := represented'.rotate_pending
    change SplitRepresented state (cursor :: (back ++ front)) (added :: detached) at rotated
    refine ⟨cursor :: added :: (back ++ front), rotated.add_detached_after_head pointer, ?_⟩
    have rotation : (cursor :: (back ++ front)).Perm (head :: tail) := by
      rw [located]
      simpa only [List.cons_append] using
        (List.perm_append_comm (l₁ := cursor :: back) (l₂ := front))
    exact (List.Perm.swap _ _ _).trans (rotation.cons added)

/-- The current cursor is a least-key root of the reconstructed pending ring. -/
def PendingLeast (state : Snapshot) (pending : Forest) : Prop :=
  ∀ root ∈ pending, state.keys state.minimum ≤ root.key

theorem SplitRepresented.pending_empty {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) : state.minimum < 0 ↔ pending = [] := by
  constructor
  · intro negative
    rcases represented.cursor with empty | ⟨root, member, pointer⟩
    · exact empty.1
    · have positive := represented.nonnegative root.vertex root.key
        (List.mem_flatMap.mpr ⟨root, by simp [member], root.root_entry⟩)
      omega
  · intro empty
    subst pending
    rcases represented.cursor with empty | ⟨root, impossible, _⟩
    · omega
    · simp at impossible

/-- Comparing the new root with the old cursor preserves the minimum invariant. -/
theorem SplitRepresented.add_detached_least {state : Snapshot} {pending detached afterPending : Forest}
    {added : Node} (represented : SplitRepresented state pending (added :: detached))
    (least : PendingLeast state pending) (permutation : afterPending.Perm (added :: pending)) :
    PendingLeast (state.addRoot added.vertex) afterPending := by
  have key := (represented.stored added (by simp)).root_key
  intro root member
  have member' := permutation.mem_iff.mp member
  simp only [List.mem_cons] at member'
  by_cases empty : state.minimum < 0
  · have noPending := represented.pending_empty.mp empty
    simp only [noPending, List.not_mem_nil, or_false] at member'
    subst root
    simp [Snapshot.addRoot, empty, key]
  · by_cases better : state.keys added.vertex < state.keys state.minimum
    · change state.keys (if state.minimum < 0 then added.vertex else
        if state.keys added.vertex < state.keys state.minimum then added.vertex else state.minimum) ≤ root.key
      rw [if_neg empty, if_pos better, key]
      rcases member' with rfl | member'
      · exact Int.le_refl _
      · have previous := least root member'
        omega
    · change state.keys (if state.minimum < 0 then added.vertex else
        if state.keys added.vertex < state.keys state.minimum then added.vertex else state.minimum) ≤ root.key
      rw [if_neg empty, if_neg better]
      rcases member' with rfl | member'
      · omega
      · exact least root member'

def Snapshot.rebuildAt (state : Snapshot) (degree : Int) : Snapshot :=
  let root := state.table degree
  let cleared := {state with table := Rings.write state.table degree (-1)}
  if root < 0 then cleared else cleared.addRoot root

/-- A finite reconstruction follows the same degree-by-degree table traversal
    as the source; counts are insertions and root-key comparisons. -/
inductive BucketRebuild (maximum : Int) : Snapshot → Int → Snapshot → Nat → Nat → Prop where
  | done (state : Snapshot) (degree : Int) (past : maximum < degree) :
      BucketRebuild maximum state degree state 0 0
  | skip {state after : Snapshot} {degree : Int} {insertions comparisons : Nat}
      (inside : degree ≤ maximum) (empty : state.table degree < 0)
      (rest : BucketRebuild maximum (state.rebuildAt degree) (degree + 1) after insertions comparisons) :
      BucketRebuild maximum state degree after insertions comparisons
  | insert {state after : Snapshot} {degree : Int} {insertions comparisons : Nat}
      (inside : degree ≤ maximum) (occupied : 0 ≤ state.table degree)
      (rest : BucketRebuild maximum (state.rebuildAt degree) (degree + 1) after insertions comparisons) :
      BucketRebuild maximum state degree after (insertions + 1)
        (comparisons + if state.minimum < 0 then 0 else 1)


/-- One table scan either leaves the forest alone or moves exactly its selected
    detached tree into the pending root ring. -/
theorem SplitRepresented.rebuild_step {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (buckets : Buckets state detached)
    (least : PendingLeast state pending) (degree : Int) :
    ∃ afterPending afterDetached,
      SplitRepresented (state.rebuildAt degree) afterPending afterDetached ∧
      Buckets (state.rebuildAt degree) afterDetached ∧
      PendingLeast (state.rebuildAt degree) afterPending ∧
      (afterPending ++ afterDetached).Perm (pending ++ detached) ∧
      afterDetached.length + (if state.table degree < 0 then 0 else 1) = detached.length := by
  by_cases empty : state.table degree < 0
  · let cleared : Snapshot := {state with table := Rings.write state.table degree (-1)}
    have unchanged : Buckets cleared detached := by
      refine ⟨buckets.unique, ?_, ?_, buckets.nonnegative⟩
      · intro root member
        have read := buckets.read root member
        have positive := buckets.nonnegative root member
        have different : (root.degree : Int) ≠ degree := by intro same; rw [same] at read; omega
        simpa only [cleared, Rings.write, if_neg different] using read
      · intro index positive
        change 0 ≤ Rings.write state.table degree (-1) index at positive
        have different : index ≠ degree := by intro same; simp [Rings.write, same] at positive
        rw [Rings.write, if_neg different] at positive
        obtain ⟨root, member, same, read⟩ := buckets.complete index positive
        exact ⟨root, member, same, by simpa only [cleared, Rings.write, if_neg different] using read⟩
    refine ⟨pending, detached, ?_, ?_, ?_, List.Perm.refl _, by simp [empty]⟩
    · simpa only [Snapshot.rebuildAt, if_pos empty] using represented.table_write degree (-1)
    · simpa only [Snapshot.rebuildAt, if_pos empty] using unchanged
    · simpa only [Snapshot.rebuildAt, if_pos empty] using least
  · have occupied : 0 ≤ state.table degree := by omega
    obtain ⟨root, member, readDegree, readVertex⟩ := buckets.complete degree occupied
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    let rest := back ++ front
    have rearranged : (root :: rest).Perm detached := by
      rw [located]
      simpa only [rest, List.cons_append] using
        (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
    have prepared := (represented.perm_detached rearranged).table_write degree (-1)
    have table := (buckets.perm rearranged).remove_head
    rw [readDegree] at table
    obtain ⟨afterPending, added, permutation⟩ := prepared.add_detached
    have afterLeast := prepared.add_detached_least least permutation
    have effect : state.rebuildAt degree =
        ({state with table := Rings.write state.table degree (-1)} : Snapshot).addRoot root.vertex := by
      simp only [Snapshot.rebuildAt, if_neg empty, readVertex]
    refine ⟨afterPending, rest, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [effect] using added
    · rw [effect]
      exact table.congr rfl
    · simpa only [effect] using afterLeast
    · have moved : (afterPending ++ rest).Perm (pending ++ root :: rest) := by
        apply (permutation.append_right rest).trans
        simpa only [List.cons_append] using
          (List.perm_middle (a := root) (l₁ := pending) (l₂ := rest)).symm
      exact moved.trans (rearranged.append_left pending)
    · have length := rearranged.length_eq
      simp only [List.length_cons] at length
      simp only [if_neg empty]
      omega


@[simp] theorem Snapshot.rebuildAt_table (state : Snapshot) (degree : Int) :
    (state.rebuildAt degree).table = Rings.write state.table degree (-1) := by
  unfold Snapshot.rebuildAt
  dsimp only
  split <;> rfl

def ClearedBelow (state : Snapshot) (degree : Int) : Prop :=
  ∀ index, index < degree → state.table index < 0

theorem Buckets.cleared_negative {state : Snapshot} {roots : Forest} (buckets : Buckets state roots) :
    ClearedBelow state 0 := by
  intro index negative
  by_cases negativeValue : state.table index < 0
  · exact negativeValue
  have nonnegative : 0 ≤ state.table index := by omega
  obtain ⟨root, _, degree, _⟩ := buckets.complete index nonnegative
  omega

theorem rebuild_scratch_bound (state : Snapshot) (degree maximum : Int) (bound : ScratchBound state maximum) :
    ScratchBound (state.rebuildAt degree) maximum := by
  intro index above
  rw [Snapshot.rebuildAt_table]
  unfold Rings.write
  split
  · omega
  · exact bound index above

theorem rebuild_cleared (state : Snapshot) (degree : Int) (cleared : ClearedBelow state degree) :
    ClearedBelow (state.rebuildAt degree) (degree + 1) := by
  intro index below
  rw [Snapshot.rebuildAt_table]
  unfold Rings.write
  split
  · omega
  · exact cleared index (by omega)

theorem SplitRepresented.finish {state : Snapshot} {pending : Forest}
    (represented : SplitRepresented state pending []) (least : PendingLeast state pending)
    (scratch : ∀ degree, state.table degree < 0) : Represented state pending := by
  refine ⟨by simpa using represented.valid, represented.pendingRing, ?_, ?_, ?_, ?_, ?_, scratch⟩
  · intro root member
    exact represented.stored root (by simpa using member)
  · simpa using represented.nonnegative
  · simpa [Forest.Has] using represented.presence
  · simpa using represented.size
  · rcases represented.cursor with empty | ⟨root, member, pointer⟩
    · exact Or.inl empty
    · refine Or.inr ⟨root, member, pointer, ?_⟩
      have key := (represented.stored root (by simpa using member)).root_key
      intro other inside
      have bound := least other inside
      rw [pointer, key] at bound
      exact bound

/-- The entire table reconstruction terminates over a finite interval. It
    preserves every entry, clears scratch storage, and makes at most one key
    comparison per moved root. -/
theorem rebuild_interval (state : Snapshot) (pending detached : Forest) (degree maximum : Int)
    (represented : SplitRepresented state pending detached) (buckets : Buckets state detached)
    (least : PendingLeast state pending) (bound : ScratchBound state maximum)
    (cleared : ClearedBelow state degree) :
    ∃ after finalPending insertions comparisons,
      BucketRebuild maximum state degree after insertions comparisons ∧
      Represented after finalPending ∧ finalPending.Perm (pending ++ detached) ∧
      insertions = detached.length ∧ comparisons ≤ insertions := by
  have terminate : ∀ fuel : Nat, ∀ before pending detached index,
      (maximum + 1 - index).toNat = fuel → SplitRepresented before pending detached →
      Buckets before detached → PendingLeast before pending → ScratchBound before maximum →
      ClearedBelow before index →
      ∃ after finalPending insertions comparisons,
        BucketRebuild maximum before index after insertions comparisons ∧
        Represented after finalPending ∧ finalPending.Perm (pending ++ detached) ∧
        insertions = detached.length ∧ comparisons ≤ insertions := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro before pending detached index measure valid table minimum bounded cleared
      by_cases done : maximum < index
      · have scratch : ∀ i, before.table i < 0 := by
          intro i
          by_cases below : i < index
          · exact cleared i below
          · exact bounded i (by omega)
        have noDetached : detached = [] := by
          cases detached with
          | nil => rfl
          | cons root tail =>
            have read := table.read root (by simp)
            have positive := table.nonnegative root (by simp)
            have negative := scratch root.degree
            omega
        subst detached
        exact ⟨before, pending, 0, 0, .done _ _ done, valid.finish minimum scratch,
          by simp, rfl, Nat.zero_le _⟩
      have inside : index ≤ maximum := by omega
      have smaller : (maximum + 1 - (index + 1)).toNat < fuel := by omega
      obtain ⟨nextPending, nextDetached, nextValid, nextTable, nextLeast, permutation, count⟩ :=
        valid.rebuild_step table minimum index
      obtain ⟨after, finalPending, insertions, comparisons, rest, finalValid, contents, moved, charged⟩ :=
        ih _ smaller (before.rebuildAt index) nextPending nextDetached (index + 1) rfl
          nextValid nextTable nextLeast (rebuild_scratch_bound _ _ _ bounded)
          (rebuild_cleared _ _ cleared)
      by_cases empty : before.table index < 0
      · refine ⟨after, finalPending, insertions, comparisons, .skip inside empty rest,
          finalValid, contents.trans permutation, ?_, charged⟩
        simp only [if_pos empty, Nat.add_zero] at count
        omega
      · refine ⟨after, finalPending, insertions + 1,
          comparisons + (if before.minimum < 0 then 0 else 1), .insert inside (by omega) rest,
          finalValid, contents.trans permutation, ?_, ?_⟩
        · simp only [if_neg empty] at count
          omega
        · split <;> omega
  exact terminate _ state pending detached degree rfl represented buckets least bound cleared

/-- Starting from the consolidated buckets produces a complete represented
    heap with distinct root degrees and the same roots, hence the same entries. -/
theorem rebuild_complete (state : Snapshot) (detached : Forest) (maximum : Int)
    (represented : SplitRepresented state [] detached) (buckets : Buckets state detached)
    (bound : ScratchBound state maximum) :
    ∃ after forest comparisons,
      BucketRebuild maximum state 0 after detached.length comparisons ∧
      Represented after forest ∧ forest.Perm detached ∧
      (forest.map Node.degree).Nodup ∧ comparisons ≤ forest.length := by
  obtain ⟨after, forest, insertions, comparisons, execution, ready, contents, count, charged⟩ :=
    rebuild_interval state [] detached 0 maximum represented buckets (by simp [PendingLeast])
      bound buckets.cleared_negative
  simp only [List.nil_append] at contents
  subst insertions
  exact ⟨after, forest, comparisons, execution, ready, contents,
    (contents.map Node.degree).nodup_iff.mpr buckets.unique, contents.length_eq ▸ charged⟩


/-- Occupied buckets lie within the recorded maximum degree. -/
theorem Buckets.within_scratch_bound {state : Snapshot} {roots : Forest} {maximum : Int}
    (buckets : Buckets state roots) (bound : ScratchBound state maximum)
    (root : Node) (member : root ∈ roots) : root.degree ≤ maximum.toNat := by
  have read := buckets.read root member
  have positive := buckets.nonnegative root member
  have degree : (root.degree : Int) ≤ maximum := by
    by_cases above : maximum < root.degree
    · have negative := bound root.degree above
      omega
    · omega
  omega

/-- Distinct degrees bound the number of roots reconnected during rebuild. -/
theorem Buckets.roots_bound {state : Snapshot} {roots : Forest} {maximum : Int}
    (buckets : Buckets state roots) (bound : ScratchBound state maximum) :
    roots.length ≤ maximum.toNat + 1 := by
  have count := distinct_degrees_bound (roots.map Node.degree) maximum.toNat buckets.unique
    (by
      intro degree member
      obtain ⟨root, inside, same⟩ := List.mem_map.mp member
      rw [← same]
      exact buckets.within_scratch_bound bound root inside)
  simpa only [List.length_map] using count

end Algo2Lean.Fibonacci
