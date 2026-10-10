import Algo2LeanLib.UnionFind
import Algo2LeanLib.Ackermann

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Inverse-Ackermann amortized analysis for union by rank and full path compression.

The Ackermann hierarchy and its least positive inverse are defined and proved
in `Algo2LeanLib.Ackermann`. This module uses the rank/level/iteration potential
argument of Cormen, Leiserson, Rivest, and Stein, Introduction to Algorithms,
second edition, §21.4. All definitions and proofs below are independent of
compiled programs and their heap representation.

A positive-rank nonroot records the largest Ackermann level below its parent's
rank and the number of iterations reached within that level. Its credit is
`alpha(n) * rank - (level * rank + iterations)`; a root has `alpha(n) * rank`
credit. A rank-zero node has zero credit. The global potential sums these
nonnegative credits over the fixed universe.

Path compression increases a node's hierarchy progress whenever its old level
occurs again later on the path. All but at most one rank-zero node and one node
per level therefore pay for their own traversed edge. A rank link can increase
credit only at the winning root, by at most `alpha(n)`. Scaling the potential
by two pays for both the find and compression events in the source cost model.

The reusable local results are `find_amortized` and `union_amortized`.
`Operations.from_initial` telescopes their bounds across arbitrary finite
operation sequences; `Operations.total_cost` includes initialization and gives
`n + 1 + 13 * (finds + unions) * alpha(n)`. The logarithmic worst-case bound
for an individual operation remains available from `Algo2LeanLib.UnionFind`.
-/

namespace Algo2Lean.UnionFind

/-- Redirect a traversed parent path to its representative, on recursive return. -/
def compressPath {n : Nat} (state : State n) (vertex : Fin n) : Nat → State n
  | 0 => state
  | steps + 1 => compress (compressPath state (state.parent vertex) steps) vertex

@[simp] theorem compressPath_representative {n : Nat} (state : State n) (vertex : Fin n)
    (steps : Nat) : (compressPath state vertex steps).representative = state.representative := by
  induction steps generalizing vertex with
  | zero => rfl
  | succ steps ih => exact ih (state.parent vertex)

@[simp] theorem compressPath_rank {n : Nat} (state : State n) (vertex : Fin n)
    (steps : Nat) : (compressPath state vertex steps).rank = state.rank := by
  induction steps generalizing vertex with
  | zero => rfl
  | succ steps ih => exact ih (state.parent vertex)

@[simp] theorem compressPath_mass {n : Nat} (state : State n) (vertex : Fin n)
    (steps : Nat) : (compressPath state vertex steps).mass = state.mass := by
  induction steps generalizing vertex with
  | zero => rfl
  | succ steps ih => exact ih (state.parent vertex)

/-- The structural invariant is preserved by every finite sequence of compression writes. -/
theorem compressPath_valid {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) (steps : Nat) : Valid (compressPath state vertex steps) := by
  induction steps generalizing vertex with
  | zero => exact valid
  | succ steps ih => exact compress_valid (ih (state.parent vertex)) vertex

/-- Largest successful natural index within a finite search bound, defaulting to zero. -/
def boundedMax (test : Nat → Bool) : Nat → Nat
  | 0 => 0
  | bound + 1 => if test (bound + 1) then bound + 1 else boundedMax test bound

theorem boundedMax_le (test : Nat → Bool) (bound : Nat) : boundedMax test bound ≤ bound := by
  induction bound with
  | zero => exact Nat.le_refl 0
  | succ bound ih => simp only [boundedMax]; split <;> omega

theorem boundedMax_spec (test : Nat → Bool) (bound : Nat) (zero : test 0 = true) :
    test (boundedMax test bound) = true := by
  induction bound with
  | zero => exact zero
  | succ bound ih => simp only [boundedMax]; split <;> simp_all

theorem le_boundedMax (test : Nat → Bool) (bound index : Nat)
    (within : index ≤ bound) (successful : test index = true) : index ≤ boundedMax test bound := by
  induction bound with
  | zero => omega
  | succ bound ih =>
    simp only [boundedMax]
    split
    · omega
    · rename_i last
      have smaller : index ≤ bound := by
        by_cases smaller : index ≤ bound
        · exact smaller
        · have equal : index = bound + 1 := by omega
          subst index
          exact False.elim (last successful)
      exact ih smaller

theorem boundedMax_upper (test : Nat → Bool) (bound index : Nat)
    (within : index ≤ bound) (above : boundedMax test bound < index) : test index = false := by
  cases success : test index
  · rfl
  · have := le_boundedMax test bound index within success
    omega

/-- Pointwise inequalities lift to sums over the fixed universe. -/
theorem total_mono {n : Nat} {first second : Fin n → Nat}
    (bounded : ∀ vertex, first vertex ≤ second vertex) : total first ≤ total second := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    have atZero := bounded 0
    have atRest := ih (fun vertex => bounded vertex.succ)
    simp only [total]
    omega

/-- A pointwise increase confined to one vertex bounds the total increase. -/
theorem total_single_increase {n : Nat} {first second : Fin n → Nat}
    (target : Fin n) (amount : Nat)
    (atTarget : second target ≤ first target + amount)
    (elsewhere : ∀ vertex, vertex ≠ target → second vertex ≤ first vertex) :
    total second ≤ total first + amount := by
  have bounded : total second ≤ total (update first target (first target + amount)) := by
    apply total_mono
    intro vertex
    by_cases same : vertex = target
    · subst vertex; simpa using atTarget
    · simpa [update, same] using elsewhere vertex same
  have replacement := total_update first target (first target + amount)
  omega

/-- Every stored rank is bounded by the fixed universe size. -/
theorem rank_le_size {n : Nat} {state : State n} (valid : Valid state) (vertex : Fin n) :
    state.rank vertex ≤ n :=
  Nat.le_trans (rank_le_representative valid vertex)
    (Nat.le_trans (root_rank_le_log valid _ (valid.representative_root vertex)) (Nat.log2_le_self n))

/-- Compression of higher-ranked vertices leaves a lower-ranked vertex untouched. -/
theorem compressPath_parent_below {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps)
    (other : Fin n) (lower : state.rank other < state.rank vertex) :
    (compressPath state vertex steps).parent other = state.parent other := by
  induction path with
  | root vertex fixed => rfl
  | step vertex root steps moving tail ih =>
    have nextLower : state.rank other < state.rank (state.parent vertex) :=
      Nat.lt_trans lower (valid.parent_rank vertex moving)
    have different : other ≠ vertex := by intro same; subst other; omega
    simpa [compressPath, compress, update, different] using ih nextLower

open Algo2Lean.Ackermann

noncomputable section

/-- Highest Ackermann level reached by a positive rank's parent rank. -/
def level (size rank parentRank : Nat) : Nat :=
  boundedMax (fun index => decide (ack index rank ≤ parentRank)) (alpha size)

/-- Number of iterations at the node's current Ackermann level. -/
def iterations (size rank parentRank : Nat) : Nat :=
  boundedMax (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1)

theorem level_spec {size rank parentRank : Nat} (rising : rank < parentRank) :
    ack (level size rank parentRank) rank ≤ parentRank := by
  have successful := boundedMax_spec (fun index => decide (ack index rank ≤ parentRank))
    (alpha size) (by simp; omega)
  simpa [level] using successful

theorem level_lt_alpha {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    level size rank parentRank < alpha size := by
  have atLevel := level_spec (size := size) rising
  have upper := boundedMax_le (fun index => decide (ack index rank ≤ parentRank)) (alpha size)
  have beyond := ack_alpha_gt size
  have monotone := ack_mono_right (alpha size) (show 1 ≤ rank by omega)
  change level size rank parentRank ≤ alpha size at upper
  by_cases same : level size rank parentRank = alpha size
  · rw [same] at atLevel
    omega
  · omega

theorem level_next_gt {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    parentRank < ack (level size rank parentRank + 1) rank := by
  have within := level_lt_alpha positive rising bounded
  have failure := boundedMax_upper (fun index => decide (ack index rank ≤ parentRank))
    (alpha size) (level size rank parentRank + 1) (by omega) (by change level _ _ _ < _; omega)
  simpa using failure

theorem iterations_spec {size rank parentRank : Nat} (rising : rank < parentRank) :
    iterate (ack (level size rank parentRank)) (iterations size rank parentRank) rank ≤ parentRank := by
  have successful := boundedMax_spec
    (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1) (by simp; omega)
  simpa [iterations] using successful

theorem iterations_pos {size rank parentRank : Nat} (rising : rank < parentRank) :
    0 < iterations size rank parentRank := by
  have first := level_spec (size := size) rising
  have success := le_boundedMax
    (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1) 1 (by omega) (by simpa using first)
  change 1 ≤ iterations size rank parentRank at success
  omega

theorem iterations_le_rank {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    iterations size rank parentRank ≤ rank := by
  have successful := iterations_spec (size := size) rising
  have nextLevel := level_next_gt positive rising bounded
  have upper := boundedMax_le
    (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1)
  change iterations size rank parentRank ≤ rank + 1 at upper
  by_cases same : iterations size rank parentRank = rank + 1
  · rw [same, ← ack_succ] at successful
    omega
  · omega

theorem level_mono {size rank before after : Nat} (rising : rank < before) (grows : before ≤ after) :
    level size rank before ≤ level size rank after := by
  apply le_boundedMax
  · exact boundedMax_le _ _
  · have successful := level_spec (size := size) rising
    simp only [decide_eq_true_eq]
    omega

theorem iterations_mono {size rank before after : Nat} (rising : rank < before)
    (grows : before ≤ after) (sameLevel : level size rank before = level size rank after) :
    iterations size rank before ≤ iterations size rank after := by
  apply le_boundedMax
  · exact boundedMax_le _ _
  · have successful := iterations_spec (size := size) rising
    rw [sameLevel] at successful
    simp only [decide_eq_true_eq]
    omega

/-- Progress within the hierarchy: increasing the level outweighs resetting its iteration. -/
def progress (size rank parentRank : Nat) : Nat :=
  level size rank parentRank * rank + iterations size rank parentRank

theorem progress_le {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    progress size rank parentRank ≤ alpha size * rank := by
  have levels := level_lt_alpha positive rising bounded
  have counts := iterations_le_rank positive rising bounded
  have product := Nat.mul_le_mul_right rank (show level size rank parentRank + 1 ≤ alpha size by omega)
  simp only [Nat.add_mul, Nat.one_mul] at product
  unfold progress
  omega

theorem progress_mono {size rank before after : Nat} (positive : 0 < rank)
    (rising : rank < before) (grows : before ≤ after) (bounded : after ≤ size) :
    progress size rank before ≤ progress size rank after := by
  have levels := level_mono (size := size) rising grows
  by_cases same : level size rank before = level size rank after
  · have counts := iterations_mono rising grows same
    simp only [progress, same]
    omega
  · have counts := iterations_le_rank positive rising (by omega : before ≤ size)
    have product := Nat.mul_le_mul_right rank
      (show level size rank before + 1 ≤ level size rank after by omega)
    simp only [Nat.add_mul, Nat.one_mul] at product
    unfold progress
    omega

theorem progress_strict {size rank before after : Nat} (positive : 0 < rank)
    (rising : rank < before) (grows : before ≤ after) (bounded : after ≤ size)
    (advanced : iterate (ack (level size rank before)) (iterations size rank before + 1) rank ≤ after) :
    progress size rank before < progress size rank after := by
  have levels := level_mono (size := size) rising grows
  by_cases same : level size rank before = level size rank after
  · have within := iterations_le_rank positive rising (by omega : before ≤ size)
    have counts := le_boundedMax
      (fun count => decide (iterate (ack (level size rank after)) count rank ≤ after))
      (rank + 1) (iterations size rank before + 1) (by omega) (by simpa [same] using advanced)
    change iterations size rank before + 1 ≤ iterations size rank after at counts
    simp only [progress, same]
    omega
  · have counts := iterations_le_rank positive rising (by omega : before ≤ size)
    have positiveCount := iterations_pos (size := size) (by omega : rank < after)
    have product := Nat.mul_le_mul_right rank
      (show level size rank before + 1 ≤ level size rank after by omega)
    simp only [Nat.add_mul, Nat.one_mul] at product
    unfold progress
    omega

/-- CLRS credit: roots own alpha times rank; a nonroot spends credit on its level and iteration. -/
def credit (size rank parentRank : Nat) : Nat :=
  if rank = 0 ∨ parentRank ≤ rank then alpha size * rank
  else alpha size * rank - progress size rank parentRank

@[simp] theorem credit_zero (size parentRank : Nat) : credit size 0 parentRank = 0 := by
  simp [credit]

@[simp] theorem credit_root (size rank : Nat) : credit size rank rank = alpha size * rank := by
  simp [credit]

theorem credit_le (size rank parentRank : Nat) : credit size rank parentRank ≤ alpha size * rank := by
  unfold credit
  split <;> omega

theorem credit_mono {size rank before after : Nat} (rising : rank < before)
    (grows : before ≤ after) (bounded : after ≤ size) : credit size rank after ≤ credit size rank before := by
  by_cases zero : rank = 0
  · simp [zero]
  · have progress := progress_mono (by omega : 0 < rank) rising grows bounded
    simp only [credit, zero, false_or, if_neg (show ¬ before ≤ rank by omega),
      if_neg (show ¬ after ≤ rank by omega)]
    omega

theorem credit_strict {size rank before after : Nat} (positive : 0 < rank)
    (rising : rank < before) (grows : before ≤ after) (bounded : after ≤ size)
    (advanced : iterate (ack (level size rank before)) (iterations size rank before + 1) rank ≤ after) :
    credit size rank after + 1 ≤ credit size rank before := by
  have progressRises := progress_strict positive rising grows bounded advanced
  have progressBound := progress_le positive (by omega : rank < after) bounded
  simp only [credit, show ¬ rank = 0 by omega, false_or,
    if_neg (show ¬ before ≤ rank by omega), if_neg (show ¬ after ≤ rank by omega)]
  omega

/-- Sum of the nonnegative node credits in the current finite universe. -/
def potential {n : Nat} (state : State n) : Nat :=
  total (fun vertex => credit n (state.rank vertex) (state.rank (state.parent vertex)))

@[simp] theorem initial_potential (n : Nat) : potential (initial n) = 0 := by
  unfold potential
  have zeros : ∀ n, total (n := n) (fun _ => 0) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [total, ih]
  simpa [initial] using zeros n

/-- One compression write changes only the credit at the written vertex. -/
theorem compress_potential_balance {n : Nat} (state : State n) (vertex : Fin n) :
    potential (compress state vertex) + credit n (state.rank vertex) (state.rank (state.parent vertex)) =
      potential state + credit n (state.rank vertex) (state.rank (state.representative vertex)) := by
  have entries : (fun other => credit n ((compress state vertex).rank other)
      ((compress state vertex).rank ((compress state vertex).parent other))) =
      update (fun other => credit n (state.rank other) (state.rank (state.parent other))) vertex
        (credit n (state.rank vertex) (state.rank (state.representative vertex))) := by
    funext other
    by_cases same : other = vertex <;> simp [compress, update, same]
  unfold potential
  rw [entries]
  exact total_update _ vertex _

/-- Redirecting one vertex to its root never increases the potential. -/
theorem compress_potential_le {n : Nat} {state : State n} (valid : Valid state) (vertex : Fin n) :
    potential (compress state vertex) ≤ potential state := by
  have balance := compress_potential_balance state vertex
  by_cases fixed : state.parent vertex = vertex
  · rw [fixed, valid.root_representative vertex fixed] at balance
    omega
  · have bound := rank_le_representative valid (state.parent vertex)
    rw [valid.parent_representative vertex] at bound
    have decrease := credit_mono (valid.parent_rank vertex fixed) bound
      (rank_le_size valid (state.representative vertex))
    omega

/-- During recursive return, the tail's compression has not changed this vertex's old parent. -/
theorem compressPath_potential_balance {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (moving : state.parent vertex ≠ vertex)
    (tail : Find state (state.parent vertex) root steps) :
    potential (compressPath state vertex (steps + 1)) +
        credit n (state.rank vertex) (state.rank (state.parent vertex)) =
      potential (compressPath state (state.parent vertex) steps) +
        credit n (state.rank vertex) (state.rank root) := by
  have balance := compress_potential_balance (compressPath state (state.parent vertex) steps) vertex
  have unchanged := compressPath_parent_below valid tail vertex (valid.parent_rank vertex moving)
  have rootCorrect := (find_correct valid (Find.step vertex root steps moving tail)).1
  simpa only [compressPath, compressPath_rank, compressPath_representative, unchanged, ← rootCorrect] using balance

/-- A rank link can increase the global potential only at its winning root,
    and only by one alpha-sized rank increment. -/
theorem link_potential {n : Nat} {state : State n} (valid : Valid state)
    (loser winner : Fin n) (different : loser ≠ winner)
    (loserRoot : state.parent loser = loser) (winnerRoot : state.parent winner = winner)
    (ordered : state.rank loser ≤ state.rank winner) :
    potential (link state loser winner) ≤ potential state + alpha n := by
  have linkedValid := link_valid valid loser winner different loserRoot winnerRoot ordered
  have winnerFixed : (link state loser winner).parent winner = winner := by
    simp [link, update, different.symm, winnerRoot]
  unfold potential
  apply total_single_increase winner (alpha n)
  · rw [winnerFixed, winnerRoot, credit_root, credit_root]
    have rise : (link state loser winner).rank winner ≤ state.rank winner + 1 := by
      simp only [link, update_same]
      split <;> omega
    have scaled := Nat.mul_le_mul_left (alpha n) rise
    simpa only [Nat.mul_add, Nat.mul_one] using scaled
  · intro vertex notWinner
    have sameRank : (link state loser winner).rank vertex = state.rank vertex := by
      simp [link, update, notWinner]
    rw [sameRank]
    by_cases same : vertex = loser
    · subst vertex
      rw [loserRoot, credit_root]
      exact credit_le _ _ _
    · have sameParent : (link state loser winner).parent vertex = state.parent vertex := by
        simp [link, update, same]
      rw [sameParent]
      by_cases fixed : state.parent vertex = vertex
      · rw [fixed, sameRank]
        exact Nat.le_refl _
      · apply credit_mono (valid.parent_rank vertex fixed)
        · exact link_rank_ge state loser winner (state.parent vertex)
        · exact rank_le_size linkedValid (state.parent vertex)

/-- Choosing the rank-ordered orientation does not affect the alpha-sized link budget. -/
theorem union_potential {n : Nat} {state : State n} (valid : Valid state) (first second : Fin n) :
    potential (union state first second) ≤ potential state + alpha n := by
  simp only [union]
  split
  · omega
  · rename_i different
    split
    · rename_i ordered
      exact link_potential valid _ _ different (valid.representative_root first)
        (valid.representative_root second) (by omega)
    · rename_i ordered
      exact link_potential valid _ _ (Ne.symm different) (valid.representative_root second)
        (valid.representative_root first) (by omega)

/-- Number of distinct path levels, counted in the finite range below alpha. -/
def levelCount (size : Nat) (levels : List Nat) : Nat :=
  total (fun index : Fin (alpha size) => if index.val ∈ levels then 1 else 0)

theorem levelCount_le (size : Nat) (levels : List Nat) : levelCount size levels ≤ alpha size := by
  have bounded : levelCount size levels ≤ total (n := alpha size) (fun _ => 1) := by
    apply total_mono
    intro index
    split <;> omega
  simpa [total_ones] using bounded

@[simp] theorem levelCount_nil (size : Nat) : levelCount size [] = 0 := by
  have zeros : ∀ n, total (n := n) (fun _ => 0) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [total, ih]
  simpa [levelCount] using zeros (alpha size)

theorem levelCount_cons_present (size level : Nat) (levels : List Nat) (present : level ∈ levels) :
    levelCount size (level :: levels) = levelCount size levels := by
  unfold levelCount
  congr 1
  funext index
  by_cases same : index.val = level
  · simp [List.mem_cons, same, present]
  · simp [List.mem_cons, same]

theorem levelCount_cons_fresh (size level : Nat) (levels : List Nat)
    (within : level < alpha size) (fresh : level ∉ levels) :
    levelCount size (level :: levels) = levelCount size levels + 1 := by
  let index : Fin (alpha size) := ⟨level, within⟩
  have entries : (fun other : Fin (alpha size) => if other.val ∈ level :: levels then 1 else 0) =
      update (fun other : Fin (alpha size) => if other.val ∈ levels then 1 else 0) index 1 := by
    funext other
    by_cases same : other = index
    · subst other
      simp [index, update]
    · have different : other.val ≠ level := by
        intro equal
        exact same (Fin.ext equal)
      simp [List.mem_cons, update, same, different]
  unfold levelCount
  rw [entries]
  have replacement := total_update (fun other : Fin (alpha size) => if other.val ∈ levels then 1 else 0) index 1
  simpa [index, fresh] using replacement

/-- The old levels of positive-rank nonroot vertices on a given traversal. -/
def pathLevels {n : Nat} (state : State n) (vertex : Fin n) : Nat → List Nat
  | 0 => []
  | steps + 1 =>
      let tail := pathLevels state (state.parent vertex) steps
      if state.rank vertex = 0 then tail
      else level n (state.rank vertex) (state.rank (state.parent vertex)) :: tail

/-- A listed path level has a positive-rank witness between the start and the root. -/
theorem pathLevels_member {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps key : Nat} (path : Find state vertex root steps)
    (member : key ∈ pathLevels state vertex steps) :
    ∃ rank parentRank, 0 < rank ∧ rank < parentRank ∧ state.rank vertex ≤ rank ∧
      parentRank ≤ state.rank root ∧ level n rank parentRank = key := by
  induction path with
  | root vertex fixed => simp [pathLevels] at member
  | step vertex root steps moving tail ih =>
    have rising := valid.parent_rank vertex moving
    have upper := (find_correct valid tail).2.2
    simp only [pathLevels] at member
    split at member
    · obtain ⟨rank, parentRank, positive, increasing, lower, upper, same⟩ := ih member
      exact ⟨rank, parentRank, positive, increasing, by omega, upper, same⟩
    · rename_i positive
      rcases List.mem_cons.mp member with same | later
      · exact ⟨_, _, by omega, rising, Nat.le_refl _, by omega, same.symm⟩
      · obtain ⟨rank, parentRank, positive, increasing, lower, upper, same⟩ := ih later
        exact ⟨rank, parentRank, positive, increasing, by omega, upper, same⟩

/-- A repeated old level forces one additional iteration after both nodes point to the root. -/
theorem repeated_level_advance {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (moving : state.parent vertex ≠ vertex)
    (tail : Find state (state.parent vertex) root steps)
    (repeated : level n (state.rank vertex) (state.rank (state.parent vertex)) ∈
      pathLevels state (state.parent vertex) steps) :
    iterate (ack (level n (state.rank vertex) (state.rank (state.parent vertex))))
      (iterations n (state.rank vertex) (state.rank (state.parent vertex)) + 1)
      (state.rank vertex) ≤ state.rank root := by
  obtain ⟨rank, parentRank, positive, increasing, lower, upper, sameLevel⟩ :=
    pathLevels_member valid tail repeated
  have first := iterations_spec (size := n) (valid.parent_rank vertex moving)
  have second := level_spec (size := n) increasing
  rw [sameLevel] at second
  rw [iterate_succ]
  exact Nat.le_trans (ack_mono_right _ (Nat.le_trans first lower)) (Nat.le_trans second upper)

/-- All path steps are paid by lost credit except a rank-zero first node and
    the last occurrence of each old Ackermann level. -/
theorem compressPath_amortized_aux {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    steps + potential (compressPath state vertex steps) ≤ potential state +
      levelCount n (pathLevels state vertex steps) + if state.rank vertex = 0 then 1 else 0 := by
  induction path with
  | root vertex fixed => simp [compressPath, pathLevels]
  | step vertex root steps moving tail ih =>
    have rising := valid.parent_rank vertex moving
    have upper := (find_correct valid tail).2.2
    have bounded := rank_le_size valid root
    have balance := compressPath_potential_balance valid moving tail
    have parentPositive : state.rank (state.parent vertex) ≠ 0 := by omega
    simp only [parentPositive, ↓reduceIte, Nat.add_zero] at ih
    by_cases zero : state.rank vertex = 0
    · simp only [zero, credit_zero] at balance
      simp only [pathLevels, zero, ↓reduceIte]
      omega
    · have smaller := credit_mono rising (by omega : state.rank (state.parent vertex) ≤ state.rank root) bounded
      by_cases repeated : level n (state.rank vertex) (state.rank (state.parent vertex)) ∈
          pathLevels state (state.parent vertex) steps
      · have strict := credit_strict (by omega : 0 < state.rank vertex) rising
          (by omega : state.rank (state.parent vertex) ≤ state.rank root) bounded
          (repeated_level_advance valid moving tail repeated)
        simp only [pathLevels, zero, ↓reduceIte, levelCount_cons_present _ _ _ repeated, Nat.add_zero]
        omega
      · have within := level_lt_alpha (by omega : 0 < state.rank vertex) rising
          (rank_le_size valid (state.parent vertex))
        simp only [pathLevels, zero, ↓reduceIte, levelCount_cons_fresh _ _ _ within repeated, Nat.add_zero]
        omega

/-- The pure inverse-Ackermann amortized path-compression bound. -/
theorem compressPath_amortized {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    steps + potential (compressPath state vertex steps) ≤ potential state + alpha n + 1 := by
  have charged := compressPath_amortized_aux valid path
  have levels := levelCount_le n (pathLevels state vertex steps)
  split at charged <;> omega

/-- Scaling credits by two pays one root test plus both events on every nonroot step. -/
theorem find_amortized {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    (2 * steps + 1) + 2 * potential (compressPath state vertex steps) ≤
      2 * potential state + 2 * alpha n + 3 := by
  have charged := compressPath_amortized valid path
  omega

/-- Two compressed finds followed by a rank link have inverse-Ackermann amortized cost. -/
theorem union_amortized {n : Nat} {state : State n} (valid : Valid state)
    {first second firstRoot secondRoot : Fin n} {firstSteps secondSteps : Nat}
    (firstPath : Find state first firstRoot firstSteps)
    (secondPath : Find (compressPath state first firstSteps) second secondRoot secondSteps) :
    (2 * (firstSteps + secondSteps) + 3) +
        2 * potential (union (compressPath (compressPath state first firstSteps) second secondSteps) first second) ≤
      2 * potential state + 6 * alpha n + 7 := by
  have firstBudget := find_amortized valid firstPath
  have middleValid := compressPath_valid valid first firstSteps
  have secondBudget := find_amortized middleValid secondPath
  have finalValid := compressPath_valid middleValid second secondSteps
  have linkBudget := union_potential finalValid first second
  omega

/-- A finite mixed sequence of finds and unions. The last three indices count
    find calls, union calls, and the source events charged by those operations. -/
inductive Operations {n : Nat} : State n → State n → Nat → Nat → Nat → Prop where
  | done (state : State n) : Operations state state 0 0 0
  | find {state final : State n} {vertex root : Fin n} {steps finds unions cost : Nat}
      (path : Find state vertex root steps)
      (rest : Operations (compressPath state vertex steps) final finds unions cost) :
      Operations state final (finds + 1) unions ((2 * steps + 1) + cost)
  | union {state final : State n} {first second firstRoot secondRoot : Fin n}
      {firstSteps secondSteps finds unions cost : Nat}
      (firstPath : Find state first firstRoot firstSteps)
      (secondPath : Find (compressPath state first firstSteps) second secondRoot secondSteps)
      (rest : Operations
        (union (compressPath (compressPath state first firstSteps) second secondSteps) first second)
        final finds unions cost) :
      Operations state final finds (unions + 1) ((2 * (firstSteps + secondSteps) + 3) + cost)

/-- Local potential budgets telescope across an arbitrary mixed operation sequence. -/
theorem Operations.amortized {n : Nat} {before after : State n} {finds unions cost : Nat}
    (operations : Operations before after finds unions cost) (valid : Valid before) :
    Valid after ∧ cost + 2 * potential after ≤ 2 * potential before +
      finds * (2 * alpha n + 3) + unions * (6 * alpha n + 7) := by
  induction operations with
  | done state => exact ⟨valid, by simp⟩
  | find path rest ih =>
    obtain ⟨finalValid, remaining⟩ := ih (compressPath_valid valid _ _)
    have current := find_amortized valid path
    refine ⟨finalValid, ?_⟩
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  | union firstPath secondPath rest ih =>
    obtain ⟨finalValid, remaining⟩ :=
      ih (union_valid (compressPath_valid (compressPath_valid valid _ _) _ _) _ _)
    have current := union_amortized valid firstPath secondPath
    refine ⟨finalValid, ?_⟩
    simp only [Nat.add_mul, Nat.one_mul]
    omega

-- Main result: Running time
/-- Starting with singleton sets, the total cost of any finite sequence is
    bounded by its find and union counts times genuine inverse-Ackermann budgets. -/
theorem Operations.from_initial {n : Nat} {after : State n} {finds unions cost : Nat}
    (operations : Operations (initial n) after finds unions cost) :
    cost ≤ finds * (2 * alpha n + 3) + unions * (6 * alpha n + 7) := by
  have budget := (operations.amortized (initial_valid n)).2
  rw [initial_potential] at budget
  omega

/-- A uniform O(m alpha(n)) bound for m operations, with constructor cost explicit. -/
theorem Operations.total_cost {n : Nat} {after : State n} {finds unions cost : Nat}
    (operations : Operations (initial n) after finds unions cost) :
    (n + 1) + cost ≤ n + 1 + 13 * (finds + unions) * alpha n := by
  have budget := operations.from_initial
  have positive := alpha_pos n
  have findBound : 2 * alpha n + 3 ≤ 13 * alpha n := by omega
  have unionBound : 6 * alpha n + 7 ≤ 13 * alpha n := by omega
  have findsBound := Nat.mul_le_mul_left finds findBound
  have unionsBound := Nat.mul_le_mul_left unions unionBound
  have combined : finds * (13 * alpha n) + unions * (13 * alpha n) =
      13 * (finds + unions) * alpha n := by
    simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm]
  rw [← combined]
  omega

end
end Algo2Lean.UnionFind
