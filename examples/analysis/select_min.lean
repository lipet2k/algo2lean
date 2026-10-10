import SelectMinGeneratedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-!
Linear minimum selection among reachable unsettled vertices, with exact scan cost.
The proof outline is: preserve a prefix minimum, execute one scan, finish the
remaining scans, then use determinism to characterize every completed call.
-/

open Algo2LeanCore Algo2LeanGenerated

namespace SelectMinAnalysis

/-- A vertex is available when unsettled and its tentative distance is finite. -/
def Candidate (distance settled : Seq) (vertex : Int) : Prop :=
  settled vertex = 0 ∧ 0 ≤ distance vertex

instance (distance settled : Seq) (vertex : Int) : Decidable (Candidate distance settled vertex) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The first minimum candidate in `[0, finish)`, or `-1` if none exists. -/
def Minimum (distance settled : Seq) (finish best : Int) : Prop :=
  (best = -1 ∧ ∀ vertex, 0 ≤ vertex → vertex < finish → ¬ Candidate distance settled vertex) ∨
  (0 ≤ best ∧ best < finish ∧ Candidate distance settled best ∧
    ∀ vertex, 0 ≤ vertex → vertex < finish → Candidate distance settled vertex →
      distance best ≤ distance vertex ∧ (distance best = distance vertex → best ≤ vertex))

def choose (distance settled : Seq) (best vertex : Int) : Int :=
  if Candidate distance settled vertex ∧ (best < 0 ∨ distance vertex < distance best)
  then vertex else best

theorem empty_minimum (distance settled : Seq) (finish : Int) (empty : finish ≤ 0) :
    Minimum distance settled finish (-1) := by
  exact Or.inl ⟨rfl, by intro vertex lower upper; omega⟩

theorem extend_minimum (distance settled : Seq) (vertex best : Int)
    (nonnegative : 0 ≤ vertex) (previous : Minimum distance settled vertex best) :
    Minimum distance settled (vertex + 1) (choose distance settled best vertex) := by
  by_cases available : Candidate distance settled vertex
  · by_cases better : best < 0 ∨ distance vertex < distance best
    · simp only [choose, available, better, and_self, ↓reduceIte]
      refine Or.inr ⟨nonnegative, by omega, available, ?_⟩
      intro other lower upper candidate
      by_cases same : other = vertex
      · simp [same]
      · have old : other < vertex := by omega
        rcases previous with ⟨_, none⟩ | ⟨bestNonnegative, bestBefore, bestCandidate, least⟩
        · exact False.elim (none other lower old candidate)
        · have bestLeast := least other lower old candidate
          have strict : distance vertex < distance best := by omega
          exact ⟨by omega, by omega⟩
    · simp only [choose, better, and_false, ↓reduceIte]
      rcases previous with ⟨absent, _⟩ | ⟨bestNonnegative, bestBefore, bestCandidate, least⟩
      · omega
      · refine Or.inr ⟨bestNonnegative, by omega, bestCandidate, ?_⟩
        intro other lower upper candidate
        by_cases same : other = vertex
        · subst other; exact ⟨by omega, by omega⟩
        · exact least other lower (by omega) candidate
  · simp only [choose, available, false_and, ↓reduceIte]
    rcases previous with ⟨absent, none⟩ | ⟨bestNonnegative, bestBefore, bestCandidate, least⟩
    · refine Or.inl ⟨absent, ?_⟩
      intro other lower upper candidate
      by_cases same : other = vertex
      · exact available (same ▸ candidate)
      · exact none other lower (by omega) candidate
    · refine Or.inr ⟨bestNonnegative, by omega, bestCandidate, ?_⟩
      intro other lower upper candidate
      by_cases same : other = vertex
      · exact False.elim (available (same ▸ candidate))
      · exact least other lower (by omega) candidate

theorem minimum_absent_iff (distance settled : Seq) (n result : Int)
    (minimum : Minimum distance settled n result) :
    result = -1 ↔ ∀ vertex, 0 ≤ vertex → vertex < n → ¬ Candidate distance settled vertex := by
  rcases minimum with ⟨absent, none⟩ | ⟨lower, upper, candidate, least⟩
  · exact ⟨fun _ => none, fun _ => absent⟩
  · constructor
    · intro absent; omega
    · intro none; exact False.elim (none result lower upper candidate)

theorem minimum_unique (distance settled : Seq) (n first second : Int)
    (one : Minimum distance settled n first) (two : Minimum distance settled n second) :
    first = second := by
  rcases one with ⟨absent, none⟩ | ⟨lower, upper, candidate, least⟩
  · rcases two with ⟨alsoAbsent, _⟩ | ⟨otherLower, otherUpper, otherCandidate, _⟩
    · omega
    · exact False.elim (none second otherLower otherUpper otherCandidate)
  · rcases two with ⟨absent, none⟩ | ⟨otherLower, otherUpper, otherCandidate, otherLeast⟩
    · exact False.elim (none first lower upper candidate)
    · have forward := least second otherLower otherUpper otherCandidate
      have backward := otherLeast first lower upper candidate
      have tied : distance first = distance second := by omega
      have left := forward.2 tied
      have right := backward.2 tied.symm
      omega

/-- A source-facing description of the local scan state. -/
def AtScan (state : Configuration) (heap : Heap) (distance settled : SeqRef)
    (n vertex best : Int) : Prop :=
  select_min.At.scan state ∧ state.heap = heap ∧
  select_min.Local.distance state = some distance ∧
  select_min.Local.settled state = some settled ∧ select_min.Local.n state = some n ∧
  select_min.Local.i state = some vertex ∧ select_min.Local.best state = some best

theorem scan_exit (state : Configuration) (heap : Heap) (distance settled : SeqRef)
    (n vertex best : Int) (located : AtScan state heap distance settled n vertex best)
    (finished : n ≤ vertex) : select_min.CallFrom state heap best := by
  obtain ⟨named, sameHeap, sameDistance, sameSettled, sameN, sameVertex, sameBest⟩ := located
  unfold select_min.At.scan at named
  split at named <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [select_min.Local.distance, select_min.Local.settled, select_min.Local.n,
    select_min.Local.i, select_min.Local.best] at sameDistance sameSettled sameN sameVertex sameBest
  intro caller
  apply Reaches.prepend (Step.select_min_pc4 _ _ _)
  apply Reaches.prepend (Step.select_min_pc3_false _ _ _ (by simp [sameVertex, sameN]; omega))
  apply Reaches.prepend (Step.select_min_pc2 _ _ _)
  simpa [sameBest] using Reaches.single (Step.select_min_pc1 heap _ caller)

/-- A scan charges one unit, selects the better candidate, and resumes at the
    next vertex. Only this lemma inspects the implementation of the loop body. -/
theorem scan_step (state : Configuration) (heap finalHeap : Heap) (distance settled : SeqRef)
    (n vertex best result : Int) (located : AtScan state heap distance settled n vertex best)
    (distanceAllocated : distance < heap.nextRef) (settledAllocated : settled < heap.nextRef)
    (unfinished : vertex < n)
    (continuation : ∀ next, AtScan next (heap.tick "scans") distance settled n (vertex + 1)
      (choose (heap.read distance) (heap.read settled) best vertex) →
      select_min.CallFrom next finalHeap result) :
    select_min.CallFrom state finalHeap result := by
  obtain ⟨named, sameHeap, sameDistance, sameSettled, sameN, sameVertex, sameBest⟩ := located
  unfold select_min.At.scan at named
  split at named <;> try contradiction
  rename_i currentHeap locals stack
  simp only [Config.heap] at sameHeap
  subst currentHeap
  simp [select_min.Local.distance, select_min.Local.settled, select_min.Local.n,
    select_min.Local.i, select_min.Local.best] at sameDistance sameSettled sameN sameVertex sameBest
  have base : ∀ next : State_select_min,
      next.v0 = distance → next.v1 = settled → next.v2 = n → next.v4 = vertex + 1 →
      next.v3 = choose (heap.read distance) (heap.read settled) best vertex →
      Summary Step (heap.tick "scans") (.fn_select_min 4 next) finalHeap (.fn_select_min result) := by
    intro next distanceEq settledEq nEq vertexEq bestEq
    exact continuation (.active (heap.tick "scans") (.fn_select_min 4 next) [])
      (by simp [AtScan, select_min.At.scan, Config.heap, select_min.Local.distance,
        select_min.Local.settled, select_min.Local.n, select_min.Local.i, select_min.Local.best,
        distanceEq, settledEq, nEq, vertexEq, bestEq])
  intro caller
  apply Reaches.prepend (Step.select_min_pc4 _ _ _)
  apply Reaches.prepend (Step.select_min_pc3_true _ _ _ (by simp [sameVertex, sameN, unfinished]))
  apply Reaches.prepend (Step.select_min_pc11 _ _ _)
  apply Reaches.prepend (Step.select_min_pc10 _ _ _
    (by simp [sameDistance, sameSettled, distanceAllocated, settledAllocated]))
  by_cases available : Candidate (heap.read distance) (heap.read settled) vertex
  · apply Reaches.prepend (Step.select_min_pc9_true _ _ _
      (by simpa [Candidate, sameDistance, sameSettled, sameVertex] using available))
    apply Reaches.prepend (Step.select_min_pc8 _ _ _ (by simp [sameDistance, distanceAllocated]))
    by_cases better : best < 0 ∨ heap.read distance vertex < heap.read distance best
    · apply Reaches.prepend (Step.select_min_pc7_true _ _ _
        (by simpa [sameDistance, sameVertex, sameBest] using better))
      apply Reaches.prepend (Step.select_min_pc6 _ _ _)
      apply Reaches.prepend (Step.select_min_pc5 _ _ _)
      apply base _ _ _ _ _ _ caller <;>
        simp [sameDistance, sameSettled, sameN, sameVertex, choose, available, better]
    · apply Reaches.prepend (Step.select_min_pc7_false _ _ _
        (by simpa [sameDistance, sameVertex, sameBest] using better))
      apply Reaches.prepend (Step.select_min_pc5 _ _ _)
      apply base _ _ _ _ _ _ caller <;>
        simp [sameDistance, sameSettled, sameN, sameVertex, sameBest, choose, available, better]
  · apply Reaches.prepend (Step.select_min_pc9_false _ _ _
      (by simpa [Candidate, sameDistance, sameSettled, sameVertex] using available))
    apply Reaches.prepend (Step.select_min_pc5 _ _ _)
    apply base _ _ _ _ _ _ caller <;>
      simp [sameDistance, sameSettled, sameN, sameVertex, sameBest, choose, available]

/-- The loop proof reuses one local scan rule; its exact cost is the remaining
    number of vertices. All other heap data and counters are preserved. -/
theorem remaining_summary (count : Nat) (heap : Heap) (distance settled : SeqRef)
    (vertex best : Int) (distanceAllocated : distance < heap.nextRef)
    (settledAllocated : settled < heap.nextRef) (nonnegative : 0 ≤ vertex)
    (previous : Minimum (heap.read distance) (heap.read settled) vertex best) :
    ∃ result, Minimum (heap.read distance) (heap.read settled) (vertex + (count : Int)) result ∧
      ∀ state, AtScan state heap distance settled (vertex + (count : Int)) vertex best →
        select_min.CallFrom state (heap.tick "scans" count) result := by
  induction count generalizing heap vertex best with
  | zero =>
    refine ⟨best, by simpa using previous, ?_⟩
    intro state located
    simpa using scan_exit state heap distance settled _ vertex best located (by simp)
  | succ count ih =>
    let nextBest := choose (heap.read distance) (heap.read settled) best vertex
    obtain ⟨result, minimum, continued⟩ := ih (heap.tick "scans") (vertex + 1) nextBest
      (by simpa using distanceAllocated) (by simpa using settledAllocated) (by omega)
      (by simpa [nextBest] using! extend_minimum _ _ vertex best nonnegative previous)
    refine ⟨result, ?_, ?_⟩
    · simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm] using! minimum
    · intro state located
      apply scan_step state heap (heap.tick "scans" (count + 1)) distance settled
        (vertex + ((count + 1 : Nat) : Int)) vertex best result located
        distanceAllocated settledAllocated (by omega)
      intro next nextLocated
      have sameBound : vertex + ((count + 1 : Nat) : Int) = vertex + 1 + (count : Int) := by omega
      rw [sameBound] at nextLocated
      simpa [Heap.tick_add, Nat.add_comm] using continued next nextLocated

/-- Reusable by callers: every finite scan terminates, selects a first minimum,
    and changes only the `scans` clock, by exactly `max(n, 0)` units. -/
theorem selection_summary (heap : Heap) (distance settled : SeqRef) (n : Int)
    (distanceAllocated : distance < heap.nextRef) (settledAllocated : settled < heap.nextRef) :
    ∃ result, Minimum (heap.read distance) (heap.read settled) n result ∧
      select_min.Call heap (distance, settled, n) (heap.tick "scans" n.toNat) result := by
  have enter : ∀ result finalHeap,
      (∀ state, AtScan state heap distance settled n 0 (-1) →
        select_min.CallFrom state finalHeap result) →
      select_min.Call heap (distance, settled, n) finalHeap result := by
    intro result finalHeap continued
    refine ⟨⟨distanceAllocated, settledAllocated⟩, ?_⟩
    intro caller
    apply Reaches.prepend (Step.select_min_pc13 _ _ _)
    apply Reaches.prepend (Step.select_min_pc12 _ _ _)
    exact continued (.active heap (.fn_select_min 4
      { v0 := distance, v1 := settled, v2 := n, v3 := -1, v4 := 0 }) [])
      (by simp [AtScan, select_min.At.scan, Config.heap, select_min.Local.distance,
        select_min.Local.settled, select_min.Local.n, select_min.Local.i, select_min.Local.best]) caller
  by_cases empty : n ≤ 0
  · refine ⟨-1, empty_minimum _ _ n empty, enter _ _ ?_⟩
    intro state located
    simpa [Int.toNat_eq_zero.mpr empty] using scan_exit state heap distance settled n 0 (-1) located empty
  · have nonnegative : 0 ≤ n := by omega
    obtain ⟨result, minimum, continued⟩ := remaining_summary n.toNat heap distance settled 0 (-1)
      distanceAllocated settledAllocated (by omega) (empty_minimum _ _ 0 (by omega))
    simp only [Int.zero_add, Int.toNat_of_nonneg nonnegative] at minimum continued
    exact ⟨result, minimum, enter _ _ continued⟩

theorem transitions_deterministic : Deterministic Step := by
  intro before left right first second
  cases first <;> cases second <;> simp_all

/-- The constructed summary describes every completed execution, including
    calls with existing counters and aliased input sequences. -/
theorem execution_correct (heap finalHeap : Heap) (distance settled : SeqRef) (n result : Int)
    (execution : select_min.Run heap (distance, settled, n) finalHeap result) :
    Minimum (heap.read distance) (heap.read settled) n result ∧
      finalHeap = heap.tick "scans" n.toNat := by
  obtain ⟨expected, minimum, summary⟩ := selection_summary heap distance settled n
    execution.1.1 execution.1.2
  have same := Reaches.eq_of_terminal (step := Step) transitions_deterministic execution.2 summary.2.root
    (by intro next impossible; cases impossible) (by intro next impossible; cases impossible)
  cases same
  exact ⟨minimum, rfl⟩

/-- Only the scan clock changes, including when the initial clocks are nonzero. -/
def scansCosts (n : Int) : Clocks := fun name => if name = "scans" then n.toNat else 0

theorem selection_costs (heap : Heap) (n : Int) :
    Heap.cost heap (heap.tick "scans" n.toNat) = scansCosts n := by
  funext name
  by_cases same : name = "scans"
  · subst name; simp [Heap.cost, Heap.tick, scansCosts]
  · simp [Heap.cost, Heap.tick, scansCosts, same]

/-- No assumptions on distances or settled markers are needed for termination.
    Negative `n` behaves like an empty range and costs zero scans. -/
theorem output_with_cost (distance settled : Seq) (n : Int) :
    ∃ result, Minimum distance settled n result ∧
      select_min.ReturnsWithCost (distance, settled, n) result (scansCosts n) := by
  let heap := (({} : Heap).allocate distance).allocate settled
  have distances : heap.read 0 = distance := by
    funext i; simp [heap, Heap.read, Heap.allocate]
  have markers : heap.read 1 = settled := by
    funext i; simp [heap, Heap.read, Heap.allocate]
  obtain ⟨result, minimum, summary⟩ := selection_summary heap 0 1 n
    (by simp [heap]) (by simp [heap])
  exact ⟨result, by simpa [distances, markers] using minimum,
    heap.tick "scans" n.toNat, ⟨summary.1, summary.2.root⟩, selection_costs heap n⟩

theorem every_output_correct (distance settled : Seq) (n result : Int)
    (produces : select_min.Returns (distance, settled, n) result) :
    Minimum distance settled n result := by
  obtain ⟨heap, execution⟩ := produces
  have correct := (execution_correct _ heap 0 1 n result execution).1
  simpa [select_min.load, Heap.read, Heap.allocate] using! correct

-- Main result: Correctness and running time
/-- A human-facing complete contract: first minimum and exactly `max(n, 0)`
    scans describe the output and running cost of the same execution. -/
theorem output_with_cost_iff (distance settled : Seq) (n result : Int) (costs : Clocks) :
    select_min.ReturnsWithCost (distance, settled, n) result costs ↔
      Minimum distance settled n result ∧ costs = scansCosts n := by
  constructor
  · intro produces
    have minimum := every_output_correct distance settled n result produces.returns
    obtain ⟨heap, execution, measured⟩ := produces
    have sameHeap := (execution_correct _ heap 0 1 n result execution).2
    refine ⟨minimum, ?_⟩
    rw [sameHeap] at measured
    exact measured.symm.trans (selection_costs _ n)
  · rintro ⟨minimum, rfl⟩
    obtain ⟨expected, expectedMinimum, produces⟩ := output_with_cost distance settled n
    have same := minimum_unique distance settled n result expected minimum expectedMinimum
    simpa [same] using produces

theorem output_iff_minimum (distance settled : Seq) (n result : Int) :
    select_min.Returns (distance, settled, n) result ↔ Minimum distance settled n result := by
  constructor
  · exact every_output_correct distance settled n result
  · intro minimum
    exact ((output_with_cost_iff distance settled n result (scansCosts n)).2 ⟨minimum, rfl⟩).returns

theorem no_vertex_iff (distance settled : Seq) (n : Int) :
    select_min.Returns (distance, settled, n) (-1) ↔
      ∀ vertex, 0 ≤ vertex → vertex < n → ¬ Candidate distance settled vertex := by
  rw [output_iff_minimum]
  constructor
  · intro minimum
    exact (minimum_absent_iff distance settled n (-1) minimum).1 rfl
  · intro none
    exact Or.inl ⟨rfl, none⟩

end SelectMinAnalysis
