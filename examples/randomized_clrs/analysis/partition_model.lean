import Algo.shuffle_model.Analysis

/-!
Lomuto partition as a finite mathematical scan of the heap. Each iteration
compares one cell with the saved pivot; successful comparisons exchange two
cells and advance the boundary. The final exchange places the pivot itself.
-/

noncomputable section
namespace PartitionAnalysis
open Algo2LeanGenerated Algo2LeanProbability
open scoped ENNReal

/-- Exchange two sequence cells and charge one swap, including a self-swap. -/
def exchange (heap : Heap) (ref : SeqRef) (first second : Int) : Heap :=
  ((heap.write ref first (heap.read ref second)).write ref second (heap.read ref first)).tick "swaps"

@[simp] theorem exchange_nextRef (heap : Heap) (ref : SeqRef) (first second : Int) :
    (exchange heap ref first second).nextRef = heap.nextRef := rfl

@[simp] theorem exchange_clocks (heap : Heap) (ref : SeqRef) (first second : Int) (clock : String) :
    (exchange heap ref first second).clocks clock = heap.clocks clock +
      (if clock = "swaps" then 1 else 0) := by
  simp [exchange, Heap.tick]
  split_ifs <;> simp

/-- A cell exchange preserves every unrelated sequence and object. -/
theorem exchange_frame (heap : Heap) (ref : SeqRef) (first second : Int) :
    heap.Footprint (exchange heap ref first second) [ref] [] [] := by
  exact (((Heap.Footprint.refl heap [ref] [] []).write ref first
    (heap.read ref second) (by simp)).write ref second
    (heap.read ref first) (by simp)).tick "swaps"

/-- A cell exchange acts on reads by a transposition of indices. -/
theorem exchange_read (heap : Heap) (ref : SeqRef) (first second index : Int) :
    (exchange heap ref first second).read ref index =
      heap.read ref (Equiv.swap first second index) := by
  by_cases h₂ : index = second
  · subst index; simp [exchange]
  by_cases h₁ : index = first
  · subst index; simp [exchange, h₂]
  simp [exchange, Heap.read, Heap.write, Equiv.swap_apply_def, h₁, h₂]

/-- Complete the scan of count cells, then exchange the boundary and pivot. -/
def scan (heap : Heap) (ref : SeqRef) (pivot boundary first : Int) : Nat → Heap × Int
  | 0 => (exchange heap ref boundary first, boundary)
  | count + 1 =>
      if heap.read ref first ≤ pivot then
        scan (exchange (heap.tick "comparisons") ref boundary first) ref pivot
          (boundary + 1) (first + 1) count
      else scan (heap.tick "comparisons") ref pivot boundary (first + 1) count

/-- The complete deterministic partition result, on a nonempty interval. -/
def partitionResult (heap : Heap) (ref : SeqRef) (lo hi : Int) : Heap × Int :=
  scan heap ref (heap.read ref (hi - 1)) lo lo (hi - lo - 1).toNat

/-- Partition rearranges only the supplied interval. -/
abbrev Rearranges := ShuffleAnalysis.Rearranges

/-- The pivot is placed between cells no larger than it and cells strictly larger. -/
def Partitioned (heap : Heap) (ref : SeqRef) (lo hi boundary pivot : Int) : Prop :=
  lo ≤ boundary ∧ boundary < hi ∧ heap.read ref boundary = pivot ∧
    (∀ index, lo ≤ index → index < boundary → heap.read ref index ≤ pivot) ∧
    (∀ index, boundary < index → index < hi → pivot < heap.read ref index)

/-- Every scan preserves allocation and unrelated storage. -/
theorem scan_frame (count : Nat) (heap : Heap) (ref : SeqRef) (pivot boundary first : Int) :
    (scan heap ref pivot boundary first count).1.nextRef = heap.nextRef ∧
      heap.Footprint (scan heap ref pivot boundary first count).1 [ref] [] [] := by
  induction count generalizing heap boundary first with
  | zero => exact ⟨rfl, exchange_frame ..⟩
  | succ count ih =>
      rw [scan]
      split
      · obtain ⟨refs, frame⟩ := ih (exchange (heap.tick "comparisons") ref boundary first)
          (boundary + 1) (first + 1)
        exact ⟨refs, ((Heap.Footprint.refl heap [ref] [] []).tick "comparisons").trans
          ((exchange_frame ..).trans frame)⟩
      · obtain ⟨refs, frame⟩ := ih (heap.tick "comparisons") boundary (first + 1)
        exact ⟨refs, ((Heap.Footprint.refl heap [ref] [] []).tick "comparisons").trans frame⟩

/-- There is exactly one comparison for each unprocessed non-pivot cell. -/
theorem scan_comparisons (count : Nat) (heap : Heap) (ref : SeqRef) (pivot boundary first : Int) :
    (scan heap ref pivot boundary first count).1.clocks "comparisons" =
      heap.clocks "comparisons" + count := by
  induction count generalizing heap boundary first with
  | zero => simp [scan]
  | succ count ih =>
      rw [scan]
      split <;> rw [ih] <;> simp [Nat.add_assoc, Nat.add_comm]

/-- The scan charges between one and count+1 swaps, including pivot placement. -/
theorem scan_swaps (count : Nat) (heap : Heap) (ref : SeqRef) (pivot boundary first : Int) :
    heap.clocks "swaps" + 1 ≤ (scan heap ref pivot boundary first count).1.clocks "swaps" ∧
    (scan heap ref pivot boundary first count).1.clocks "swaps" ≤
      heap.clocks "swaps" + count + 1 := by
  induction count generalizing heap boundary first with
  | zero => simp [scan]
  | succ count ih =>
      rw [scan]
      split
      · have bounds := ih (exchange (heap.tick "comparisons") ref boundary first) (boundary + 1) (first + 1)
        simp at bounds
        omega
      · have bounds := ih (heap.tick "comparisons") boundary (first + 1)
        simp at bounds
        omega

/-- Every clock other than comparisons and swaps is unchanged. -/
theorem scan_other_clock (count : Nat) (heap : Heap) (ref : SeqRef) (pivot boundary first : Int)
    (clock : String) (notComparisons : clock ≠ "comparisons") (notSwaps : clock ≠ "swaps") :
    (scan heap ref pivot boundary first count).1.clocks clock = heap.clocks clock := by
  induction count generalizing heap boundary first with
  | zero => simp [scan, notSwaps]
  | succ count ih =>
      rw [scan]
      split <;> rw [ih] <;> simp [notSwaps, Heap.tick, notComparisons]

/-- Interval-preserving rearrangements compose, retaining the outside cells. -/
theorem rearranges_trans {before middle after : Heap} {ref : SeqRef} {lo hi : Int}
    (first : Rearranges before middle ref lo hi) (second : Rearranges middle after ref lo hi) :
    Rearranges before after ref lo hi := by
  obtain ⟨p, po, pv⟩ := first
  obtain ⟨q, qo, qv⟩ := second
  refine ⟨q.trans p, ?_, ?_⟩
  · intro index outside
    simp [Equiv.trans_apply, qo index outside, po index outside]
  · intro index
    rw [qv index, pv]
    rfl

/-- Exchanging positions inside an interval preserves its multiset and outside cells. -/
theorem exchange_rearranges (heap : Heap) (ref : SeqRef) (first second lo hi : Int)
    (firstBounds : lo ≤ first ∧ first < hi) (secondBounds : lo ≤ second ∧ second < hi) :
    Rearranges heap (exchange heap ref first second) ref lo hi := by
  refine ⟨Equiv.swap first second, ?_, exchange_read heap ref first second⟩
  intro index outside
  apply Equiv.swap_apply_of_ne_of_ne <;> omega

/-- Every scan permutes the original interval, including its pivot cell. -/
theorem scan_rearranges (count : Nat) (heap : Heap) (ref : SeqRef)
    (pivot boundary first lo : Int) (low : lo ≤ boundary) (ordered : boundary ≤ first) :
    Rearranges heap (scan heap ref pivot boundary first count).1 ref lo (first + count + 1) := by
  induction count generalizing heap boundary first with
  | zero =>
      exact exchange_rearranges heap ref boundary first lo (first + 0 + 1)
        (by constructor <;> omega) (by constructor <;> omega)
  | succ count ih =>
      rw [scan]
      split
      · have previous := exchange_rearranges (heap.tick "comparisons") ref boundary first lo
          (first + (count + 1 : Nat) + 1) (by constructor <;> omega) (by constructor <;> omega)
        have later := ih (exchange (heap.tick "comparisons") ref boundary first)
          (boundary + 1) (first + 1) (by omega) (by omega)
        have same : first + 1 + (count : Int) + 1 = first + (count + 1 : Nat) + 1 := by omega
        rw [same] at later
        have combined := rearranges_trans previous later
        simpa only [Rearranges, ShuffleAnalysis.Rearranges, Heap.read_tick] using combined
      · have later := ih (heap.tick "comparisons") boundary (first + 1) low (by omega)
        have same : first + 1 + (count : Int) + 1 = first + (count + 1 : Nat) + 1 := by omega
        rw [same] at later
        simpa only [Rearranges, ShuffleAnalysis.Rearranges, Heap.read_tick] using later

/-- The loop invariant separates small values, large processed values, and the
unprocessed suffix. Completing it establishes the textbook partition contract. -/
theorem scan_partitioned (count : Nat) (heap : Heap) (ref : SeqRef)
    (pivot boundary first lo : Int)
    (low : lo ≤ boundary) (ordered : boundary ≤ first)
    (pivotCell : heap.read ref (first + count) = pivot)
    (small : ∀ index, lo ≤ index → index < boundary → heap.read ref index ≤ pivot)
    (large : ∀ index, boundary ≤ index → index < first → pivot < heap.read ref index) :
    Partitioned (scan heap ref pivot boundary first count).1 ref lo (first + count + 1)
      (scan heap ref pivot boundary first count).2 pivot := by
  induction count generalizing heap boundary first with
  | zero =>
      simp only [Nat.cast_zero, add_zero] at pivotCell ⊢
      simp only [scan, Partitioned]
      refine ⟨low, by omega, ?_, ?_, ?_⟩
      · simpa [scan, exchange_read] using pivotCell
      · intro index lower upper
        have neBoundary : index ≠ boundary := by omega
        have neFirst : index ≠ first := by omega
        simpa [scan, exchange_read, Equiv.swap_apply_of_ne_of_ne neBoundary neFirst]
          using small index lower upper
      · intro index lower upper
        by_cases last : index = first
        · subst index
          simpa [scan, exchange_read] using large boundary le_rfl (by omega)
        · have neBoundary : index ≠ boundary := by omega
          simpa [scan, exchange_read, Equiv.swap_apply_of_ne_of_ne neBoundary last]
            using large index (by omega) (by omega)
  | succ count ih =>
      rw [scan]
      by_cases accepted : heap.read ref first ≤ pivot
      · rw [if_pos accepted]
        have newPivot : (exchange (heap.tick "comparisons") ref boundary first).read ref
            (first + 1 + count) = pivot := by
          have neBoundary : first + 1 + (count : Int) ≠ boundary := by omega
          have neFirst : first + 1 + (count : Int) ≠ first := by omega
          rw [exchange_read, Equiv.swap_apply_of_ne_of_ne neBoundary neFirst, Heap.read_tick]
          convert pivotCell using 1
          congr 1
          omega
        have newSmall : ∀ index, lo ≤ index → index < boundary + 1 →
            (exchange (heap.tick "comparisons") ref boundary first).read ref index ≤ pivot := by
          intro index lower upper
          by_cases atBoundary : index = boundary
          · subst index; simpa [exchange_read] using accepted
          · have neFirst : index ≠ first := by omega
            simpa [exchange_read, Equiv.swap_apply_of_ne_of_ne atBoundary neFirst]
              using small index lower (by omega)
        have newLarge : ∀ index, boundary + 1 ≤ index → index < first + 1 →
            pivot < (exchange (heap.tick "comparisons") ref boundary first).read ref index := by
          intro index lower upper
          by_cases atFirst : index = first
          · subst index
            simpa [exchange_read] using large boundary le_rfl (by omega)
          · have neBoundary : index ≠ boundary := by omega
            simpa [exchange_read, Equiv.swap_apply_of_ne_of_ne neBoundary atFirst]
              using large index (by omega) (by omega)
        have result := ih (exchange (heap.tick "comparisons") ref boundary first)
          (boundary + 1) (first + 1) (by omega) (by omega) newPivot newSmall newLarge
        convert result using 1
        congr 1
        omega
      · rw [if_neg accepted]
        have newPivot : (heap.tick "comparisons").read ref (first + 1 + count) = pivot := by
          simpa [Nat.cast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using pivotCell
        have newLarge : ∀ index, boundary ≤ index → index < first + 1 →
            pivot < (heap.tick "comparisons").read ref index := by
          intro index lower upper
          by_cases atFirst : index = first
          · subst index; simpa using lt_of_not_ge accepted
          · simpa using large index lower (by omega)
        have result := ih (heap.tick "comparisons") boundary (first + 1) low (by omega)
          newPivot (by simpa using small) newLarge
        convert result using 1
        congr 1
        omega

/-- The full model satisfies partition correctness for every nonempty interval. -/
theorem partitionResult_partitioned (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi) :
    Partitioned (partitionResult heap ref lo hi).1 ref lo hi (partitionResult heap ref lo hi).2
      (heap.read ref (hi - 1)) := by
  have size : lo + ((hi - lo - 1).toNat : Int) = hi - 1 := by omega
  have result := scan_partitioned (hi - lo - 1).toNat heap ref (heap.read ref (hi - 1)) lo lo lo
    le_rfl le_rfl (by rw [size]) (by intros; omega) (by intros; omega)
  have finish : lo + ((hi - lo - 1).toNat : Int) + 1 = hi := by omega
  rw [finish] at result
  exact result

/-- Partition preserves the sequence's elements, allocation, and unrelated storage. -/
theorem partitionResult_frame (heap : Heap) (ref : SeqRef) (lo hi : Int) :
    (partitionResult heap ref lo hi).1.nextRef = heap.nextRef ∧
    heap.Footprint (partitionResult heap ref lo hi).1 [ref] [] [] :=
  scan_frame ..

theorem partitionResult_rearranges (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi) :
    Rearranges heap (partitionResult heap ref lo hi).1 ref lo hi := by
  have result := scan_rearranges (hi - lo - 1).toNat heap ref (heap.read ref (hi - 1)) lo lo lo
    le_rfl le_rfl
  have finish : lo + ((hi - lo - 1).toNat : Int) + 1 = hi := by omega
  rw [finish] at result
  exact result

/-- A partition of n+1 values performs exactly n comparisons. -/
theorem partitionResult_comparisons (heap : Heap) (ref : SeqRef) (lo hi : Int) :
    Heap.cost heap (partitionResult heap ref lo hi).1 "comparisons" = (hi - lo - 1).toNat := by
  unfold Heap.cost partitionResult
  rw [scan_comparisons]
  omega

/-- At most one swap per scanned cell, plus one final pivot swap. -/
theorem partitionResult_swaps (heap : Heap) (ref : SeqRef) (lo hi : Int) (nonempty : lo < hi) :
    1 ≤ Heap.cost heap (partitionResult heap ref lo hi).1 "swaps" ∧
    Heap.cost heap (partitionResult heap ref lo hi).1 "swaps" ≤ (hi - lo).toNat := by
  have bounds := scan_swaps (hi - lo - 1).toNat heap ref (heap.read ref (hi - 1)) lo lo
  unfold Heap.cost partitionResult
  omega

end PartitionAnalysis
