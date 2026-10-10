import Algo2Lean

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Finite integer ranges and injective-prefix bounds, independent of algorithms. -/
namespace Algo2Lean.FiniteIndex

/-- Integer indices from zero to `size - 1`; nonpositive sizes give an empty list. -/
def range (size : Int) : List Int := (List.range size.toNat).map Int.ofNat

@[simp] theorem range_length (size : Int) : (range size).length = size.toNat := by
  simp [range]

theorem range_nodup (size : Int) : (range size).Nodup := by
  exact List.Pairwise.map Int.ofNat (fun a b different same => different (Int.ofNat.inj same)) List.nodup_range

@[simp] theorem range_member (size vertex : Int) :
    vertex ∈ range size ↔ 0 ≤ vertex ∧ vertex < size := by
  simp only [range, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨index, bound, rfl⟩
    change 0 ≤ (index : Int) ∧ (index : Int) < size
    omega
  · rintro ⟨nonnegative, bound⟩
    exact ⟨vertex.toNat, by omega, Int.toNat_of_nonneg nonnegative⟩

/-- Erasing one present integer shortens the list by exactly one occurrence. -/
theorem erase_length (remaining : List Int) (selected : Int) (member : selected ∈ remaining) :
    (remaining.erase selected).length + 1 = remaining.length := by
  have positive := List.length_pos_of_mem member
  rw [List.length_erase_of_mem member]
  omega

/-- A duplicate-free list cannot inject by membership into a shorter list. -/
theorem nodup_subset_length (first second : List Int) (unique : first.Nodup)
    (contained : ∀ vertex ∈ first, vertex ∈ second) : first.length ≤ second.length := by
  induction first generalizing second with
  | nil => simp
  | cons vertex rest ih =>
    obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
    have member := contained vertex (by simp)
    have remaining := ih (second.erase vertex) restUnique (by
      intro other inRest
      apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
      exact contained other (by simp [inRest]))
    have length := erase_length second vertex member
    simp only [List.length_cons]
    omega

/-- A finite injective prefix has no more entries than a list containing all
    its values. The `positions` left inverse establishes injectivity. -/
theorem active_prefix_bound (vertices positions : Int → Int) (size : Int)
    (nonnegative : 0 ≤ size)
    (inverse : ∀ index, 0 ≤ index → index < size → positions (vertices index) = index)
    (remaining : List Int)
    (contained : ∀ index, 0 ≤ index → index < size → vertices index ∈ remaining) :
    size ≤ (remaining.length : Int) := by
  let active := (List.range size.toNat).map (fun index : Nat => vertices (index : Int))
  have unique : active.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (l := List.range size.toNat) _ List.nodup_range
    intro i j iMember jMember different same
    have iBound := List.mem_range.mp iMember
    have jBound := List.mem_range.mp jMember
    have left := inverse (i : Int) (by omega) (by omega)
    have right := inverse (j : Int) (by omega) (by omega)
    rw [same] at left
    exact different (by omega)
  have included : ∀ vertex ∈ active, vertex ∈ remaining := by
    intro vertex member
    obtain ⟨index, bound, rfl⟩ := List.mem_map.mp member
    have indexBound := List.mem_range.mp bound
    exact contained (index : Int) (by omega) (by omega)
  have bound := nodup_subset_length active remaining unique included
  simp only [active, List.length_map, List.length_range] at bound
  omega

end Algo2Lean.FiniteIndex
