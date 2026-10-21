import Algo.safety.Generated

open Algo2LeanCore Algo2LeanGenerated
open Algo.safety Algo.safety.Algo2LeanGenerated

namespace FiniteSafety

/-- A missing dictionary entry cannot be read as a default integer. -/
theorem missing_read (heap after : Heap) (values : CollectionRef) (key output : Int)
    (missing : «dict[Int, Int]».get heap values key = none) :
    ¬ read.Call heap (values, key) after output := by
  intro call
  obtain ⟨_, trace, execution⟩ := read.Call.run call
  unfold read.initial start at execution
  cases execution with
  | cons transition tail => cases transition <;> simp_all

/-- Deleting an absent key fails after evaluating the receiver and key. -/
theorem missing_delete (heap after : Heap) (values : CollectionRef) (key : Int)
    (missing : «dict[Int, Int]».get heap values key = none) :
    ¬ remove.Call heap (values, key) after () := by
  intro call
  obtain ⟨_, trace, execution⟩ := remove.Call.run call
  unfold remove.initial start at execution
  cases execution with
  | cons first tail =>
    cases first
    cases tail with
    | cons second rest =>
      cases second
      cases rest with
      | cons third final => cases third <;> simp_all [DictType.contains]

/-- A shallow copy returns a new identity with the same typed lookups. -/
theorem clone_call (heap : Heap) (values : CollectionRef)
    (valid : clone.ValidInput heap values) :
    clone.Call heap values («dict[Int, Int]».copy heap values).1
      («dict[Int, Int]».copy heap values).2 := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.clone_pc3 _ _ caller)
  apply Reaches.prepend (Step.clone_pc2 heap { v0 := values, t2 := values } caller valid)
  exact Reaches.single (Step.clone_pc1 («dict[Int, Int]».copy heap values).1
    { v0 := values, t1 := heap.nextCollection, t2 := values } caller
    (DictType.valid_copy «dict[Int, Int]» heap values))

theorem clone_fresh_contents (heap : Heap) (values : CollectionRef)
    (valid : clone.ValidInput heap values) :
    ∃ after copied, clone.Call heap values after copied ∧ copied ≠ values ∧
      ∀ key, «dict[Int, Int]».get after copied key = «dict[Int, Int]».get heap values key := by
  exact ⟨_, _, clone_call heap values valid,
    DictType.copy_fresh «dict[Int, Int]» heap values valid,
    DictType.get_copy «dict[Int, Int]» heap values⟩

end FiniteSafety
