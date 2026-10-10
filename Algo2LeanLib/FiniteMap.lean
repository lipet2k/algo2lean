import Algo2Lean

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


/-! Association-list membership and update lemmas for finite dictionary and queue models. -/
namespace Algo2Lean.FiniteMap

variable {Key Value : Type} [DecidableEq Key]

def erase (entries : List (Key × Value)) (key : Key) : List (Key × Value) :=
  entries.filter (fun entry => entry.1 != key)

def set (entries : List (Key × Value)) (key : Key) (value : Value) : List (Key × Value) :=
  (key, value) :: erase entries key

@[simp] theorem mem_erase {entries : List (Key × Value)} {key other : Key} {value : Value} :
    (other, value) ∈ erase entries key ↔ other ≠ key ∧ (other, value) ∈ entries := by
  simp [erase, and_comm]

@[simp] theorem mem_set {entries : List (Key × Value)} {key other : Key} {value found : Value} :
    (other, found) ∈ set entries key value ↔
      (other = key ∧ found = value) ∨ (other ≠ key ∧ (other, found) ∈ entries) := by
  simp [set, Prod.mk.injEq]

theorem erase_unique {entries : List (Key × Value)} (unique : (entries.map Prod.fst).Nodup)
    (key : Key) : ((erase entries key).map Prod.fst).Nodup := by
  exact List.pairwise_map.mpr ((List.pairwise_map.mp unique).filter _)

theorem set_unique {entries : List (Key × Value)} (unique : (entries.map Prod.fst).Nodup)
    (key : Key) (value : Value) : ((set entries key value).map Prod.fst).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_, erase_unique unique key⟩
  intro member
  obtain ⟨entry, present, equal⟩ := List.mem_map.mp member
  obtain ⟨different, _⟩ := mem_erase.mp present
  exact different equal

end Algo2Lean.FiniteMap
