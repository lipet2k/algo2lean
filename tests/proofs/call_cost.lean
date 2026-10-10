import Algo2LeanLib.CallCost
import Algo2LeanLib.Footprint

open Algo2LeanGenerated
open Algo2LeanCore

namespace CostFootprintCheck

def call (before after : Heap) : Prop := after = (before.write 0 0 7).tick "work" 2

theorem call_monotone (before after : Heap) (executed : call before after) :
    before.ClocksMonotone after := by
  subst after
  intro name
  exact Heap.clocks_le_tick (before.write 0 0 7) "work" name 2

theorem call_bound (before after : Heap) (executed : call before after) :
    Heap.weightedCost [("work", 2), ("work", 1)] before after ≤ 6 := by
  subst after
  simp [Heap.weightedCost, Clocks.weighted, Heap.cost, Heap.tick]

-- Both executions and their weighted bound share precisely the same final heap.
example (heap : Heap) :
    let middle := (heap.write 0 0 7).tick "work" 2
    let final := (middle.write 0 0 7).tick "work" 2
    Valid call heap [heap, middle, final] final ∧
      Heap.weightedCost [("work", 2), ("work", 1)] heap final ≤ 12 := by
  intro middle final
  have run : Valid call heap [heap, middle, final] final :=
    .cons rfl (.cons rfl (.single _))
  refine ⟨run, ?_⟩
  have bound := CallCost.bound [("work", 2), ("work", 1)] id (fun _ => 0)
    (fun _ _ => 6) run call_monotone (by simpa using call_bound)
  simpa [CallCost.total] using bound

-- Exact increments compose independently of data mutation and starting clocks.
example (before middle after : Heap) (one : before.Increments middle (Clocks.single "work" 3))
    (two : middle.Increments after (Clocks.single "work" 5)) :
    Heap.cost before after "work" = 8 := by
  have cost := (one.trans two).cost
  simpa [Clocks.add, Clocks.single] using congrFun cost "work"

-- Newly allocated storage can be initialized without adding it to the old footprint.
example (heap : Heap) :
    heap.Footprint ((heap.allocate (fun _ => 0)).write heap.nextRef 4 99) [] [] [] := by
  exact ((Heap.Footprint.refl heap [] [] []).allocate (fun _ => 0)).write
    heap.nextRef 4 99 (Or.inr (Nat.le_refl _))

example (heap : Heap) :
    heap.Footprint
      ((heap.allocateObject "Cell").writeField heap.nextObject "value" (.intValue 99)) [] [] [] := by
  exact ((Heap.Footprint.refl heap [] [] []).allocateObject "Cell").writeField
    heap.nextObject "value" (.intValue 99) (Or.inr (Nat.le_refl _))

example (heap : Heap) :
    heap.Footprint
      ((heap.allocateSequence "Int" (fun _ => .intValue 0)).writeElement
        heap.nextCollection (-7) (.intValue 99)) [] [] [] := by
  exact ((Heap.Footprint.refl heap [] [] []).allocateSequence "Int" (fun _ => .intValue 0)).writeElement
    heap.nextCollection (-7) (.intValue 99) (Or.inr (Nat.le_refl _))

-- All old collection elements, including negative indices, survive fresh allocation.
example (heap : Heap) (old : CollectionRef) (allocated : old < heap.nextCollection) :
    ((heap.allocateSequence "Int" (fun _ => .intValue 0)).writeElement
      heap.nextCollection (-7) (.intValue 99)).readElement old (-7) = heap.readElement old (-7) := by
  have frame := ((Heap.Footprint.refl heap [] [] []).allocateSequence "Int"
    (fun _ => .intValue 0)).writeElement heap.nextCollection (-7) (.intValue 99)
    (Or.inr (Nat.le_refl _))
  exact frame.readElement old allocated (by simp) (-7)

end CostFootprintCheck
