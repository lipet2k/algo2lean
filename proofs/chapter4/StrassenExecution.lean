import MatrixMath
import StrassenValue
import StrassenQuadrant
import Algo2LeanLib.MatrixHeap
import StrassenComposition
import StrassenLinear

open Algo2LeanCore Algo2LeanGenerated MatrixStrassenAnalysis MatrixStrassenHelpers
open Algo2LeanCore.MatrixHeap
open MatrixStrassenComposition

namespace MatrixStrassenExecution

/-- Exact counters for the source execution, including all copying passes. -/
def costs (depth : Nat) : Clocks := fun name =>
  (if name = "calls" then Chapter4Math.calls 7 depth else 0) +
  (if name = "products" then 7^depth else 0) +
  (if name = "linear_cells" then 18*Chapter4Math.strassenOverhead depth else 0) +
  (if name = "copied_cells" then 12*Chapter4Math.strassenOverhead depth else 0)

@[simp] theorem square_half (depth : Nat) : (2^depth)*(2^depth) = (4:Nat)^depth := by
  rw [← Nat.mul_pow]

/-- This is the actual call tree and per-node instrumentation of the source. -/
theorem costs_step (depth : Nat) (name : String) :
    costs (depth+1) name = (if name = "calls" then 1 else 0) + 7*costs depth name +
      (if name = "linear_cells" then 18*((2^depth)*(2^depth)) else 0) +
      (if name = "copied_cells" then 12*((2^depth)*(2^depth)) else 0) := by
  by_cases calls : name = "calls" <;> by_cases products : name = "products" <;>
    by_cases linear : name = "linear_cells" <;> by_cases copied : name = "copied_cells" <;>
    simp_all [costs, Chapter4Math.calls, Chapter4Math.strassenOverhead, Nat.pow_succ] <;> omega

theorem tick_preserves (heap : Heap) : Extends heap (heap.tick "calls") := extends_tick heap "calls" 1

private theorem leaf_contract_rows (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, strassen.Call heap (a,b,1) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.strassenValue 0 av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + costs 0 name) ∧ heap.nextCollection ≤ result ∧ FreshRows heap after result 1 := by
  let zero := (heap.tick "calls").allocate (fun _ => 0)
  let outer := (rows.const zero heap.nextRef).1
  let allocated := outer.allocate (fun _ => 0)
  let installed := rows.set allocated heap.nextCollection 0 (heap.nextRef+1)
  let final := (installed.write (heap.nextRef+1) 0 (av 0 0*bv 0 0)).tick "products"
  have frameZero : Extends heap zero := (extends_tick heap "calls" 1).trans (extends_allocate _ _)
  have frameOuter : Extends heap outer := frameZero.trans (extends_const _ _)
  have frameAllocated : Extends heap allocated := frameOuter.trans (extends_allocate _ _)
  have frameInstalled : Extends heap installed := frameAllocated.set heap.nextCollection (Nat.le_refl _) 0 _
  have ai := sa.mono frameInstalled
  have bi := sb.mono frameInstalled
  have initialStored : Stored outer heap.nextCollection (fun _ _ => 0) :=
    stored_const zero heap.nextRef _ (Nat.lt_succ_self _) (by simp [zero,Heap.allocate])
  have allocatedStored := initialStored.mono (extends_allocate outer (fun _ => 0))
  have installedStored : Stored installed heap.nextCollection (fun _ _ => 0) := by
    have st := allocatedStored.set 0 (heap.nextRef+1) (fun _ => 0)
      (by simp [allocated,outer,zero,SequenceType.const,SequenceType.create,Heap.createSequence])
      (by simp [allocated,outer,zero,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.allocate])
    simpa only [ite_self] using st
  have outputRow : rows.get installed heap.nextCollection 0 = some (heap.nextRef+1) :=
    rows.get_set_same allocated heap.nextCollection 0 _ allocatedStored.1
  refine ⟨final,heap.nextCollection,?_,?_,?_,?_,Nat.le_refl _,?_⟩
  · refine ⟨⟨sa.1,sb.1⟩,?_⟩
    intro stack
    apply Reaches.prepend (Step.strassen_pc195 ..)
    apply Reaches.prepend (Step.strassen_pc194 ..)
    apply Reaches.prepend (Step.strassen_pc193_true _ _ _ (by simp))
    apply Reaches.prepend (Step.strassen_pc13 ..)
    apply Reaches.prepend (Step.strassen_pc12 ..)
    apply Reaches.prepend (Step.strassen_pc11 ..)
    apply Reaches.prepend (Step.strassen_pc10 ..)
    apply Reaches.prepend (Step.strassen_pc9 ..)
    apply Reaches.prepend (Step.strassen_pc8 ..)
    apply Reaches.prepend (Step.strassen_pc7 ..)
    apply Reaches.prepend (Step.strassen_pc6 ..)
    apply Reaches.prepend (Step.strassen_pc5 _ _ _ (by exact allocatedStored.1))
    apply Reaches.prepend (Step.strassen_pc4 _ _ _ (by
      repeat' apply And.intro
      all_goals first | exact ai.row 0 | exact ai.row_valid 0 | exact bi.row 0 | exact bi.row_valid 0 | exact installedStored.row 0 | exact installedStored.row_valid 0))
    dsimp only
    change Reaches Step (.active (installed.write ((rows.get installed heap.nextCollection 0).getD 0) 0
      (installed.read ((rows.get installed a 0).getD 0) 0 * installed.read ((rows.get installed b 0).getD 0) 0)) _ _) _
    rw [outputRow,ai.read,bi.read]
    dsimp only [Option.getD]
    apply Reaches.prepend (Step.strassen_pc3 ..)
    apply Reaches.prepend (Step.strassen_pc2 ..)
    exact Reaches.single (Step.strassen_pc1 _ _ _ installedStored.1)
  · exact (frameInstalled.write (heap.nextRef+1) (by omega) 0 _).trans (extends_tick _ "products" 1)
  · refine ⟨installedStored.1,?_⟩
    intro i
    by_cases same : i = 0
    · subst i
      refine ⟨heap.nextRef+1,?_,?_,?_⟩
      · simpa only [final,rows_get_tick,rows_get_write] using outputRow
      · change heap.nextRef + 1 < heap.nextRef + 1 + 1
        omega
      · funext j
        simp [final,installed,allocated,outer,zero,SequenceType.set,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.writeElement,Heap.write,Heap.allocate,StrassenValues.strassenValue]
    · refine ⟨heap.nextRef,?_,?_,?_⟩
      · change rows.get installed heap.nextCollection i = some heap.nextRef
        rw [rows.get_set_other_index allocated heap.nextCollection i 0 _ same]
        change rows.get outer heap.nextCollection i = some heap.nextRef
        exact rows.get_const zero heap.nextRef i
      · change heap.nextRef < heap.nextRef + 1 + 1
        exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
      · funext j
        simp [final,installed,allocated,outer,zero,SequenceType.set,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.writeElement,Heap.write,Heap.allocate,StrassenValues.strassenValue,same]
  · intro name
    by_cases calls : name = "calls" <;> by_cases products : name = "products" <;>
      simp_all [final,installed,allocated,outer,zero,SequenceType.set,SequenceType.const,SequenceType.create,Heap.createSequence,Heap.writeElement,Heap.write,Heap.tick,costs,Chapter4Math.calls,Chapter4Math.strassenOverhead]
  · constructor
    · intro i valid
      have izero : i = 0 := by omega
      subst i
      refine ⟨heap.nextRef+1,?_,by omega,?_⟩
      · simpa only [Int.natCast_zero,final,rows_get_tick,rows_get_write] using outputRow
      · change heap.nextRef+1 < heap.nextRef+1+1
        exact Nat.lt_succ_self _
    · intro i j hi hj _
      omega

/-- Every source invocation terminates on a power-of-two dimension, returns the
    mathematically specified Strassen value, preserves all earlier arrays, and
    charges these exact counters in the same execution. Its result reference
    is fresh relative to every sequence allocated before the invocation. -/
theorem strassen_summary_rows (depth : Nat) (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, strassen.Call heap (a,b,((2^depth:Nat):Int)) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.strassenValue depth av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + costs depth name) ∧ heap.nextCollection ≤ result ∧ FreshRows heap after result (2^depth) := by
  induction depth generalizing heap a b av bv with
  | zero => simpa only [Nat.pow_zero,Int.natCast_one] using leaf_contract_rows heap a b av bv sa sb
  | succ depth ih =>
    let h : Nat := 2^depth
    let n : Int := 2*h
    have positive : 0 < h := Nat.pow_pos (by decide)
    have startA := sa.mono (tick_preserves heap)
    have startB := sb.mono (tick_preserves heap)
    let a11Values : Values := StrassenValues.quadrantValues n h 0 0 av
    obtain ⟨a11Heap, a11Ref, a11Run, a11Frame, a11Stored, a11Clocks⟩ :=
      quadrant_contract (heap.tick "calls") a av n 0 0 h startA positive
    change Stored a11Heap a11Ref a11Values at a11Stored
    let a12Values : Values := StrassenValues.quadrantValues n h 0 h av
    obtain ⟨a12Heap, a12Ref, a12Run, a12Frame, a12Stored, a12Clocks⟩ :=
      quadrant_contract a11Heap a av n 0 h h (startA.mono a11Frame) positive
    change Stored a12Heap a12Ref a12Values at a12Stored
    let a21Values : Values := StrassenValues.quadrantValues n h h 0 av
    obtain ⟨a21Heap, a21Ref, a21Run, a21Frame, a21Stored, a21Clocks⟩ :=
      quadrant_contract a12Heap a av n h 0 h (startA.mono (a11Frame.trans a12Frame)) positive
    change Stored a21Heap a21Ref a21Values at a21Stored
    let a22Values : Values := StrassenValues.quadrantValues n h h h av
    obtain ⟨a22Heap, a22Ref, a22Run, a22Frame, a22Stored, a22Clocks⟩ :=
      quadrant_contract a21Heap a av n h h h (startA.mono (a11Frame.trans (a12Frame.trans a21Frame))) positive
    change Stored a22Heap a22Ref a22Values at a22Stored
    let b11Values : Values := StrassenValues.quadrantValues n h 0 0 bv
    obtain ⟨b11Heap, b11Ref, b11Run, b11Frame, b11Stored, b11Clocks⟩ :=
      quadrant_contract a22Heap b bv n 0 0 h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans a22Frame)))) positive
    change Stored b11Heap b11Ref b11Values at b11Stored
    let b12Values : Values := StrassenValues.quadrantValues n h 0 h bv
    obtain ⟨b12Heap, b12Ref, b12Run, b12Frame, b12Stored, b12Clocks⟩ :=
      quadrant_contract b11Heap b bv n 0 h h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans b11Frame))))) positive
    change Stored b12Heap b12Ref b12Values at b12Stored
    let b21Values : Values := StrassenValues.quadrantValues n h h 0 bv
    obtain ⟨b21Heap, b21Ref, b21Run, b21Frame, b21Stored, b21Clocks⟩ :=
      quadrant_contract b12Heap b bv n h 0 h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans b12Frame)))))) positive
    change Stored b21Heap b21Ref b21Values at b21Stored
    let b22Values : Values := StrassenValues.quadrantValues n h h h bv
    obtain ⟨b22Heap, b22Ref, b22Run, b22Frame, b22Stored, b22Clocks⟩ :=
      quadrant_contract b21Heap b bv n h h h (startB.mono (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans b21Frame))))))) positive
    change Stored b22Heap b22Ref b22Values at b22Stored
    let linear1Values : Values := StrassenValues.linearValues h (-1) b12Values b22Values
    obtain ⟨linear1Heap, linear1Ref, linear1Run, linear1Frame, linear1Stored, linear1Clocks⟩ :=
      linear_contract b22Heap b12Ref b22Ref b12Values b22Values h (-1) (b12Stored.mono (b21Frame.trans b22Frame)) b22Stored
    change Stored linear1Heap linear1Ref linear1Values at linear1Stored
    let p1Values : Values := StrassenValues.strassenValue depth a11Values linear1Values
    obtain ⟨p1Heap, p1Ref, p1Run, p1Frame, p1Stored, p1Clocks, _⟩ :=
      ih linear1Heap a11Ref linear1Ref a11Values linear1Values (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans linear1Frame)))))))) linear1Stored
    change Stored p1Heap p1Ref p1Values at p1Stored
    let linear2Values : Values := StrassenValues.linearValues h (1) a11Values a12Values
    obtain ⟨linear2Heap, linear2Ref, linear2Run, linear2Frame, linear2Stored, linear2Clocks⟩ :=
      linear_contract p1Heap a11Ref a12Ref a11Values a12Values h (1) (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans p1Frame))))))))) (a12Stored.mono (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans p1Frame))))))))
    change Stored linear2Heap linear2Ref linear2Values at linear2Stored
    let p2Values : Values := StrassenValues.strassenValue depth linear2Values b22Values
    obtain ⟨p2Heap, p2Ref, p2Run, p2Frame, p2Stored, p2Clocks, _⟩ :=
      ih linear2Heap linear2Ref b22Ref linear2Values b22Values linear2Stored (b22Stored.mono (linear1Frame.trans (p1Frame.trans linear2Frame)))
    change Stored p2Heap p2Ref p2Values at p2Stored
    let linear3Values : Values := StrassenValues.linearValues h (1) a21Values a22Values
    obtain ⟨linear3Heap, linear3Ref, linear3Run, linear3Frame, linear3Stored, linear3Clocks⟩ :=
      linear_contract p2Heap a21Ref a22Ref a21Values a22Values h (1) (a21Stored.mono (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans p2Frame))))))))) (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans p2Frame))))))))
    change Stored linear3Heap linear3Ref linear3Values at linear3Stored
    let p3Values : Values := StrassenValues.strassenValue depth linear3Values b11Values
    obtain ⟨p3Heap, p3Ref, p3Run, p3Frame, p3Stored, p3Clocks, _⟩ :=
      ih linear3Heap linear3Ref b11Ref linear3Values b11Values linear3Stored (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans linear3Frame))))))))
    change Stored p3Heap p3Ref p3Values at p3Stored
    let linear4Values : Values := StrassenValues.linearValues h (-1) b21Values b11Values
    obtain ⟨linear4Heap, linear4Ref, linear4Run, linear4Frame, linear4Stored, linear4Clocks⟩ :=
      linear_contract p3Heap b21Ref b11Ref b21Values b11Values h (-1) (b21Stored.mono (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans p3Frame))))))) (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans p3Frame)))))))))
    change Stored linear4Heap linear4Ref linear4Values at linear4Stored
    let p4Values : Values := StrassenValues.strassenValue depth a22Values linear4Values
    obtain ⟨p4Heap, p4Ref, p4Run, p4Frame, p4Stored, p4Clocks, _⟩ :=
      ih linear4Heap a22Ref linear4Ref a22Values linear4Values (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans linear4Frame))))))))))) linear4Stored
    change Stored p4Heap p4Ref p4Values at p4Stored
    let linear5Values : Values := StrassenValues.linearValues h (1) a11Values a22Values
    obtain ⟨linear5Heap, linear5Ref, linear5Run, linear5Frame, linear5Stored, linear5Clocks⟩ :=
      linear_contract p4Heap a11Ref a22Ref a11Values a22Values h (1) (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans p4Frame))))))))))))))) (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans p4Frame))))))))))))
    change Stored linear5Heap linear5Ref linear5Values at linear5Stored
    let linear6Values : Values := StrassenValues.linearValues h (1) b11Values b22Values
    obtain ⟨linear6Heap, linear6Ref, linear6Run, linear6Frame, linear6Stored, linear6Clocks⟩ :=
      linear_contract linear5Heap b11Ref b22Ref b11Values b22Values h (1) (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans linear5Frame)))))))))))) (b22Stored.mono (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans linear5Frame)))))))))
    change Stored linear6Heap linear6Ref linear6Values at linear6Stored
    let p5Values : Values := StrassenValues.strassenValue depth linear5Values linear6Values
    obtain ⟨p5Heap, p5Ref, p5Run, p5Frame, p5Stored, p5Clocks, _⟩ :=
      ih linear6Heap linear5Ref linear6Ref linear5Values linear6Values (linear5Stored.mono linear6Frame) linear6Stored
    change Stored p5Heap p5Ref p5Values at p5Stored
    let linear7Values : Values := StrassenValues.linearValues h (-1) a12Values a22Values
    obtain ⟨linear7Heap, linear7Ref, linear7Run, linear7Frame, linear7Stored, linear7Clocks⟩ :=
      linear_contract p5Heap a12Ref a22Ref a12Values a22Values h (-1) (a12Stored.mono (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans p5Frame))))))))))))))))) (a22Stored.mono (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans p5Frame)))))))))))))))
    change Stored linear7Heap linear7Ref linear7Values at linear7Stored
    let linear8Values : Values := StrassenValues.linearValues h (1) b21Values b22Values
    obtain ⟨linear8Heap, linear8Ref, linear8Run, linear8Frame, linear8Stored, linear8Clocks⟩ :=
      linear_contract linear7Heap b21Ref b22Ref b21Values b22Values h (1) (b21Stored.mono (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans linear7Frame))))))))))))) (b22Stored.mono (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans linear7Frame))))))))))))
    change Stored linear8Heap linear8Ref linear8Values at linear8Stored
    let p6Values : Values := StrassenValues.strassenValue depth linear7Values linear8Values
    obtain ⟨p6Heap, p6Ref, p6Run, p6Frame, p6Stored, p6Clocks, _⟩ :=
      ih linear8Heap linear7Ref linear8Ref linear7Values linear8Values (linear7Stored.mono linear8Frame) linear8Stored
    change Stored p6Heap p6Ref p6Values at p6Stored
    let linear9Values : Values := StrassenValues.linearValues h (-1) a11Values a21Values
    obtain ⟨linear9Heap, linear9Ref, linear9Run, linear9Frame, linear9Stored, linear9Clocks⟩ :=
      linear_contract p6Heap a11Ref a21Ref a11Values a21Values h (-1) (a11Stored.mono (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans p6Frame))))))))))))))))))))) (a21Stored.mono (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans p6Frame)))))))))))))))))))
    change Stored linear9Heap linear9Ref linear9Values at linear9Stored
    let linear10Values : Values := StrassenValues.linearValues h (1) b11Values b12Values
    obtain ⟨linear10Heap, linear10Ref, linear10Run, linear10Frame, linear10Stored, linear10Clocks⟩ :=
      linear_contract linear9Heap b11Ref b12Ref b11Values b12Values h (1) (b11Stored.mono (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans linear9Frame)))))))))))))))))) (b12Stored.mono (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans linear9Frame)))))))))))))))))
    change Stored linear10Heap linear10Ref linear10Values at linear10Stored
    let p7Values : Values := StrassenValues.strassenValue depth linear9Values linear10Values
    obtain ⟨p7Heap, p7Ref, p7Run, p7Frame, p7Stored, p7Clocks, _⟩ :=
      ih linear10Heap linear9Ref linear10Ref linear9Values linear10Values (linear9Stored.mono linear10Frame) linear10Stored
    change Stored p7Heap p7Ref p7Values at p7Stored
    let linear11Values : Values := StrassenValues.linearValues h (1) p5Values p4Values
    obtain ⟨linear11Heap, linear11Ref, linear11Run, linear11Frame, linear11Stored, linear11Clocks⟩ :=
      linear_contract p7Heap p5Ref p4Ref p5Values p4Values h (1) (p5Stored.mono (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans p7Frame)))))) (p4Stored.mono (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans p7Frame)))))))))
    change Stored linear11Heap linear11Ref linear11Values at linear11Stored
    let linear12Values : Values := StrassenValues.linearValues h (-1) linear11Values p2Values
    obtain ⟨linear12Heap, linear12Ref, linear12Run, linear12Frame, linear12Stored, linear12Clocks⟩ :=
      linear_contract linear11Heap linear11Ref p2Ref linear11Values p2Values h (-1) linear11Stored (p2Stored.mono (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans linear11Frame))))))))))))))
    change Stored linear12Heap linear12Ref linear12Values at linear12Stored
    let c11Values : Values := StrassenValues.linearValues h (1) linear12Values p6Values
    obtain ⟨c11Heap, c11Ref, c11Run, c11Frame, c11Stored, c11Clocks⟩ :=
      linear_contract linear12Heap linear12Ref p6Ref linear12Values p6Values h (1) linear12Stored (p6Stored.mono (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans linear12Frame)))))
    change Stored c11Heap c11Ref c11Values at c11Stored
    let c12Values : Values := StrassenValues.linearValues h (1) p1Values p2Values
    obtain ⟨c12Heap, c12Ref, c12Run, c12Frame, c12Stored, c12Clocks⟩ :=
      linear_contract c11Heap p1Ref p2Ref p1Values p2Values h (1) (p1Stored.mono (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans c11Frame)))))))))))))))))) (p2Stored.mono (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans c11Frame))))))))))))))))
    change Stored c12Heap c12Ref c12Values at c12Stored
    let c21Values : Values := StrassenValues.linearValues h (1) p3Values p4Values
    obtain ⟨c21Heap, c21Ref, c21Run, c21Frame, c21Stored, c21Clocks⟩ :=
      linear_contract c12Heap p3Ref p4Ref p3Values p4Values h (1) (p3Stored.mono (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans c12Frame))))))))))))))) (p4Stored.mono (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans c12Frame)))))))))))))
    change Stored c21Heap c21Ref c21Values at c21Stored
    let linear16Values : Values := StrassenValues.linearValues h (1) p5Values p1Values
    obtain ⟨linear16Heap, linear16Ref, linear16Run, linear16Frame, linear16Stored, linear16Clocks⟩ :=
      linear_contract c21Heap p5Ref p1Ref p5Values p1Values h (1) (p5Stored.mono (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans c21Frame))))))))))) (p1Stored.mono (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans c21Frame))))))))))))))))))))
    change Stored linear16Heap linear16Ref linear16Values at linear16Stored
    let linear17Values : Values := StrassenValues.linearValues h (-1) linear16Values p3Values
    obtain ⟨linear17Heap, linear17Ref, linear17Run, linear17Frame, linear17Stored, linear17Clocks⟩ :=
      linear_contract linear16Heap linear16Ref p3Ref linear16Values p3Values h (-1) linear16Stored (p3Stored.mono (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans (c21Frame.trans linear16Frame)))))))))))))))))
    change Stored linear17Heap linear17Ref linear17Values at linear17Stored
    let c22Values : Values := StrassenValues.linearValues h (-1) linear17Values p7Values
    obtain ⟨c22Heap, c22Ref, c22Run, c22Frame, c22Stored, c22Clocks⟩ :=
      linear_contract linear17Heap linear17Ref p7Ref linear17Values p7Values h (-1) linear17Stored (p7Stored.mono (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans (c21Frame.trans (linear16Frame.trans linear17Frame)))))))
    change Stored c22Heap c22Ref c22Values at c22Stored
    let joinedValues : Values := StrassenValues.joinValues h c11Values c12Values c21Values c22Values
    obtain ⟨joinedHeap, joinedRef, joinedRun, joinedFrame, joinedStored, joinedClocks, joinedFresh, joinedRows⟩ :=
      join_contract_rows c22Heap c11Ref c12Ref c21Ref c22Ref c11Values c12Values c21Values c22Values h (c11Stored.mono (c12Frame.trans (c21Frame.trans (linear16Frame.trans (linear17Frame.trans c22Frame))))) (c12Stored.mono (c21Frame.trans (linear16Frame.trans (linear17Frame.trans c22Frame)))) (c21Stored.mono (linear16Frame.trans (linear17Frame.trans c22Frame))) c22Stored positive
    change Stored joinedHeap joinedRef joinedValues at joinedStored
    let plan : BranchRun (heap.tick "calls") a b n h := {
      a11 := ⟨a11Heap, a11Ref⟩
      a12 := ⟨a12Heap, a12Ref⟩
      a21 := ⟨a21Heap, a21Ref⟩
      a22 := ⟨a22Heap, a22Ref⟩
      b11 := ⟨b11Heap, b11Ref⟩
      b12 := ⟨b12Heap, b12Ref⟩
      b21 := ⟨b21Heap, b21Ref⟩
      b22 := ⟨b22Heap, b22Ref⟩
      linear1 := ⟨linear1Heap, linear1Ref⟩
      p1 := ⟨p1Heap, p1Ref⟩
      linear2 := ⟨linear2Heap, linear2Ref⟩
      p2 := ⟨p2Heap, p2Ref⟩
      linear3 := ⟨linear3Heap, linear3Ref⟩
      p3 := ⟨p3Heap, p3Ref⟩
      linear4 := ⟨linear4Heap, linear4Ref⟩
      p4 := ⟨p4Heap, p4Ref⟩
      linear5 := ⟨linear5Heap, linear5Ref⟩
      linear6 := ⟨linear6Heap, linear6Ref⟩
      p5 := ⟨p5Heap, p5Ref⟩
      linear7 := ⟨linear7Heap, linear7Ref⟩
      linear8 := ⟨linear8Heap, linear8Ref⟩
      p6 := ⟨p6Heap, p6Ref⟩
      linear9 := ⟨linear9Heap, linear9Ref⟩
      linear10 := ⟨linear10Heap, linear10Ref⟩
      p7 := ⟨p7Heap, p7Ref⟩
      linear11 := ⟨linear11Heap, linear11Ref⟩
      linear12 := ⟨linear12Heap, linear12Ref⟩
      c11 := ⟨c11Heap, c11Ref⟩
      c12 := ⟨c12Heap, c12Ref⟩
      c21 := ⟨c21Heap, c21Ref⟩
      linear16 := ⟨linear16Heap, linear16Ref⟩
      linear17 := ⟨linear17Heap, linear17Ref⟩
      c22 := ⟨c22Heap, c22Ref⟩
      joined := ⟨joinedHeap, joinedRef⟩
      a11_run := a11Run
      a12_run := a12Run
      a21_run := a21Run
      a22_run := a22Run
      b11_run := b11Run
      b12_run := b12Run
      b21_run := b21Run
      b22_run := b22Run
      linear1_run := by simpa only [Int.natCast_mul] using linear1Run
      p1_run := p1Run
      linear2_run := by simpa only [Int.natCast_mul] using linear2Run
      p2_run := p2Run
      linear3_run := by simpa only [Int.natCast_mul] using linear3Run
      p3_run := p3Run
      linear4_run := by simpa only [Int.natCast_mul] using linear4Run
      p4_run := p4Run
      linear5_run := by simpa only [Int.natCast_mul] using linear5Run
      linear6_run := by simpa only [Int.natCast_mul] using linear6Run
      p5_run := p5Run
      linear7_run := by simpa only [Int.natCast_mul] using linear7Run
      linear8_run := by simpa only [Int.natCast_mul] using linear8Run
      p6_run := p6Run
      linear9_run := by simpa only [Int.natCast_mul] using linear9Run
      linear10_run := by simpa only [Int.natCast_mul] using linear10Run
      p7_run := p7Run
      linear11_run := by simpa only [Int.natCast_mul] using linear11Run
      linear12_run := by simpa only [Int.natCast_mul] using linear12Run
      c11_run := by simpa only [Int.natCast_mul] using c11Run
      c12_run := by simpa only [Int.natCast_mul] using c12Run
      c21_run := by simpa only [Int.natCast_mul] using c21Run
      linear16_run := by simpa only [Int.natCast_mul] using linear16Run
      linear17_run := by simpa only [Int.natCast_mul] using linear17Run
      c22_run := by simpa only [Int.natCast_mul] using c22Run
      joined_run := joinedRun
      result_valid := joinedStored.1 }
    have width : ((2^(depth+1):Nat):Int) = n := by
      simp [n, h, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
    have recursive : 1 < n := by dsimp [n]; omega
    have half : Int.fdiv n 2 = (h:Int) := by
      simp [n, Int.fdiv_eq_ediv]
    have priorFrame : Extends heap c22Heap := (tick_preserves heap).trans (a11Frame.trans (a12Frame.trans (a21Frame.trans (a22Frame.trans (b11Frame.trans (b12Frame.trans (b21Frame.trans (b22Frame.trans (linear1Frame.trans (p1Frame.trans (linear2Frame.trans (p2Frame.trans (linear3Frame.trans (p3Frame.trans (linear4Frame.trans (p4Frame.trans (linear5Frame.trans (linear6Frame.trans (p5Frame.trans (linear7Frame.trans (linear8Frame.trans (p6Frame.trans (linear9Frame.trans (linear10Frame.trans (p7Frame.trans (linear11Frame.trans (linear12Frame.trans (c11Frame.trans (c12Frame.trans (c21Frame.trans (linear16Frame.trans (linear17Frame.trans (c22Frame)))))))))))))))))))))))))))))))))
    refine ⟨joinedHeap, joinedRef, ?_, priorFrame.trans joinedFrame, ?_, ?_,
      Nat.le_trans priorFrame.nextCollection joinedFresh, ?_⟩
    · rw [width]
      exact recursive_summary heap a b n h sa.1 sb.1 recursive half plan
    · exact joinedStored
    · intro name
      rw [joinedClocks name, c22Clocks name, linear17Clocks name, linear16Clocks name, c21Clocks name, c12Clocks name, c11Clocks name, linear12Clocks name, linear11Clocks name, p7Clocks name, linear10Clocks name, linear9Clocks name, p6Clocks name, linear8Clocks name, linear7Clocks name, p5Clocks name, linear6Clocks name, linear5Clocks name, p4Clocks name, linear4Clocks name, p3Clocks name, linear3Clocks name, p2Clocks name, linear2Clocks name, p1Clocks name, linear1Clocks name, b22Clocks name, b21Clocks name, b12Clocks name, b11Clocks name, a22Clocks name, a21Clocks name, a12Clocks name, a11Clocks name]
      rw [costs_step]
      simp only [Clocks.single, Heap.tick]
      by_cases calls : name = "calls" <;> by_cases linear : name = "linear_cells" <;>
        by_cases copied : name = "copied_cells" <;> simp [calls, linear, copied, h] <;> omega
    · have sameSize : 2^ (depth+1) = 2*h := by simp [h,Nat.pow_succ,Nat.mul_comm]
      rw [sameSize]
      exact joinedRows.before_mono priorFrame.nextRef

/-- Termination, exact value, preservation and clocks, with a fresh outer array. -/
theorem strassen_summary_fresh (depth : Nat) (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, strassen.Call heap (a,b,((2^depth:Nat):Int)) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.strassenValue depth av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + costs depth name) ∧ heap.nextCollection ≤ result := by
  obtain ⟨after,result,run,frame,stored,clocks,fresh,_⟩ := strassen_summary_rows depth heap a b av bv sa sb
  exact ⟨after,result,run,frame,stored,clocks,fresh⟩

/-- Every source invocation terminates on a power-of-two dimension, returns the
    mathematically specified Strassen value, preserves all earlier arrays, and
    charges these exact counters in the same execution. -/
theorem strassen_summary (depth : Nat) (heap : Heap) (a b : CollectionRef) (av bv : Values)
    (sa : Stored heap a av) (sb : Stored heap b bv) :
    ∃ after result, strassen.Call heap (a,b,((2^depth:Nat):Int)) after result ∧
      Extends heap after ∧ Stored after result (StrassenValues.strassenValue depth av bv) ∧
      (∀ name, after.clocks name = heap.clocks name + costs depth name) := by
  obtain ⟨after, result, run, frame, stored, clocks, _⟩ :=
    strassen_summary_fresh depth heap a b av bv sa sb
  exact ⟨after, result, run, frame, stored, clocks⟩

end MatrixStrassenExecution
