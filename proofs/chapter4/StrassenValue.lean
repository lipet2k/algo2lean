import MatrixMath

open Chapter4Math
namespace StrassenValues
abbrev Seq := Int → Int

/-- Pointwise addition/subtraction on a finite flat prefix. -/
def linearValues (count : Nat) (sign : Int) (a b : Seq) : Seq := fun index =>
  if 0 ≤ index ∧ index < (count : Int) then a index + sign * b index else 0

/-- Copy a square block into a fresh row-major matrix. -/
def quadrantValues (n h row col : Int) (a : Seq) : Seq := fun index =>
  if 0 ≤ index ∧ index < h*h then a ((row + index / h)*n + col + index % h) else 0

/-- Place four flat blocks into the corresponding quadrants. -/
def joinValues (h : Int) (a b c d : Seq) : Seq := fun index =>
  let n := 2*h
  let row := index / n
  let col := index % n
  if 0 ≤ index ∧ index < n*n then
    if row < h then
      if col < h then a (row*h+col) else b (row*h+(col-h))
    else
      if col < h then c ((row-h)*h+col) else d ((row-h)*h+(col-h))
  else 0

/-- Finite matrix entries represented by the first n*n flat sequence entries. -/
def Rep (n : Nat) (a : Seq) (A : Matrix) : Prop :=
  ∀ i j, i < n → j < n → a ((i*n+j : Nat) : Int) = A i j

/-- Pure value returned by the seven recursive products in the source. -/
def strassenValue : Nat → Seq → Seq → Seq
  | 0, a, b => fun index => if index = 0 then a 0 * b 0 else 0
  | depth+1, a, b =>
    let h : Nat := 2^depth
    let n : Int := 2*h
    let a11 := quadrantValues n h 0 0 a
    let a12 := quadrantValues n h 0 h a
    let a21 := quadrantValues n h h 0 a
    let a22 := quadrantValues n h h h a
    let b11 := quadrantValues n h 0 0 b
    let b12 := quadrantValues n h 0 h b
    let b21 := quadrantValues n h h 0 b
    let b22 := quadrantValues n h h h b
    let p1 := strassenValue depth a11 (linearValues (h*h) (-1) b12 b22)
    let p2 := strassenValue depth (linearValues (h*h) 1 a11 a12) b22
    let p3 := strassenValue depth (linearValues (h*h) 1 a21 a22) b11
    let p4 := strassenValue depth a22 (linearValues (h*h) (-1) b21 b11)
    let p5 := strassenValue depth (linearValues (h*h) 1 a11 a22) (linearValues (h*h) 1 b11 b22)
    let p6 := strassenValue depth (linearValues (h*h) (-1) a12 a22) (linearValues (h*h) 1 b21 b22)
    let p7 := strassenValue depth (linearValues (h*h) (-1) a11 a21) (linearValues (h*h) 1 b11 b12)
    let c11 := linearValues (h*h) 1 (linearValues (h*h) (-1) (linearValues (h*h) 1 p5 p4) p2) p6
    let c12 := linearValues (h*h) 1 p1 p2
    let c21 := linearValues (h*h) 1 p3 p4
    let c22 := linearValues (h*h) (-1) (linearValues (h*h) (-1) (linearValues (h*h) 1 p5 p1) p3) p7
    joinValues h c11 c12 c21 c22

/-- Every row-major coordinate lies in the finite square prefix. -/
theorem flat_bound (n i j : Nat) (hi : i < n) (hj : j < n) : i*n+j < n*n := by
  have bound := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
  simp only [Nat.succ_mul] at bound
  omega

/-- Dividing a row-major address recovers its row and column. -/
theorem flat_coordinates (n i j : Nat) (positive : 0 < n) (hj : j < n) :
    ((i*n+j : Nat) : Int) / (n : Int) = (i : Int) ∧
    ((i*n+j : Nat) : Int) % (n : Int) = (j : Int) := by
  have nonzero : (n : Int) ≠ 0 := by omega
  have jq : (j : Int) / (n : Int) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have jr : (j : Int) % (n : Int) = (j : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  simp [Int.natCast_add, Int.natCast_mul, Int.mul_add_ediv_right _ _ nonzero, jq, jr,
    Int.add_emod]

/-- Linear combinations preserve the matrix representation. -/
theorem linear_rep (n : Nat) (sign : Int) (a b : Seq) (A B : Matrix)
    (ra : Rep n a A) (rb : Rep n b B) :
    Rep n (linearValues (n*n) sign a b) (fun i j => A i j + sign * B i j) := by
  intro i j hi hj
  have bound := flat_bound n i j hi hj
  simp only [linearValues]
  rw [if_pos (by constructor <;> omega), ra i j hi hj, rb i j hi hj]

theorem add_rep {n : Nat} {a b : Seq} {A B : Matrix}
    (ra : Rep n a A) (rb : Rep n b B) :
    Rep n (linearValues (n*n) 1 a b) (add A B) := by
  simpa [add] using! linear_rep n 1 a b A B ra rb

theorem sub_rep {n : Nat} {a b : Seq} {A B : Matrix}
    (ra : Rep n a A) (rb : Rep n b B) :
    Rep n (linearValues (n*n) (-1) a b) (sub A B) := by
  simpa [sub, Int.sub_eq_add_neg] using! linear_rep n (-1) a b A B ra rb

/-- Taking a quadrant preserves every entry of its mathematical block. -/
theorem quadrant_rep (n h row col : Nat) (a : Seq) (A : Matrix)
    (positive : 0 < h) (rbound : row+h ≤ n) (cbound : col+h ≤ n) (ra : Rep n a A) :
    Rep h (quadrantValues n h row col a) (block A row col) := by
  intro i j hi hj
  have bound := flat_bound h i j hi hj
  obtain ⟨quotient, remainder⟩ := flat_coordinates h i j positive hj
  have hr : row+i < n := by omega
  have hc : col+j < n := by omega
  simp only [quadrantValues]
  rw [if_pos (by constructor <;> omega), quotient, remainder]
  simpa [block, Int.natCast_add, Int.natCast_mul, Int.add_assoc] using ra (row+i) (col+j) hr hc



/-- Joining representations of the four mathematical quadrants recovers M. -/
theorem join_rep (h : Nat) (a b c d : Seq) (M : Matrix) (positive : 0 < h)
    (ra : Rep h a (block M 0 0)) (rb : Rep h b (block M 0 h))
    (rc : Rep h c (block M h 0)) (rd : Rep h d (block M h h)) :
    Rep (h+h) (joinValues h a b c d) M := by
  intro i j hi hj
  have bound := flat_bound (h+h) i j hi hj
  obtain ⟨quotient, remainder⟩ := flat_coordinates (h+h) i j (by omega) hj
  have width : ((h+h:Nat):Int) = 2*(h:Int) := by omega
  rw [width] at quotient remainder
  have boundInt : ((i*(h+h)+j:Nat):Int) < (2*(h:Int))*(2*h) := by
    have castBound : ((i*(h+h)+j:Nat):Int) < (((h+h)*(h+h):Nat):Int) := by omega
    simpa only [Int.natCast_mul, width] using castBound
  simp only [joinValues]
  rw [if_pos ⟨by omega, boundInt⟩, quotient, remainder]
  by_cases rowLow : i < h
  · rw [if_pos (show (i:Int) < h by omega)]
    by_cases colLow : j < h
    · rw [if_pos (show (j:Int) < h by omega)]
      simpa [block, Int.natCast_add, Int.natCast_mul] using ra i j rowLow colLow
    · rw [if_neg (show ¬(j:Int) < h by omega)]
      have hle : h ≤ j := by omega
      simpa [block, Nat.add_sub_of_le hle, Int.natCast_add, Int.natCast_mul,
        Int.natCast_sub hle] using rb i (j-h) rowLow (by omega)
  · rw [if_neg (show ¬(i:Int) < h by omega)]
    have hleI : h ≤ i := by omega
    by_cases colLow : j < h
    · rw [if_pos (show (j:Int) < h by omega)]
      simpa [block, Nat.add_sub_of_le hleI, Int.natCast_add, Int.natCast_mul,
        Int.natCast_sub hleI] using rc (i-h) j (by omega) colLow
    · rw [if_neg (show ¬(j:Int) < h by omega)]
      have hleJ : h ≤ j := by omega
      simpa [block, Nat.add_sub_of_le hleI, Nat.add_sub_of_le hleJ,
        Int.natCast_add, Int.natCast_mul, Int.natCast_sub hleI, Int.natCast_sub hleJ]
        using rd (i-h) (j-h) (by omega) (by omega)



/-- The recursive seven-product program has the ordinary matrix product value
    for every finite power-of-two dimension and arbitrary integer entries. -/
theorem strassen_correct (depth : Nat) (a b : Seq) (A B : Matrix)
    (ra : Rep (2^depth) a A) (rb : Rep (2^depth) b B) :
    Rep (2^depth) (strassenValue depth a b) (mul (2^depth) A B) := by
  induction depth generalizing a b A B with
  | zero =>
    intro i j hi hj
    have izero : i = 0 := by have : i < 1 := hi; omega
    have jzero : j = 0 := by have : j < 1 := hj; omega
    subst i; subst j
    have aa := ra 0 0 (by decide) (by decide)
    have bb := rb 0 0 (by decide) (by decide)
    change a 0 = A 0 0 at aa
    change b 0 = B 0 0 at bb
    simp [strassenValue, mul, dot, aa, bb]
  | succ depth ih =>
    let h : Nat := 2^depth
    have positive : 0 < h := Nat.pow_pos (by decide)
    have width : 2^(depth+1) = h+h := by simp [h, Nat.pow_succ, Nat.mul_two]
    have widthInt : ((h+h:Nat):Int) = 2*(h:Int) := by omega
    rw [width] at ra rb ⊢
    have qa11 := quadrant_rep (h+h) h 0 0 a A positive (by omega) (by omega) ra
    have qa12 := quadrant_rep (h+h) h 0 h a A positive (by omega) (by omega) ra
    have qa21 := quadrant_rep (h+h) h h 0 a A positive (by omega) (by omega) ra
    have qa22 := quadrant_rep (h+h) h h h a A positive (by omega) (by omega) ra
    have qb11 := quadrant_rep (h+h) h 0 0 b B positive (by omega) (by omega) rb
    have qb12 := quadrant_rep (h+h) h 0 h b B positive (by omega) (by omega) rb
    have qb21 := quadrant_rep (h+h) h h 0 b B positive (by omega) (by omega) rb
    have qb22 := quadrant_rep (h+h) h h h b B positive (by omega) (by omega) rb
    rw [widthInt] at qa11 qa12 qa21 qa22 qb11 qb12 qb21 qb22
    have p1 := ih _ _ _ _ qa11 (sub_rep qb12 qb22)
    have p2 := ih _ _ _ _ (add_rep qa11 qa12) qb22
    have p3 := ih _ _ _ _ (add_rep qa21 qa22) qb11
    have p4 := ih _ _ _ _ qa22 (sub_rep qb21 qb11)
    have p5 := ih _ _ _ _ (add_rep qa11 qa22) (add_rep qb11 qb22)
    have p6 := ih _ _ _ _ (sub_rep qa12 qa22) (add_rep qb21 qb22)
    have p7 := ih _ _ _ _ (sub_rep qa11 qa21) (add_rep qb11 qb12)
    have c11 := add_rep (sub_rep (add_rep p5 p4) p2) p6
    have c12 := add_rep p1 p2
    have c21 := add_rep p3 p4
    have c22 := sub_rep (sub_rep (add_rep p5 p1) p3) p7
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).nw at c11
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).ne at c12
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).sw at c21
    change Rep h _ (strassen h (quadrants h A) (quadrants h B)).se at c22
    rw [strassen_quadrants] at c11 c12 c21 c22
    have joined := join_rep h _ _ _ _ (mul (h+h) A B) positive c11 c12 c21 c22
    exact joined

/-- Directly usable entrywise correctness, with the standard finite dot product. -/
theorem strassen_entry (depth : Nat) (a b : Seq) (i j : Nat)
    (hi : i < 2^depth) (hj : j < 2^depth) :
    strassenValue depth a b ((i*(2^depth)+j:Nat):Int) =
      dot (2^depth) (fun k => a ((i*(2^depth)+k:Nat):Int))
        (fun k => b ((k*(2^depth)+j:Nat):Int)) := by
  exact strassen_correct depth a b
    (fun r c => a ((r*(2^depth)+c:Nat):Int))
    (fun r c => b ((r*(2^depth)+c:Nat):Int))
    (by intro r c hr hc; rfl) (by intro r c hr hc; rfl) i j hi hj



/-- All entries outside the finite result matrix are zero. -/
theorem strassen_outside (depth : Nat) (a b : Seq) (index : Int)
    (outside : index < 0 ∨ ((2^depth * 2^depth : Nat):Int) ≤ index) :
    strassenValue depth a b index = 0 := by
  cases depth with
  | zero =>
    have nonzero : index ≠ 0 := by simp only [Nat.pow_zero, Nat.one_mul] at outside; omega
    simp [strassenValue, nonzero]
  | succ depth =>
    change joinValues _ _ _ _ _ index = 0
    have size : ((2^(depth+1) * 2^(depth+1):Nat):Int) =
        (2*((2^depth:Nat):Int))*(2*((2^depth:Nat):Int)) := by
      simp [Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
    rw [size] at outside
    simp only [joinValues]
    rw [if_neg (by omega)]

end StrassenValues
