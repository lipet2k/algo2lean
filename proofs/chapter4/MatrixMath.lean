import Std

/-!
Finite integer-matrix algebra and arithmetic-operation recurrences for CLRS 4.

These are mathematical lemmas. An application to an Algo2Lean source program
must additionally prove that the generated execution relation implements these
operations and charges these recurrences; this file alone makes no such claim.
Matrices are unbounded mathematical functions; `mul n` reads the first n inner
coordinates. In applications n is the finite matrix dimension.
-/
namespace Chapter4Math
abbrev Vector := Nat → Int
def dot : Nat → Vector → Vector → Int
  | 0, _, _ => 0
  | n + 1, a, b => dot n a b + a n * b n

theorem dot_add_left (n : Nat) (a b c : Vector) :
    dot n (fun i => a i + b i) c = dot n a c + dot n b c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.add_mul]; omega

theorem dot_sub_left (n : Nat) (a b c : Vector) :
    dot n (fun i => a i - b i) c = dot n a c - dot n b c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.sub_mul]; omega

theorem dot_add_right (n : Nat) (a b c : Vector) :
    dot n a (fun i => b i + c i) = dot n a b + dot n a c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.mul_add]; omega

theorem dot_sub_right (n : Nat) (a b c : Vector) :
    dot n a (fun i => b i - c i) = dot n a b - dot n a c := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp only [dot, ih, Int.mul_sub]; omega

theorem strassen_identity (n : Nat) (a11 a12 a21 a22 b11 b12 b21 b22 : Vector) :
    let p1 := dot n a11 (fun i => b12 i - b22 i)
    let p2 := dot n (fun i => a11 i + a12 i) b22
    let p3 := dot n (fun i => a21 i + a22 i) b11
    let p4 := dot n a22 (fun i => b21 i - b11 i)
    let p5 := dot n (fun i => a11 i + a22 i) (fun i => b11 i + b22 i)
    let p6 := dot n (fun i => a12 i - a22 i) (fun i => b21 i + b22 i)
    let p7 := dot n (fun i => a11 i - a21 i) (fun i => b11 i + b12 i)
    p5 + p4 - p2 + p6 = dot n a11 b11 + dot n a12 b21 ∧
    p1 + p2 = dot n a11 b12 + dot n a12 b22 ∧
    p3 + p4 = dot n a21 b11 + dot n a22 b21 ∧
    p5 + p1 - p3 - p7 = dot n a21 b12 + dot n a22 b22 := by
  dsimp
  simp only [dot_add_left, dot_add_right, dot_sub_left, dot_sub_right]
  omega

end Chapter4Math

namespace Chapter4Math

/-- Split a dot product at an arbitrary finite inner coordinate. -/
theorem dot_append (n m : Nat) (a b : Vector) :
    dot (n + m) a b = dot n a b +
      dot m (fun k => a (n + k)) (fun k => b (n + k)) := by
  induction m with
  | zero => simp [dot]
  | succ m ih =>
    change dot (n + m) a b + a (n + m) * b (n + m) =
      dot n a b + (dot m (fun k => a (n + k)) (fun k => b (n + k)) +
        a (n + m) * b (n + m))
    rw [ih]
    omega

abbrev Matrix := Nat → Nat → Int

def add (a b : Matrix) : Matrix := fun i j => a i j + b i j

def sub (a b : Matrix) : Matrix := fun i j => a i j - b i j

def mul (n : Nat) (a b : Matrix) : Matrix :=
  fun i j => dot n (a i) (fun k => b k j)

/-- A block is a view; it does not copy or mutate its source matrix. -/
def block (a : Matrix) (row col : Nat) : Matrix := fun i j => a (row + i) (col + j)

theorem mul_add_left (n : Nat) (a b c : Matrix) :
    mul n (add a b) c = add (mul n a c) (mul n b c) := by
  funext i j
  exact dot_add_left n (a i) (b i) (fun k => c k j)

theorem mul_sub_left (n : Nat) (a b c : Matrix) :
    mul n (sub a b) c = sub (mul n a c) (mul n b c) := by
  funext i j
  exact dot_sub_left n (a i) (b i) (fun k => c k j)

theorem mul_add_right (n : Nat) (a b c : Matrix) :
    mul n a (add b c) = add (mul n a b) (mul n a c) := by
  funext i j
  exact dot_add_right n (a i) (fun k => b k j) (fun k => c k j)

theorem mul_sub_right (n : Nat) (a b c : Matrix) :
    mul n a (sub b c) = sub (mul n a b) (mul n a c) := by
  funext i j
  exact dot_sub_right n (a i) (fun k => b k j) (fun k => c k j)

structure Blocks where
  nw : Matrix
  ne : Matrix
  sw : Matrix
  se : Matrix

/-- The four equal-sized square blocks of a matrix with dimension `2*n`. -/
def quadrants (n : Nat) (a : Matrix) : Blocks :=
  ⟨block a 0 0, block a 0 n, block a n 0, block a n n⟩

/-- Ordinary multiplication written with eight block products. -/
def blockMul (n : Nat) (a b : Blocks) : Blocks :=
  ⟨add (mul n a.nw b.nw) (mul n a.ne b.sw),
   add (mul n a.nw b.ne) (mul n a.ne b.se),
   add (mul n a.sw b.nw) (mul n a.se b.sw),
   add (mul n a.sw b.ne) (mul n a.se b.se)⟩

/-- The seven products and eight combining additions/subtractions in CLRS. -/
def strassen (n : Nat) (a b : Blocks) : Blocks :=
  let p1 := mul n a.nw (sub b.ne b.se)
  let p2 := mul n (add a.nw a.ne) b.se
  let p3 := mul n (add a.sw a.se) b.nw
  let p4 := mul n a.se (sub b.sw b.nw)
  let p5 := mul n (add a.nw a.se) (add b.nw b.se)
  let p6 := mul n (sub a.ne a.se) (add b.sw b.se)
  let p7 := mul n (sub a.nw a.sw) (add b.nw b.ne)
  ⟨add (sub (add p5 p4) p2) p6, add p1 p2,
    add p3 p4, sub (sub (add p5 p1) p3) p7⟩

/-- Seven products reproduce all four quadrants of the usual eight products.
This identity uses distributivity only and does not assume commutative blocks. -/
theorem strassen_eq_blockMul (n : Nat) (a b : Blocks) :
    strassen n a b = blockMul n a b := by
  simp only [strassen, blockMul, mul_add_left, mul_add_right, mul_sub_left, mul_sub_right]
  congr 1 <;> funext i j <;> simp only [add, sub] <;> omega

/-- Splitting the inner product commutes with taking any output block. -/
theorem block_mul (n row col : Nat) (a b : Matrix) :
    block (mul (n + n) a b) row col =
      add (mul n (block a row 0) (block b 0 col))
          (mul n (block a row n) (block b n col)) := by
  funext i j
  change dot (n + n) (a (row + i)) (fun k => b k (col + j)) =
    dot n (fun k => a (row + i) (0 + k)) (fun k => b (0 + k) (col + j)) +
    dot n (fun k => a (row + i) (n + k)) (fun k => b (n + k) (col + j))
  simpa only [Nat.zero_add] using
    dot_append n n (fun k => a (row + i) k) (fun k => b k (col + j))

/-- Ordinary finite matrix multiplication obeys the block multiplication rule. -/
theorem quadrants_mul (n : Nat) (a b : Matrix) :
    quadrants n (mul (n + n) a b) = blockMul n (quadrants n a) (quadrants n b) := by
  simp only [quadrants, blockMul, block_mul]

/-- The Strassen formulas agree with every entry of all four product blocks. -/
theorem strassen_quadrants (n : Nat) (a b : Matrix) :
    strassen n (quadrants n a) (quadrants n b) = quadrants n (mul (n + n) a b) := by
  rw [strassen_eq_blockMul, quadrants_mul]

/-- At dimension 2^k the classical cubic bound is exactly 8^k. -/
theorem cubic_power_two (k : Nat) : ((2 : Nat)^k)^3 = 8^k := by
  rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]

end Chapter4Math

namespace Chapter4Math

/-- The sum of squared half-dimensions over the Strassen recursion tree. -/
def strassenOverhead : Nat → Nat
  | 0 => 0
  | k + 1 => 7 * strassenOverhead k + 4^k

theorem strassenOverhead_exact (k : Nat) :
    3 * strassenOverhead k + 4^k = 7^k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [strassenOverhead, Nat.pow_succ]; omega

theorem strassenOverhead_le (k : Nat) : strassenOverhead k ≤ 7^k := by
  have equation := strassenOverhead_exact k
  have nonnegative : 0 ≤ (4:Nat)^k := Nat.zero_le _
  omega

/-- `c` cell operations per half-dimension squared, plus scalar leaf products
at the leaves. Instantiating c=30 counts 8 block copies, 18 arithmetic passes,
and 4 output block copies per internal node. -/
def strassenCellWork (c k : Nat) : Nat := 7^k + c * strassenOverhead k

@[simp] theorem strassenCellWork_zero (c : Nat) : strassenCellWork c 0 = 1 := by
  simp [strassenCellWork, strassenOverhead]

theorem strassenCellWork_step (c k : Nat) :
    strassenCellWork c (k+1) = 7 * strassenCellWork c k + c * 4^k := by
  simp only [strassenCellWork, strassenOverhead, Nat.pow_succ, Nat.mul_add]
  ac_rfl

theorem strassenCellWork_exact (c k : Nat) :
    3 * strassenCellWork c k + c * 4^k = (c+3) * 7^k := by
  have equation := congrArg (fun x => c * x) (strassenOverhead_exact k)
  simp only [Nat.mul_add] at equation
  simp only [strassenCellWork, Nat.mul_add, Nat.add_mul]
  rw [← Nat.mul_assoc 3 c, Nat.mul_comm 3 c, Nat.mul_assoc]
  omega

/-- Explicit constants are the natural-depth form of Θ(7^k). -/
theorem strassenCellWork_theta (c k : Nat) :
    7^k ≤ strassenCellWork c k ∧ strassenCellWork c k ≤ (c+1) * 7^k := by
  have bound := Nat.mul_le_mul_left c (strassenOverhead_le k)
  simp only [strassenCellWork, Nat.add_mul, Nat.one_mul]
  omega

/-- Number of nodes (including leaves) in an arity-ary full recursion tree. -/
def calls (arity : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => 1 + arity * calls arity k

theorem calls7_exact (k : Nat) : 6 * calls 7 k + 1 = 7^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih => simp only [calls, Nat.pow_succ] at *; omega

theorem calls8_exact (k : Nat) : 7 * calls 8 k + 1 = 8^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih => simp only [calls, Nat.pow_succ] at *; omega

theorem calls7_bound (k : Nat) : calls 7 k ≤ 2 * 7^k := by
  have equation := calls7_exact k
  simp only [Nat.pow_succ] at equation
  omega

theorem calls8_bound (k : Nat) : calls 8 k ≤ 2 * 8^k := by
  have equation := calls8_exact k
  simp only [Nat.pow_succ] at equation
  omega

/-- Count the function-entry clock in addition to all copying and arithmetic
cells. This covers the c=30 implementation using at most 33*7^k charged work. -/
theorem strassen_total_theta (c k : Nat) :
    7^k ≤ strassenCellWork c k + calls 7 k ∧
    strassenCellWork c k + calls 7 k ≤ (c+3)*7^k := by
  obtain ⟨lower, upper⟩ := strassenCellWork_theta c k
  have callsBound := calls7_bound k
  simp only [Nat.add_mul, Nat.one_mul] at upper ⊢
  omega

/-- Accumulating into C uses exactly one scalar multiplication per leaf.
Adding the recursion-entry clock preserves the cubic asymptotic bound. -/
theorem recursive_total_theta (k : Nat) :
    ((2:Nat)^k)^3 ≤ 8^k + calls 8 k ∧
    8^k + calls 8 k ≤ 3*((2:Nat)^k)^3 := by
  rw [cubic_power_two]
  have bound := calls8_bound k
  omega

end Chapter4Math

namespace Chapter4Math

/-- Only the finite inner coordinates matter to a dot product. -/
theorem dot_congr (n : Nat) (a b c d : Vector)
    (left : ∀ k, k < n → a k = c k)
    (right : ∀ k, k < n → b k = d k) : dot n a b = dot n c d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dot, left n (by omega), right n (by omega)]
    rw [ih (fun k hk => left k (by omega)) (fun k hk => right k (by omega))]

/-- Entrywise multiplication respects bounded equality of the input row/column. -/
theorem mul_congr (n : Nat) (a b c d : Matrix) (i j : Nat)
    (left : ∀ k, k < n → a i k = c i k)
    (right : ∀ k, k < n → b k j = d k j) : mul n a b i j = mul n c d i j :=
  dot_congr n _ _ _ _ left right

end Chapter4Math
