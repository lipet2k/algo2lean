import Substitution

/-!
Generic finite recursion-tree accounting. Branching factors and child heights
may differ at every node. Work is a mathematical natural-number charge attached
to a call; these theorems do not assume a balanced or fixed-arity call tree.
-/

namespace Chapter4RecursionTree

/-- A call records its input size, its own work, and its ordered recursive calls. -/
inductive Tree where
  | node (size work : Nat) (children : List Tree)

def Tree.rootSize : Tree → Nat
  | .node size _ _ => size

def Tree.rootWork : Tree → Nat
  | .node _ work _ => work

def Tree.totalCost : Tree → Nat
  | .node _ work children => work + (children.map Tree.totalCost).sum

/-- Height counts the root level, so a leaf has height one. -/
def Tree.height : Tree → Nat
  | .node _ _ children => 1 + (children.map Tree.height).foldr max 0

/-- The calls at a specified depth; leaves contribute no calls at later depths. -/
def Tree.frontier : Tree → Nat → List Tree
  | tree, 0 => [tree]
  | .node _ _ children, depth+1 => children.flatMap (fun child => child.frontier depth)

def Tree.levelCost : Tree → Nat → Nat
  | .node _ work _, 0 => work
  | .node _ _ children, depth+1 => (children.map (fun child => child.levelCost depth)).sum

/-- The sum of f(0), ..., f(count-1), with an empty sum at count zero. -/
def sumBelow : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | count+1, f => sumBelow count f + f count

theorem sumBelow_shift (count : Nat) (f : Nat → Nat) :
    sumBelow (count+1) f = f 0 + sumBelow count (fun i => f (i+1)) := by
  induction count with
  | zero => simp [sumBelow]
  | succ count ih => simp only [sumBelow] at ih ⊢; omega

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (pointwise : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have head := pointwise x (by simp)
    have tail := ih (fun y member => pointwise y (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    omega

@[simp] theorem sum_map_zero {α : Type} (xs : List α) : (xs.map (fun _ => (0:Nat))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-- Interchange two finite sums; no convergence assumption is needed. -/
theorem sumBelow_map_sum {α : Type} (count : Nat) (xs : List α) (f : α → Nat → Nat) :
    sumBelow count (fun i => (xs.map (fun x => f x i)).sum) =
      (xs.map (fun x => sumBelow count (f x))).sum := by
  induction count with
  | zero => simp [sumBelow]
  | succ count ih =>
    simp only [sumBelow, ih, sum_map_add]

theorem sumBelow_le (count : Nat) (f g : Nat → Nat)
    (pointwise : ∀ i, i < count → f i ≤ g i) : sumBelow count f ≤ sumBelow count g := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    have head := pointwise count (by omega)
    have tail := ih (fun i hi => pointwise i (by omega))
    simp only [sumBelow]
    omega

theorem sum_map_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Nat) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.map_append, List.sum_append_nat, ih]

/-- A level's work is precisely the sum of the work of calls on its frontier. -/
theorem Tree.levelCost_frontier (tree : Tree) (depth : Nat) :
    tree.levelCost depth = ((tree.frontier depth).map Tree.rootWork).sum := by
  induction depth generalizing tree with
  | zero => cases tree; simp [Tree.levelCost, Tree.frontier, Tree.rootWork]
  | succ depth ih =>
    cases tree with
    | node size work children =>
      simp only [Tree.levelCost, Tree.frontier, sum_map_flatMap]
      congr 1
      apply List.map_congr_left
      intro child _
      exact ih child

theorem le_foldr_max (xs : List Nat) (value : Nat) (member : value ∈ xs) :
    value ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    simp only [List.foldr_cons]
    rcases member with rfl | tail
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

theorem Tree.child_height_lt (size work : Nat) (children : List Tree) (child : Tree)
    (member : child ∈ children) : child.height < (Tree.node size work children).height := by
  have bound := le_foldr_max (children.map Tree.height) child.height (List.mem_map.mpr ⟨child, member, rfl⟩)
  simp only [Tree.height]
  omega

/-- A finite tree has no work beyond its height, even when leaf depths differ. -/
theorem Tree.levelCost_zero (tree : Tree) (depth : Nat) (past : tree.height ≤ depth) :
    tree.levelCost depth = 0 := by
  induction tree using Tree.totalCost.induct generalizing depth with
  | case1 size work children ih =>
    cases depth with
    | zero => simp only [Tree.height] at past; omega
    | succ depth =>
      simp only [Tree.levelCost]
      have zeroes : children.map (fun child => child.levelCost depth) = children.map (fun _ => 0) := by
        apply List.map_congr_left
        intro child member
        exact ih child member depth (by have := Tree.child_height_lt size work children child member; omega)
      rw [zeroes]
      simp

/-- Summing a sufficient number of complete levels gives the total work. -/
theorem Tree.sum_levels (tree : Tree) (levels : Nat) (complete : tree.height ≤ levels) :
    sumBelow levels tree.levelCost = tree.totalCost := by
  induction tree using Tree.totalCost.induct generalizing levels with
  | case1 size work children ih =>
    cases levels with
    | zero => simp only [Tree.height] at complete; omega
    | succ levels =>
      rw [sumBelow_shift]
      simp only [Tree.levelCost, Tree.totalCost, sumBelow_map_sum]
      congr 1
      congr 1
      apply List.map_congr_left
      intro child member
      exact ih child member levels (by have := Tree.child_height_lt size work children child member; omega)

/-- The exact recursion-tree decomposition by levels. -/
theorem Tree.total_eq_levels (tree : Tree) :
    tree.totalCost = sumBelow tree.height tree.levelCost :=
  (tree.sum_levels tree.height (Nat.le_refl _)).symm

/-- A level-by-level upper bound gives a bound for the complete tree. -/
theorem Tree.upper_bound (tree : Tree) (bound : Nat → Nat)
    (perLevel : ∀ level, level < tree.height → tree.levelCost level ≤ bound level) :
    tree.totalCost ≤ sumBelow tree.height bound := by
  rw [tree.total_eq_levels]
  exact sumBelow_le _ _ _ perLevel

/-- Lower bounds add over the same complete levels. -/
theorem Tree.lower_bound (tree : Tree) (bound : Nat → Nat)
    (perLevel : ∀ level, level < tree.height → bound level ≤ tree.levelCost level) :
    sumBelow tree.height bound ≤ tree.totalCost := by
  rw [tree.total_eq_levels]
  exact sumBelow_le _ _ _ perLevel

/-- Work performed by the leaves, retaining their potentially unequal depths. -/
def Tree.leafCost : Tree → Nat
  | .node _ work [] => work
  | .node _ _ children => (children.map Tree.leafCost).sum

def Tree.internalCost : Tree → Nat
  | .node _ _ [] => 0
  | .node _ work children => work + (children.map Tree.internalCost).sum

/-- Work partitions into internal calls and leaves without a balance premise. -/
theorem Tree.internal_add_leaf (tree : Tree) :
    tree.internalCost + tree.leafCost = tree.totalCost := by
  induction tree using Tree.totalCost.induct with
  | case1 size work children ih =>
    cases children with
    | nil => simp [Tree.internalCost, Tree.leafCost, Tree.totalCost]
    | cons child children =>
      have childrenEqual : ((child::children).map (fun t => t.internalCost + t.leafCost)).sum =
          ((child::children).map Tree.totalCost).sum := by
        congr 1
        apply List.map_congr_left
        exact ih
      rw [sum_map_add] at childrenEqual
      simp only [Tree.internalCost, Tree.leafCost, Tree.totalCost]
      omega


/-- A finite tree follows a size recurrence. Base work is explicit; internal
nodes use exactly the prescribed child list, including repeated children. -/
inductive Consistent (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat) : Tree → Prop where
  | leaf (size : Nat) (small : size < cutoff) :
      Consistent children toll base cutoff (.node size (base size) [])
  | branch (size : Nat) (forest : List Tree) (large : cutoff ≤ size)
      (sizes : forest.map Tree.rootSize = children size)
      (subtrees : ∀ tree ∈ forest, Consistent children toll base cutoff tree) :
      Consistent children toll base cutoff (.node size (toll size) forest)

/-- Every consistent finite tree computes the cost specified by the recurrence.
Different shapes at different input sizes and unequal subtree heights are allowed. -/
theorem consistent_total (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (cost : Nat → Nat) (baseCost : ∀ n, n < cutoff → cost n = base n)
    (recurrence : Chapter4Substitution.ExactRecurrence children toll cutoff cost)
    (tree : Tree) (consistent : Consistent children toll base cutoff tree) :
    tree.totalCost = cost tree.rootSize := by
  induction tree using Tree.totalCost.induct with
  | case1 size work forest ih =>
    cases consistent with
    | leaf size small =>
      simpa [Tree.totalCost, Tree.rootSize] using (baseCost size small).symm
    | branch size forest large sizes subtrees =>
      simp only [Tree.totalCost, Tree.rootSize]
      rw [recurrence size large, ← sizes]
      simp only [Chapter4Substitution.childSum, List.map_map]
      congr 1
      congr 1
      apply List.map_congr_left
      intro tree member
      exact ih tree member (subtrees tree member)

/-- Assemble a forest while retaining the exact ordered list of root sizes. -/
theorem forest_exists (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (sizes : List Nat)
    (available : ∀ n ∈ sizes, ∃ tree, tree.rootSize = n ∧ Consistent children toll base cutoff tree) :
    ∃ forest : List Tree, forest.map Tree.rootSize = sizes ∧
      ∀ tree ∈ forest, Consistent children toll base cutoff tree := by
  induction sizes with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons size sizes ih =>
    obtain ⟨head, headSize, headProof⟩ := available size (by simp)
    obtain ⟨tail, tailSizes, tailProof⟩ := ih (fun n member => available n (by simp [member]))
    refine ⟨head::tail, ?_, ?_⟩
    · simp [headSize, tailSizes]
    · intro tree member
      rcases List.mem_cons.mp member with rfl | later
      · exact headProof
      · exact tailProof tree later

/-- Strictly decreasing natural child sizes guarantee a finite recursion tree
for every input size, even with size-dependent arity and unequal splits. -/
theorem consistent_exists (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (smaller : Chapter4Substitution.SmallerChildren children cutoff) (size : Nat) :
    ∃ tree, tree.rootSize = size ∧ Consistent children toll base cutoff tree := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    by_cases small : size < cutoff
    · exact ⟨.node size (base size) [], rfl, .leaf size small⟩
    · have large : cutoff ≤ size := by omega
      obtain ⟨forest, sizes, subtrees⟩ := forest_exists children toll base cutoff (children size)
        (fun child member => ih child (smaller size large child member))
      exact ⟨.node size (toll size) forest, rfl, .branch size forest large sizes subtrees⟩

/-- A recurrence cost is exactly the sum of work on a finite tree's levels. -/
theorem recurrence_tree_accounting (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat)
    (cost : Nat → Nat) (smaller : Chapter4Substitution.SmallerChildren children cutoff)
    (baseCost : ∀ n, n < cutoff → cost n = base n)
    (recurrence : Chapter4Substitution.ExactRecurrence children toll cutoff cost) (size : Nat) :
    ∃ tree, tree.rootSize = size ∧ Consistent children toll base cutoff tree ∧
      cost size = tree.totalCost ∧ cost size = sumBelow tree.height tree.levelCost := by
  obtain ⟨tree, root, consistent⟩ := consistent_exists children toll base cutoff smaller size
  have exactCost := consistent_total children toll base cutoff cost baseCost recurrence tree consistent
  rw [root] at exactCost
  exact ⟨tree, root, consistent, exactCost.symm, exactCost.symm.trans tree.total_eq_levels⟩

theorem sumBelow_congr (count : Nat) (f g : Nat → Nat)
    (same : ∀ i, i < count → f i = g i) : sumBelow count f = sumBelow count g := by
  apply Nat.le_antisymm
  · exact sumBelow_le _ _ _ (fun i hi => Nat.le_of_eq (same i hi))
  · exact sumBelow_le _ _ _ (fun i hi => Nat.le_of_eq (same i hi).symm)

theorem sumBelow_mul (count multiplier : Nat) (f : Nat → Nat) :
    sumBelow count (fun i => multiplier*f i) = multiplier*sumBelow count f := by
  induction count with
  | zero => simp [sumBelow]
  | succ count ih => simp [sumBelow, ih, Nat.mul_add]

/-- Internal-level contribution to T(k+1)=a*T(k)+g(k), written as an explicit
finite weighted sum. The exponent counts ancestors duplicating that work. -/
def weightedTolls (arity depth : Nat) (toll : Nat → Nat) : Nat :=
  sumBelow depth (fun level => arity^(depth-1-level)*toll level)

@[simp] theorem weightedTolls_zero (arity : Nat) (toll : Nat → Nat) :
    weightedTolls arity 0 toll = 0 := rfl

theorem weightedTolls_step (arity depth : Nat) (toll : Nat → Nat) :
    weightedTolls arity (depth+1) toll = arity*weightedTolls arity depth toll + toll depth := by
  have same : ∀ level, level < depth →
      arity^((depth+1)-1-level)*toll level = arity*(arity^(depth-1-level)*toll level) := by
    intro level bound
    have exponent : (depth+1)-1-level = (depth-1-level)+1 := by omega
    rw [exponent, Nat.pow_succ]
    ac_rfl
  unfold weightedTolls
  rw [sumBelow]
  rw [sumBelow_congr _ _ _ same, sumBelow_mul]
  simp

theorem balanced_formula_step (arity base depth : Nat) (toll : Nat → Nat) :
    arity^(depth+1)*base + weightedTolls arity (depth+1) toll =
      arity*(arity^depth*base + weightedTolls arity depth toll)+toll depth := by
  rw [weightedTolls_step, Nat.pow_succ]
  simp only [Nat.mul_add]
  ac_rfl

/-- Exact recursion-tree unrolling for every arity, base cost, and toll sequence.
No polynomial form, positivity, or asymptotic regularity of the toll is needed. -/
theorem balanced_unroll (arity : Nat) (cost toll : Nat → Nat)
    (recurrence : ∀ depth, cost (depth+1) = arity*cost depth+toll depth) (depth : Nat) :
    cost depth = arity^depth*cost 0 + weightedTolls arity depth toll := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    rw [recurrence, ih, balanced_formula_step]

/-- The exact unrolling also bounds any cost satisfying an upper recurrence. -/
theorem balanced_upper (arity : Nat) (cost toll : Nat → Nat)
    (recurrence : ∀ depth, cost (depth+1) ≤ arity*cost depth+toll depth) (depth : Nat) :
    cost depth ≤ arity^depth*cost 0 + weightedTolls arity depth toll := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    have next := recurrence depth
    have bound := Nat.mul_le_mul_left arity ih
    rw [balanced_formula_step]
    exact Nat.le_trans next (Nat.add_le_add_right bound _)

/-- Matching lower recurrence inequalities retain every leaf contribution. -/
theorem balanced_lower (arity : Nat) (cost toll : Nat → Nat)
    (recurrence : ∀ depth, arity*cost depth+toll depth ≤ cost (depth+1)) (depth : Nat) :
    arity^depth*cost 0 + weightedTolls arity depth toll ≤ cost depth := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    have next := recurrence depth
    have bound := Nat.mul_le_mul_left arity ih
    rw [balanced_formula_step]
    exact Nat.le_trans (Nat.add_le_add_right bound _) next

/-- A literal equal-branching recursion tree, including the arity-zero case. -/
def balancedTree (arity base : Nat) (toll : Nat → Nat) : Nat → Tree
  | 0 => .node 0 base []
  | depth+1 => .node (depth+1) (toll depth) (List.replicate arity (balancedTree arity base toll depth))

theorem balancedTree_total (arity base : Nat) (toll : Nat → Nat) (depth : Nat) :
    (balancedTree arity base toll depth).totalCost =
      arity^depth*base + weightedTolls arity depth toll := by
  have expansion := balanced_unroll arity (fun d => (balancedTree arity base toll d).totalCost) toll
    (fun d => by simp [balancedTree, Tree.totalCost, Nat.add_comm]) depth
  simpa [balancedTree, Tree.totalCost] using expansion

end Chapter4RecursionTree
