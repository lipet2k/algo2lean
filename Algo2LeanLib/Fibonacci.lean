import Std

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Mathematical building blocks for Fibonacci heaps.

The tree lemmas use children in reverse link order (newest first). The rank
invariant records the consequence of equal-degree links and cutting a nonroot
when it loses its second child. The accounting relations describe actual
root/mark changes; they do not assume their amortized bounds.

This module is independent of any generated program. A compiled implementation
must separately establish the rank invariant and realize the accounting steps.
References: Fredman and Tarjan, JACM 34(3), 1987; David Karger's MIT 6.854 notes,
https://courses.csail.mit.edu/6.854/21/Notes/n01-fibonacci.html.
-/

namespace Algo2Lean.Fibonacci

/-- `minimumNodes degree` is the Fibonacci number F(degree + 2). -/
def minimumNodes : Nat → Nat
  | 0 => 1
  | 1 => 2
  | degree + 2 => minimumNodes (degree + 1) + minimumNodes degree

@[simp] theorem minimumNodes_zero : minimumNodes 0 = 1 := rfl
@[simp] theorem minimumNodes_one : minimumNodes 1 = 2 := rfl

theorem minimumNodes_step (degree : Nat) :
    minimumNodes (degree + 1) = minimumNodes degree + minimumNodes (degree - 1) := by
  cases degree with
  | zero => rfl
  | succ degree => simp only [Nat.add_sub_cancel, minimumNodes]

theorem minimumNodes_mono_step (degree : Nat) : minimumNodes degree ≤ minimumNodes (degree + 1) := by
  rw [minimumNodes_step]
  omega

theorem minimumNodes_mono {first second : Nat} (ordered : first ≤ second) :
    minimumNodes first ≤ minimumNodes second := by
  induction ordered with
  | refl => exact Nat.le_refl _
  | @step second ordered ih => exact Nat.le_trans ih (minimumNodes_mono_step second)

/-- Two rank increases at least double the minimum subtree size. -/
theorem minimumNodes_exponential (degree : Nat) : 2 ^ (degree / 2) ≤ minimumNodes degree := by
  induction degree using Nat.strongRecOn with
  | ind degree ih =>
    cases degree with
    | zero => decide
    | succ degree =>
      cases degree with
      | zero => decide
      | succ degree =>
        have smaller := ih degree (by omega)
        have monotone := minimumNodes_mono_step degree
        have half : (degree + 1 + 1) / 2 = degree / 2 + 1 := by omega
        simp only [half, Nat.pow_succ, minimumNodes]
        omega

/-- An exponential subtree bound gives a binary-logarithmic degree bound,
    avoiding real numbers or an approximation to the golden ratio. -/
theorem degree_logarithmic {degree nodes : Nat} (subtreeBound : minimumNodes degree ≤ nodes) :
    degree ≤ 2 * nodes.log2 + 1 := by
  have exponential := Nat.le_trans (minimumNodes_exponential degree) subtreeBound
  have positive : nodes ≠ 0 := by
    have powerPositive : 0 < (2 : Nat) ^ (degree / 2) := Nat.pow_pos (by decide)
    omega
  have half := (Nat.le_log2 positive).mpr exponential
  omega

/-- Tree shape only; keys and addresses do not affect the rank argument. -/
inductive Tree where
  | node : List Tree → Tree

def Tree.degree : Tree → Nat
  | .node children => children.length

def Tree.nodes : Tree → Nat
  | .node children => 1 + (children.map Tree.nodes).sum

/-- Each child's degree is at least its number of older siblings minus one.
    Newest-first order models equal-degree links followed by at most one child loss. -/
def RankOrder : List Tree → Prop
  | [] => True
  | child :: older => older.length ≤ child.degree + 1 ∧ RankOrder older

inductive Tree.Ranked : Tree → Prop where
  | node {children : List Tree} : RankOrder children →
    (∀ child ∈ children, Tree.Ranked child) → Tree.Ranked (.node children)

/-- The children's induction bounds and link order force the parent's
    Fibonacci bound; no subtree-size conclusion is assumed for the parent. -/
theorem ranked_children_bound (children : List Tree)
    (ordered : RankOrder children)
    (childrenBound : ∀ child ∈ children, minimumNodes child.degree ≤ child.nodes) :
    minimumNodes children.length ≤ 1 + (children.map Tree.nodes).sum := by
  induction children with
  | nil => simp
  | cons child older ih =>
    have rest := ih ordered.2 (fun tree member => childrenBound tree (by simp [member]))
    have head := childrenBound child (by simp)
    have degreeBound : older.length - 1 ≤ child.degree := by have := ordered.1; omega
    have headMinimum := minimumNodes_mono degreeBound
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    rw [minimumNodes_step]
    omega

/-- Every tree satisfying the local rank invariant has exponentially many
    nodes in its degree, with the sharper Fibonacci lower bound. -/
theorem Tree.Ranked.subtree_bound {tree : Tree} (ranked : tree.Ranked) :
    minimumNodes tree.degree ≤ tree.nodes := by
  induction ranked with
  | node ordered children ih => simpa only [Tree.degree, Tree.nodes] using ranked_children_bound _ ordered ih

theorem Tree.Ranked.degree_bound {tree : Tree} (ranked : tree.Ranked) :
    tree.degree ≤ 2 * tree.nodes.log2 + 1 :=
  degree_logarithmic ranked.subtree_bound

/-- Enlarging the finite size bound can only enlarge its logarithmic budget. -/
theorem log2_mono {smaller larger : Nat} (bound : smaller ≤ larger) :
    smaller.log2 ≤ larger.log2 := by
  by_cases zero : smaller = 0
  · simp [zero]
  · have positive : larger ≠ 0 := by omega
    exact (Nat.le_log2 positive).mpr (Nat.le_trans (Nat.log2_self_le zero) bound)

/-- One common heap-size bound applies to every represented subtree. -/
theorem Tree.Ranked.degree_bound_of_size {tree : Tree} {heapSize : Nat}
    (ranked : tree.Ranked) (contained : tree.nodes ≤ heapSize) :
    tree.degree ≤ 2 * heapSize.log2 + 1 :=
  degree_logarithmic (Nat.le_trans ranked.subtree_bound contained)

/-- Removing children preserves chronological rank bounds for the survivors. -/
theorem RankOrder.sublist {children kept : List Tree} (ordered : RankOrder children)
    (remaining : kept.Sublist children) : RankOrder kept := by
  induction remaining with
  | slnil => trivial
  | cons child remaining ih => exact ih ordered.2
  | _ child remaining ih =>
    exact ⟨Nat.le_trans remaining.length_le ordered.1, ih ordered.2⟩

def Tree.link (parent child : Tree) : Tree :=
  match parent with
  | .node children => .node (child :: children)

/-- Equal-degree linking preserves the rank invariant and increases degree
    by exactly one, as required by consolidation's bucket collision. -/
theorem Tree.Ranked.link {parent child : Tree} (parentRanked : parent.Ranked)
    (childRanked : child.Ranked) (equalDegree : parent.degree = child.degree) :
    (parent.link child).Ranked := by
  cases parentRanked with
  | @node childList ordered children =>
    apply Tree.Ranked.node
    · refine ⟨?_, ordered⟩
      change _ ≤ child.degree + 1
      change childList.length = child.degree at equalDegree
      omega
    · intro tree member
      simp only [List.mem_cons] at member
      rcases member with rfl | old
      · exact childRanked
      · exact children tree old

@[simp] theorem Tree.link_degree (parent child : Tree) :
    (parent.link child).degree = parent.degree + 1 := by cases parent; rfl

@[simp] theorem Tree.link_nodes (parent child : Tree) :
    (parent.link child).nodes = parent.nodes + child.nodes := by
  cases parent
  simp [Tree.link, Tree.nodes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Cutting some children leaves a valid root tree; parent-history obligations
    for a nonroot are separately discharged by the mark/cascading-cut rule. -/
theorem Tree.Ranked.prune {children kept : List Tree} (ranked : (Tree.node children).Ranked)
    (remaining : kept.Sublist children) : (Tree.node kept).Ranked := by
  cases ranked with
  | node ordered valid =>
    exact .node (ordered.sublist remaining) (fun child member => valid child (remaining.subset member))

/-- Equal-degree linking followed by at most one child loss supplies the
    degree lower bound required by the child's rank clause. -/
theorem rank_from_link_history (olderChildren linkedDegree currentDegree losses : Nat)
    (linkedAfter : olderChildren ≤ linkedDegree)
    (lostAtMostOne : losses ≤ 1) (current : currentDegree + losses = linkedDegree) :
    olderChildren ≤ currentDegree + 1 := by omega

/-- Counts used by the standard Fibonacci-heap potential. Marks count marked
    nonroots; adding a root clears its mark. -/
structure Counts where
  roots : Nat
  marks : Nat
  deriving DecidableEq

def potential (counts : Counts) : Nat := counts.roots + 2 * counts.marks

def scaledPotential (counts : Counts) : Nat := 4 * potential counts

/-- Cascade after a child was cut: stop at a root, mark an unmarked nonroot,
    or cut a marked nonroot and continue at its parent. -/
inductive Cascade : Counts → Counts → Nat → Prop where
  | root (state : Counts) : Cascade state state 0
  | mark (roots marks : Nat) : Cascade ⟨roots, marks⟩ ⟨roots, marks + 1⟩ 0
  | cut {roots marks cuts : Nat} {after : Counts} :
      Cascade ⟨roots + 1, marks⟩ after cuts → Cascade ⟨roots, marks + 1⟩ after (cuts + 1)

/-- Every additional cascading cut pays for itself by clearing its mark. -/
theorem Cascade.amortized {before after : Counts} {cuts : Nat}
    (cascade : Cascade before after cuts) : cuts + potential after ≤ potential before + 2 := by
  induction cascade with
  | root => simp [potential]
  | mark => simp [potential]; omega
  | cut cascade ih => simp only [potential] at *; omega

/-- A decrease either makes no cut, or cuts the requested node (which may or
    may not have been marked) and then follows the cascading-cut rule. -/
inductive Decrease : Counts → Counts → Nat → Prop where
  | unchanged (state : Counts) : Decrease state state 0
  | unmarked {roots marks cuts : Nat} {after : Counts} :
      Cascade ⟨roots + 1, marks⟩ after cuts → Decrease ⟨roots, marks⟩ after (cuts + 1)
  | marked {roots marks cuts : Nat} {after : Counts} :
      Cascade ⟨roots + 1, marks⟩ after cuts → Decrease ⟨roots, marks + 1⟩ after (cuts + 1)

theorem Decrease.amortized {before after : Counts} {cuts : Nat}
    (decrease : Decrease before after cuts) : cuts + potential after ≤ potential before + 4 := by
  cases decrease with
  | unchanged => simp [potential]
  | unmarked cascade => have bound := cascade.amortized; simp only [potential] at *; omega
  | marked cascade => have bound := cascade.amortized; simp only [potential] at *; omega

/-- Four units per cut allow comparisons and pointer-work event counters to
    share one potential. The resulting decrease-key charge is constant. -/
theorem Decrease.work_bound {before after : Counts} {cuts work : Nat}
    (decrease : Decrease before after cuts) (events : work ≤ 4 * cuts + 4) :
    work + scaledPotential after ≤ scaledPotential before + 20 := by
  have accounting := decrease.amortized
  simp only [scaledPotential]
  omega

/-- Inserting an unmarked singleton costs at most two events and deposits
    enough root credit to pay for its eventual consolidation. -/
theorem insertion_work_bound (roots marks work : Nat) (events : work ≤ 2) :
    work + scaledPotential ⟨roots + 1, marks⟩ ≤ scaledPotential ⟨roots, marks⟩ + 6 := by
  simp only [scaledPotential, potential]
  omega

/-- Consolidation repeatedly links two roots into one. Existing roots are
    unmarked, so the operation preserves the number of marked nonroots. -/
inductive Consolidation : Counts → Counts → Nat → Prop where
  | done (state : Counts) : Consolidation state state 0
  | link {roots marks links : Nat} {after : Counts} (remainingRoot : 0 < roots) :
      Consolidation ⟨roots, marks⟩ after links → Consolidation ⟨roots + 1, marks⟩ after (links + 1)

theorem Consolidation.roots_accounted {before after : Counts} {links : Nat}
    (consolidation : Consolidation before after links) : links + after.roots = before.roots := by
  induction consolidation with
  | done => simp
  | link positive rest ih => simp only at *; omega

theorem Consolidation.marks_unchanged {before after : Counts} {links : Nat}
    (consolidation : Consolidation before after links) : after.marks = before.marks := by
  induction consolidation with
  | done => rfl
  | link positive rest ih => exact ih

/-- Explicit event counts for one extraction, before any amortized argument.
    Root scans visit the promoted forest once; links compare their roots;
    rebuilding visits the degree table and compares its surviving roots. -/
structure ExtractEvents where
  rootScans : Nat
  links : Nat
  promotions : Nat
  degreeScans : Nat
  comparisons : Nat

def ExtractEvents.work (events : ExtractEvents) : Nat :=
  1 + events.rootScans + events.links + events.promotions + events.degreeScans + events.comparisons

/-- Consolidation pays for its links using old root credit. Only logarithmically
    many promoted children and surviving degree buckets remain to be charged. -/
theorem extraction_work_bound (before promoted after : Counts) (degree maximumDegree : Nat)
    (events : ExtractEvents)
    (promotedRoots : promoted.roots + 1 = before.roots + degree)
    (clearedMarks : promoted.marks ≤ before.marks)
    (consolidation : Consolidation promoted after events.links)
    (degreeBound : degree ≤ maximumDegree) (finalRoots : after.roots ≤ maximumDegree + 1)
    (scanBound : events.rootScans ≤ promoted.roots)
    (promotionCount : events.promotions = degree)
    (tableBound : events.degreeScans ≤ maximumDegree + 1)
    (comparisonBound : events.comparisons ≤ degree + events.links + after.roots) :
    events.work + scaledPotential after ≤ scaledPotential before + 12 * (maximumDegree + 1) := by
  have roots := consolidation.roots_accounted
  have marks := consolidation.marks_unchanged
  simp only [ExtractEvents.work, scaledPotential, potential]
  omega

/-- No-duplicate degree buckets fit inside the finite range `0..maximum`. -/
theorem distinct_degrees_bound (degrees : List Nat) (maximum : Nat)
    (unique : degrees.Nodup) (bounded : ∀ degree ∈ degrees, degree ≤ maximum) :
    degrees.length ≤ maximum + 1 := by
  have subsetLength : ∀ first second : List Nat, first.Nodup →
      (∀ value ∈ first, value ∈ second) → first.length ≤ second.length := by
    intro first
    induction first with
    | nil => intro second unique contained; simp
    | cons value rest ih =>
      intro second unique contained
      obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
      have member := contained value (by simp)
      have tailBound := ih (second.erase value) restUnique (by
        intro other inRest
        apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
        exact contained other (by simp [inRest]))
      have length := List.length_erase_of_mem member
      have positive := List.length_pos_of_mem member
      simp only [List.length_cons]
      omega
  have bound := subsetLength degrees (List.range (maximum + 1)) unique (by
    intro degree member
    exact List.mem_range.mpr (by have := bounded degree member; omega))
  simpa using bound

/-- After consolidation, one root per degree and the subtree bound imply
    logarithmically many roots. Each subtree may use a common heap-size bound. -/
theorem consolidated_forest_bound (forest : List Tree) (heapSize : Nat)
    (ranked : ∀ tree ∈ forest, tree.Ranked)
    (contained : ∀ tree ∈ forest, tree.nodes ≤ heapSize)
    (uniqueDegrees : (forest.map Tree.degree).Nodup) :
    forest.length ≤ 2 * heapSize.log2 + 2 := by
  have bound := distinct_degrees_bound (forest.map Tree.degree) (2 * heapSize.log2 + 1)
    uniqueDegrees (by
      intro degree member
      obtain ⟨tree, inForest, rfl⟩ := List.mem_map.mp member
      exact (ranked tree inForest).degree_bound_of_size (contained tree inForest))
  simpa only [List.length_map, Nat.add_assoc] using bound

/-- Abstract operation accounting with local, independently checkable events.
    `updates` counts insert/decrease calls; `extractions` counts delete-min calls.
    Extraction requires explicit bounds on the promoted degree, final root count,
    table scans, and comparisons; these are premises of the operation relation. -/
inductive Operation (maximumDegree : Nat) : Counts → Counts → Nat → Nat → Nat → Prop where
  | insert (roots marks work : Nat) (events : work ≤ 2) :
      Operation maximumDegree ⟨roots, marks⟩ ⟨roots + 1, marks⟩ work 1 0
  | decrease {before after : Counts} {cuts work : Nat}
      (cascade : Decrease before after cuts) (events : work ≤ 4 * cuts + 4) :
      Operation maximumDegree before after work 1 0
  | extract (before promoted after : Counts) (degree : Nat) (events : ExtractEvents)
      (promotedRoots : promoted.roots + 1 = before.roots + degree)
      (clearedMarks : promoted.marks ≤ before.marks)
      (consolidation : Consolidation promoted after events.links)
      (degreeBound : degree ≤ maximumDegree) (finalRoots : after.roots ≤ maximumDegree + 1)
      (scanBound : events.rootScans ≤ promoted.roots)
      (promotionCount : events.promotions = degree)
      (tableBound : events.degreeScans ≤ maximumDegree + 1)
      (comparisonBound : events.comparisons ≤ degree + events.links + after.roots) :
      Operation maximumDegree before after events.work 0 1

theorem Operation.amortized {maximumDegree work updates extractions : Nat} {before after : Counts}
    (operation : Operation maximumDegree before after work updates extractions) :
    work + scaledPotential after ≤
      scaledPotential before + 20 * updates + 12 * (maximumDegree + 1) * extractions := by
  cases operation with
  | insert roots marks work events =>
    have bound := insertion_work_bound roots marks work events
    simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
    omega
  | decrease cascade events => simpa using cascade.work_bound events
  | extract before promoted after degree events roots marks consolidation degreeBound finalRoots
      scans promotions table comparisons =>
    simpa using extraction_work_bound before promoted after degree maximumDegree events
      roots marks consolidation degreeBound finalRoots scans promotions table comparisons

/-- A finite sequence of modeled heap operations. The clock total and numbers
    of update/extract calls are sums of the concrete operation events. -/
inductive Run (maximumDegree : Nat) : Counts → Counts → Nat → Nat → Nat → Prop where
  | empty (state : Counts) : Run maximumDegree state state 0 0 0
  | step {before middle after : Counts} {work updates extractions tailWork tailUpdates tailExtractions : Nat} :
      Operation maximumDegree before middle work updates extractions →
      Run maximumDegree middle after tailWork tailUpdates tailExtractions →
      Run maximumDegree before after (work + tailWork) (updates + tailUpdates) (extractions + tailExtractions)

/-- Potential telescopes across an arbitrary mix of operations. No worst-case
    bound on an individual cascade or a single root scan is assumed. -/
theorem Run.amortized {maximumDegree work updates extractions : Nat} {before after : Counts}
    (run : Run maximumDegree before after work updates extractions) :
    work + scaledPotential after ≤
      scaledPotential before + 20 * updates + 12 * (maximumDegree + 1) * extractions := by
  induction run with
  | empty => simp
  | @step before middle after work updates extractions tailWork tailUpdates tailExtractions operation rest ih =>
    have localBound := operation.amortized
    simp only [Nat.mul_add] at *
    omega

theorem Run.total_work {maximumDegree work updates extractions : Nat} {before after : Counts}
    (run : Run maximumDegree before after work updates extractions) :
    work ≤ scaledPotential before + 20 * updates + 12 * (maximumDegree + 1) * extractions := by
  have bound := run.amortized
  omega

/-- Dijkstra performs at most one initial insertion plus one update per edge,
    and at most one extraction per vertex. Combined with the rank bound, the
    modeled heap work is bounded in the form `E + V log V`. -/
theorem Run.dijkstra_work {vertices edges work updates extractions : Nat} {after : Counts}
    (run : Run (2 * vertices.log2 + 1) ⟨0, 0⟩ after work updates extractions)
    (updateBound : updates ≤ edges + 1) (extractionBound : extractions ≤ vertices) :
    work ≤ 20 * (edges + 1) + 24 * (vertices.log2 + 1) * vertices := by
  have bound := run.total_work
  have updateCost := Nat.mul_le_mul_left 20 updateBound
  have extractionCost := Nat.mul_le_mul_left (12 * (2 * vertices.log2 + 1 + 1)) extractionBound
  have coefficient : 12 * (2 * vertices.log2 + 1 + 1) = 24 * (vertices.log2 + 1) := by omega
  simp only [scaledPotential, potential, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at bound
  rw [coefficient] at bound extractionCost
  omega

end Algo2Lean.Fibonacci
