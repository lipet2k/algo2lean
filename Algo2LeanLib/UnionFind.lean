import Std

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Union-find mathematics for implementations using union by rank.

The parent and rank maps describe the stored data. Representatives and masses
are proof-only witnesses: a root owns the mass of its component, and linking
two roots transfers all losing mass to the winner. Starting from singleton
components gives a fixed mass budget of `n`. A root of rank `r` owns at least
`2 ^ r` mass, so every find follows at most `log₂ n` parent links.

Path compression preserves these bounds and the represented partition. The
module proves a logarithmic worst-case bound, not an inverse-Ackermann amortized
bound. It imports no generated algorithm or execution model.
-/

namespace Algo2Lean.UnionFind

/-- Replace one entry of a finite map. -/
def update {n : Nat} {α : Type} (f : Fin n → α) (index : Fin n) (value : α) : Fin n → α :=
  fun vertex => if vertex = index then value else f vertex

@[simp] theorem update_same {n : Nat} {α : Type} (f : Fin n → α) (index : Fin n) (value : α) :
    update f index value index = value := by simp [update]

@[simp] theorem update_other {n : Nat} {α : Type} (f : Fin n → α)
    (index vertex : Fin n) (value : α) (different : vertex ≠ index) :
    update f index value vertex = f vertex := by simp [update, different]

/-- Sum a natural-valued finite map without importing additional libraries. -/
def total : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => f 0 + total (fun vertex => f vertex.succ)

theorem total_ones (n : Nat) : total (n := n) (fun _ => 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih, Nat.add_comm]

theorem entry_le_total {n : Nat} (f : Fin n → Nat) (vertex : Fin n) :
    f vertex ≤ total f := by
  induction n with
  | zero => exact Fin.elim0 vertex
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) vertex
    · simp [total]
    · have bound := ih (fun index => f index.succ) index
      change f index.succ ≤ f 0 + total (fun index => f index.succ)
      omega

theorem total_update {n : Nat} (f : Fin n → Nat) (index : Fin n) (value : Nat) :
    total (update f index value) + f index = total f + value := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · simp [total, update, Fin.succ_ne_zero, Nat.add_comm, Nat.add_left_comm]
    · have next := ih (fun index => f index.succ) index
      simpa [total, update, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero index), Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using! congrArg (fun x => f 0 + x) next

/-- A parent forest with proof-only representatives and component masses. -/
structure State (n : Nat) where
  parent : Fin n → Fin n
  rank : Fin n → Nat
  representative : Fin n → Fin n
  mass : Fin n → Nat

/-- The structural and accounting facts needed by find and union proofs. -/
structure Valid {n : Nat} (state : State n) : Prop where
  representative_root : ∀ vertex, state.parent (state.representative vertex) = state.representative vertex
  root_representative : ∀ vertex, state.parent vertex = vertex → state.representative vertex = vertex
  parent_representative : ∀ vertex, state.representative (state.parent vertex) = state.representative vertex
  parent_rank : ∀ vertex, state.parent vertex ≠ vertex → state.rank vertex < state.rank (state.parent vertex)
  root_mass : ∀ vertex, state.parent vertex = vertex → 2 ^ state.rank vertex ≤ state.mass vertex
  nonroot_mass : ∀ vertex, state.parent vertex ≠ vertex → state.mass vertex = 0
  mass_budget : total state.mass ≤ n

/-- Two vertices belong to the same represented component. -/
def Connected {n : Nat} (state : State n) (first second : Fin n) : Prop :=
  state.representative first = state.representative second

/-- Initially every vertex is its own component, with rank zero and mass one. -/
def initial (n : Nat) : State n where
  parent := id
  rank := fun _ => 0
  representative := id
  mass := fun _ => 1

theorem initial_valid (n : Nat) : Valid (initial n) := by
  constructor
  · intro vertex; rfl
  · intro vertex _; rfl
  · intro vertex; rfl
  · intro vertex different; exact False.elim (different rfl)
  · intro vertex _; simp [initial]
  · intro vertex different; exact False.elim (different rfl)
  · simp [initial, total_ones]

@[simp] theorem initial_connected (n : Nat) (first second : Fin n) :
    Connected (initial n) first second ↔ first = second := Iff.rfl

/-- A find traverses one parent link at a time and stops at a root.
    The final index counts traversed links, excluding the final root test. -/
inductive Find {n : Nat} (state : State n) : Fin n → Fin n → Nat → Prop where
  | root (vertex : Fin n) : state.parent vertex = vertex → Find state vertex vertex 0
  | step (vertex root : Fin n) (steps : Nat) :
      state.parent vertex ≠ vertex → Find state (state.parent vertex) root steps →
      Find state vertex root (steps + 1)

theorem find_correct {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (run : Find state vertex root steps) :
    root = state.representative vertex ∧ state.parent root = root ∧
      state.rank vertex + steps ≤ state.rank root := by
  induction run with
  | root vertex fixed => exact ⟨(valid.root_representative vertex fixed).symm, fixed, by simp⟩
  | step vertex root steps moving _ ih =>
    obtain ⟨correct, fixed, bound⟩ := ih
    have rising := valid.parent_rank vertex moving
    exact ⟨correct.trans (valid.parent_representative vertex), fixed, by omega⟩

theorem root_rank_le_log {n : Nat} {state : State n} (valid : Valid state)
    (root : Fin n) (fixed : state.parent root = root) : state.rank root ≤ Nat.log2 n := by
  have massBound := Nat.le_trans (entry_le_total state.mass root) valid.mass_budget
  apply (Nat.le_log2 (by have := root.isLt; omega : n ≠ 0)).mpr
  exact Nat.le_trans (valid.root_mass root fixed) massBound

theorem find_cost {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (run : Find state vertex root steps) :
    steps ≤ Nat.log2 n := by
  obtain ⟨_, fixed, bounded⟩ := find_correct valid run
  have height := root_rank_le_log valid root fixed
  omega

/-- Every valid forest admits a finite find traversal. -/
theorem find_exists {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) : ∃ steps, Find state vertex (state.representative vertex) steps := by
  by_cases fixed : state.parent vertex = vertex
  · exact ⟨0, by simpa [valid.root_representative vertex fixed] using Find.root vertex fixed⟩
  · obtain ⟨steps, run⟩ := find_exists valid (state.parent vertex)
    exact ⟨steps + 1, Find.step vertex _ steps fixed
      (by simpa [valid.parent_representative vertex] using run)⟩
termination_by total state.rank - state.rank vertex
decreasing_by
  have rising := valid.parent_rank vertex fixed
  have bounded := entry_le_total state.rank (state.parent vertex)
  omega

theorem rank_le_representative {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) : state.rank vertex ≤ state.rank (state.representative vertex) := by
  obtain ⟨steps, run⟩ := find_exists valid vertex
  have := (find_correct valid run).2.2
  omega

theorem rank_lt_representative {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) (moving : state.parent vertex ≠ vertex) :
    state.rank vertex < state.rank (state.representative vertex) := by
  have rising := valid.parent_rank vertex moving
  have bounded := rank_le_representative valid (state.parent vertex)
  rw [valid.parent_representative vertex] at bounded
  omega

/-- Compress one visited vertex directly to its component root. -/
def compress {n : Nat} (state : State n) (vertex : Fin n) : State n :=
  { state with parent := update state.parent vertex (state.representative vertex) }

@[simp] theorem compress_representative {n : Nat} (state : State n) (vertex other : Fin n) :
    (compress state vertex).representative other = state.representative other := rfl

@[simp] theorem compress_connected {n : Nat} (state : State n) (vertex first second : Fin n) :
    Connected (compress state vertex) first second ↔ Connected state first second := Iff.rfl

theorem compress_root_iff {n : Nat} {state : State n} (valid : Valid state)
    (vertex other : Fin n) :
    (compress state vertex).parent other = other ↔ state.parent other = other := by
  by_cases same : other = vertex
  · subst other
    simp only [compress, update_same]
    constructor
    · intro fixed
      have := valid.representative_root vertex
      simpa [fixed] using this
    · exact valid.root_representative vertex
  · simp [compress, update, same]

/-- A path-compression write preserves all forest and mass invariants. -/
theorem compress_valid {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) : Valid (compress state vertex) := by
  constructor
  · intro other
    exact (compress_root_iff valid vertex _).mpr (valid.representative_root other)
  · intro other fixed
    exact valid.root_representative other ((compress_root_iff valid vertex other).mp fixed)
  · intro other
    by_cases same : other = vertex
    · subst other
      simp only [compress, update_same]
      exact valid.root_representative _ (valid.representative_root vertex)
    · simpa [compress, update, same] using valid.parent_representative other
  · intro other moving
    have oldMoving : state.parent other ≠ other := fun fixed =>
      moving ((compress_root_iff valid vertex other).mpr fixed)
    by_cases same : other = vertex
    · subst other
      simpa [compress] using rank_lt_representative valid vertex oldMoving
    · simpa [compress, update, same] using valid.parent_rank other oldMoving
  · intro other fixed
    exact valid.root_mass other ((compress_root_iff valid vertex other).mp fixed)
  · intro other moving
    exact valid.nonroot_mass other (fun fixed => moving ((compress_root_iff valid vertex other).mpr fixed))
  · exact valid.mass_budget

/-- Redirect every name of the losing component to the winning root. -/
def mergeRepresentative {n : Nat} (representative : Fin n → Fin n)
    (loser winner : Fin n) : Fin n → Fin n :=
  fun vertex => if representative vertex = loser then winner else representative vertex

/-- Link two distinct roots whose ranks are in nondecreasing order. -/
def link {n : Nat} (state : State n) (loser winner : Fin n) : State n where
  parent := update state.parent loser winner
  rank := update state.rank winner
    (if state.rank loser = state.rank winner then state.rank winner + 1 else state.rank winner)
  representative := mergeRepresentative state.representative loser winner
  mass := update (update state.mass loser 0) winner (state.mass loser + state.mass winner)

theorem link_rank_ge {n : Nat} (state : State n) (loser winner vertex : Fin n) :
    state.rank vertex ≤ (link state loser winner).rank vertex := by
  by_cases same : vertex = winner
  · subst vertex
    simp only [link, update_same]
    split <;> omega
  · simp [link, update, same]

theorem link_root_iff {n : Nat} {state : State n}
    (loser winner : Fin n) (different : loser ≠ winner) :
    ∀ vertex, (link state loser winner).parent vertex = vertex ↔
      vertex ≠ loser ∧ state.parent vertex = vertex := by
  intro vertex
  by_cases same : vertex = loser
  · subst vertex
    simp [link, different.symm]
  · simp [link, update, same]

theorem link_mass_total {n : Nat} (state : State n)
    (loser winner : Fin n) (different : loser ≠ winner) :
    total (link state loser winner).mass = total state.mass := by
  have first := total_update state.mass loser 0
  have second := total_update (update state.mass loser 0) winner
    (state.mass loser + state.mass winner)
  rw [update_other state.mass loser winner 0 different.symm] at second
  change total (update (update state.mass loser 0) winner
    (state.mass loser + state.mass winner)) = total state.mass
  omega

/-- Linking roots by rank preserves validity and the fixed mass budget. -/
theorem link_valid {n : Nat} {state : State n} (valid : Valid state)
    (loser winner : Fin n) (different : loser ≠ winner)
    (loserRoot : state.parent loser = loser) (winnerRoot : state.parent winner = winner)
    (ordered : state.rank loser ≤ state.rank winner) : Valid (link state loser winner) := by
  have loserRep := valid.root_representative loser loserRoot
  have winnerRep := valid.root_representative winner winnerRoot
  have winnerFixed : (link state loser winner).parent winner = winner := by
    simp [link, update, different.symm, winnerRoot]
  have winnerRank : state.rank loser < (link state loser winner).rank winner := by
    simp only [link, update_same]
    split <;> omega
  constructor
  · intro vertex
    simp only [link, mergeRepresentative]
    split
    · simpa [link] using winnerFixed
    · rename_i other
      exact (link_root_iff loser winner different _).mpr
        ⟨other, valid.representative_root vertex⟩
  · intro vertex fixed
    obtain ⟨other, oldFixed⟩ := (link_root_iff loser winner different vertex).mp fixed
    simp [link, mergeRepresentative, valid.root_representative vertex oldFixed, other]
  · intro vertex
    by_cases same : vertex = loser
    · subst vertex
      simp [link, update_same, mergeRepresentative, loserRep, winnerRep, different.symm]
    · change mergeRepresentative state.representative loser winner
        (update state.parent loser winner vertex) =
        mergeRepresentative state.representative loser winner vertex
      rw [update_other _ _ _ _ same]
      simp only [mergeRepresentative, valid.parent_representative]
  · intro vertex moving
    by_cases same : vertex = loser
    · subst vertex
      simpa [link, update, different] using winnerRank
    · have oldMoving : state.parent vertex ≠ vertex := by
        simpa [link, update, same] using moving
      have notWinner : vertex ≠ winner := by
        intro equal
        subst vertex
        exact oldMoving winnerRoot
      have rising := valid.parent_rank vertex oldMoving
      have raised := link_rank_ge state loser winner (state.parent vertex)
      change update state.rank winner _ vertex <
        (link state loser winner).rank (update state.parent loser winner vertex)
      rw [update_other _ _ _ _ notWinner, update_other _ _ _ _ same]
      omega
  · intro vertex fixed
    obtain ⟨notLoser, oldFixed⟩ := (link_root_iff loser winner different vertex).mp fixed
    by_cases same : vertex = winner
    · subst vertex
      have massLoser := valid.root_mass loser loserRoot
      have massWinner := valid.root_mass winner winnerRoot
      simp only [link, update_same]
      split
      · rename_i equal
        rw [Nat.pow_succ]
        rw [equal] at massLoser
        omega
      · omega
    · simpa [link, update, same, notLoser] using valid.root_mass vertex oldFixed
  · intro vertex moving
    by_cases same : vertex = loser
    · subst vertex
      simp [link, update, different]
    · have notWinner : vertex ≠ winner := by
        intro equal
        subst vertex
        exact moving winnerFixed
      have oldMoving : state.parent vertex ≠ vertex := by
        simpa [link, update, same] using moving
      simpa [link, update, same, notWinner] using valid.nonroot_mass vertex oldMoving
  · rw [link_mass_total state loser winner different]
    exact valid.mass_budget

theorem mergeRepresentative_eq_iff {n : Nat} (representative : Fin n → Fin n)
    (loser winner first second : Fin n) :
    mergeRepresentative representative loser winner first =
        mergeRepresentative representative loser winner second ↔
      representative first = representative second ∨
      (representative first = loser ∧ representative second = winner) ∨
      (representative first = winner ∧ representative second = loser) := by
  by_cases firstLoser : representative first = loser <;>
    by_cases secondLoser : representative second = loser
  · simp [mergeRepresentative, firstLoser, secondLoser]
  · simp [mergeRepresentative, firstLoser, secondLoser, Ne.symm secondLoser, eq_comm]
  · simp [mergeRepresentative, firstLoser, secondLoser, eq_comm]
  · simp [mergeRepresentative, firstLoser, secondLoser]

/-- A root link joins exactly its two former components. -/
theorem link_connected {n : Nat} {state : State n} (valid : Valid state)
    (loser winner : Fin n) (loserRoot : state.parent loser = loser)
    (winnerRoot : state.parent winner = winner) (first second : Fin n) :
    Connected (link state loser winner) first second ↔
      Connected state first second ∨
      (Connected state first loser ∧ Connected state second winner) ∨
      (Connected state first winner ∧ Connected state second loser) := by
  simpa only [Connected, link, valid.root_representative loser loserRoot,
    valid.root_representative winner winnerRoot] using
    mergeRepresentative_eq_iff state.representative loser winner first second

/-- Link representatives by rank; an already connected pair leaves the state alone.
    The first argument wins rank ties, matching the usual union-by-rank code. -/
def union {n : Nat} (state : State n) (first second : Fin n) : State n :=
  let left := state.representative first
  let right := state.representative second
  if left = right then state
  else if state.rank left < state.rank right then link state left right
  else link state right left

/-- Union preserves the forest representation and rank/mass accounting. -/
theorem union_valid {n : Nat} {state : State n} (valid : Valid state)
    (first second : Fin n) : Valid (union state first second) := by
  simp only [union]
  split
  · exact valid
  · rename_i different
    split
    · rename_i ordered
      exact link_valid valid _ _ different (valid.representative_root first)
        (valid.representative_root second) (by omega)
    · rename_i ordered
      exact link_valid valid _ _ (Ne.symm different) (valid.representative_root second)
        (valid.representative_root first) (by omega)

/-- Union's precise partition contract, independent of root selection and ranks. -/
theorem union_connected {n : Nat} {state : State n} (valid : Valid state)
    (first second a b : Fin n) :
    Connected (union state first second) a b ↔
      Connected state a b ∨
      (Connected state a first ∧ Connected state b second) ∨
      (Connected state a second ∧ Connected state b first) := by
  have firstRoot := valid.representative_root first
  have secondRoot := valid.representative_root second
  have firstRep := valid.root_representative _ firstRoot
  have secondRep := valid.root_representative _ secondRoot
  simp only [union]
  split
  · rename_i same
    simp only [Connected, same]
    constructor
    · exact Or.inl
    · intro joined
      rcases joined with old | joined | joined
      · exact old
      · exact joined.1.trans joined.2.symm
      · exact joined.1.trans joined.2.symm
  · split
    · simpa only [Connected, firstRep, secondRep] using
        link_connected valid _ _ firstRoot secondRoot a b
    · have joined := link_connected valid _ _ secondRoot firstRoot a b
      simp only [Connected, firstRep, secondRep] at joined ⊢
      constructor
      · intro connected
        rcases joined.mp connected with old | cross | cross
        · exact Or.inl old
        · exact Or.inr (Or.inr cross)
        · exact Or.inr (Or.inl cross)
      · intro connected
        apply joined.mpr
        rcases connected with old | cross | cross
        · exact Or.inl old
        · exact Or.inr (Or.inr cross)
        · exact Or.inr (Or.inl cross)

/-- A successful union joins the requested pair. -/
theorem union_joins {n : Nat} {state : State n} (valid : Valid state)
    (first second : Fin n) : Connected (union state first second) first second :=
  (union_connected valid first second first second).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- Every preexisting connection survives a union. -/
theorem union_preserves {n : Nat} {state : State n} (valid : Valid state)
    (first second a b : Fin n) (connected : Connected state a b) :
    Connected (union state first second) a b :=
  (union_connected valid first second a b).mpr (Or.inl connected)

end Algo2Lean.UnionFind
