import Algo2LeanLib.Dijkstra

/-!
The finite Dijkstra driver shared by compiled queue backends. It composes
verified local iterations; it does not assume a search transcript, shortest
path correctness, or termination of the whole algorithm.
-/

namespace Algo2Lean.Dijkstra.Execution

/-- Concrete states may include a heap, queue layout, and amortized potential.
    Accounting is an arbitrary compositional relation, rather than a fixed
    binary-heap cost formula. Completion is the compiled continuation contract. -/
structure Interface (State : Type) where
  distance : State → Int → Int
  settled : State → Int → Prop
  invariant : State → List Int → Prop
  completion : State → State → Prop
  accounting : State → State → Nat → Nat → Prop
  zero : ∀ state, accounting state state 0 0
  compose : ∀ {before middle after firstVertices firstEdges lastVertices lastEdges},
    accounting before middle firstVertices firstEdges →
    accounting middle after lastVertices lastEdges →
    accounting before after (firstVertices + lastVertices) (firstEdges + lastEdges)
  weaken : ∀ {before after vertices edges moreVertices moreEdges},
    accounting before after vertices edges → vertices ≤ moreVertices → edges ≤ moreEdges →
    accounting before after moreVertices moreEdges

/-- One verified extraction and adjacency scan. The premises describe local
    state changes and one compiled segment; all recursive reasoning is shared. -/
structure Iteration {State : Type} (api : Interface State) (edge : Edges)
    (adjacency : Adjacency) (before after : State) (remaining : List Int) (selected : Int) : Prop where
  member : selected ∈ remaining
  next : api.invariant after (remaining.erase selected)
  minimum : MinimumSelection (api.distance before) (api.settled before) selected
  represents : ∀ target weight, (target, weight) ∈ adjacency selected ↔ edge selected target weight
  scan : RelaxScan (settleVertex (api.settled before) selected) selected
    (adjacency selected) (api.distance before) (api.distance after)
  settled : api.settled after = settleVertex (api.settled before) selected
  continuation : ∀ final, api.completion after final → api.completion before final
  cost : api.accounting before after 1 (adjacency selected).length

/-- The queue either proves exhaustion or supplies one local iteration. -/
inductive Progress {State : Type} (api : Interface State) (edge : Edges)
    (adjacency : Adjacency) (state : State) (remaining : List Int) : Prop where
  | done (exhausted : Exhausted (api.distance state) (api.settled state))
      (complete : api.completion state state) : Progress api edge adjacency state remaining
  | next {after : State} {selected : Int}
      (iteration : Iteration api edge adjacency state after remaining selected) :
      Progress api edge adjacency state remaining

/-- A complete compiled continuation, an independently reusable logical search
    run, and the accumulated local accounting. Final invariants are retained. -/
structure Completed {State : Type} (api : Interface State) (edge : Edges)
    (adjacency : Adjacency) (before after : State) (remaining : List Int) : Prop where
  invariant : ∃ pending, api.invariant after pending
  search : ∃ vertices, SearchRun edge adjacency (api.distance before) (api.settled before)
    (api.distance after) vertices ∧ ∀ vertex ∈ vertices, vertex ∈ remaining
  cost : api.accounting before after remaining.length (edgeBudget adjacency remaining)
  execution : api.completion before after

/-- The remaining vertex list strictly decreases, so verified local iterations
    suffice for finite compiled execution and the shared `SearchRun` interface. -/
theorem run {State : Type} (api : Interface State) (edge : Edges) (adjacency : Adjacency)
    (progress : ∀ state remaining, api.invariant state remaining →
      Progress api edge adjacency state remaining)
    (state : State) (remaining : List Int) (invariant : api.invariant state remaining) :
    ∃ after, Completed api edge adjacency state after remaining := by
  suffices all : ∀ count state remaining, remaining.length = count → api.invariant state remaining →
      ∃ after, Completed api edge adjacency state after remaining by
    exact all remaining.length state remaining rfl invariant
  intro count
  induction count using Nat.strongRecOn with
  | ind count ih =>
    intro state remaining length invariant
    cases progress state remaining invariant with
    | done exhausted complete =>
      exact ⟨state, ⟨remaining, invariant⟩, ⟨[], .done _ _ exhausted, by simp⟩,
        api.weaken (api.zero state) (Nat.zero_le _) (Nat.zero_le _), complete⟩
    | @next after selected iteration =>
      have decreases := remaining_length remaining selected iteration.member
      have smaller : (remaining.erase selected).length < count := by omega
      obtain ⟨final, completed⟩ := ih (remaining.erase selected).length smaller after
        (remaining.erase selected) rfl iteration.next
      obtain ⟨vertices, tail, contained⟩ := completed.search
      have tailRun := tail
      rw [iteration.settled] at tailRun
      have vertexSum : 1 + (remaining.erase selected).length = remaining.length := by omega
      have edgeSum : (adjacency selected).length + edgeBudget adjacency (remaining.erase selected) =
          edgeBudget adjacency remaining := by
        have account := edgeBudget_erase adjacency remaining selected iteration.member
        omega
      refine ⟨final, completed.invariant, ?_, ?_, iteration.continuation final completed.execution⟩
      · refine ⟨selected :: vertices,
          .select iteration.minimum iteration.represents iteration.scan tailRun, ?_⟩
        intro vertex member
        rcases List.mem_cons.mp member with rfl | later
        · exact iteration.member
        · exact List.mem_of_mem_erase (contained vertex later)
      · simpa only [Nat.add_zero, Nat.zero_add, vertexSum, edgeSum] using
          api.compose iteration.cost completed.cost

end Algo2Lean.Dijkstra.Execution
