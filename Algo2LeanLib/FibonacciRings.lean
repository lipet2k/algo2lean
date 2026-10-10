import Std

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite circular doubly linked lists for Fibonacci-heap pointer proofs.

The representation is independent of heaps and sequence references: `left` and
`right` are the integer-indexed pointer arrays observed through an allocated
sequence. Primitive effects below follow the source's precise write order.
-/

namespace Algo2Lean.Fibonacci.Rings

def write (values : Int → Int) (index value : Int) : Int → Int :=
  fun other => if other = index then value else values other

@[simp] theorem write_same (values : Int → Int) (index value : Int) :
    write values index value index = value := by simp [write]

@[simp] theorem write_other (values : Int → Int) (index value other : Int)
    (different : other ≠ index) : write values index value other = values other := by
  simp [write, different]

/-- An open chain records both pointers along every adjacent pair. Its first
    predecessor and last successor are supplied by the enclosing ring. -/
inductive Chain (left right : Int → Int) : Int → List Int → Int → Prop where
  | singleton (vertex : Int) : Chain left right vertex [vertex] vertex
  | cons (first : Int) {next last : Int} {tail : List Int} :
      right first = next → left next = first → Chain left right next tail last →
      Chain left right first (first :: tail) last

/-- A nonempty ring in its chosen traversal order. Rotating the list changes
    the chosen head while describing exactly the same pointer arrays. -/
structure Ring (left right : Int → Int) (vertices : List Int) : Prop where
  unique : vertices.Nodup
  closed : ∃ first last, Chain left right first vertices last ∧ right last = first ∧ left first = last

def RingOrEmpty (left right : Int → Int) (vertices : List Int) : Prop :=
  vertices = [] ∨ Ring left right vertices

theorem Chain.first_mem {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : first ∈ vertices := by
  cases chain <;> simp

theorem Chain.last_mem {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : last ∈ vertices := by
  induction chain with
  | singleton => simp
  | cons first _ _ _ ih => simp [ih]

theorem Chain.head {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : ∃ tail, vertices = first :: tail := by
  cases chain <;> exact ⟨_, rfl⟩

theorem Ring.nonempty {left right : Int → Int} {vertices : List Int}
    (ring : Ring left right vertices) : vertices ≠ [] := by
  obtain ⟨first, last, chain, _, _⟩ := ring.closed
  intro empty
  have present := chain.first_mem
  simp [empty] at present

/-- Open chains can be joined at one new edge. -/
theorem Chain.append {left right : Int → Int} {first middle next last : Int}
    {front back : List Int} (one : Chain left right first front middle)
    (two : Chain left right next back last) (forward : right middle = next)
    (backward : left next = middle) : Chain left right first (front ++ back) last := by
  induction one with
  | singleton => exact .cons _ forward backward two
  | cons first rightFirst leftNext tail ih => exact .cons first rightFirst leftNext (ih forward backward)

/-- Pointer updates at a chain's external endpoints do not affect its
    internal links. All other observations only need agree on this chain. -/
theorem Chain.frame {left right newLeft newRight : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) (unique : vertices.Nodup)
    (leftSame : ∀ vertex ∈ vertices, vertex ≠ first → newLeft vertex = left vertex)
    (rightSame : ∀ vertex ∈ vertices, vertex ≠ last → newRight vertex = right vertex) :
    Chain newLeft newRight first vertices last := by
  induction chain with
  | singleton => exact .singleton _
  | @cons first next last tail forward backward chain ih =>
    obtain ⟨firstAbsent, tailUnique⟩ := List.nodup_cons.mp unique
    have firstLast : first ≠ last := by intro same; exact firstAbsent (same.symm ▸ chain.last_mem)
    have nextFirst : next ≠ first := by intro same; exact firstAbsent (same ▸ chain.first_mem)
    refine Chain.cons first (next := next) ?_ ?_ ?_
    · rw [rightSame first (by simp) firstLast]
      exact forward
    · rw [leftSame next (by simp [chain.first_mem]) nextFirst]
      exact backward
    · apply ih tailUnique
      · intro vertex member _
        apply leftSame vertex (by simp [member])
        intro same
        subst vertex
        exact firstAbsent member
      · intro vertex member different
        exact rightSame vertex (by simp [member]) different

/-- Equal pointer values on ring members preserve the ring; other array entries
    may differ. -/
theorem Ring.frame {left right newLeft newRight : Int → Int} {vertices : List Int}
    (ring : Ring left right vertices)
    (leftSame : ∀ vertex ∈ vertices, newLeft vertex = left vertex)
    (rightSame : ∀ vertex ∈ vertices, newRight vertex = right vertex) :
    Ring newLeft newRight vertices := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  refine ⟨ring.unique, first, last, chain.frame ring.unique (fun v member _ => leftSame v member)
    (fun v member _ => rightSame v member), ?_, ?_⟩
  · rw [rightSame last chain.last_mem]
    exact forward
  · rw [leftSame first chain.first_mem]
    exact backward

/-- Every pointer read at a ring member stays within that finite ring. -/
theorem Chain.neighbors {left right : Int → Int} {first last vertex : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) (member : vertex ∈ vertices) :
    (vertex = first ∨ left vertex ∈ vertices) ∧ (vertex = last ∨ right vertex ∈ vertices) := by
  induction chain with
  | singleton =>
    have same := List.mem_singleton.mp member
    exact ⟨Or.inl same, Or.inl same⟩
  | @cons first next last tail forward backward chain ih =>
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨Or.inl rfl, Or.inr (by rw [forward]; simp [chain.first_mem])⟩
    · obtain ⟨leftNeighbor, rightNeighbor⟩ := ih inTail
      constructor
      · rcases leftNeighbor with rfl | inside
        · exact Or.inr (by rw [backward]; simp)
        · exact Or.inr (by simp [inside])
      · rcases rightNeighbor with same | inside
        · exact Or.inl same
        · exact Or.inr (by simp [inside])

theorem Ring.neighbors {left right : Int → Int} {vertex : Int} {vertices : List Int}
    (ring : Ring left right vertices) (member : vertex ∈ vertices) :
    left vertex ∈ vertices ∧ right vertex ∈ vertices := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  obtain ⟨leftNeighbor, rightNeighbor⟩ := chain.neighbors member
  constructor
  · rcases leftNeighbor with rfl | inside
    · rw [backward]; exact chain.last_mem
    · exact inside
  · rcases rightNeighbor with rfl | inside
    · rw [forward]; exact chain.first_mem
    · exact inside

/-- A displayed list head is the first endpoint of its open chain. -/
theorem Ring.open_head {left right : Int → Int} {head : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) :
    ∃ last, Chain left right head (head :: tail) last ∧ right last = head ∧ left head = last := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  obtain ⟨rest, same⟩ := chain.head
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  exact ⟨last, chain, forward, backward⟩

def insertBeforeLeft (left : Int → Int) (head vertex : Int) : Int → Int :=
  write (write left vertex (left head)) head vertex

def insertBeforeRight (left right : Int → Int) (head vertex : Int) : Int → Int :=
  write (write right vertex head) (left head) vertex

def removeLeft (left right : Int → Int) (vertex : Int) : Int → Int :=
  write (write left (right vertex) (left vertex)) vertex vertex

def removeRight (left right : Int → Int) (vertex : Int) : Int → Int :=
  write (write right (left vertex) (right vertex)) vertex vertex

theorem singleton_ring (left right : Int → Int) (vertex : Int)
    (selfLeft : left vertex = vertex) (selfRight : right vertex = vertex) : Ring left right [vertex] :=
  ⟨by simp, vertex, vertex, Chain.singleton vertex, selfRight, selfLeft⟩

/-- Inserting a fresh vertex before the chosen head realizes list prepend.
    The inserted vertex's previous pointers need not already be self-links. -/
theorem Ring.insert_before {left right : Int → Int} {head vertex : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) (fresh : vertex ∉ head :: tail) :
    Ring (insertBeforeLeft left head vertex) (insertBeforeRight left right head vertex)
      (vertex :: head :: tail) := by
  obtain ⟨last, chain, closesRight, closesLeft⟩ := ring.open_head
  have vertexHead : vertex ≠ head := by intro same; exact fresh (by simp [same])
  have oldDifferent (other : Int) (member : other ∈ head :: tail) : other ≠ vertex := by
    intro same
    exact fresh (same ▸ member)
  have vertexLast : vertex ≠ last := Ne.symm (oldDifferent last chain.last_mem)
  have inside : Chain (insertBeforeLeft left head vertex) (insertBeforeRight left right head vertex)
      head (head :: tail) last := by
    apply chain.frame ring.unique
    · intro other member notHead
      simp [insertBeforeLeft, write, oldDifferent other member, notHead]
    · intro other member notLast
      simp [insertBeforeRight, write, closesLeft, oldDifferent other member, notLast]
  refine ⟨List.nodup_cons.mpr ⟨fresh, ring.unique⟩, vertex, last,
    Chain.cons vertex (next := head) ?_ ?_ inside, ?_, ?_⟩
  · simp [insertBeforeRight, write, closesLeft, vertexLast]
  · simp [insertBeforeLeft, write]
  · simp [insertBeforeRight, write, closesLeft]
  · simp [insertBeforeLeft, write, closesLeft, vertexHead]

/-- The removed vertex is always detached into a singleton, including removal
    from an original singleton ring. This follows from the last two writes. -/
theorem remove_detaches (left right : Int → Int) (vertex : Int) :
    Ring (removeLeft left right vertex) (removeRight left right vertex) [vertex] := by
  apply singleton_ring <;> simp [removeLeft, removeRight]

/-- Removing the displayed head leaves its tail as the surviving ring, or
    leaves no surviving ring when the original was a singleton. -/
theorem Ring.remove_head {left right : Int → Int} {vertex : Int} {tail : List Int}
    (ring : Ring left right (vertex :: tail)) :
    RingOrEmpty (removeLeft left right vertex) (removeRight left right vertex) tail := by
  obtain ⟨last, chain, closesRight, closesLeft⟩ := ring.open_head
  cases chain with
  | singleton => exact Or.inl rfl
  | @cons first next last tail forward backward chain =>
    obtain ⟨firstAbsent, tailUnique⟩ := List.nodup_cons.mp ring.unique
    have nextFirst : next ≠ vertex := by intro same; exact firstAbsent (same ▸ chain.first_mem)
    have lastFirst : last ≠ vertex := by intro same; exact firstAbsent (same ▸ chain.last_mem)
    have tailDifferent (other : Int) (member : other ∈ tail) : other ≠ vertex := by
      intro same
      exact firstAbsent (same ▸ member)
    refine Or.inr ⟨tailUnique, next, last, ?_, ?_, ?_⟩
    · apply chain.frame tailUnique
      · intro other member notNext
        simp [removeLeft, write, forward, notNext, tailDifferent other member]
      · intro other member notLast
        simp [removeRight, write, closesLeft, notLast, tailDifferent other member]
    · simp [removeRight, write, closesLeft, forward, lastFirst]
    · simp [removeLeft, write, closesLeft, forward, nextFirst]

/-- Choosing the next node as the head rotates the list but changes no pointers. -/
theorem Ring.rotate_head {left right : Int → Int} {head : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) : Ring left right (tail ++ [head]) := by
  obtain ⟨last, chain, forward, backward⟩ := ring.open_head
  have unique : (tail ++ [head]).Nodup := by
    exact (List.perm_append_comm (l₁ := tail) (l₂ := [head])).nodup_iff.mpr ring.unique
  cases chain with
  | singleton => exact ring
  | @cons first next last tail rightHead leftNext rest =>
    exact ⟨unique, next, head, rest.append (.singleton head) forward backward, rightHead, leftNext⟩

/-- Any cyclic rotation describes the same ring. -/
theorem Ring.rotate_append {left right : Int → Int} (front back : List Int)
    (ring : Ring left right (front ++ back)) : Ring left right (back ++ front) := by
  induction front generalizing back with
  | nil => simpa using ring
  | cons head front ih =>
    have rotated := ring.rotate_head
    change Ring left right ((front ++ back) ++ [head]) at rotated
    have nextRing : Ring left right (front ++ (back ++ [head])) := by
      simpa only [List.append_assoc] using rotated
    have final := ih (back ++ [head]) nextRing
    simpa only [List.append_assoc, List.singleton_append] using final

theorem RingOrEmpty.rotate_append {left right : Int → Int} (front back : List Int)
    (ring : RingOrEmpty left right (front ++ back)) : RingOrEmpty left right (back ++ front) := by
  rcases ring with empty | ring
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp empty
    exact Or.inl rfl
  · exact Or.inr (ring.rotate_append front back)

/-- Removal preserves the relative order of every survivor, including when
    the removed vertex is not the chosen list head. -/
theorem Ring.remove_from_decomposition {left right : Int → Int} (front back : List Int) (vertex : Int)
    (ring : Ring left right (front ++ vertex :: back)) :
    RingOrEmpty (removeLeft left right vertex) (removeRight left right vertex) (front ++ back) := by
  have rotated : Ring left right (vertex :: (back ++ front)) := ring.rotate_append front (vertex :: back)
  exact rotated.remove_head.rotate_append back front

/-- The pointer primitive agrees with ordinary list erasure on unique handles. -/
theorem Ring.remove {left right : Int → Int} {vertices : List Int} {vertex : Int}
    (ring : Ring left right vertices) (member : vertex ∈ vertices) :
    RingOrEmpty (removeLeft left right vertex) (removeRight left right vertex) (vertices.erase vertex) := by
  obtain ⟨front, back, rfl⟩ := List.mem_iff_append.mp member
  have notEarlier : vertex ∉ front := by
    have disjoint := (List.nodup_append.mp ring.unique).2.2
    intro earlier
    exact disjoint vertex earlier vertex (by simp) rfl
  rw [List.erase_append_right _ notEarlier, List.erase_cons_head]
  exact ring.remove_from_decomposition front back vertex

/-- Cutting one ring cannot change another ring with disjoint handles. -/
theorem Ring.remove_disjoint {left right : Int → Int} {vertices untouched : List Int} {vertex : Int}
    (ring : Ring left right vertices) (other : Ring left right untouched) (member : vertex ∈ vertices)
    (disjoint : ∀ node ∈ vertices, node ∉ untouched) :
    Ring (removeLeft left right vertex) (removeRight left right vertex) untouched := by
  obtain ⟨leftMember, rightMember⟩ := ring.neighbors member
  have different (node : Int) (old : node ∈ untouched) (changed : Int) (inside : changed ∈ vertices) :
      node ≠ changed := by
    intro same
    exact disjoint changed inside (same ▸ old)
  apply other.frame
  · intro node old
    simp [removeLeft, write, different node old vertex member, different node old (right vertex) rightMember]
  · intro node old
    simp [removeRight, write, different node old vertex member, different node old (left vertex) leftMember]

/-- Insertion changes only its fresh vertex and two neighboring ring members. -/
theorem Ring.insert_before_disjoint {left right : Int → Int} {head vertex : Int}
    {tail untouched : List Int} (ring : Ring left right (head :: tail)) (other : Ring left right untouched)
    (fresh : vertex ∉ untouched) (disjoint : ∀ node ∈ head :: tail, node ∉ untouched) :
    Ring (insertBeforeLeft left head vertex) (insertBeforeRight left right head vertex) untouched := by
  have headMember : head ∈ head :: tail := by simp
  have leftMember := (ring.neighbors headMember).1
  have different (node : Int) (old : node ∈ untouched) (changed : Int) (inside : changed ∈ head :: tail) :
      node ≠ changed := by
    intro same
    exact disjoint changed inside (same ▸ old)
  have notFresh (node : Int) (old : node ∈ untouched) : node ≠ vertex := by
    intro same
    exact fresh (same ▸ old)
  apply other.frame
  · intro node old
    simp [insertBeforeLeft, write, notFresh node old, different node old head headMember]
  · intro node old
    simp [insertBeforeRight, write, notFresh node old, different node old (left head) leftMember]

theorem Ring.singleton_pointers {left right : Int → Int} {vertex : Int}
    (ring : Ring left right [vertex]) : left vertex = vertex ∧ right vertex = vertex := by
  obtain ⟨last, chain, forward, backward⟩ := ring.open_head
  cases chain with
  | singleton => exact ⟨backward, forward⟩
  | cons _ _ _ rest => cases rest

theorem Ring.head_next {left right : Int → Int} {head next : Int} {tail : List Int}
    (ring : Ring left right (head :: next :: tail)) : right head = next ∧ left next = head := by
  obtain ⟨last, chain, _, _⟩ := ring.open_head
  cases chain with
  | @cons _ child _ _ forward backward rest =>
    obtain ⟨remaining, same⟩ := rest.head
    obtain ⟨rfl, rfl⟩ := List.cons.inj same
    exact ⟨forward, backward⟩

/-- The root-list helper inserts after its minimum representative. These are
    its exact effects, distinct from the child-list insertion before its head. -/
def insertAfterLeft (left right : Int → Int) (head vertex : Int) : Int → Int :=
  write (write left vertex head) (right head) vertex

def insertAfterRight (right : Int → Int) (head vertex : Int) : Int → Int :=
  write (write right vertex (right head)) head vertex

/-- Insertion after a representative is insertion before its successor, so
    the resulting ring order is `head :: vertex :: tail`. -/
theorem Ring.insert_after {left right : Int → Int} {head vertex : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) (fresh : vertex ∉ head :: tail) :
    Ring (insertAfterLeft left right head vertex) (insertAfterRight right head vertex)
      (head :: vertex :: tail) := by
  cases tail with
  | nil =>
    obtain ⟨selfLeft, selfRight⟩ := ring.singleton_pointers
    have result := (ring.insert_before fresh).rotate_head
    simpa [insertBeforeLeft, insertBeforeRight, insertAfterLeft, insertAfterRight, selfLeft, selfRight] using result
  | cons next rest =>
    obtain ⟨forward, backward⟩ := ring.head_next
    have rotated : Ring left right (next :: (rest ++ [head])) := ring.rotate_head
    have freshRotated : vertex ∉ next :: (rest ++ [head]) := by
      simpa [or_comm, or_left_comm, or_assoc] using fresh
    have inserted := rotated.insert_before freshRotated
    have restored := inserted.rotate_append (vertex :: next :: rest) [head]
    simpa only [List.singleton_append, insertBeforeLeft, insertBeforeRight,
      insertAfterLeft, insertAfterRight, forward, backward] using restored

theorem Ring.insert_after_disjoint {left right : Int → Int} {head vertex : Int}
    {tail untouched : List Int} (ring : Ring left right (head :: tail)) (other : Ring left right untouched)
    (fresh : vertex ∉ untouched) (disjoint : ∀ node ∈ head :: tail, node ∉ untouched) :
    Ring (insertAfterLeft left right head vertex) (insertAfterRight right head vertex) untouched := by
  have headMember : head ∈ head :: tail := by simp
  have rightMember := (ring.neighbors headMember).2
  have different (node : Int) (old : node ∈ untouched) (changed : Int) (inside : changed ∈ head :: tail) :
      node ≠ changed := by
    intro same
    exact disjoint changed inside (same ▸ old)
  have notFresh (node : Int) (old : node ∈ untouched) : node ≠ vertex := by
    intro same
    exact fresh (same ▸ old)
  apply other.frame
  · intro node old
    simp [insertAfterLeft, write, notFresh node old, different node old (right head) rightMember]
  · intro node old
    simp [insertAfterRight, write, notFresh node old, different node old head headMember]

end Algo2Lean.Fibonacci.Rings
