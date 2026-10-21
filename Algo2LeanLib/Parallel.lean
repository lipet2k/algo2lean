import Algo2Lean

/-!
Structured fork–join evaluations and their source-connected work/span costs.
A fork has two independent children and a continuation after both return. Its
finite evaluation records a deterministic left-to-right serialization, the
access bounds of each child, and the associated series-parallel cost.
This module does not assert a processor scheduler or an elapsed-time bound.
Allocation inside a fork child is excluded until references can be allocated
independently. Ordinary execution before a fork or after its join may allocate.
-/

namespace Algo2LeanParallel

universe u v w

/-- Work counts primitive operations; span counts the longest dependency chain.
Both use the same abstract unit-cost model. -/
structure Cost where
  work : Nat
  span : Nat
  deriving DecidableEq, Repr

namespace Cost

def zero : Cost := ⟨0, 0⟩
def one : Cost := ⟨1, 1⟩

/-- Dependent computations add both costs. -/
def seq (first second : Cost) : Cost :=
  ⟨first.work + second.work, first.span + second.span⟩

/-- A fork and its join each cost one unit. The children can overlap. -/
def fork (left right : Cost) : Cost :=
  ⟨left.work + right.work + 2, max left.span right.span + 2⟩

@[simp] theorem work_seq (a b : Cost) : (seq a b).work = a.work + b.work := rfl
@[simp] theorem span_seq (a b : Cost) : (seq a b).span = a.span + b.span := rfl
@[simp] theorem work_fork (a b : Cost) : (fork a b).work = a.work + b.work + 2 := rfl
@[simp] theorem span_fork (a b : Cost) : (fork a b).span = max a.span b.span + 2 := rfl
@[simp] theorem zero_seq (a : Cost) : seq zero a = a := by cases a; simp [seq, zero]
@[simp] theorem seq_zero (a : Cost) : seq a zero = a := by cases a; simp [seq, zero]

theorem seq_assoc (a b c : Cost) : seq (seq a b) c = seq a (seq b c) := by
  cases a; cases b; cases c; simp [seq, Nat.add_assoc]

theorem seq_span_le_work {a b : Cost} (ha : a.span ≤ a.work) (hb : b.span ≤ b.work) :
    (seq a b).span ≤ (seq a b).work := Nat.add_le_add ha hb

theorem fork_span_le_work {a b : Cost} (ha : a.span ≤ a.work) (hb : b.span ≤ b.work) :
    (fork a b).span ≤ (fork a b).work := by
  simp only [span_fork, work_fork]
  have : max a.span b.span ≤ a.work + b.work := by omega
  omega

end Cost

/-- Actual sequence cells, rather than just source variable names, identify
memory. Aliased references therefore name the same location. -/
inductive Location where
  | seq (ref : Nat) (index : Int)
  | object (ref : Nat) (field : String)
  | collection (ref : Nat) (index : Int)
  deriving DecidableEq, Repr

/-- An access bound covering all reads and writes during an execution, not merely a
comparison of its initial and final heaps. Allocation is tracked separately. -/
structure Access where
  reads : Location → Prop
  writes : Location → Prop
  allocates : Bool

namespace Access

def empty : Access := ⟨fun _ => False, fun _ => False, false⟩
def read (location : Location) : Access := ⟨fun x => x = location, fun _ => False, false⟩
def write (location : Location) : Access := ⟨fun _ => False, fun x => x = location, false⟩
def allocation : Access := ⟨fun _ => False, fun _ => False, true⟩
def readSeq (ref : Nat) (index : Int) : Access := read (.seq ref index)
def writeSeq (ref : Nat) (index : Int) : Access := write (.seq ref index)

def union (first second : Access) : Access :=
  ⟨fun x => first.reads x ∨ second.reads x,
   fun x => first.writes x ∨ second.writes x,
   first.allocates || second.allocates⟩

/-- Both children may read a cell. Neither may write a cell read or written by
the other, and neither may allocate. This excludes read/write races as well as
write/write races. -/
structure Compatible (left right : Access) : Prop where
  left_no_allocation : left.allocates = false
  right_no_allocation : right.allocates = false
  left_write : ∀ x, left.writes x → ¬ right.reads x ∧ ¬ right.writes x
  right_write : ∀ x, right.writes x → ¬ left.reads x ∧ ¬ left.writes x

theorem Compatible.symm {a b : Access} (h : Compatible a b) : Compatible b a :=
  ⟨h.right_no_allocation, h.left_no_allocation, h.right_write, h.left_write⟩

theorem empty_compatible (a : Access) (ha : a.allocates = false) : Compatible empty a := by
  refine ⟨rfl, ha, ?_, ?_⟩ <;> simp [empty]

theorem compatible_empty (a : Access) (ha : a.allocates = false) : Compatible a empty :=
  (empty_compatible a ha).symm

theorem reads_compatible (a b : Access) (ha : a.allocates = false)
    (hb : b.allocates = false) (wa : ∀ x, ¬ a.writes x) (wb : ∀ x, ¬ b.writes x) :
    Compatible a b := by
  exact ⟨ha, hb, fun x h => (wa x h).elim, fun x h => (wb x h).elim⟩

theorem Compatible.union_left {a b c : Access} (ha : Compatible a c)
    (hb : Compatible b c) : Compatible (union a b) c := by
  refine ⟨by simp [union, ha.left_no_allocation, hb.left_no_allocation],
    ha.right_no_allocation, ?_, ?_⟩
  · intro x h
    cases h with
    | inl h => exact ha.left_write x h
    | inr h => exact hb.left_write x h
  · intro x h
    have a := ha.right_write x h
    have b := hb.right_write x h
    exact ⟨fun h => h.elim a.1 b.1, fun h => h.elim a.2 b.2⟩

theorem Compatible.union_right {a b c : Access} (hb : Compatible a b)
    (hc : Compatible a c) : Compatible a (union b c) :=
  (hb.symm.union_left hc.symm).symm

/-- A source-facing upper bound for an execution's permitted accesses. -/
def Within (actual allowed : Access) : Prop :=
  (∀ x, actual.reads x → allowed.reads x) ∧
  (∀ x, actual.writes x → allowed.writes x) ∧
  (actual.allocates = true → allowed.allocates = true)

theorem Within.refl (a : Access) : Within a a := ⟨fun _ h => h, fun _ h => h, id⟩

theorem Within.empty (a : Access) : Within empty a := by
  simp [Within, Access.empty]

theorem Within.union {a b c : Access} (ha : Within a c) (hb : Within b c) :
    Within (Access.union a b) c := by
  refine ⟨fun x h => h.elim (ha.1 x) (hb.1 x),
    fun x h => h.elim (ha.2.1 x) (hb.2.1 x), ?_⟩
  intro h
  simp only [Access.union, Bool.or_eq_true] at h
  exact h.elim ha.2.2 hb.2.2

theorem Within.union_mono {a b c d : Access} (ha : Within a c) (hb : Within b d) :
    Within (Access.union a b) (Access.union c d) := by
  refine ⟨fun x h => h.elim (fun h => Or.inl (ha.1 x h))
    (fun h => Or.inr (hb.1 x h)),
    fun x h => h.elim (fun h => Or.inl (ha.2.1 x h))
    (fun h => Or.inr (hb.2.1 x h)), ?_⟩
  intro h
  simp only [Access.union, Bool.or_eq_true] at h ⊢
  exact h.elim (fun h => Or.inl (ha.2.2 h)) (fun h => Or.inr (hb.2.2 h))

theorem Within.trans {a b c : Access} (ab : Within a b) (bc : Within b c) : Within a c :=
  ⟨fun x h => bc.1 x (ab.1 x h), fun x h => bc.2.1 x (ab.2.1 x h),
   fun h => bc.2.2 (ab.2.2 h)⟩

theorem Compatible.of_within {a b a' b' : Access} (h : Compatible a' b')
    (ha : Within a a') (hb : Within b b') : Compatible a b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases e : a.allocates
    · rfl
    · have := ha.2.2 e; simp [h.left_no_allocation] at this
  · cases e : b.allocates
    · rfl
    · have := hb.2.2 e; simp [h.right_no_allocation] at this
  · intro x hx
    have safe := h.left_write x (ha.2.1 x hx)
    exact ⟨fun hr => safe.1 (hb.1 x hr), fun hw => safe.2 (hb.2.1 x hw)⟩
  · intro x hx
    have safe := h.right_write x (hb.2.1 x hx)
    exact ⟨fun hr => safe.1 (ha.1 x hr), fun hw => safe.2 (ha.2.1 x hw)⟩

/-- Even writing a cell back to its old value conflicts with a sibling read. -/
theorem not_write_read (ref : Nat) (index : Int) :
    ¬ Compatible (writeSeq ref index) (readSeq ref index) := by
  intro h
  exact (h.left_write (.seq ref index) rfl).1 rfl

theorem not_write_write (ref : Nat) (index : Int) :
    ¬ Compatible (writeSeq ref index) (writeSeq ref index) := by
  intro h
  exact (h.left_write (.seq ref index) rfl).2 rfl

theorem not_allocation (other : Access) : ¬ Compatible allocation other := by
  intro h
  have := h.left_no_allocation
  contradiction

end Access

/-- A separately checked completed call, retaining its cost and access record.
The continuation permits importing a module with a different result type. -/
structure Invocation (Heap : Type u) (Frame : Type v) where
  run : Heap → Frame → Cost → Access → Prop
  unique : ∀ {h f c a h' f' c' a'}, run h f c a → run h' f' c' a' →
    h = h' ∧ f = f' ∧ c = c' ∧ a = a'
  bounded : ∀ {h f c a}, run h f c a → c.span ≤ c.work

/-- One generated instruction. Pure expression accesses are included in the
primitive or return instruction that evaluates them. Calls evaluate arguments
before entering the callee; fork arguments are evaluated before either child. -/
inductive Action (Heap : Type u) (Frame : Type v) (Result : Type w) where
  | ret (result : Result) (access : Access)
  | step (heap : Heap) (frame : Frame) (access : Access)
  | call (child : Frame) (resume : Result → Frame)
  | fork (left right : Frame) (resume : Result → Result → Frame)
  | invoke (callee : Invocation Heap Frame)
  | fail

variable {Heap : Type u} {Frame : Type v} {Result : Type w}

/-- Completed structured execution. The heap/result, costs, and access record
belong to the same derivation. The fork's right child starts from the left
child's final heap, giving the canonical serialization; the compatibility
premise checks all recorded access bounds before assigning parallel span. -/
inductive Eval (next : Heap → Frame → Action Heap Frame Result) :
    Heap → Frame → Heap → Result → Cost → Access → Prop where
  | ret (instruction : next h f = .ret result access) :
      Eval next h f h result Cost.one access
  | step (instruction : next h f = .step middle following access)
      (rest : Eval next middle following final result cost tail) :
      Eval next h f final result (Cost.seq Cost.one cost) (Access.union access tail)
  | call (instruction : next h f = .call child resume)
      (first : Eval next h child middle value firstCost firstAccess)
      (rest : Eval next middle (resume value) final result restCost restAccess) :
      Eval next h f final result (Cost.seq Cost.one (Cost.seq firstCost restCost))
        (Access.union firstAccess restAccess)
  | fork (instruction : next h f = .fork left right resume)
      (first : Eval next h left middle leftValue leftCost leftAccess)
      (second : Eval next middle right joined rightValue rightCost rightAccess)
      (independent : Access.Compatible leftAccess rightAccess)
      (rest : Eval next joined (resume leftValue rightValue) final result restCost restAccess) :
      Eval next h f final result (Cost.seq (Cost.fork leftCost rightCost) restCost)
        (Access.union (Access.union leftAccess rightAccess) restAccess)

  | invoke (instruction : next h f = .invoke callee)
      (first : callee.run middle following firstCost firstAccess)
      (rest : Eval next middle following final result restCost restAccess) :
      Eval next h f final result (Cost.seq Cost.one (Cost.seq firstCost restCost))
        (Access.union firstAccess restAccess)

/-- Sequential erasure retains every source operation and actual heap effect.
It drops only parallel access checks and work/span bookkeeping. -/
inductive SerialEval (next : Heap → Frame → Action Heap Frame Result) :
    Heap → Frame → Heap → Result → Prop where
  | ret (instruction : next h f = .ret result access) : SerialEval next h f h result
  | step (instruction : next h f = .step middle following access)
      (rest : SerialEval next middle following final result) : SerialEval next h f final result
  | call (instruction : next h f = .call child resume)
      (first : SerialEval next h child middle value)
      (rest : SerialEval next middle (resume value) final result) : SerialEval next h f final result
  | fork (instruction : next h f = .fork left right resume)
      (first : SerialEval next h left middle leftValue)
      (second : SerialEval next middle right joined rightValue)
      (rest : SerialEval next joined (resume leftValue rightValue) final result) :
      SerialEval next h f final result

  | invoke (instruction : next h f = .invoke callee)
      (first : callee.run middle following firstCost firstAccess)
      (rest : SerialEval next middle following final result) :
      SerialEval next h f final result

namespace Eval

variable {next : Heap → Frame → Action Heap Frame Result}

theorem serial (run : Eval next h f final result cost access) :
    SerialEval next h f final result := by
  induction run with
  | ret instruction => exact .ret instruction
  | invoke instruction first _ ih => exact .invoke instruction first ih
  | step instruction _ ih => exact .step instruction ih
  | call instruction _ _ ihFirst ihRest => exact .call instruction ihFirst ihRest
  | fork instruction _ _ _ _ ihFirst ihSecond ihRest =>
      exact .fork instruction ihFirst ihSecond ihRest

/-- Span never exceeds total work for the same completed execution. -/
theorem span_le_work (run : Eval next h f final result cost access) : cost.span ≤ cost.work := by
  induction run with
  | ret => exact Nat.le_refl _
  | invoke _ first _ ih =>
      exact Cost.seq_span_le_work (Nat.le_refl _) (Cost.seq_span_le_work (Invocation.bounded _ first) ih)
  | step _ _ ih => exact Cost.seq_span_le_work (Nat.le_refl _) ih
  | call _ _ _ ihFirst ihRest =>
      exact Cost.seq_span_le_work (Nat.le_refl _) (Cost.seq_span_le_work ihFirst ihRest)
  | fork _ _ _ _ _ ihFirst ihSecond ihRest =>
      exact Cost.seq_span_le_work (Cost.fork_span_le_work ihFirst ihSecond) ihRest

/-- A fixed initial heap and source frame determine all completed results and
costs. Compatibility cannot be used to select a cheaper successful schedule. -/
theorem deterministic (first : Eval next h f final result cost access)
    (second : Eval next h f other output otherCost otherAccess) :
    final = other ∧ result = output ∧ cost = otherCost ∧ access = otherAccess := by
  induction first generalizing other output otherCost otherAccess with
  | ret instruction => cases second <;> simp_all
  | step instruction rest ih =>
      cases second with
      | ret => simp_all
      | invoke => simp_all
      | call => simp_all
      | fork => simp_all
      | step other rest2 =>
          obtain ⟨rfl, rfl, rfl⟩ := Action.step.inj (instruction.symm.trans other)
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ih rest2
          exact ⟨rfl, rfl, rfl, rfl⟩
  | call instruction first rest ihFirst ihRest =>
      cases second with
      | ret => simp_all
      | invoke => simp_all
      | step => simp_all
      | fork => simp_all
      | call other first2 rest2 =>
          obtain ⟨rfl, rfl⟩ := Action.call.inj (instruction.symm.trans other)
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ihFirst first2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ihRest rest2
          exact ⟨rfl, rfl, rfl, rfl⟩
  | fork instruction first branch independent rest ihFirst ihSecond ihRest =>
      cases second with
      | ret => simp_all
      | invoke => simp_all
      | step => simp_all
      | call => simp_all
      | fork other first2 second2 safe rest2 =>
          obtain ⟨rfl, rfl, rfl⟩ := Action.fork.inj (instruction.symm.trans other)
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ihFirst first2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ihSecond second2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ihRest rest2
          exact ⟨rfl, rfl, rfl, rfl⟩
  | invoke instruction first rest ih =>
      cases second with
      | ret => simp_all
      | step => simp_all
      | call => simp_all
      | fork => simp_all
      | invoke other first2 rest2 =>
          obtain rfl := Action.invoke.inj (instruction.symm.trans other)
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Invocation.unique _ first first2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ih rest2
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem not_of_fail (failed : next h f = .fail) :
    ¬ Eval next h f final result cost access := by
  intro run
  cases run <;> simp_all

/-- Package the original module's evaluation without copying its instructions. -/
def invocation {TargetFrame : Type v'} (next : Heap → Frame → Action Heap Frame Result)
    (heap : Heap) (frame : Frame) (resume : Result → TargetFrame) : Invocation Heap TargetFrame where
  run final following cost access := ∃ result,
    Eval next heap frame final result cost access ∧ following = resume result
  unique := by
    rintro h f c a h' f' c' a' ⟨r, first, rfl⟩ ⟨r', second, rfl⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := first.deterministic second
    exact ⟨rfl, rfl, rfl, rfl⟩
  bounded := by
    rintro h f c a ⟨r, run, _⟩
    exact run.span_le_work

end Eval

/-- Local obligations for connecting the structured descriptions to the
compiler's ordinary stack-transition semantics. Fork simulation uses the two
sequential call sites generated by erasing the fork. These obligations mention
only one instruction and reusable child summaries, not complete executions. -/
structure Simulation (next : Heap → Frame → Action Heap Frame Result)
    (transition : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop) : Prop where
  ret : ∀ h f result access, next h f = .ret result access →
    Algo2LeanCore.Summary transition h f h result
  step : ∀ h f middle following access, next h f = .step middle following access →
    ∀ final result, Algo2LeanCore.Summary transition middle following final result →
      Algo2LeanCore.Summary transition h f final result
  call : ∀ h f child resume, next h f = .call child resume →
    ∀ middle value final result,
      Algo2LeanCore.Summary transition h child middle value →
      Algo2LeanCore.Summary transition middle (resume value) final result →
      Algo2LeanCore.Summary transition h f final result
  fork : ∀ h f left right resume, next h f = .fork left right resume →
    ∀ middle leftValue joined rightValue final result,
      Algo2LeanCore.Summary transition h left middle leftValue →
      Algo2LeanCore.Summary transition middle right joined rightValue →
      Algo2LeanCore.Summary transition joined (resume leftValue rightValue) final result →
      Algo2LeanCore.Summary transition h f final result

  invoke : ∀ h f callee, next h f = .invoke callee →
    ∀ middle following cost access final result, callee.run middle following cost access →
      Algo2LeanCore.Summary transition middle following final result →
      Algo2LeanCore.Summary transition h f final result

/-- A single instruction preserves the sequential meaning of its children.
This form lets generated code check the simulation once per program counter. -/
def Action.Simulates
    (transition : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop)
    (h : Heap) (f : Frame) : Action Heap Frame Result → Prop
  | .ret result _ => Algo2LeanCore.Summary transition h f h result
  | .step middle following _ => ∀ final result,
      Algo2LeanCore.Summary transition middle following final result →
      Algo2LeanCore.Summary transition h f final result
  | .call child resume => ∀ middle value final result,
      Algo2LeanCore.Summary transition h child middle value →
      Algo2LeanCore.Summary transition middle (resume value) final result →
      Algo2LeanCore.Summary transition h f final result
  | .fork left right resume => ∀ middle leftValue joined rightValue final result,
      Algo2LeanCore.Summary transition h left middle leftValue →
      Algo2LeanCore.Summary transition middle right joined rightValue →
      Algo2LeanCore.Summary transition joined (resume leftValue rightValue) final result →
      Algo2LeanCore.Summary transition h f final result
  | .invoke callee => ∀ middle following cost access final result,
      callee.run middle following cost access →
      Algo2LeanCore.Summary transition middle following final result →
      Algo2LeanCore.Summary transition h f final result
  | .fail => True

theorem Simulation.of_simulates
    {next : Heap → Frame → Action Heap Frame Result}
    {transition : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop}
    (sound : ∀ h f, Action.Simulates transition h f (next h f)) : Simulation next transition := by
  constructor
  · intro h f result access instruction
    simpa only [instruction, Action.Simulates] using sound h f
  · intro h f middle following access instruction
    simpa only [instruction, Action.Simulates] using sound h f
  · intro h f child resume instruction
    simpa only [instruction, Action.Simulates] using sound h f
  · intro h f left right resume instruction
    simpa only [instruction, Action.Simulates] using sound h f

  · intro h f callee instruction
    simpa only [instruction, Action.Simulates] using sound h f

/-- A stuck active frame cannot complete even with an empty caller stack. -/
theorem not_summary_of_stuck
    {transition : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop}
    (stuck : ∀ after, ¬ transition (.active h f []) after) :
    ¬ Algo2LeanCore.Summary transition h f final result := by
  intro summary
  obtain ⟨states, valid⟩ := summary []
  cases valid with
  | cons first rest => exact stuck _ first

namespace SerialEval

variable {next : Heap → Frame → Action Heap Frame Result}
variable {step : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop}

theorem summary (run : SerialEval next h f final result) (simulation : Simulation next step) :
    Algo2LeanCore.Summary step h f final result := by
  induction run with
  | ret instruction => exact simulation.ret _ _ _ _ instruction
  | invoke instruction first _ ih => exact simulation.invoke _ _ _ instruction _ _ _ _ _ _ first ih
  | step instruction _ ih => exact simulation.step _ _ _ _ _ instruction _ _ ih
  | call instruction _ _ ihFirst ihRest =>
      exact simulation.call _ _ _ _ instruction _ _ _ _ ihFirst ihRest
  | fork instruction _ _ _ ihFirst ihSecond ihRest =>
      exact simulation.fork _ _ _ _ _ instruction _ _ _ _ _ _ ihFirst ihSecond ihRest

/-- The canonical serialization is deterministic whenever it completes. -/
theorem deterministic (first : SerialEval next h f final result)
    (second : SerialEval next h f other output) : final = other ∧ result = output := by
  induction first generalizing other output with
  | ret instruction => cases second <;> simp_all
  | step instruction rest ih =>
      cases second with
      | ret => simp_all
      | invoke => simp_all
      | call => simp_all
      | fork => simp_all
      | step other rest2 =>
          obtain ⟨rfl, rfl, rfl⟩ := Action.step.inj (instruction.symm.trans other)
          exact ih rest2
  | call instruction first rest ihFirst ihRest =>
      cases second with
      | ret => simp_all
      | invoke => simp_all
      | step => simp_all
      | fork => simp_all
      | call other first2 rest2 =>
          obtain ⟨rfl, rfl⟩ := Action.call.inj (instruction.symm.trans other)
          obtain ⟨rfl, rfl⟩ := ihFirst first2
          exact ihRest rest2
  | fork instruction first branch rest ihFirst ihSecond ihRest =>
      cases second with
      | ret => simp_all
      | invoke => simp_all
      | step => simp_all
      | call => simp_all
      | fork other first2 second2 rest2 =>
          obtain ⟨rfl, rfl, rfl⟩ := Action.fork.inj (instruction.symm.trans other)
          obtain ⟨rfl, rfl⟩ := ihFirst first2
          obtain ⟨rfl, rfl⟩ := ihSecond second2
          exact ihRest rest2
  | invoke instruction first rest ih =>
      cases second with
      | ret => simp_all
      | step => simp_all
      | call => simp_all
      | fork => simp_all
      | invoke other first2 rest2 =>
          obtain rfl := Action.invoke.inj (instruction.symm.trans other)
          obtain ⟨rfl, rfl, _, _⟩ := Invocation.unique _ first first2
          exact ih rest2

end SerialEval

namespace Eval

variable {next : Heap → Frame → Action Heap Frame Result}
variable {step : Algo2LeanCore.Config Heap Frame Result → Algo2LeanCore.Config Heap Frame Result → Prop}

theorem summary (run : Eval next h f final result cost access) (simulation : Simulation next step) :
    Algo2LeanCore.Summary step h f final result := run.serial.summary simulation

end Eval

end Algo2LeanParallel
