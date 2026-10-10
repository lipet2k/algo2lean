import MatrixStrassenGenerated

/-! Composition of the recursive branch using only source-level call summaries.
Each field records one real source call in evaluation order, including nested
arguments. This lemma by itself assumes no mathematical correctness contract. -/

open Algo2LeanCore Algo2LeanGenerated

namespace MatrixStrassenComposition

/-- The returned heap and reference of one source call. -/
structure SeqResult where
  heap : Heap
  result : SeqRef

/-- One completed source call, valid under every caller stack. -/
structure SeqRun (summary : Heap → SeqRef → Prop) extends SeqResult where
  run : summary heap result

/-- The 34 completed calls of a nontrivial Strassen invocation, in their actual
    left-to-right evaluation order. Intermediate references are explicit. -/
structure BranchRun (startHeap : Heap) (a b : SeqRef) (n half : Int) where
  a11 : SeqResult
  a12 : SeqResult
  a21 : SeqResult
  a22 : SeqResult
  b11 : SeqResult
  b12 : SeqResult
  b21 : SeqResult
  b22 : SeqResult
  linear1 : SeqResult
  p1 : SeqResult
  linear2 : SeqResult
  p2 : SeqResult
  linear3 : SeqResult
  p3 : SeqResult
  linear4 : SeqResult
  p4 : SeqResult
  linear5 : SeqResult
  linear6 : SeqResult
  p5 : SeqResult
  linear7 : SeqResult
  linear8 : SeqResult
  p6 : SeqResult
  linear9 : SeqResult
  linear10 : SeqResult
  p7 : SeqResult
  linear11 : SeqResult
  linear12 : SeqResult
  c11 : SeqResult
  c12 : SeqResult
  c21 : SeqResult
  linear16 : SeqResult
  linear17 : SeqResult
  c22 : SeqResult
  joined : SeqResult
  a11_run : matrix_quadrant.Call startHeap (a, n, half, 0, 0) a11.heap a11.result
  a12_run : matrix_quadrant.Call a11.heap (a, n, half, 0, half) a12.heap a12.result
  a21_run : matrix_quadrant.Call a12.heap (a, n, half, half, 0) a21.heap a21.result
  a22_run : matrix_quadrant.Call a21.heap (a, n, half, half, half) a22.heap a22.result
  b11_run : matrix_quadrant.Call a22.heap (b, n, half, 0, 0) b11.heap b11.result
  b12_run : matrix_quadrant.Call b11.heap (b, n, half, 0, half) b12.heap b12.result
  b21_run : matrix_quadrant.Call b12.heap (b, n, half, half, 0) b21.heap b21.result
  b22_run : matrix_quadrant.Call b21.heap (b, n, half, half, half) b22.heap b22.result
  linear1_run : matrix_linear.Call b22.heap (b12.result, b22.result, (half * half), -1) linear1.heap linear1.result
  p1_run : strassen.Call linear1.heap (a11.result, linear1.result, half) p1.heap p1.result
  linear2_run : matrix_linear.Call p1.heap (a11.result, a12.result, (half * half), 1) linear2.heap linear2.result
  p2_run : strassen.Call linear2.heap (linear2.result, b22.result, half) p2.heap p2.result
  linear3_run : matrix_linear.Call p2.heap (a21.result, a22.result, (half * half), 1) linear3.heap linear3.result
  p3_run : strassen.Call linear3.heap (linear3.result, b11.result, half) p3.heap p3.result
  linear4_run : matrix_linear.Call p3.heap (b21.result, b11.result, (half * half), -1) linear4.heap linear4.result
  p4_run : strassen.Call linear4.heap (a22.result, linear4.result, half) p4.heap p4.result
  linear5_run : matrix_linear.Call p4.heap (a11.result, a22.result, (half * half), 1) linear5.heap linear5.result
  linear6_run : matrix_linear.Call linear5.heap (b11.result, b22.result, (half * half), 1) linear6.heap linear6.result
  p5_run : strassen.Call linear6.heap (linear5.result, linear6.result, half) p5.heap p5.result
  linear7_run : matrix_linear.Call p5.heap (a12.result, a22.result, (half * half), -1) linear7.heap linear7.result
  linear8_run : matrix_linear.Call linear7.heap (b21.result, b22.result, (half * half), 1) linear8.heap linear8.result
  p6_run : strassen.Call linear8.heap (linear7.result, linear8.result, half) p6.heap p6.result
  linear9_run : matrix_linear.Call p6.heap (a11.result, a21.result, (half * half), -1) linear9.heap linear9.result
  linear10_run : matrix_linear.Call linear9.heap (b11.result, b12.result, (half * half), 1) linear10.heap linear10.result
  p7_run : strassen.Call linear10.heap (linear9.result, linear10.result, half) p7.heap p7.result
  linear11_run : matrix_linear.Call p7.heap (p5.result, p4.result, (half * half), 1) linear11.heap linear11.result
  linear12_run : matrix_linear.Call linear11.heap (linear11.result, p2.result, (half * half), -1) linear12.heap linear12.result
  c11_run : matrix_linear.Call linear12.heap (linear12.result, p6.result, (half * half), 1) c11.heap c11.result
  c12_run : matrix_linear.Call c11.heap (p1.result, p2.result, (half * half), 1) c12.heap c12.result
  c21_run : matrix_linear.Call c12.heap (p3.result, p4.result, (half * half), 1) c21.heap c21.result
  linear16_run : matrix_linear.Call c21.heap (p5.result, p1.result, (half * half), 1) linear16.heap linear16.result
  linear17_run : matrix_linear.Call linear16.heap (linear16.result, p3.result, (half * half), -1) linear17.heap linear17.result
  c22_run : matrix_linear.Call linear17.heap (linear17.result, p7.result, (half * half), -1) c22.heap c22.result
  joined_run : matrix_join.Call c22.heap (c11.result, c12.result, c21.result, c22.result, half) joined.heap joined.result
  result_valid : joined.result < joined.heap.nextRef

abbrev BranchRun.finalHeap {heap a b n half} (plan : BranchRun heap a b n half) : Heap :=
  plan.joined.heap

abbrev BranchRun.result {heap a b n half} (plan : BranchRun heap a b n half) : SeqRef :=
  plan.joined.result

set_option maxHeartbeats 1600000 in
/-- Composing the branch calls produces a summary of the actual generated
    program. The initial call tick is included, while each supplied summary
    accounts for its own heap effects and operation counts. -/
theorem recursive_summary (heap : Heap) (a b : SeqRef) (n half : Int)
    (validA : a < heap.nextRef) (validB : b < heap.nextRef)
    (recursive : 1 < n) (halfEq : Int.fdiv n 2 = half)
    (plan : BranchRun (heap.tick "calls") a b n half) :
    strassen.Call heap (a, b, n) plan.finalHeap plan.result := by
  refine ⟨⟨validA, validB⟩, ?_⟩
  intro stack
  apply Reaches.prepend (Step.strassen_pc189 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc188 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc187_false _ _ _ (by simp; omega))
  dsimp only
  apply Reaches.prepend (Step.strassen_pc186 _ _ _ (by decide))
  dsimp only
  simp only [halfEq]
  apply Reaches.prepend (Step.strassen_pc185 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc184 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc183 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc182 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc181 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc180 ..)
  dsimp only
  apply Reaches.trans (plan.a11_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc179 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc178 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc177 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc176 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc175 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc174 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc173 ..)
  dsimp only
  apply Reaches.trans (plan.a12_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc172 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc171 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc170 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc169 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc168 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc167 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc166 ..)
  dsimp only
  apply Reaches.trans (plan.a21_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc165 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc164 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc163 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc162 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc161 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc160 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc159 ..)
  dsimp only
  apply Reaches.trans (plan.a22_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc158 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc157 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc156 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc155 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc154 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc153 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc152 ..)
  dsimp only
  apply Reaches.trans (plan.b11_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc151 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc150 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc149 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc148 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc147 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc146 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc145 ..)
  dsimp only
  apply Reaches.trans (plan.b12_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc144 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc143 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc142 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc141 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc140 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc139 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc138 ..)
  dsimp only
  apply Reaches.trans (plan.b21_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc137 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc136 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc135 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc134 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc133 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc132 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc131 ..)
  dsimp only
  apply Reaches.trans (plan.b22_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc130 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc129 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc128 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc127 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc126 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc125 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc124 ..)
  dsimp only
  apply Reaches.trans (plan.linear1_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc123 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc122 ..)
  dsimp only
  apply Reaches.trans (plan.p1_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc121 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc120 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc119 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc118 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc117 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc116 ..)
  dsimp only
  apply Reaches.trans (plan.linear2_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc115 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc114 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc113 ..)
  dsimp only
  apply Reaches.trans (plan.p2_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc112 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc111 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc110 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc109 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc108 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc107 ..)
  dsimp only
  apply Reaches.trans (plan.linear3_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc106 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc105 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc104 ..)
  dsimp only
  apply Reaches.trans (plan.p3_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc103 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc102 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc101 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc100 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc99 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc98 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc97 ..)
  dsimp only
  apply Reaches.trans (plan.linear4_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc96 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc95 ..)
  dsimp only
  apply Reaches.trans (plan.p4_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc94 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc93 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc92 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc91 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc90 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc89 ..)
  dsimp only
  apply Reaches.trans (plan.linear5_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc88 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc87 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc86 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc85 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc84 ..)
  dsimp only
  apply Reaches.trans (plan.linear6_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc83 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc82 ..)
  dsimp only
  apply Reaches.trans (plan.p5_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc81 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc80 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc79 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc78 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc77 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc76 ..)
  dsimp only
  apply Reaches.trans (plan.linear7_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc75 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc74 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc73 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc72 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc71 ..)
  dsimp only
  apply Reaches.trans (plan.linear8_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc70 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc69 ..)
  dsimp only
  apply Reaches.trans (plan.p6_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc68 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc67 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc66 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc65 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc64 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc63 ..)
  dsimp only
  apply Reaches.trans (plan.linear9_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc62 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc61 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc60 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc59 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc58 ..)
  dsimp only
  apply Reaches.trans (plan.linear10_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc57 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc56 ..)
  dsimp only
  apply Reaches.trans (plan.p7_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc55 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc54 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc53 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc52 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc51 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc50 ..)
  dsimp only
  apply Reaches.trans (plan.linear11_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc49 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc48 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc47 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc46 ..)
  dsimp only
  apply Reaches.trans (plan.linear12_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc45 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc44 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc43 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc42 ..)
  dsimp only
  apply Reaches.trans (plan.c11_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc41 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc40 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc39 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc38 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc37 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc36 ..)
  dsimp only
  apply Reaches.trans (plan.c12_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc35 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc34 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc33 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc32 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc31 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc30 ..)
  dsimp only
  apply Reaches.trans (plan.c21_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc29 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc28 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc27 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc26 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc25 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc24 ..)
  dsimp only
  apply Reaches.trans (plan.linear16_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc23 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc22 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc21 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc20 ..)
  dsimp only
  apply Reaches.trans (plan.linear17_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc19 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc18 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc17 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc16 ..)
  dsimp only
  apply Reaches.trans (plan.c22_run.2 _)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc15 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc14 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc13 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc12 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc11 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc10 ..)
  dsimp only
  apply Reaches.prepend (Step.strassen_pc9 ..)
  dsimp only
  apply Reaches.trans (plan.joined_run.2 _)
  dsimp only
  exact Reaches.single (Step.strassen_pc8 _ _ _ plan.result_valid)

end MatrixStrassenComposition
