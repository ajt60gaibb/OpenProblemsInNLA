import NLA.Proofs.TR04.TTMemoryLayoutBounds
import NLA.Proofs.TR04.MachineMatrixMultiplyMemory

/-! Actual strided matrix-routine entry contracts for contraction and lifting.
The frame fits its square reservation. Each dense work size is an explicit
hypothesis; individual dimension bounds do not replace a product bound. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine

 def Layout.contraction (L : Layout) (level rows width cols : ℕ) (memory : ℕ → ℝ) :
    NLA.Proofs.TR04.MatrixMultiplyData where
  rows := width
  inner := rows
  cols := cols
  bBase := L.frame level
  cBase := L.workA
  dBase := L.workB
  bRowStride := 1
  bColStride := width
  cRowStride := cols
  cColStride := 1
  memory := memory

 def Layout.lifting (L : Layout) (level rows width cols : ℕ) (memory : ℕ → ℝ) :
    NLA.Proofs.TR04.MatrixMultiplyData where
  rows := rows
  inner := width
  cols := cols
  bBase := L.frame level
  cBase := L.workA
  dBase := L.workB
  bRowStride := width
  bColStride := 1
  cRowStride := cols
  cColStride := 1
  memory := memory

 theorem Layout.contraction_inputsOutsideOutput (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) (hlevel : level < L.order)
    (hm : rows ≤ L.entries) (hq : width ≤ L.entries)
    (hinput : rows * cols ≤ L.entries) (houtput : width * cols ≤ L.entries) :
    (L.contraction level rows width cols memory).InputsOutsideOutput := by
  have hframe := (L.frame_work_disjoint level hlevel).2.1
  have hwork := L.work_buffers_disjoint
  constructor
  · intro i hi a ha
    have hcell := NLA.Proofs.TR04.matrix_offset_lt (⟨a, ha⟩ : Fin rows) (⟨i, hi⟩ : Fin width)
    change a * width + i < rows * width at hcell
    have hcap := rectangle_capacity hm hq
    intro hout
    apply NLA.Proofs.TR04.disjointBlocks_not_mem_right
      (address := L.frame level + i * 1 + a * width) hframe
    · omega
    · change L.workB ≤ L.frame level + i * 1 + a * width ∧
        L.frame level + i * 1 + a * width < L.workB + width * cols at hout
      omega
  · intro a ha j hj
    have hcell := NLA.Proofs.TR04.matrix_offset_lt (⟨a, ha⟩ : Fin rows) (⟨j, hj⟩ : Fin cols)
    change a * cols + j < rows * cols at hcell
    intro hout
    apply NLA.Proofs.TR04.disjointBlocks_not_mem_right
      (address := L.workA + a * cols + j * 1) hwork
    · omega
    · change L.workB ≤ L.workA + a * cols + j * 1 ∧
        L.workA + a * cols + j * 1 < L.workB + width * cols at hout
      omega

 theorem Layout.lifting_inputsOutsideOutput (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) (hlevel : level < L.order)
    (hm : rows ≤ L.entries) (hq : width ≤ L.entries)
    (hinput : width * cols ≤ L.entries) (houtput : rows * cols ≤ L.entries) :
    (L.lifting level rows width cols memory).InputsOutsideOutput := by
  apply NLA.Proofs.TR04.MatrixMultiplyData.dense_inputsOutsideOutput
    _ rfl rfl rfl rfl
  · exact disjoint_fits (L.frame_work_disjoint level hlevel).2.1
      (L.frame_rectangle_fits level rows width hm hq)
      (L.workB_rectangle_fits rows cols houtput)
  · exact L.work_rectangle_disjoint width cols rows cols hinput houtput

 theorem Layout.contraction_leftMatrix (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) :
    (L.contraction level rows width cols memory).leftMatrix =
      (readMatrix memory rows width (L.frame level)).transpose :=
  NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_transpose _ rfl rfl

 theorem Layout.contraction_rightMatrix (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) :
    (L.contraction level rows width cols memory).rightMatrix =
      readMatrix memory rows cols L.workA :=
  NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense _ rfl rfl

 theorem Layout.lifting_leftMatrix (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) :
    (L.lifting level rows width cols memory).leftMatrix =
      readMatrix memory rows width (L.frame level) :=
  NLA.Proofs.TR04.MatrixMultiplyData.leftMatrix_dense _ rfl rfl

 theorem Layout.lifting_rightMatrix (L : Layout) (level rows width cols : ℕ)
    (memory : ℕ → ℝ) :
    (L.lifting level rows width cols memory).rightMatrix =
      readMatrix memory width cols L.workA :=
  NLA.Proofs.TR04.MatrixMultiplyData.rightMatrix_dense _ rfl rfl

#assert_trust kernel Layout.contraction_inputsOutsideOutput
#assert_trust kernel Layout.lifting_inputsOutsideOutput
#assert_trust kernel Layout.contraction_leftMatrix
#print axioms Layout.contraction_inputsOutsideOutput
#print axioms Layout.lifting_inputsOutsideOutput
end NLA.Proofs.TR04.TTMemoryLayout
