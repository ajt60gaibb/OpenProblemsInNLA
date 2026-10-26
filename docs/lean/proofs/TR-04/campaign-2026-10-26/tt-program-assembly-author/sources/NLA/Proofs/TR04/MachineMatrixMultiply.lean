import NLA.Proofs.TR04.MachineMatrixMultiplyMemory
import NLA.Proofs.TR04.MachineScalarBlocks
import Mathlib.Tactic.FinCases

/-! One fixed finite exact-real RAM program for strided matrix multiplication.
All loop tests, address arithmetic, scalar products, additions and stores are
literal instructions of the unchanged machine. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Natural registers are i,j,a,m,k,n,B,C,D,bp,cp,dp,zero,br,bc,cr,cc.
Real registers are the accumulating sum, the B value/product, and the C value.
No constant pool and no division instruction is used. -/
def matrixMultiplyProgram : Program where
  extraLabels := 21
  realRegisters := 3
  extraNatRegisters := 16
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .lessNat 0 3 1 21
    | 1 => .natural 1 0 2
    | 2 => .lessNat 1 5 3 20
    | 3 => .natural 2 0 4
    | 4 => .castNat 0 12 5
    | 5 => .mulNat 9 0 13 6
    | 6 => .addNat 9 6 9 7
    | 7 => .mulNat 10 1 16 8
    | 8 => .addNat 10 7 10 9
    | 9 => .lessNat 2 4 10 17
    | 10 => .read 1 9 11
    | 11 => .read 2 10 12
    | 12 => .mulReal 1 1 2 13
    | 13 => .addReal 0 0 1 14
    | 14 => .addNat 9 9 14 15
    | 15 => .addNat 10 10 15 16
    | 16 => .increment 2 9
    | 17 => .write 11 0 18
    | 18 => .increment 11 19
    | 19 => .increment 1 2
    | 20 => .increment 0 0
    | _ => .halt 8

structure MatrixMultiplyScratch where
  a : ℕ
  bp : ℕ
  cp : ℕ
  real : Fin 3 → ℝ

def matrixMultiplyState (p : MatrixMultiplyData) (i j a bp cp dp : ℕ)
    (reals : Fin 3 → ℝ) (memory : ℕ → ℝ) (label : Fin 22) : State matrixMultiplyProgram where
  label := label
  real := reals
  natural := ![i, j, a, p.rows, p.inner, p.cols, p.bBase, p.cBase, p.dBase,
    bp, cp, dp, 0, p.bRowStride, p.bColStride, p.cRowStride, p.cColStride]
  memory := memory
  status := .running

def matrixMultiplyCellState (p : MatrixMultiplyData) (i j : ℕ)
    (scratch : MatrixMultiplyScratch) : State matrixMultiplyProgram :=
  matrixMultiplyState p i j scratch.a scratch.bp scratch.cp (p.dBase + i * p.cols + j)
    scratch.real (p.outputPrefix (i * p.cols + j)) 2

def matrixMultiplyInnerState (p : MatrixMultiplyData) (i j a : ℕ) (rb rc : ℝ) :
    State matrixMultiplyProgram :=
  matrixMultiplyState p i j a (p.bAddress i a) (p.cAddress a j)
    (p.dBase + i * p.cols + j) ![p.partialProduct i j a, rb, rc]
    (p.outputPrefix (i * p.cols + j)) 9

def matrixMultiplyRowState (p : MatrixMultiplyData) (i : ℕ)
    (scratch : MatrixMultiplyScratch) : State matrixMultiplyProgram :=
  matrixMultiplyState p i p.cols scratch.a scratch.bp scratch.cp (p.dBase + i * p.cols)
    scratch.real (p.outputPrefix (i * p.cols)) 0

theorem matrixMultiplyProgram_scalar (s : State matrixMultiplyProgram) :
    instructionIsSVD (matrixMultiplyProgram.code s.label) = false := by
  rcases s with ⟨label, reals, naturals, memory, status⟩
  fin_cases label <;> rfl

/-- The seven setup transitions reset the sum and compute both starting pointers. -/
theorem matrixMultiplyProgram_cell_setup (p : MatrixMultiplyData) (i j : ℕ)
    (scratch : MatrixMultiplyScratch) (hj : j < p.cols) :
    (ordinaryStep matrixMultiplyProgram)^[7] (matrixMultiplyCellState p i j scratch) =
      matrixMultiplyInnerState p i j 0 (scratch.real 1) (scratch.real 2) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    matrixMultiplyProgram, matrixMultiplyCellState, matrixMultiplyInnerState,
    matrixMultiplyState, MatrixMultiplyData.bAddress, MatrixMultiplyData.cAddress,
    MatrixMultiplyData.partialProduct_zero, hj]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

/-- One dot-product term uses exactly eight actual scalar transitions. -/
theorem matrixMultiplyProgram_inner_eight (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (i j a : ℕ) (rb rc : ℝ)
    (hi : i < p.rows) (hj : j < p.cols) (ha : a < p.inner) :
    (ordinaryStep matrixMultiplyProgram)^[8] (matrixMultiplyInnerState p i j a rb rc) =
      matrixMultiplyInnerState p i j (a + 1)
        (p.memory (p.bAddress i a) * p.memory (p.cAddress a j))
        (p.memory (p.cAddress a j)) := by
  have hbound : i * p.cols + j ≤ p.rows * p.cols :=
    Nat.le_of_lt (matrix_offset_lt (⟨i, hi⟩ : Fin p.rows) (⟨j, hj⟩ : Fin p.cols))
  have hb := p.outputPrefix_b h _ i a hbound hi ha
  have hc := p.outputPrefix_c h _ a j hbound ha hj
  have hsum := p.partialProduct_succ i j a
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    matrixMultiplyProgram, matrixMultiplyInnerState, matrixMultiplyState, ha,
    hb, hc, hsum]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, MatrixMultiplyData.bAddress,
      MatrixMultiplyData.cAddress, Nat.add_mul, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]

theorem matrixMultiplyProgram_inner_iterations (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (i j : ℕ) (rb rc : ℝ)
    (hi : i < p.rows) (hj : j < p.cols) (a : ℕ) (ha : a ≤ p.inner) :
    ∃ vb vc : ℝ, (ordinaryStep matrixMultiplyProgram)^[8 * a]
      (matrixMultiplyInnerState p i j 0 rb rc) = matrixMultiplyInnerState p i j a vb vc := by
  induction a with
  | zero => exact ⟨rb, rc, rfl⟩
  | succ a ih =>
      obtain ⟨vb, vc, hv⟩ := ih (by omega)
      refine ⟨p.memory (p.bAddress i a) * p.memory (p.cAddress a j),
        p.memory (p.cAddress a j), ?_⟩
      rw [Nat.mul_succ, Nat.add_comm (8 * a) 8, Function.iterate_add_apply, hv]
      exact matrixMultiplyProgram_inner_eight p h i j a vb vc hi hj (by omega)

/-- The failed inner test, output store and two increments take four transitions. -/
theorem matrixMultiplyProgram_cell_exit (p : MatrixMultiplyData)
    (i j : ℕ) (rb rc : ℝ) (hi : i < p.rows) (hj : j < p.cols) :
    (ordinaryStep matrixMultiplyProgram)^[4]
      (matrixMultiplyInnerState p i j p.inner rb rc) =
      matrixMultiplyCellState p i (j + 1)
        ⟨p.inner, p.bAddress i p.inner, p.cAddress p.inner j,
          ![p.partialProduct i j p.inner, rb, rc]⟩ := by
  have hm := p.outputPrefix_update (⟨i, hi⟩ : Fin p.rows) (⟨j, hj⟩ : Fin p.cols)
  change Function.update (p.outputPrefix (i * p.cols + j))
    (p.dBase + i * p.cols + j) (p.partialProduct i j p.inner) =
    p.outputPrefix (i * p.cols + j + 1) at hm
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    matrixMultiplyProgram, matrixMultiplyInnerState, matrixMultiplyCellState,
    matrixMultiplyState, Nat.add_assoc]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]
  · simpa only [Nat.add_assoc] using hm

#assert_trust kernel matrixMultiplyProgram_inner_eight
#assert_trust kernel matrixMultiplyProgram_cell_exit
#print axioms matrixMultiplyProgram_inner_eight
#print axioms matrixMultiplyProgram_cell_exit
end NLA.Proofs.TR04
