import NLA.Proofs.TR04.MachineSVDMemory
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-! Exact memory interpretation for a strided matrix multiplication routine.
Input strides may be zero and the two input arrays may overlap. Only actual
input entries must be outside the dense output block. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
open scoped BigOperators

structure MatrixMultiplyData where
  rows : ℕ
  inner : ℕ
  cols : ℕ
  bBase : ℕ
  cBase : ℕ
  dBase : ℕ
  bRowStride : ℕ
  bColStride : ℕ
  cRowStride : ℕ
  cColStride : ℕ
  memory : ℕ → ℝ

def MatrixMultiplyData.bAddress (p : MatrixMultiplyData) (i a : ℕ) : ℕ :=
  p.bBase + i * p.bRowStride + a * p.bColStride

def MatrixMultiplyData.cAddress (p : MatrixMultiplyData) (a j : ℕ) : ℕ :=
  p.cBase + a * p.cRowStride + j * p.cColStride

def MatrixMultiplyData.leftMatrix (p : MatrixMultiplyData) :
    Matrix (Fin p.rows) (Fin p.inner) ℝ :=
  fun i a => p.memory (p.bAddress i.val a.val)

def MatrixMultiplyData.rightMatrix (p : MatrixMultiplyData) :
    Matrix (Fin p.inner) (Fin p.cols) ℝ :=
  fun a j => p.memory (p.cAddress a.val j.val)

def MatrixMultiplyData.productMatrix (p : MatrixMultiplyData) :
    Matrix (Fin p.rows) (Fin p.cols) ℝ := p.leftMatrix * p.rightMatrix

theorem MatrixMultiplyData.leftMatrix_dense (p : MatrixMultiplyData)
    (hr : p.bRowStride = p.inner) (hc : p.bColStride = 1) :
    p.leftMatrix = readMatrix p.memory p.rows p.inner p.bBase := by
  funext i a
  simp [leftMatrix, bAddress, readMatrix, hr, hc]

theorem MatrixMultiplyData.rightMatrix_dense (p : MatrixMultiplyData)
    (hr : p.cRowStride = p.cols) (hc : p.cColStride = 1) :
    p.rightMatrix = readMatrix p.memory p.inner p.cols p.cBase := by
  funext a j
  simp [rightMatrix, cAddress, readMatrix, hr, hc]

theorem MatrixMultiplyData.leftMatrix_transpose (p : MatrixMultiplyData)
    (hr : p.bRowStride = 1) (hc : p.bColStride = p.rows) :
    p.leftMatrix = (readMatrix p.memory p.inner p.rows p.bBase).transpose := by
  funext i a
  simp [leftMatrix, bAddress, readMatrix, hr, hc, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm]

theorem MatrixMultiplyData.rightMatrix_transpose (p : MatrixMultiplyData)
    (hr : p.cRowStride = 1) (hc : p.cColStride = p.inner) :
    p.rightMatrix = (readMatrix p.memory p.cols p.inner p.cBase).transpose := by
  funext a j
  simp [rightMatrix, cAddress, readMatrix, hr, hc, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm]

def MatrixMultiplyData.partialProduct (p : MatrixMultiplyData) (i j t : ℕ) : ℝ :=
  ∑ a ∈ Finset.range t, p.memory (p.bAddress i a) * p.memory (p.cAddress a j)

theorem MatrixMultiplyData.partialProduct_zero (p : MatrixMultiplyData) (i j : ℕ) :
    p.partialProduct i j 0 = 0 := by simp [partialProduct]

theorem MatrixMultiplyData.partialProduct_succ (p : MatrixMultiplyData) (i j t : ℕ) :
    p.partialProduct i j (t + 1) = p.partialProduct i j t +
      p.memory (p.bAddress i t) * p.memory (p.cAddress t j) := by
  exact Finset.sum_range_succ _ _

theorem MatrixMultiplyData.productMatrix_entry (p : MatrixMultiplyData)
    (i : Fin p.rows) (j : Fin p.cols) :
    p.productMatrix i j = p.partialProduct i.val j.val p.inner := by
  simp only [productMatrix, Matrix.mul_apply, leftMatrix, rightMatrix, partialProduct]
  exact Fin.sum_univ_eq_sum_range
    (fun a => p.memory (p.bAddress i.val a) * p.memory (p.cAddress a j.val)) p.inner

def MatrixMultiplyData.InputsOutsideOutput (p : MatrixMultiplyData) : Prop :=
  (∀ i < p.rows, ∀ a < p.inner,
    ¬ (p.dBase ≤ p.bAddress i a ∧ p.bAddress i a < p.dBase + p.rows * p.cols)) ∧
  (∀ a < p.inner, ∀ j < p.cols,
    ¬ (p.dBase ≤ p.cAddress a j ∧ p.cAddress a j < p.dBase + p.rows * p.cols))

def prefixMemory (old cells : ℕ → ℝ) (base done address : ℕ) : ℝ :=
  if base ≤ address ∧ address < base + done then cells (address - base) else old address

theorem prefixMemory_zero (old cells : ℕ → ℝ) (base : ℕ) :
    prefixMemory old cells base 0 = old := by
  funext address
  simp [prefixMemory]

theorem prefixMemory_outside (old cells : ℕ → ℝ) (base done address : ℕ)
    (h : ¬ (base ≤ address ∧ address < base + done)) :
    prefixMemory old cells base done address = old address := by
  simp only [prefixMemory, if_neg h]

theorem prefixMemory_update (old cells : ℕ → ℝ) (base done : ℕ) :
    Function.update (prefixMemory old cells base done) (base + done) (cells done) =
      prefixMemory old cells base (done + 1) := by
  funext address
  by_cases h : address = base + done
  · subst address
    simp [prefixMemory]
  · rw [Function.update_of_ne h]
    unfold prefixMemory
    by_cases h' : base ≤ address ∧ address < base + done
    · have h'' : base ≤ address ∧ address < base + (done + 1) := by omega
      rw [if_pos h', if_pos h'']
    · have h'' : ¬ (base ≤ address ∧ address < base + (done + 1)) := by omega
      rw [if_neg h', if_neg h'']

def MatrixMultiplyData.outputPrefix (p : MatrixMultiplyData) (done : ℕ) : ℕ → ℝ :=
  prefixMemory p.memory (matrixCell p.productMatrix) p.dBase done

theorem MatrixMultiplyData.outputPrefix_source (p : MatrixMultiplyData)
    (done address : ℕ) (hd : done ≤ p.rows * p.cols)
    (ha : ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols)) :
    p.outputPrefix done address = p.memory address := by
  apply prefixMemory_outside
  omega

theorem MatrixMultiplyData.outputPrefix_b (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (done i a : ℕ) (hd : done ≤ p.rows * p.cols)
    (hi : i < p.rows) (ha : a < p.inner) :
    p.outputPrefix done (p.bAddress i a) = p.memory (p.bAddress i a) :=
  p.outputPrefix_source done _ hd (h.1 i hi a ha)

theorem MatrixMultiplyData.outputPrefix_c (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (done a j : ℕ) (hd : done ≤ p.rows * p.cols)
    (ha : a < p.inner) (hj : j < p.cols) :
    p.outputPrefix done (p.cAddress a j) = p.memory (p.cAddress a j) :=
  p.outputPrefix_source done _ hd (h.2 a ha j hj)

theorem MatrixMultiplyData.outputPrefix_update (p : MatrixMultiplyData)
    (i : Fin p.rows) (j : Fin p.cols) :
    Function.update (p.outputPrefix (i.val * p.cols + j.val))
      (p.dBase + i.val * p.cols + j.val) (p.partialProduct i.val j.val p.inner) =
      p.outputPrefix (i.val * p.cols + j.val + 1) := by
  rw [← p.productMatrix_entry i j, ← matrixCell_entry p.productMatrix i j]
  simpa only [outputPrefix, Nat.add_assoc] using
    prefixMemory_update p.memory (matrixCell p.productMatrix) p.dBase (i.val * p.cols + j.val)

theorem MatrixMultiplyData.outputPrefix_read (p : MatrixMultiplyData) :
    readMatrix (p.outputPrefix (p.rows * p.cols)) p.rows p.cols p.dBase =
      p.productMatrix := by
  funext i j
  have hi := matrix_offset_lt i j
  have hm : p.dBase ≤ p.dBase + i.val * p.cols + j.val ∧
      p.dBase + i.val * p.cols + j.val < p.dBase + p.rows * p.cols := by omega
  have hs : p.dBase + i.val * p.cols + j.val - p.dBase = i.val * p.cols + j.val := by omega
  simp only [readMatrix, outputPrefix, prefixMemory, if_pos hm, hs]
  exact matrixCell_entry p.productMatrix i j

theorem MatrixMultiplyData.dense_inputsOutsideOutput (p : MatrixMultiplyData)
    (hbr : p.bRowStride = p.inner) (hbc : p.bColStride = 1)
    (hcr : p.cRowStride = p.cols) (hcc : p.cColStride = 1)
    (hb : DisjointBlocks p.bBase (p.rows * p.inner) p.dBase (p.rows * p.cols))
    (hc : DisjointBlocks p.cBase (p.inner * p.cols) p.dBase (p.rows * p.cols)) :
    p.InputsOutsideOutput := by
  constructor
  · intro i hi a ha
    have hh := matrix_offset_lt (⟨i, hi⟩ : Fin p.rows) (⟨a, ha⟩ : Fin p.inner)
    change i * p.inner + a < p.rows * p.inner at hh
    apply disjointBlocks_not_mem_right hb
    simp only [bAddress, hbr, hbc, Nat.mul_one]
    constructor <;> omega
  · intro a ha j hj
    have hh := matrix_offset_lt (⟨a, ha⟩ : Fin p.inner) (⟨j, hj⟩ : Fin p.cols)
    change a * p.cols + j < p.inner * p.cols at hh
    apply disjointBlocks_not_mem_right hc
    simp only [cAddress, hcr, hcc, Nat.mul_one]
    constructor <;> omega

#assert_trust kernel MatrixMultiplyData.outputPrefix_read
#assert_trust kernel MatrixMultiplyData.dense_inputsOutsideOutput
#print axioms MatrixMultiplyData.outputPrefix_read
#print axioms MatrixMultiplyData.dense_inputsOutsideOutput
end NLA.Proofs.TR04
