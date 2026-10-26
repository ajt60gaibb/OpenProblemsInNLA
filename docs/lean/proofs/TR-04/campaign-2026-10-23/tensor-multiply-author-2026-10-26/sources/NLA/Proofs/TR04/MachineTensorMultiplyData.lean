import NLA.Proofs.TR04.MachineTensorMemory

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine

def actMultiplyData (memory : ℕ → ℝ) (rows inner : ℕ) (ns : List ℕ)
    (frameBase rowStride colStride inputBase outputBase : ℕ) : MatrixMultiplyData where
  rows := rows
  inner := inner
  cols := suffixSize ns
  bBase := frameBase
  cBase := inputBase
  dBase := outputBase
  bRowStride := rowStride
  bColStride := colStride
  cRowStride := suffixSize ns
  cColStride := 1
  memory := memory

def contractMultiplyData (memory : ℕ → ℝ) (m q : ℕ) (ns : List ℕ)
    (frameBase stride inputBase outputBase : ℕ) : MatrixMultiplyData :=
  actMultiplyData memory q m ns frameBase 1 stride inputBase outputBase

def liftMultiplyData (memory : ℕ → ℝ) (m q : ℕ) (ns : List ℕ)
    (frameBase stride inputBase outputBase : ℕ) : MatrixMultiplyData :=
  actMultiplyData memory m q ns frameBase stride 1 inputBase outputBase

theorem actMultiplyData_left (memory : ℕ → ℝ) (rows inner : ℕ) (ns : List ℕ)
    (frameBase rowStride colStride inputBase outputBase : ℕ)
    (M : Matrix (Fin rows) (Fin inner) ℝ)
    (hM : ∀ i k, memory (frameBase + i.val * rowStride + k.val * colStride) = M i k) :
    (actMultiplyData memory rows inner ns frameBase rowStride colStride inputBase outputBase).leftMatrix = M := by
  ext i k
  exact hM i k

theorem actMultiplyData_right (memory : ℕ → ℝ) (rows inner : ℕ) (ns : List ℕ)
    (frameBase rowStride colStride inputBase outputBase : ℕ)
    (A : Tensor (inner :: ns)) (hA : StoresTensor memory inputBase (inner :: ns) A) :
    (actMultiplyData memory rows inner ns frameBase rowStride colStride inputBase outputBase).rightMatrix =
      radixDenseFirst A := by
  rw [MatrixMultiplyData.rightMatrix_dense _ rfl rfl]
  exact (storesTensor_readMatrix_iff memory inputBase A).mp hA

theorem actMultiplyData_product (memory : ℕ → ℝ) (rows inner : ℕ) (ns : List ℕ)
    (frameBase rowStride colStride inputBase outputBase : ℕ)
    (M : Matrix (Fin rows) (Fin inner) ℝ)
    (hM : ∀ i k, memory (frameBase + i.val * rowStride + k.val * colStride) = M i k)
    (A : Tensor (inner :: ns)) (hA : StoresTensor memory inputBase (inner :: ns) A) :
    (actMultiplyData memory rows inner ns frameBase rowStride colStride inputBase outputBase).productMatrix =
      radixDenseFirst (actFirst M A) := by
  unfold MatrixMultiplyData.productMatrix
  rw [actMultiplyData_left memory rows inner ns frameBase rowStride colStride inputBase outputBase M hM,
    actMultiplyData_right memory rows inner ns frameBase rowStride colStride inputBase outputBase A hA]
  exact (radixDenseFirst_actFirst M A).symm

theorem contractMultiplyData_product {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (m :: ns)) (hA : StoresTensor memory inputBase (m :: ns) A) :
    (contractMultiplyData memory m q ns frameBase stride inputBase outputBase).productMatrix =
      radixDenseFirst (contract Q A) := by
  apply actMultiplyData_product memory q m ns frameBase 1 stride inputBase outputBase Q.transpose _ A hA
  intro i k
  simpa only [Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Matrix.transpose_apply] using hQ k i

theorem liftMultiplyData_product {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (q :: ns)) (hA : StoresTensor memory inputBase (q :: ns) A) :
    (liftMultiplyData memory m q ns frameBase stride inputBase outputBase).productMatrix =
      radixDenseFirst (lift Q A) := by
  apply actMultiplyData_product memory m q ns frameBase stride 1 inputBase outputBase Q _ A hA
  intro i k
  simpa only [Nat.mul_one] using hQ i k

theorem contractMultiplyData_safe (memory : ℕ → ℝ) (m q : ℕ) (ns : List ℕ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (hQ : DisjointBlocks frameBase (m * stride) outputBase (q * suffixSize ns))
    (hA : DisjointBlocks inputBase (m * suffixSize ns) outputBase (q * suffixSize ns)) :
    (contractMultiplyData memory m q ns frameBase stride inputBase outputBase).InputsOutsideOutput := by
  constructor
  · intro i hi k hk
    have hb := matrix_offset_lt (⟨k, hk⟩ : Fin m) (Fin.castLE hq (⟨i, hi⟩ : Fin q))
    change k * stride + i < m * stride at hb
    apply disjointBlocks_not_mem_right hQ
    simp only [contractMultiplyData, actMultiplyData, MatrixMultiplyData.bAddress, Nat.mul_one]
    constructor <;> omega
  · intro k hk j hj
    have hb := matrix_offset_lt (⟨k, hk⟩ : Fin m) (⟨j, hj⟩ : Fin (suffixSize ns))
    change k * suffixSize ns + j < m * suffixSize ns at hb
    apply disjointBlocks_not_mem_right hA
    simp only [contractMultiplyData, actMultiplyData, MatrixMultiplyData.cAddress, Nat.mul_one]
    constructor <;> omega

theorem liftMultiplyData_safe (memory : ℕ → ℝ) (m q : ℕ) (ns : List ℕ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (hQ : DisjointBlocks frameBase (m * stride) outputBase (m * suffixSize ns))
    (hA : DisjointBlocks inputBase (q * suffixSize ns) outputBase (m * suffixSize ns)) :
    (liftMultiplyData memory m q ns frameBase stride inputBase outputBase).InputsOutsideOutput := by
  constructor
  · intro i hi k hk
    have hb := matrix_offset_lt (⟨i, hi⟩ : Fin m) (Fin.castLE hq (⟨k, hk⟩ : Fin q))
    change i * stride + k < m * stride at hb
    apply disjointBlocks_not_mem_right hQ
    simp only [liftMultiplyData, actMultiplyData, MatrixMultiplyData.bAddress, Nat.mul_one]
    constructor <;> omega
  · intro k hk j hj
    have hb := matrix_offset_lt (⟨k, hk⟩ : Fin q) (⟨j, hj⟩ : Fin (suffixSize ns))
    change k * suffixSize ns + j < q * suffixSize ns at hb
    apply disjointBlocks_not_mem_right hA
    simp only [liftMultiplyData, actMultiplyData, MatrixMultiplyData.cAddress, Nat.mul_one]
    constructor <;> omega

#assert_trust kernel actMultiplyData_product
#assert_trust kernel contractMultiplyData_product
#assert_trust kernel liftMultiplyData_product
#assert_trust kernel contractMultiplyData_safe
#assert_trust kernel liftMultiplyData_safe
#print axioms contractMultiplyData_product
end NLA.Proofs.TR04.TensorFormat
