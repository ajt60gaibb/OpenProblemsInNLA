import NLA.Proofs.TR04.TensorFormat
import NLA.Proofs.TR04.SVDEnergy

/-! Actual first-mode contraction and lifting. Every identity is entrywise or
an exact finite Frobenius identity; no selected SVD basis is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.TR04.TensorFormat

/-- Expose exactly the first mode as a matrix row coordinate. -/
def firstMatrix {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    Matrix (Fin m) (Index ns) ℝ := fun i x => A (i, x)

def firstMatrixLinearEquiv (m : ℕ) (ns : List ℕ) :
    Tensor (m :: ns) ≃ₗ[ℝ] Matrix (Fin m) (Index ns) ℝ where
  toFun := firstMatrix
  invFun M x := M x.1 x.2
  left_inv A := by funext x; rfl
  right_inv M := rfl
  map_add' A B := rfl
  map_smul' c A := rfl

/-- Apply an actual finite matrix only to the first mode. -/
def actFirst {m k : ℕ} {ns : List ℕ} (M : Matrix (Fin k) (Fin m) ℝ)
    (A : Tensor (m :: ns)) : Tensor (k :: ns) :=
  fun x => ∑ i, M x.1 i * A (i, x.2)

def contract {m k : ℕ} {ns : List ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (A : Tensor (m :: ns)) : Tensor (k :: ns) := actFirst U.transpose A

def lift {m k : ℕ} {ns : List ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (A : Tensor (k :: ns)) : Tensor (m :: ns) := actFirst U A

@[simp] theorem firstMatrix_actFirst {m k : ℕ} {ns : List ℕ}
    (M : Matrix (Fin k) (Fin m) ℝ) (A : Tensor (m :: ns)) :
    firstMatrix (actFirst M A) = M * firstMatrix A := rfl

@[simp] theorem actFirst_zero {m k : ℕ} {ns : List ℕ}
    (M : Matrix (Fin k) (Fin m) ℝ) : actFirst M (0 : Tensor (m :: ns)) = 0 := by
  funext x
  simp [actFirst]

@[simp] theorem actFirst_sub {m k : ℕ} {ns : List ℕ}
    (M : Matrix (Fin k) (Fin m) ℝ) (A B : Tensor (m :: ns)) :
    actFirst M (A - B) = actFirst M A - actFirst M B := by
  funext x
  simp only [actFirst, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem actFirst_comp {m k l : ℕ} {ns : List ℕ}
    (M : Matrix (Fin k) (Fin m) ℝ) (N : Matrix (Fin l) (Fin k) ℝ)
    (A : Tensor (m :: ns)) : actFirst N (actFirst M A) = actFirst (N * M) A := by
  apply (firstMatrixLinearEquiv l ns).injective
  change N * (M * firstMatrix A) = (N * M) * firstMatrix A
  exact (Matrix.mul_assoc _ _ _).symm

@[simp] theorem actFirst_one {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    actFirst (1 : Matrix (Fin m) (Fin m) ℝ) A = A := by
  apply (firstMatrixLinearEquiv m ns).injective
  change (1 : Matrix (Fin m) (Fin m) ℝ) * firstMatrix A = firstMatrix A
  exact Matrix.one_mul _

@[simp] theorem contract_lift {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A : Tensor (k :: ns)) : contract U (lift U A) = A := by
  rw [contract, lift, actFirst_comp, SVD.transpose_mul_eq_one hU, actFirst_one]

theorem energy_firstMatrix {m : ℕ} {ns : List ℕ} (A : Tensor (m :: ns)) :
    energy (m :: ns) A = SVD.matrixEnergy (firstMatrix A) := by
  simp only [energy, SVD.matrixEnergy, firstMatrix, Fintype.sum_prod_type]

/-- Lifting through orthonormal columns preserves the complete squared norm. -/
theorem energy_lift {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A : Tensor (k :: ns)) : energy (m :: ns) (lift U A) = energy (k :: ns) A := by
  simp only [energy, Fintype.sum_prod_type, lift, actFirst]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i x => (A (i, x))^2)]
  apply Finset.sum_congr rfl
  intro x _
  exact SVD.orthonormalColumns_sum_sq hU (fun i => A (i, x))

theorem error_lift {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A B : Tensor (k :: ns)) :
    error (m :: ns) (lift U A) (lift U B) = error (k :: ns) A B := by
  change energy (m :: ns) (actFirst U A - actFirst U B) = energy (k :: ns) (A - B)
  rw [← actFirst_sub]
  exact energy_lift hU (A - B)

/-- Exact finite inner product, compatible with every empty mode product. -/
def inner (ns : List ℕ) (A B : Tensor ns) : ℝ := ∑ x, A x * B x

theorem energy_add (ns : List ℕ) (A B : Tensor ns) :
    energy ns (A + B) = energy ns A + 2 * inner ns A B + energy ns B := by
  unfold energy inner
  simp only [Pi.add_apply]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

theorem inner_contract_lift {m k : ℕ} {ns : List ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (A : Tensor (m :: ns)) (B : Tensor (k :: ns)) :
    inner (m :: ns) A (lift U B) = inner (k :: ns) (contract U A) B := by
  simp only [inner, Fintype.sum_prod_type, lift, contract, actFirst,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i : Fin m, ∑ q : Fin k, ∑ x : Index ns,
        A (i, x) * (U i q * B (q, x)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ q : Fin k, ∑ i : Fin m, ∑ x : Index ns,
        A (i, x) * (U i q * B (q, x)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The discarded first-mode residual is orthogonal to every lifted tensor. -/
theorem residual_inner_lift {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A : Tensor (m :: ns)) (B : Tensor (k :: ns)) :
    inner (m :: ns) (A - lift U (contract U A)) (lift U B) = 0 := by
  rw [inner_contract_lift]
  change inner (k :: ns)
    (actFirst U.transpose (A - lift U (contract U A))) B = 0
  rw [actFirst_sub]
  change inner (k :: ns) (contract U A - contract U (lift U (contract U A))) B = 0
  rw [contract_lift hU, sub_self]
  simp [inner]

/-- Pythagoras with the full compressed comparator, not a weakened residual. -/
theorem error_lift_decomposition {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A : Tensor (m :: ns)) (B : Tensor (k :: ns)) :
    error (m :: ns) A (lift U B) =
      error (m :: ns) A (lift U (contract U A)) + error (k :: ns) (contract U A) B := by
  have hsplit : A - lift U B =
      (A - lift U (contract U A)) + lift U (contract U A - B) := by
    have hlin : lift U (contract U A - B) = lift U (contract U A) - lift U B :=
      actFirst_sub U (contract U A) B
    rw [hlin]
    abel
  unfold error
  rw [hsplit, energy_add, residual_inner_lift hU, mul_zero, add_zero, energy_lift hU]

/-- Contracting an orthonormal first-mode frame cannot increase full error. -/
theorem energy_contract_le {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A : Tensor (m :: ns)) : energy (k :: ns) (contract U A) ≤ energy (m :: ns) A := by
  have h := error_lift_decomposition hU A 0
  have hz : lift U (0 : Tensor (k :: ns)) = 0 := actFirst_zero U
  rw [hz, error_zero_right, error_zero_right] at h
  have hn := error_nonneg (m :: ns) A (lift U (contract U A))
  linarith

theorem error_contract_le {m k : ℕ} {ns : List ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A B : Tensor (m :: ns)) :
    error (k :: ns) (contract U A) (contract U B) ≤ error (m :: ns) A B := by
  change energy (k :: ns) (actFirst U.transpose A - actFirst U.transpose B) ≤
    energy (m :: ns) (A - B)
  rw [← actFirst_sub]
  exact energy_contract_le hU (A - B)

#assert_trust kernel firstMatrixLinearEquiv
#assert_trust kernel actFirst_comp
#assert_trust kernel contract_lift
#assert_trust kernel energy_lift
#assert_trust kernel error_lift
#assert_trust kernel residual_inner_lift
#assert_trust kernel error_lift_decomposition
#assert_trust kernel energy_contract_le
#assert_trust kernel error_contract_le
#print axioms error_lift_decomposition
end NLA.Proofs.TR04.TensorFormat
