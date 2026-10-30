import NLA.Proofs.RE05.LeverageMask

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix

def residualSingularValues {n q : ℕ} (P : Basis n q) (ξ : ℝ) (j : Fin n) : ℝ :=
  if threshold q ξ < leverageSingularValues P j then 0 else leverageSingularValues P j

theorem residualMask_spectrum {n q : ℕ} (P : Basis n q) (ξ : ℝ) :
    Matrix.diagonal (residualMask P ξ) * Matrix.diagonal (leverageSingularValues P) *
      Matrix.diagonal (residualMask P ξ) = Matrix.diagonal (residualSingularValues P ξ) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [residualMask, residualSingularValues]
  split_ifs <;> simp

theorem makePlan_residualLeverage_diagonalization {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (makePlan P ξ ω copy) * leverage P *
      residualProjection (makePlan P ξ ω copy) =
        leverageFrame P * Matrix.diagonal (residualSingularValues P ξ) *
          (leverageFrame P).transpose := by
  rw [makePlan_residualProjection_mask, leverage_diagonalization,
    frame_conjugate_mul _ (leverageFrame_gram P),
    frame_conjugate_mul _ (leverageFrame_gram P), residualMask_spectrum]

theorem residualSingularValues_le_threshold {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (j : Fin n) : residualSingularValues P ξ j ≤ threshold q ξ := by
  unfold residualSingularValues
  split_ifs with hj
  · exact Real.sqrt_nonneg _
  · exact le_of_not_gt hj

theorem frame_constant_diagonal {n q : ℕ} (P : Basis n q) (t : ℝ) :
    leverageFrame P * Matrix.diagonal (fun _ : Fin n => t) * (leverageFrame P).transpose =
      t • (1 : Square n) := by
  have hd : Matrix.diagonal (fun _ : Fin n => t) = t • (1 : Square n) := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, leverageFrame_cogram]

/-- Literal Loewner upper bound on the residual leverage of the actual
strict-threshold selection. It needs no independent-basis or positive-accuracy
promise: the model's square-root threshold is always nonnegative. -/
theorem makePlan_residualLeverage_bound {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (threshold q ξ • (1 : Square n) -
      residualProjection (makePlan P ξ ω copy) * leverage P *
        residualProjection (makePlan P ξ ω copy)).PosSemidef := by
  have hd : (Matrix.diagonal (fun j : Fin n =>
      threshold q ξ - residualSingularValues P ξ j)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (residualSingularValues_le_threshold P ξ j))
  have hp := hd.mul_mul_conjTranspose_same (leverageFrame P)
  have heq : threshold q ξ • (1 : Square n) -
      residualProjection (makePlan P ξ ω copy) * leverage P *
        residualProjection (makePlan P ξ ω copy) =
      leverageFrame P * Matrix.diagonal (fun j : Fin n =>
        threshold q ξ - residualSingularValues P ξ j) * (leverageFrame P).transpose := by
    rw [makePlan_residualLeverage_diagonalization, ← frame_constant_diagonal P (threshold q ξ),
      ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  rw [heq]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hp

theorem makePlan_residualLeverage_quadratic {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    dot (complement (makePlan P ξ ω copy) x)
      (leverage P *ᵥ complement (makePlan P ξ ω copy) x) ≤
        threshold q ξ * dot x x := by
  let H := residualProjection (makePlan P ξ ω copy)
  have h := (makePlan_residualLeverage_bound P ξ ω copy).dotProduct_mulVec_nonneg x
  have hs : H.transpose = H := (residualProjection_symmetric _).eq
  have hform : dot (complement (makePlan P ξ ω copy) x)
      (leverage P *ᵥ complement (makePlan P ξ ω copy) x) =
      x ⬝ᵥ ((H * leverage P * H) *ᵥ x) := by
    simp only [complement_eq_mulVec, dot]
    change (H *ᵥ x) ⬝ᵥ (leverage P *ᵥ (H *ᵥ x)) = _
    calc
      (H *ᵥ x) ⬝ᵥ (leverage P *ᵥ (H *ᵥ x)) =
          (leverage P *ᵥ (H *ᵥ x)) ⬝ᵥ (H.transpose *ᵥ x) := by
        rw [hs]
        exact dotProduct_comm _ _
      _ = x ⬝ᵥ (H *ᵥ (leverage P *ᵥ (H *ᵥ x))) :=
        Matrix.dotProduct_transpose_mulVec _ _ _
      _ = x ⬝ᵥ ((H * leverage P * H) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hform]
  change _ ≤ threshold q ξ * (x ⬝ᵥ x)
  have hn : 0 ≤ threshold q ξ * (x ⬝ᵥ x) - x ⬝ᵥ ((H * leverage P * H) *ᵥ x) := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, star_trivial,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, H] using h
  exact sub_nonneg.mp hn

/-- The actual residual blocks of the supplied fold basis. -/
def residualBasisBlock {n q : ℕ} (P : Basis n q) (plan : Plan n) (j : Fin (q + 1)) : Square n :=
  residualProjection plan * orthonormalMember P j

theorem residualBasisBlock_gram {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (∑ j : Fin (q + 1), residualBasisBlock P plan j * (residualBasisBlock P plan j).transpose) =
      residualProjection plan * leverage P * residualProjection plan := by
  calc
    (∑ j : Fin (q + 1), residualBasisBlock P plan j * (residualBasisBlock P plan j).transpose) =
      ∑ j : Fin (q + 1), residualProjection plan *
        (orthonormalMember P j * (orthonormalMember P j).transpose) * residualProjection plan := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [residualBasisBlock, Matrix.transpose_mul, (residualProjection_symmetric plan).eq,
        Matrix.mul_assoc]
    _ = residualProjection plan * (∑ j : Fin (q + 1),
        orthonormalMember P j * (orthonormalMember P j).transpose) * residualProjection plan := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = residualProjection plan * leverage P * residualProjection plan := by
      rw [leverage_eq_sum_gram]

theorem actual_basis_split {n q : ℕ} (P : Basis n q) (plan : Plan n) (j : Fin (q + 1)) :
    selectedProjection plan * orthonormalMember P j + residualBasisBlock P plan j =
      orthonormalMember P j := projection_basis_split plan _

end NLA.Proofs.RE05
