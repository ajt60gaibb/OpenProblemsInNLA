import NLA.Proofs.RE05.BasisProjection
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RE05SpectralSplitGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05
open scoped BigOperators Matrix

theorem actual_complement_selfAdjoint {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x y : Fin n → ℝ) :
    dot (complement (plans P ε ω copy) x) y = dot x (complement (plans P ε ω copy) y) :=
  complement_selfAdjoint _ x y

theorem actual_complement_idempotent {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    complement (plans P ε ω copy) (complement (plans P ε ω copy) x) =
      complement (plans P ε ω copy) x := makePlan_complement_idempotent P (squaredAccuracy ε) ω copy x

theorem actual_residual_matrix_idempotent {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (plans P ε ω copy) * residualProjection (plans P ε ω copy) =
      residualProjection (plans P ε ω copy) :=
  makePlan_residualProjection_idempotent P (squaredAccuracy ε) ω copy

theorem actual_residual_leverage_bound {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (threshold q (squaredAccuracy ε) • (1 : Square n) -
      residualProjection (plans P ε ω copy) * leverage P *
        residualProjection (plans P ε ω copy)).PosSemidef :=
  makePlan_residualLeverage_bound P (squaredAccuracy ε) ω copy

theorem actual_residual_quadratic {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    dot (complement (plans P ε ω copy) x)
      (leverage P *ᵥ complement (plans P ε ω copy) x) ≤
        threshold q (squaredAccuracy ε) * dot x x :=
  makePlan_residualLeverage_quadratic P (squaredAccuracy ε) ω copy x

theorem literal_residual_block_sum {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (∑ j : Fin (q + 1),
      (residualProjection (plans P ε ω copy) * orthonormalMember P j) *
        (residualProjection (plans P ε ω copy) * orthonormalMember P j).transpose) =
      residualProjection (plans P ε ω copy) * leverage P * residualProjection (plans P ε ω copy) :=
  residualBasisBlock_gram P _

theorem row_K_add_H {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedProjection (plans P ε ω copy) + residualProjection (plans P ε ω copy) = 1 :=
  projection_add_residual _

theorem coefficient_K_add_H {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedBasisGram P (plans P ε ω copy) + residualBasisGram P (plans P ε ω copy) = 1 :=
  makePlan_basisGram_split P hP (squaredAccuracy ε) ω copy

theorem coefficient_H_psd {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (residualBasisGram P (plans P ε ω copy)).PosSemidef :=
  residualBasisGram_posSemidef _ _

theorem coefficient_H_le_I {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (1 - residualBasisGram P (plans P ε ω copy)).PosSemidef :=
  makePlan_residualBasisGram_le_one P hP (squaredAccuracy ε) ω copy

theorem actual_residual_basis_norm {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (j : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.norm n
      (residualProjection (plans P ε ω copy) * orthonormalMember P j) ≤ 1 :=
  makePlan_residualBasis_norm_le_one P hP (squaredAccuracy ε) ω copy j

theorem actual_basis_frobenius_split {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (E F : Square n) :
    NLA.Computation.LinearFamilyQuery.inner E F =
      NLA.Computation.LinearFamilyQuery.inner (selectedProjection (plans P ε ω copy) * E)
        (selectedProjection (plans P ε ω copy) * F) +
      NLA.Computation.LinearFamilyQuery.inner (residualProjection (plans P ε ω copy) * E)
        (residualProjection (plans P ε ω copy) * F) :=
  projection_matrix_inner_split _ (makePlan_frame_gram P (squaredAccuracy ε) ω copy) E F

theorem dependent_zero_family_bound (n q : ℕ) (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    let P : Basis n q := fun _ => 0
    (threshold q ξ • (1 : Square n) - residualProjection (makePlan P ξ ω copy) * leverage P *
      residualProjection (makePlan P ξ ω copy)).PosSemidef :=
  makePlan_residualLeverage_bound _ ξ ω copy

theorem empty_complement (q : ℕ) (P : Basis 0 q) (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15)
    (x : Fin 0 → ℝ) : complement (makePlan P ξ ω copy) x = x := by
  funext i
  exact Fin.elim0 i

theorem preserved_full_target_identity :
    NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel actual_complement_selfAdjoint
#assert_trust kernel actual_complement_idempotent
#assert_trust kernel actual_residual_matrix_idempotent
#assert_trust kernel actual_residual_leverage_bound
#assert_trust kernel actual_residual_quadratic
#assert_trust kernel literal_residual_block_sum
#assert_trust kernel row_K_add_H
#assert_trust kernel coefficient_K_add_H
#assert_trust kernel coefficient_H_psd
#assert_trust kernel coefficient_H_le_I
#assert_trust kernel actual_residual_basis_norm
#assert_trust kernel actual_basis_frobenius_split
#assert_trust kernel dependent_zero_family_bound
#assert_trust kernel empty_complement
#assert_trust kernel preserved_full_target_identity
#print axioms actual_complement_selfAdjoint
#print axioms actual_complement_idempotent
#print axioms actual_residual_leverage_bound
#print axioms actual_residual_quadratic
#print axioms literal_residual_block_sum
#print axioms coefficient_K_add_H
#print axioms coefficient_H_le_I
#print axioms actual_residual_basis_norm
#print axioms actual_basis_frobenius_split
#print axioms dependent_zero_family_bound
#print axioms empty_complement
#print axioms preserved_full_target_identity
end RE05SpectralSplitGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.planFrame
#print axioms NLA.Proofs.RE05.planFrame
#assert_trust kernel NLA.Proofs.RE05.selectedProjection
#print axioms NLA.Proofs.RE05.selectedProjection
#assert_trust kernel NLA.Proofs.RE05.residualProjection
#print axioms NLA.Proofs.RE05.residualProjection
#assert_trust kernel NLA.Proofs.RE05.projection_add_residual
#print axioms NLA.Proofs.RE05.projection_add_residual
#assert_trust kernel NLA.Proofs.RE05.selectedProjection_symmetric
#print axioms NLA.Proofs.RE05.selectedProjection_symmetric
#assert_trust kernel NLA.Proofs.RE05.residualProjection_symmetric
#print axioms NLA.Proofs.RE05.residualProjection_symmetric
#assert_trust kernel NLA.Proofs.RE05.complement_eq_mulVec
#print axioms NLA.Proofs.RE05.complement_eq_mulVec
#assert_trust kernel NLA.Proofs.RE05.complement_selfAdjoint
#print axioms NLA.Proofs.RE05.complement_selfAdjoint
#assert_trust kernel NLA.Proofs.RE05.makePlan_selected_nodup
#print axioms NLA.Proofs.RE05.makePlan_selected_nodup
#assert_trust kernel NLA.Proofs.RE05.makePlan_frame_gram
#print axioms NLA.Proofs.RE05.makePlan_frame_gram
#assert_trust kernel NLA.Proofs.RE05.selectedProjection_idempotent
#print axioms NLA.Proofs.RE05.selectedProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.residualProjection_idempotent
#print axioms NLA.Proofs.RE05.residualProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.makePlan_complement_idempotent
#print axioms NLA.Proofs.RE05.makePlan_complement_idempotent
#assert_trust kernel NLA.Proofs.RE05.makePlan_selectedProjection_idempotent
#print axioms NLA.Proofs.RE05.makePlan_selectedProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_idempotent
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.projection_basis_split
#print axioms NLA.Proofs.RE05.projection_basis_split
#assert_trust kernel NLA.Proofs.RE05.selected_residual_mul_zero
#print axioms NLA.Proofs.RE05.selected_residual_mul_zero
#assert_trust kernel NLA.Proofs.RE05.residual_selected_mul_zero
#print axioms NLA.Proofs.RE05.residual_selected_mul_zero
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_positive_column
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_positive_column
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_weighted_entry
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_weighted_entry
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_diagonalization
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_diagonalization
#assert_trust kernel NLA.Proofs.RE05.leverageFrame
#print axioms NLA.Proofs.RE05.leverageFrame
#assert_trust kernel NLA.Proofs.RE05.leverageSingularValues
#print axioms NLA.Proofs.RE05.leverageSingularValues
#assert_trust kernel NLA.Proofs.RE05.selectedMask
#print axioms NLA.Proofs.RE05.selectedMask
#assert_trust kernel NLA.Proofs.RE05.residualMask
#print axioms NLA.Proofs.RE05.residualMask
#assert_trust kernel NLA.Proofs.RE05.validSVD_left_gram
#print axioms NLA.Proofs.RE05.validSVD_left_gram
#assert_trust kernel NLA.Proofs.RE05.leverageFrame_gram
#print axioms NLA.Proofs.RE05.leverageFrame_gram
#assert_trust kernel NLA.Proofs.RE05.leverageFrame_cogram
#print axioms NLA.Proofs.RE05.leverageFrame_cogram
#assert_trust kernel NLA.Proofs.RE05.frame_conjugate_mul
#print axioms NLA.Proofs.RE05.frame_conjugate_mul
#assert_trust kernel NLA.Proofs.RE05.makePlan_sum_selected
#print axioms NLA.Proofs.RE05.makePlan_sum_selected
#assert_trust kernel NLA.Proofs.RE05.makePlan_selectedProjection_mask
#print axioms NLA.Proofs.RE05.makePlan_selectedProjection_mask
#assert_trust kernel NLA.Proofs.RE05.residualMask_diagonal
#print axioms NLA.Proofs.RE05.residualMask_diagonal
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_mask
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_mask
#assert_trust kernel NLA.Proofs.RE05.leverage_diagonalization
#print axioms NLA.Proofs.RE05.leverage_diagonalization
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_posSemidef
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_posSemidef
#assert_trust kernel NLA.Proofs.RE05.residualSingularValues
#print axioms NLA.Proofs.RE05.residualSingularValues
#assert_trust kernel NLA.Proofs.RE05.residualMask_spectrum
#print axioms NLA.Proofs.RE05.residualMask_spectrum
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualLeverage_diagonalization
#print axioms NLA.Proofs.RE05.makePlan_residualLeverage_diagonalization
#assert_trust kernel NLA.Proofs.RE05.residualSingularValues_le_threshold
#print axioms NLA.Proofs.RE05.residualSingularValues_le_threshold
#assert_trust kernel NLA.Proofs.RE05.frame_constant_diagonal
#print axioms NLA.Proofs.RE05.frame_constant_diagonal
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualLeverage_bound
#print axioms NLA.Proofs.RE05.makePlan_residualLeverage_bound
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualLeverage_quadratic
#print axioms NLA.Proofs.RE05.makePlan_residualLeverage_quadratic
#assert_trust kernel NLA.Proofs.RE05.residualBasisBlock
#print axioms NLA.Proofs.RE05.residualBasisBlock
#assert_trust kernel NLA.Proofs.RE05.residualBasisBlock_gram
#print axioms NLA.Proofs.RE05.residualBasisBlock_gram
#assert_trust kernel NLA.Proofs.RE05.actual_basis_split
#print axioms NLA.Proofs.RE05.actual_basis_split
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_trace
#print axioms NLA.Proofs.RE05.matrix_inner_trace
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_comm
#print axioms NLA.Proofs.RE05.matrix_inner_comm
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_add_left
#print axioms NLA.Proofs.RE05.matrix_inner_add_left
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_add_right
#print axioms NLA.Proofs.RE05.matrix_inner_add_right
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_self_nonnegative
#print axioms NLA.Proofs.RE05.matrix_inner_self_nonnegative
#assert_trust kernel NLA.Proofs.RE05.projection_matrix_inner_cross
#print axioms NLA.Proofs.RE05.projection_matrix_inner_cross
#assert_trust kernel NLA.Proofs.RE05.projection_matrix_inner_split
#print axioms NLA.Proofs.RE05.projection_matrix_inner_split
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualBasis_inner_le_one
#print axioms NLA.Proofs.RE05.makePlan_residualBasis_inner_le_one
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualBasis_norm_le_one
#print axioms NLA.Proofs.RE05.makePlan_residualBasis_norm_le_one
#assert_trust kernel NLA.Proofs.RE05.matrixFamilyGram
#print axioms NLA.Proofs.RE05.matrixFamilyGram
#assert_trust kernel NLA.Proofs.RE05.matrixFamilyGram_posSemidef
#print axioms NLA.Proofs.RE05.matrixFamilyGram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.selectedBasisGram
#print axioms NLA.Proofs.RE05.selectedBasisGram
#assert_trust kernel NLA.Proofs.RE05.residualBasisGram
#print axioms NLA.Proofs.RE05.residualBasisGram
#assert_trust kernel NLA.Proofs.RE05.selectedBasisGram_posSemidef
#print axioms NLA.Proofs.RE05.selectedBasisGram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.residualBasisGram_posSemidef
#print axioms NLA.Proofs.RE05.residualBasisGram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.makePlan_basisGram_split
#print axioms NLA.Proofs.RE05.makePlan_basisGram_split
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualBasisGram_le_one
#print axioms NLA.Proofs.RE05.makePlan_residualBasisGram_le_one
#assert_trust kernel NLA.Proofs.RE05.makePlan_selectedBasisGram_le_one
#print axioms NLA.Proofs.RE05.makePlan_selectedBasisGram_le_one
