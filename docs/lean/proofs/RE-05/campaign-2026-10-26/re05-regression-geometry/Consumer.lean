import NLA.Proofs.RE05.RegressionSolveTransport
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RE05RegressionGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05
open scoped BigOperators Matrix InnerProductSpace

theorem literal_response_slice {n : ℕ} (A : Square n) (schedule : Fin 15 → Plan n)
    (copy : Fin 15) :
    copyResponses schedule (batchAnswers A schedule) copy =
      (queries (schedule copy)).map (NLA.Computation.NonadaptiveMatrixQuery.answer A) :=
  copyResponses_batchAnswers A schedule copy

theorem literal_left_answer {n q : ℕ} (P : Basis n q) (A : Square n) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (h : Fin (plans P ε ω copy).selected.length) :
    observedLeft (plans P ε ω copy)
      (copyResponses (plans P ε ω) (batchAnswers A (plans P ε ω)) copy) h =
      A.transpose *ᵥ uColumn (plans P ε ω copy) h :=
  observedLeft_copyResponses A (plans P ε ω) copy h

theorem literal_right_answer {n q : ℕ} (P : Basis n q) (A : Square n) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (g : Fin (plans P ε ω copy).s) :
    observedRight (plans P ε ω copy)
      (copyResponses (plans P ε ω) (batchAnswers A (plans P ε ω)) copy) g =
      A *ᵥ (fun k => (plans P ε ω copy).G k g) :=
  observedRight_copyResponses A (plans P ε ω) copy g

theorem literal_mp_entry {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (j : Fin (q + 1)) :
    singleOutput P plan R j = ∑ k,
      NLA.Computation.NonadaptiveMatrixQuery.pseudoInverse (gram P plan) j k * rhs P plan R k := rfl

theorem literal_original_normal_entry {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (j : Fin (q + 1)) :
    (∑ k, gram P plan j k * singleOutput P plan R k) = rhs P plan R j :=
  congrFun (singleOutput_normal P plan R) j

theorem literal_measured_quadratic {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    ‖observationVector plan R - measurementVector plan (represent P c)‖ ^ 2 =
      ‖observationVector plan R‖ ^ 2 - 2 * dot c (rhs P plan R) + dot c (gram P plan *ᵥ c) :=
  regression_quadratic P plan R c

theorem literal_original_minimum {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (d : Fin (q + 1) → ℝ) :
    ‖observationVector plan R - measurementVector plan (represent P (singleOutput P plan R))‖ ^ 2 ≤
      ‖observationVector plan R - measurementVector plan (represent P d)‖ ^ 2 :=
  singleOutput_minimizes P plan R d

theorem literal_actual_basis_reconstruction {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (c : Fin (q + 1) → ℝ) :
    represent (orthonormalMember P)
      (fun j => NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) (represent P c)) =
      represent P c :=
  orthonormalCoordinates_reconstruct P hP _ (represent_mem_span P c)

theorem literal_lower_event_full_rank {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (α : ℝ) (hα : 0 < α)
    (hLower : ∀ d : Fin (q + 1) → ℝ,
      α * dot d d ≤ dot d (gram (orthonormalMember P) plan *ᵥ d)) :
    Matrix.rank (gram P plan) = q + 1 :=
  gram_full_rank_of_lower_bound P hP plan α hα hLower

theorem literal_conditional_matrix_output {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (R : List (Fin n → ℝ)) (α : ℝ) (hα : 0 < α)
    (hLower : ∀ d : Fin (q + 1) → ℝ,
      α * dot d d ≤ dot d (gram (orthonormalMember P) plan *ᵥ d)) :
    represent P (singleOutput P plan R) =
      represent (orthonormalMember P) (singleOutput (orthonormalMember P) plan R) :=
  singleOutput_matrix_basis_invariant_of_lower_bound P hP plan R α hα hLower

/-- No selected columns, zero sketch width and dependent generators are
allowed by the unconditional solve, for any actual response list. -/
theorem zero_width_dependent_output {n q : ℕ} (P : Basis n q) (U : Square n)
    (G : Matrix (Fin n) (Fin 0) ℝ) (R : List (Fin n → ℝ)) :
    singleOutput P ⟨[], U, 0, G⟩ R = 0 := by
  rw [singleOutput_eq_pseudoInverse_mulVec]
  have hb : rhs P ⟨[], U, 0, G⟩ R = 0 := by ext j; simp [rhs]
  rw [hb, Matrix.mulVec_zero]

theorem empty_matrix_normal (q : ℕ) (P : Basis 0 q) (plan : Plan 0)
    (R : List (Fin 0 → ℝ)) :
    gram P plan *ᵥ singleOutput P plan R = rhs P plan R := singleOutput_normal P plan R

theorem actual_rectangular_mp (a b : ℕ) (B : Matrix (Fin a) (Fin b) ℝ) :
    B * NLA.Computation.NonadaptiveMatrixQuery.pseudoInverse B * B = B :=
  Pseudo.mul_pseudoinverse_mul B

end RE05RegressionGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_U_gram
#print axioms NLA.Proofs.RE05.Pseudo.svd_U_gram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_V_gram
#print axioms NLA.Proofs.RE05.Pseudo.svd_V_gram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_U_cogram
#print axioms NLA.Proofs.RE05.Pseudo.svd_U_cogram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_V_cogram
#print axioms NLA.Proofs.RE05.Pseudo.svd_V_cogram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinU
#print axioms NLA.Proofs.RE05.Pseudo.thinU
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinV
#print axioms NLA.Proofs.RE05.Pseudo.thinV
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sigma
#print axioms NLA.Proofs.RE05.Pseudo.sigma
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sigmaInv
#print axioms NLA.Proofs.RE05.Pseudo.sigmaInv
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinU_orthogonal
#print axioms NLA.Proofs.RE05.Pseudo.thinU_orthogonal
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinV_orthogonal
#print axioms NLA.Proofs.RE05.Pseudo.thinV_orthogonal
#assert_trust kernel NLA.Proofs.RE05.Pseudo.reconstruction
#print axioms NLA.Proofs.RE05.Pseudo.reconstruction
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_decomposition
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_decomposition
#assert_trust kernel NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_sigma
#print axioms NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_sigma
#assert_trust kernel NLA.Proofs.RE05.Pseudo.diagonal_inv_sigma_inv
#print axioms NLA.Proofs.RE05.Pseudo.diagonal_inv_sigma_inv
#assert_trust kernel NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_commute
#print axioms NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_commute
#assert_trust kernel NLA.Proofs.RE05.Pseudo.mul_pseudoinverse
#print axioms NLA.Proofs.RE05.Pseudo.mul_pseudoinverse
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_mul
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_mul
#assert_trust kernel NLA.Proofs.RE05.Pseudo.IsMP
#print axioms NLA.Proofs.RE05.Pseudo.IsMP
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sandwich_contract
#print axioms NLA.Proofs.RE05.Pseudo.sandwich_contract
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sandwich_diagonal_transpose
#print axioms NLA.Proofs.RE05.Pseudo.sandwich_diagonal_transpose
#assert_trust kernel NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_mul
#print axioms NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_mul
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_pseudoinverse
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_pseudoinverse
#assert_trust kernel NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_transpose
#print axioms NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_transpose
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_transpose
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_transpose
#assert_trust kernel NLA.Proofs.RE05.Pseudo.actual_isMP
#print axioms NLA.Proofs.RE05.Pseudo.actual_isMP
#assert_trust kernel NLA.Proofs.RE05.finRange_flatMap_slice
#print axioms NLA.Proofs.RE05.finRange_flatMap_slice
#assert_trust kernel NLA.Proofs.RE05.planAnswers
#print axioms NLA.Proofs.RE05.planAnswers
#assert_trust kernel NLA.Proofs.RE05.copyResponses_batchAnswers
#print axioms NLA.Proofs.RE05.copyResponses_batchAnswers
#assert_trust kernel NLA.Proofs.RE05.planAnswers_layout
#print axioms NLA.Proofs.RE05.planAnswers_layout
#assert_trust kernel NLA.Proofs.RE05.storedVector_append_left
#print axioms NLA.Proofs.RE05.storedVector_append_left
#assert_trust kernel NLA.Proofs.RE05.storedVector_append_right
#print axioms NLA.Proofs.RE05.storedVector_append_right
#assert_trust kernel NLA.Proofs.RE05.storedVector_map_get
#print axioms NLA.Proofs.RE05.storedVector_map_get
#assert_trust kernel NLA.Proofs.RE05.observedLeft_planAnswers
#print axioms NLA.Proofs.RE05.observedLeft_planAnswers
#assert_trust kernel NLA.Proofs.RE05.observedRight_planAnswers
#print axioms NLA.Proofs.RE05.observedRight_planAnswers
#assert_trust kernel NLA.Proofs.RE05.observedLeft_copyResponses
#print axioms NLA.Proofs.RE05.observedLeft_copyResponses
#assert_trust kernel NLA.Proofs.RE05.observedRight_copyResponses
#print axioms NLA.Proofs.RE05.observedRight_copyResponses
#assert_trust kernel NLA.Proofs.RE05.MeasurementIndex
#print axioms NLA.Proofs.RE05.MeasurementIndex
#assert_trust kernel NLA.Proofs.RE05.MeasurementSpace
#print axioms NLA.Proofs.RE05.MeasurementSpace
#assert_trust kernel NLA.Proofs.RE05.measurementScale
#print axioms NLA.Proofs.RE05.measurementScale
#assert_trust kernel NLA.Proofs.RE05.measurementScale_sq
#print axioms NLA.Proofs.RE05.measurementScale_sq
#assert_trust kernel NLA.Proofs.RE05.packedMeasurement
#print axioms NLA.Proofs.RE05.packedMeasurement
#assert_trust kernel NLA.Proofs.RE05.packedMeasurement_inner
#print axioms NLA.Proofs.RE05.packedMeasurement_inner
#assert_trust kernel NLA.Proofs.RE05.measurementVector
#print axioms NLA.Proofs.RE05.measurementVector
#assert_trust kernel NLA.Proofs.RE05.observationVector
#print axioms NLA.Proofs.RE05.observationVector
#assert_trust kernel NLA.Proofs.RE05.measurementMap
#print axioms NLA.Proofs.RE05.measurementMap
#assert_trust kernel NLA.Proofs.RE05.observationVector_planAnswers
#print axioms NLA.Proofs.RE05.observationVector_planAnswers
#assert_trust kernel NLA.Proofs.RE05.observationVector_copyResponses
#print axioms NLA.Proofs.RE05.observationVector_copyResponses
#assert_trust kernel NLA.Proofs.RE05.matrixRepresentationMap
#print axioms NLA.Proofs.RE05.matrixRepresentationMap
#assert_trust kernel NLA.Proofs.RE05.represent_eq_sum
#print axioms NLA.Proofs.RE05.represent_eq_sum
#assert_trust kernel NLA.Proofs.RE05.represent_single
#print axioms NLA.Proofs.RE05.represent_single
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement
#print axioms NLA.Proofs.RE05.coefficientMeasurement
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement_apply
#print axioms NLA.Proofs.RE05.coefficientMeasurement_apply
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement_single
#print axioms NLA.Proofs.RE05.coefficientMeasurement_single
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement_sum
#print axioms NLA.Proofs.RE05.coefficientMeasurement_sum
#assert_trust kernel NLA.Proofs.RE05.gram_eq_measurement_inner
#print axioms NLA.Proofs.RE05.gram_eq_measurement_inner
#assert_trust kernel NLA.Proofs.RE05.rhs_eq_measurement_inner
#print axioms NLA.Proofs.RE05.rhs_eq_measurement_inner
#assert_trust kernel NLA.Proofs.RE05.gram_mulVec_eq_inner
#print axioms NLA.Proofs.RE05.gram_mulVec_eq_inner
#assert_trust kernel NLA.Proofs.RE05.gram_quadratic
#print axioms NLA.Proofs.RE05.gram_quadratic
#assert_trust kernel NLA.Proofs.RE05.rhs_linear
#print axioms NLA.Proofs.RE05.rhs_linear
#assert_trust kernel NLA.Proofs.RE05.gram_hermitian
#print axioms NLA.Proofs.RE05.gram_hermitian
#assert_trust kernel NLA.Proofs.RE05.gram_posSemidef
#print axioms NLA.Proofs.RE05.gram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.regression_quadratic
#print axioms NLA.Proofs.RE05.regression_quadratic
#assert_trust kernel NLA.Proofs.RE05.exists_normal_coefficients
#print axioms NLA.Proofs.RE05.exists_normal_coefficients
#assert_trust kernel NLA.Proofs.RE05.singleOutput_eq_pseudoInverse_mulVec
#print axioms NLA.Proofs.RE05.singleOutput_eq_pseudoInverse_mulVec
#assert_trust kernel NLA.Proofs.RE05.singleOutput_normal
#print axioms NLA.Proofs.RE05.singleOutput_normal
#assert_trust kernel NLA.Proofs.RE05.normal_measurement_orthogonal
#print axioms NLA.Proofs.RE05.normal_measurement_orthogonal
#assert_trust kernel NLA.Proofs.RE05.normal_pythagorean
#print axioms NLA.Proofs.RE05.normal_pythagorean
#assert_trust kernel NLA.Proofs.RE05.singleOutput_minimizes
#print axioms NLA.Proofs.RE05.singleOutput_minimizes
#assert_trust kernel NLA.Proofs.RE05.singleOutput_batch_normal
#print axioms NLA.Proofs.RE05.singleOutput_batch_normal
#assert_trust kernel NLA.Proofs.RE05.represent_mem_span_iff
#print axioms NLA.Proofs.RE05.represent_mem_span_iff
#assert_trust kernel NLA.Proofs.RE05.represent_mem_span
#print axioms NLA.Proofs.RE05.represent_mem_span
#assert_trust kernel NLA.Proofs.RE05.represent_injective
#print axioms NLA.Proofs.RE05.represent_injective
#assert_trust kernel NLA.Proofs.RE05.matrixVector_represent_sum
#print axioms NLA.Proofs.RE05.matrixVector_represent_sum
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates
#print axioms NLA.Proofs.RE05.orthonormalCoordinates
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates_represent
#print axioms NLA.Proofs.RE05.orthonormalCoordinates_represent
#assert_trust kernel NLA.Proofs.RE05.represent_in_orthonormal_span
#print axioms NLA.Proofs.RE05.represent_in_orthonormal_span
#assert_trust kernel NLA.Proofs.RE05.orthonormal_represent_in_supplied_span
#print axioms NLA.Proofs.RE05.orthonormal_represent_in_supplied_span
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates_reconstruct
#print axioms NLA.Proofs.RE05.orthonormalCoordinates_reconstruct
#assert_trust kernel NLA.Proofs.RE05.orthonormal_representation_inner
#print axioms NLA.Proofs.RE05.orthonormal_representation_inner
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates_inner
#print axioms NLA.Proofs.RE05.orthonormalCoordinates_inner
#assert_trust kernel NLA.Proofs.RE05.gram_orthonormal_transport
#print axioms NLA.Proofs.RE05.gram_orthonormal_transport
#assert_trust kernel NLA.Proofs.RE05.rhs_orthonormal_transport
#print axioms NLA.Proofs.RE05.rhs_orthonormal_transport
#assert_trust kernel NLA.Proofs.RE05.OrthonormalMeasurementLowerBound
#print axioms NLA.Proofs.RE05.OrthonormalMeasurementLowerBound
#assert_trust kernel NLA.Proofs.RE05.measurement_lower_bound_supplied
#print axioms NLA.Proofs.RE05.measurement_lower_bound_supplied
#assert_trust kernel NLA.Proofs.RE05.gram_posDef_of_lower_bound
#print axioms NLA.Proofs.RE05.gram_posDef_of_lower_bound
#assert_trust kernel NLA.Proofs.RE05.gram_full_rank_of_lower_bound
#print axioms NLA.Proofs.RE05.gram_full_rank_of_lower_bound
#assert_trust kernel NLA.Proofs.RE05.singleOutput_unique_of_lower_bound
#print axioms NLA.Proofs.RE05.singleOutput_unique_of_lower_bound
#assert_trust kernel NLA.Proofs.RE05.orthonormal_solve_supplied_normal
#print axioms NLA.Proofs.RE05.orthonormal_solve_supplied_normal
#assert_trust kernel NLA.Proofs.RE05.singleOutput_matrix_basis_invariant_of_lower_bound
#print axioms NLA.Proofs.RE05.singleOutput_matrix_basis_invariant_of_lower_bound
#assert_trust kernel RE05RegressionGeometryConsumer.literal_response_slice
#print axioms RE05RegressionGeometryConsumer.literal_response_slice
#assert_trust kernel RE05RegressionGeometryConsumer.literal_left_answer
#print axioms RE05RegressionGeometryConsumer.literal_left_answer
#assert_trust kernel RE05RegressionGeometryConsumer.literal_right_answer
#print axioms RE05RegressionGeometryConsumer.literal_right_answer
#assert_trust kernel RE05RegressionGeometryConsumer.literal_mp_entry
#print axioms RE05RegressionGeometryConsumer.literal_mp_entry
#assert_trust kernel RE05RegressionGeometryConsumer.literal_original_normal_entry
#print axioms RE05RegressionGeometryConsumer.literal_original_normal_entry
#assert_trust kernel RE05RegressionGeometryConsumer.literal_measured_quadratic
#print axioms RE05RegressionGeometryConsumer.literal_measured_quadratic
#assert_trust kernel RE05RegressionGeometryConsumer.literal_original_minimum
#print axioms RE05RegressionGeometryConsumer.literal_original_minimum
#assert_trust kernel RE05RegressionGeometryConsumer.literal_actual_basis_reconstruction
#print axioms RE05RegressionGeometryConsumer.literal_actual_basis_reconstruction
#assert_trust kernel RE05RegressionGeometryConsumer.literal_lower_event_full_rank
#print axioms RE05RegressionGeometryConsumer.literal_lower_event_full_rank
#assert_trust kernel RE05RegressionGeometryConsumer.literal_conditional_matrix_output
#print axioms RE05RegressionGeometryConsumer.literal_conditional_matrix_output
#assert_trust kernel RE05RegressionGeometryConsumer.zero_width_dependent_output
#print axioms RE05RegressionGeometryConsumer.zero_width_dependent_output
#assert_trust kernel RE05RegressionGeometryConsumer.empty_matrix_normal
#print axioms RE05RegressionGeometryConsumer.empty_matrix_normal
#assert_trust kernel RE05RegressionGeometryConsumer.actual_rectangular_mp
#print axioms RE05RegressionGeometryConsumer.actual_rectangular_mp
