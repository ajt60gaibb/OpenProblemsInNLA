import NLA.Proofs.RE05.MeasurementGeometry
import NLA.Proofs.RE05.PseudoIdentities

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

theorem gram_hermitian {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (gram P plan).IsHermitian := by
  change (gram P plan).conjTranspose = gram P plan
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, gram_eq_measurement_inner]
  exact real_inner_comm _ _

theorem gram_posSemidef {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (gram P plan).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gram_hermitian P plan)
  intro c
  change 0 ≤ dot c (gram P plan *ᵥ c)
  rw [gram_quadratic]
  exact real_inner_self_nonneg

/-- The literal least-squares quadratic, including the model's reciprocal
weight at zero width and arbitrary response lists. -/
theorem regression_quadratic {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    ‖observationVector plan responses - coefficientMeasurement P plan c‖ ^ 2 =
      ‖observationVector plan responses‖ ^ 2 - 2 * dot c (rhs P plan responses) +
        dot c (gram P plan *ᵥ c) := by
  rw [norm_sub_sq_real, rhs_linear, gram_quadratic, real_inner_self_eq_norm_sq,
    real_inner_comm (observationVector plan responses)]

/-- A genuine finite-dimensional projection proves that these actual normal
equations are consistent; no rank or optimizer assumption is added. -/
theorem exists_normal_coefficients {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) :
    ∃ c : Fin (q + 1) → ℝ, gram P plan *ᵥ c = rhs P plan responses := by
  let L := coefficientMeasurement P plan
  let K := LinearMap.range L
  let y := observationVector plan responses
  have hK : IsComplete (K : Set (MeasurementSpace plan)) :=
    K.closed_of_finiteDimensional.isComplete
  rcases K.exists_norm_eq_iInf_of_complete_subspace hK y with ⟨v, hv, hmin⟩
  have horth := (K.norm_eq_iInf_iff_real_inner_eq_zero hv).mp hmin
  rcases hv with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  ext j
  have hj := horth (L (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
  rw [← hc] at hj
  change ⟪y - coefficientMeasurement P plan c,
    coefficientMeasurement P plan (Pi.single j 1)⟫_ℝ = 0 at hj
  rw [coefficientMeasurement_single] at hj
  have he : rhs P plan responses j - (gram P plan *ᵥ c) j = 0 := by
    rw [rhs_eq_measurement_inner, gram_mulVec_eq_inner, ← inner_sub_right,
      real_inner_comm]
    exact hj
  exact (sub_eq_zero.mp he).symm

/-- The model's original coefficient output is precisely its actual exact-SVD
Moore--Penrose Gram solve, with no change of basis. -/
theorem singleOutput_eq_pseudoInverse_mulVec {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) :
    singleOutput P plan responses =
      NLA.Computation.NonadaptiveMatrixQuery.pseudoInverse (gram P plan) *ᵥ
        rhs P plan responses := rfl

/-- Consistency and the actual Moore--Penrose sandwich identity make the
original algorithm solve the actual normal equations even when singular. -/
theorem singleOutput_normal {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) :
    gram P plan *ᵥ singleOutput P plan responses = rhs P plan responses := by
  rcases exists_normal_coefficients P plan responses with ⟨c, hc⟩
  rw [singleOutput_eq_pseudoInverse_mulVec, ← hc, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Pseudo.mul_pseudoinverse_mul]

theorem normal_measurement_orthogonal {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ)
    (hc : gram P plan *ᵥ c = rhs P plan responses) (d : Fin (q + 1) → ℝ) :
    ⟪observationVector plan responses - coefficientMeasurement P plan c,
      coefficientMeasurement P plan d⟫_ℝ = 0 := by
  rw [inner_sub_left, real_inner_comm (coefficientMeasurement P plan d)
      (observationVector plan responses),
    ← rhs_linear, real_inner_comm (coefficientMeasurement P plan d)
      (coefficientMeasurement P plan c),
    ← gram_quadratic, hc, sub_self]

/-- Every solution satisfies the exact measured Pythagorean identity. -/
theorem normal_pythagorean {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ)
    (hc : gram P plan *ᵥ c = rhs P plan responses) (d : Fin (q + 1) → ℝ) :
    ‖observationVector plan responses - coefficientMeasurement P plan d‖ ^ 2 =
      ‖observationVector plan responses - coefficientMeasurement P plan c‖ ^ 2 +
      ‖coefficientMeasurement P plan c - coefficientMeasurement P plan d‖ ^ 2 := by
  have h := normal_measurement_orthogonal P plan responses c hc (c - d)
  rw [map_sub] at h
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (observationVector plan responses - coefficientMeasurement P plan c)
    (coefficientMeasurement P plan c - coefficientMeasurement P plan d) h
  rw [show observationVector plan responses - coefficientMeasurement P plan c +
    (coefficientMeasurement P plan c - coefficientMeasurement P plan d) =
      observationVector plan responses - coefficientMeasurement P plan d by abel] at hp
  simpa only [pow_two] using hp

/-- The actual coefficient output minimizes the literal measured objective. -/
theorem singleOutput_minimizes {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (d : Fin (q + 1) → ℝ) :
    ‖observationVector plan responses - coefficientMeasurement P plan
      (singleOutput P plan responses)‖ ^ 2 ≤
      ‖observationVector plan responses - coefficientMeasurement P plan d‖ ^ 2 := by
  rw [normal_pythagorean P plan responses _ (singleOutput_normal P plan responses) d]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The true-query version uses precisely the original batch responses. -/
theorem singleOutput_batch_normal {n q : ℕ} (P : Basis n q) (A : Square n)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) (j : Fin (q + 1)) :
    ⟪measurementVector (schedule copy) (P j),
      measurementVector (schedule copy)
        (A - represent P (singleOutput P (schedule copy)
          (copyResponses schedule (batchAnswers A schedule) copy)))⟫_ℝ = 0 := by
  have h := normal_measurement_orthogonal P (schedule copy)
    (copyResponses schedule (batchAnswers A schedule) copy) _
    (singleOutput_normal P (schedule copy) _) (Pi.single j 1)
  rw [observationVector_copyResponses, coefficientMeasurement_single,
    coefficientMeasurement_apply, real_inner_comm] at h
  change ⟪measurementVector (schedule copy) (P j),
    (measurementMap (schedule copy)) (A - represent P _)⟫_ℝ = 0
  rw [map_sub]
  exact h

end NLA.Proofs.RE05
