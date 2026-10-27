import NLA.Proofs.RE05.OneCopyOptimum

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

/-- Deterministic original-output error for a fixed original plan and an
analysis optimum. The plan is never regenerated using the fold basis. -/
theorem singleCopy_squared_error_bound {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (plan : Plan n) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (α : ℝ) (hα : 0 < α) (hLower : OrthonormalMeasurementLowerBound P plan α) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (singleOutput P plan (planAnswers A plan))) ^ 2 ≤
        optimum P A ^ 2 + (1 / α ^ 2) *
          dot (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
            (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) := by
  rw [singleOutput_matrix_basis_invariant_of_lower_bound P hP plan _ α hα hLower, hPyth]
  exact add_le_add (le_refl (optimum P A ^ 2))
    (singleOutput_coefficient_error (orthonormalMember P) plan A c α hα hLower)

/-- The optimum witness depends only on P and A, before every plan and lower
event. Its orthogonal residual and actual Opt identity are both derived. -/
theorem exists_oneCopy_error_analysis {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) c) = optimum P A ∧
      (∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.inner (A - represent (orthonormalMember P) c)
          (represent (orthonormalMember P) d) = 0) ∧
      (∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.NonadaptiveMatrixQuery.frobenius A
          (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c)) ∧
      ∀ (plan : Plan n) (α : ℝ), 0 < α → OrthonormalMeasurementLowerBound P plan α →
        NLA.Computation.NonadaptiveMatrixQuery.frobenius A
          (represent P (singleOutput P plan (planAnswers A plan))) ^ 2 ≤
          optimum P A ^ 2 + (1 / α ^ 2) *
            dot (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
              (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) := by
  rcases exists_orthonormal_analysis_optimum P hP A with ⟨c, hc, ho, hp⟩
  exact ⟨c, hc, ho, hp, fun plan α hα hLower =>
    singleCopy_squared_error_bound P hP A plan c hp α hα hLower⟩

/-- With Gram lower bound one half and offset square at most xi/4 times
actual Opt squared, the original actual output has relative squared error.
The argument includes Opt=0 and does not divide by it. -/
theorem singleCopy_relative_squared {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (plan : Plan n) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (ξ : ℝ) (hLower : OrthonormalMeasurementLowerBound P plan (1 / 2))
    (hOffset : dot
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) ≤
        (ξ / 4) * optimum P A ^ 2) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (singleOutput P plan (planAnswers A plan))) ^ 2 ≤
        (1 + ξ) * optimum P A ^ 2 := by
  have h := singleCopy_squared_error_bound P hP A plan c hPyth (1 / 2) (by norm_num) hLower
  norm_num at h
  calc
    _ ≤ _ := h
    _ ≤ optimum P A ^ 2 + 4 * ((ξ / 4) * optimum P A ^ 2) :=
      add_le_add (le_refl (optimum P A ^ 2))
        (mul_le_mul_of_nonneg_left hOffset (by norm_num : (0 : ℝ) ≤ 4))
    _ = _ := by ring

theorem singleCopy_batch_relative_squared {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (schedule : Fin 15 → Plan n) (copy : Fin 15) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (ξ : ℝ) (hLower : OrthonormalMeasurementLowerBound P (schedule copy) (1 / 2))
    (hOffset : dot
      (regressionOffset (orthonormalMember P) (schedule copy) (A - represent (orthonormalMember P) c))
      (regressionOffset (orthonormalMember P) (schedule copy) (A - represent (orthonormalMember P) c)) ≤
        (ξ / 4) * optimum P A ^ 2) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (singleOutput P (schedule copy)
        (copyResponses schedule (batchAnswers A schedule) copy))) ^ 2 ≤
        (1 + ξ) * optimum P A ^ 2 := by
  rw [copyResponses_batchAnswers]
  exact singleCopy_relative_squared P hP A _ c hPyth ξ hLower hOffset

theorem singleCopy_zero_optimum_exact {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (plan : Plan n) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (hLower : OrthonormalMeasurementLowerBound P plan (1 / 2))
    (hOpt : optimum P A = 0)
    (hOffset : dot
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) ≤ 0) :
    A = represent P (singleOutput P plan (planAnswers A plan)) := by
  have h := singleCopy_relative_squared P hP A plan c hPyth 0 hLower (by simpa using hOffset)
  rw [hOpt] at h
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  apply (frobenius_eq_zero_iff A _).mp
  exact sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))

end NLA.Proofs.RE05
