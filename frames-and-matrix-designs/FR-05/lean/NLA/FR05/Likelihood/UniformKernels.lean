import NLA.FR05.Likelihood.PlantedGlobalBound
import NLA.FR05.Likelihood.ReferenceKernelExact
import NLA.FR05.Likelihood.GaussianKernelCauchySchwarz

set_option autoImplicit false
noncomputable section
open Real

namespace NLA.FR05

theorem sourceDensityCorrelation_diagonal_global_bound {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation a a M K ≤
      Real.exp (2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 -
        overlapOperatorNorm K ^ 2 / 2000) * overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
  cases a with
  | planted => exact sourceDensityCorrelation_planted_global_bound hM hK
  | reference =>
    apply (sourceDensityCorrelation_reference_global_bound hM hK).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (overlapDeterminant_pos hK).le _)
    apply Real.exp_le_exp.mpr
    have hd : 0 ≤ sourceDelta M := by unfold sourceDelta; positivity
    nlinarith [sq_nonneg (sourceEpsilon M)]

theorem sourceDensityCorrelation_global_bound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation a b M K ≤
      Real.exp (2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 -
        overlapOperatorNorm K ^ 2 / 2000) * overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
  have hL : overlapOperatorNorm (overlapLeftRoot K) < 1 := by
    rw [overlapLeftRoot_norm]; exact hK
  have hR : overlapOperatorNorm (overlapRightRoot K) < 1 := by
    rw [overlapRightRoot_norm]; exact hK
  have hl := sourceDensityCorrelation_diagonal_global_bound hM a hL
  have hr := sourceDensityCorrelation_diagonal_global_bound hM b hR
  rw [overlapLeftRoot_norm, overlapLeftRoot_determinant] at hl
  rw [overlapRightRoot_norm, overlapRightRoot_determinant] at hr
  have hB : 0 ≤ Real.exp (2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 -
      overlapOperatorNorm K ^ 2 / 2000) * overlapDeterminant K ^ (-(1 / 4 : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (overlapDeterminant_pos hK).le _)
  have hprod := mul_le_mul hl hr (sourceDensityCorrelation_nonneg hR b b M) hB
  have hcs := sourceDensityCorrelation_cauchy_schwarz hM a b hK
  nlinarith [sourceDensityCorrelation_nonneg hK a b M]

/-- Lemma 3.4, with explicit constants and a fixed Taylor radius. -/
theorem lemma_3_4 {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    0 ≤ sourceDensityCorrelation a b M K ∧
    sourceDensityCorrelation a b M K ≤
      Real.exp (2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 -
        overlapOperatorNorm K ^ 2 / 2000) * overlapDeterminant K ^ (-(1 / 4 : ℝ)) ∧
    sourceDensityCorrelation a b M K ≤ (Real.exp 1 + 4) * (M : ℝ)^52 ∧
    (overlapOperatorNorm K ≤ 1 / 128 →
      |sourceDensityCorrelation a b M K -
        (1 + (1 - sourceVariance M)^2 * overlapFrobeniusSq K)| ≤
        (11000 * kernelMomentConstant 4) * overlapFrobeniusSq K ^ 2) :=
  ⟨sourceDensityCorrelation_nonneg hK a b M,
    sourceDensityCorrelation_global_bound hM a b hK,
    sourceDensityCorrelation_polynomial_bound hM a b hK,
    fun hlocal ↦ sourceDensityCorrelation_local_expansion hM a b hlocal⟩

theorem sourcePairKernel_global_bound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (U V : SourceUnitary M)
    (hK : overlapOperatorNorm (sourceOverlap hM U V) < 1) :
    sourcePairKernel hM a b U V ≤
      Real.exp (2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 -
        overlapOperatorNorm (sourceOverlap hM U V) ^ 2 / 2000) *
          overlapDeterminant (sourceOverlap hM U V) ^ (-(1 / 4 : ℝ)) := by
  rw [sourcePairKernel_eq_densityCorrelation hM a b U V hK]
  exact sourceDensityCorrelation_global_bound hM a b hK

theorem sourceOverlapKernel_global_bound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceOverlapKernel hM a b K ≤
      Real.exp (2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 -
        overlapOperatorNorm K ^ 2 / 2000) * overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
  by_cases hr : K ∈ Set.range (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2)
  · obtain ⟨⟨U, V⟩, rfl⟩ := hr
    rw [sourceOverlapKernel_apply]
    exact sourcePairKernel_global_bound hM a b U V hK
  · rw [sourceOverlapKernel_eq_zero hM a b K hr]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (overlapDeterminant_pos hK).le _)

theorem sourceOverlapKernel_local_expansion {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hr : K ∈ Set.range (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2))
    (hK : overlapOperatorNorm K ≤ 1 / 128) :
    |sourceOverlapKernel hM a b K -
      (1 + (1 - sourceVariance M)^2 * overlapFrobeniusSq K)| ≤
      (11000 * kernelMomentConstant 4) * overlapFrobeniusSq K ^ 2 := by
  obtain ⟨⟨U, V⟩, rfl⟩ := hr
  rw [sourceOverlapKernel_apply]
  exact sourcePairKernel_local_expansion hM a b U V hK

end NLA.FR05
