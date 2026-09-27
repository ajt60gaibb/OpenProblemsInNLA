import NLA.FR05.Likelihood.LikelihoodDensityBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NLA.FR05

def sourcePairComparisonConstant : ℝ :=
  8 * sourceTaylorConstant *
    (∫ K : SourceOverlapMatrix, overlapFrobeniusSq K ^ 2 *
      Real.exp (-(1 / 400) * overlapFrobeniusSq K)) + 1

theorem sourcePairComparisonConstant_pos : 0 < sourcePairComparisonConstant := by
  have hI : 0 ≤ ∫ K : SourceOverlapMatrix, overlapFrobeniusSq K ^ 2 *
      Real.exp (-(1 / 400) * overlapFrobeniusSq K) :=
    integral_nonneg (fun _ ↦ by positivity)
  have hR := sourceTaylorConstant_pos
  unfold sourcePairComparisonConstant
  positivity

theorem integrable_source_local_majorant (M : ℕ) (hM : 1 ≤ M) :
    Integrable (fun K : SourceOverlapMatrix ↦
      8 * sourceTaylorConstant * (M : ℝ) ^ 5 * overlapFrobeniusSq K ^ 2 *
        Real.exp (-(1 / 400) * M * overlapFrobeniusSq K)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by lia)
  have h := (integrable_matrix_quartic_gaussian
    (show 0 < (1 / 400 : ℝ) * M by positivity)).const_mul
      (8 * sourceTaylorConstant * (M : ℝ) ^ 5)
  simpa only [neg_mul, mul_assoc] using h

theorem integral_source_local_majorant (M : ℕ) (hM : 1 ≤ M) :
    (∫ K : SourceOverlapMatrix,
      8 * sourceTaylorConstant * (M : ℝ) ^ 5 * overlapFrobeniusSq K ^ 2 *
        Real.exp (-(1 / 400) * M * overlapFrobeniusSq K)) =
      (sourcePairComparisonConstant - 1) / M := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by lia)
  have he : (fun K : SourceOverlapMatrix ↦
      8 * sourceTaylorConstant * (M : ℝ) ^ 5 * overlapFrobeniusSq K ^ 2 *
        Real.exp (-(1 / 400) * M * overlapFrobeniusSq K)) =
      fun K ↦ (8 * sourceTaylorConstant) * ((M : ℝ) ^ 5 *
        (overlapFrobeniusSq K ^ 2 * Real.exp (-(1 / 400) * M * overlapFrobeniusSq K))) := by
    funext K
    ring
  rw [he, integral_const_mul, integral_const_mul, matrix_local_integral_scale _ hm]
  unfold sourcePairComparisonConstant
  ring

theorem source_overlap_differences_le :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (M : ℕ) (hM : 2 ≤ M), D ≤ M →
      ∀ a b : SourceDensityKind,
        (∫ K, sourceKernelDifference hM a b K ∂sourceOverlapLaw M hM) ≤
          sourcePairComparisonConstant / M := by
  obtain ⟨D₀, hD₀⟩ := source_tail_parameters_small
  let J := ∫ K : SourceOverlapMatrix, Real.exp (-overlapFrobeniusSq K)
  obtain ⟨D₁, hD₁⟩ := polynomial_exp_tail_le_inv
    (2 * sourceTailCoefficient * Real.exp 2 * J) sourceTailRate sourceTailRate_pos 784
  refine ⟨max 1600 (max D₀ D₁), by lia, ?_⟩
  intro M hM hD a b
  have hm : 1600 ≤ M := by lia
  have hp := hD₀ M (by lia)
  have ht := hD₁ M (by lia)
  have hi := integrable_sourceWeightedKernelDifference (by lia : 4 ≤ M) a b
  have hl := integrable_source_local_majorant M (by lia)
  have hg : Integrable (fun K : SourceOverlapMatrix ↦ Real.exp (-overlapFrobeniusSq K)) := by
    simpa using integrable_matrix_gaussian (by norm_num : (0 : ℝ) < 1)
  have htail := hg.const_mul
    (2 * sourceTailCoefficient * Real.exp 2 * (M : ℝ) ^ 784 * Real.exp (-sourceTailRate * M))
  rw [integral_sourceOverlapLaw_density (by lia : 4 ≤ M)]
  calc
    _ ≤ ∫ K : SourceOverlapMatrix,
        (8 * sourceTaylorConstant * (M : ℝ) ^ 5 * overlapFrobeniusSq K ^ 2 *
          Real.exp (-(1 / 400) * M * overlapFrobeniusSq K)) +
        (2 * sourceTailCoefficient * Real.exp 2 * (M : ℝ) ^ 784 * Real.exp (-sourceTailRate * M)) *
          Real.exp (-overlapFrobeniusSq K) :=
      integral_mono hi (hl.add htail) (source_weighted_difference_majorant hm hp a b)
    _ = (sourcePairComparisonConstant - 1) / M +
        (2 * sourceTailCoefficient * Real.exp 2 * J) * (M : ℝ) ^ 784 *
          Real.exp (-sourceTailRate * M) := by
      rw [integral_add hl htail, integral_source_local_majorant M (by lia), integral_const_mul]
      dsimp [J]
      ring
    _ ≤ (sourcePairComparisonConstant - 1) / M + 1 / M := add_le_add le_rfl ht
    _ = sourcePairComparisonConstant / M := by ring

theorem source_second_moment_comparisons :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, 2 ≤ D ∧
      ∀ (M : ℕ) (hM : 2 ≤ M), D ≤ M → ∀ a b : SourceDensityKind,
        |(∫ A, sourceLikelihood hM (sourceDensity a M) A *
            sourceLikelihood hM (sourceDensity b M) A
            ∂standardComplexGaussianFrame (sourceRowCount M) M) -
          (∫ A, sourceReferenceLikelihood hM A * sourceReferenceLikelihood hM A
            ∂standardComplexGaussianFrame (sourceRowCount M) M)| ≤ C / M := by
  obtain ⟨D, hD, hbound⟩ := source_overlap_differences_le
  refine ⟨sourcePairComparisonConstant, sourcePairComparisonConstant_pos, D, hD, ?_⟩
  intro M hM hDM a b
  change |(∫ A, sourceLikelihood hM (sourceDensity a M) A *
      sourceLikelihood hM (sourceDensity b M) A ∂_) -
      (∫ A, sourceLikelihood hM (sourceDensity .reference M) A *
        sourceLikelihood hM (sourceDensity .reference M) A ∂_)| ≤ _
  rw [source_second_moment_eq_overlap_integral, source_second_moment_eq_overlap_integral,
    ← integral_sub (integrable_sourceOverlapKernel_pow hM a b _)
      (integrable_sourceOverlapKernel_pow hM .reference .reference _)]
  exact abs_integral_le_integral_abs.trans (hbound M hM hDM a b)

/-- Proposition 3.2 for the concrete source likelihoods. -/
theorem proposition_3_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, 2 ≤ D ∧
      ∀ (M : ℕ) (hM : 2 ≤ M), D ≤ M → sourceLikelihoodL2 M hM ≤ C / M := by
  obtain ⟨D, hD, hbound⟩ := source_overlap_differences_le
  refine ⟨3 * sourcePairComparisonConstant, by have := sourcePairComparisonConstant_pos; positivity,
    D, hD, ?_⟩
  intro M hM hDM
  have hgg := hbound M hM hDM .planted .planted
  have hgr := hbound M hM hDM .planted .reference
  have h := sourceLikelihoodL2_le_overlap_differences M hM
  change sourceLikelihoodL2 M hM ≤
    (∫ K, sourceKernelDifference hM .planted .planted K ∂sourceOverlapLaw M hM) +
    2 * (∫ K, sourceKernelDifference hM .planted .reference K ∂sourceOverlapLaw M hM) at h
  calc
    _ ≤ sourcePairComparisonConstant / M + 2 * (sourcePairComparisonConstant / M) := by linarith
    _ = _ := by ring

end NLA.FR05
