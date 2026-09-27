import NLA.FR05.Planted.SourceRowDistance
import NLA.FR05.Planted.SourceGoodEvent
import NLA.FR05.Likelihood.CanonicalKernelBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace NLA.FR05

theorem sourceJacobian_leastGain_failure_le {M : ℕ} (hM : 2 ≤ M) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
      (sourceRowCount M) (sourceTailDimension M)).real
      {sample | ¬ HasEuclideanLowerBound (sourceJacobianMatrixAt M hM sample) (sourceKappa M)} ≤
      112 / (M : ℝ) ^ 2 + 100 * M * Real.exp (-(4 * (M : ℝ))) := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by lia)
  have hu : 0 ≤ (sourceRowCount M : ℝ) * sourceKappa M :=
    mul_nonneg (Nat.cast_nonneg _) (sourceKappa_pos M (by lia)).le
  have hc := source_smallBall_calibration (by exact_mod_cast hM) hu (source_row_threshold_le hM)
  have hh := iidSourceCoordinateLaw_leastGain_failure_le (by lia : 1 ≤ M)
    (sourceJacobianCoordinateEquivSourceRows M hM) (sourceKappa_pos M (by lia))
    (t := 1 / (M : ℝ) ^ 6) (by positivity) hc.1
  have hp : (max (sourceTailSmallBallBound M
        ((sourceRowCount M : ℝ) * sourceKappa M) (1 / (M : ℝ) ^ 6))
      (sourceNonTailSmallBallBound
        ((sourceRowCount M : ℝ) * sourceKappa M) (1 / (M : ℝ) ^ 6))).toReal ≤
      28 / (M : ℝ) ^ 3 + 25 * Real.exp (-(4 * (M : ℝ))) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (source_smallBall_bound_calibrated hM)
    simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ 28 / (M : ℝ) ^ 3 + 25 * Real.exp (-(4 * (M : ℝ))))] using h
  have hn : (sourceRowCount M : ℝ) ≤ 4 * M := by
    exact_mod_cast (show sourceRowCount M ≤ 4 * M by unfold sourceRowCount; lia)
  calc
    _ ≤ (sourceRowCount M : ℝ) *
        (28 / (M : ℝ) ^ 3 + 25 * Real.exp (-(4 * (M : ℝ)))) :=
      hh.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
    _ ≤ (4 * M) * (28 / (M : ℝ) ^ 3 + 25 * Real.exp (-(4 * (M : ℝ)))) := by gcongr
    _ = _ := by field_simp; ring

def SourceNewtonGood (M : ℕ) (hM : 2 ≤ M)
    (sample : Fin (sourceRowCount M) → SourcePlantedCoordinates (sourceTailDimension M)) : Prop :=
  SourceCoordinateSampleGood M sample ∧
    HasEuclideanLowerBound (sourceJacobianMatrixAt M hM sample) (sourceKappa M) ∧
    ∀ i, |(sample i).1.2.1| ≤ sourceEpsilon M

theorem sourceNewtonGood_failure_le {M : ℕ} (hM : 3 ≤ M) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
      (sourceRowCount M) (sourceTailDimension M)).real
      {sample | ¬ SourceNewtonGood M (by lia) sample} ≤
      112 / (M : ℝ) ^ 2 + 204 * M * Real.exp (-(M : ℝ)) := by
  let μ := iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
    (sourceRowCount M) (sourceTailDimension M)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_iidSourceCoordinateLaw
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M (by lia)) _ _
  have hs := ae_iidSourceCoordinateLaw_support (m := sourceRowCount M)
    (n := sourceTailDimension M) (δ := sourceDelta M)
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M (by lia))
  have hsub : {sample | ¬ SourceNewtonGood M (by lia) sample} ≤ᵐ[μ]
      ({sample | ¬ SourceCoordinateSampleGood M sample} ∪
      {sample | ¬ HasEuclideanLowerBound (sourceJacobianMatrixAt M (by lia) sample)
        (sourceKappa M)} : Set (Fin (sourceRowCount M) →
          SourcePlantedCoordinates (sourceTailDimension M))) := by
    filter_upwards [hs] with sample hsample
    change (¬ SourceNewtonGood M _ sample) → _
    intro h
    by_contra hc
    change ¬ (¬ SourceCoordinateSampleGood M sample ∨
      ¬ HasEuclideanLowerBound (sourceJacobianMatrixAt M (by lia) sample) (sourceKappa M)) at hc
    push Not at hc
    exact h ⟨hc.1, hc.2, fun i ↦ (hsample i).2⟩
  have hmeasure := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have he := iidSourceCoordinateLawAt_not_sourceCoordinateSampleGood_real_le
    (m := sourceRowCount M) (n := sourceTailDimension M) (by lia : 2 ≤ M)
    (by unfold sourceTailDimension; lia)
  have hj := sourceJacobian_leastGain_failure_le (by lia : 2 ≤ M)
  have hn : (sourceRowCount M : ℝ) ≤ 4 * M := by
    exact_mod_cast (show sourceRowCount M ≤ 4 * M by unfold sourceRowCount; lia)
  have hdim : (M : ℝ) ≤ 3 * sourceTailDimension M := by
    exact_mod_cast (show M ≤ 3 * sourceTailDimension M by unfold sourceTailDimension; lia)
  have he1 : Real.exp (-(4 * (M : ℝ))) ≤ Real.exp (-(M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith [Nat.cast_nonneg (α := ℝ) M]
  have he2 : Real.exp (-3 * (sourceTailDimension M : ℝ)) ≤ Real.exp (-(M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    _ ≤ μ.real ({sample | ¬ SourceCoordinateSampleGood M sample} ∪
        {sample | ¬ HasEuclideanLowerBound (sourceJacobianMatrixAt M (by lia) sample)
          (sourceKappa M)}) := hmeasure
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (sourceRowCount M : ℝ) * (25 * Real.exp (-(4 * (M : ℝ))) +
          Real.exp (-3 * (sourceTailDimension M : ℝ))) +
        (112 / (M : ℝ) ^ 2 + 100 * M * Real.exp (-(4 * (M : ℝ)))) := add_le_add he hj
    _ ≤ (4 * M) * (25 * Real.exp (-(M : ℝ)) + Real.exp (-(M : ℝ))) +
        (112 / (M : ℝ) ^ 2 + 100 * M * Real.exp (-(M : ℝ))) := by gcongr
    _ = _ := by ring

theorem sourceNewtonGood_failure_order :
    ∃ D : ℕ, 3 ≤ D ∧ ∀ M (hM : 2 ≤ M), D ≤ M →
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceRowCount M) (sourceTailDimension M)).real
        {sample | ¬ SourceNewtonGood M hM sample} ≤ 113 / (M : ℝ) ^ 2 := by
  obtain ⟨D, hD⟩ := polynomial_exp_tail_le_inv 204 1 (by norm_num) 2
  refine ⟨max D 3, le_max_right _ _, fun M hM hlarge ↦ ?_⟩
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by lia)
  have h := hD M ((le_max_left _ _).trans hlarge)
  have ht : 204 * M * Real.exp (-(M : ℝ)) ≤ 1 / (M : ℝ) ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < (M : ℝ) ^ 2)).2
    have hh := (le_div_iff₀ hm).mp h
    norm_num only [neg_mul, one_mul] at hh
    nlinarith only [hh]
  have hb := sourceNewtonGood_failure_le
    (show 3 ≤ M from (le_max_right _ _).trans hlarge)
  simp only [div_eq_mul_inv] at ht hb ⊢
  linarith
end NLA.FR05
