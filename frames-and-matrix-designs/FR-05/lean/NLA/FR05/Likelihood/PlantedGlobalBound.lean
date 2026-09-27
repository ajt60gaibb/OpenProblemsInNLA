import NLA.FR05.Cone.PlantedConeDomination

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Real Set
open scoped ENNReal

namespace NLA.FR05

theorem sourceEpsilon_le_quarter {M : ℕ} (hM : 2 ≤ M) :
    sourceEpsilon M ≤ 1 / 4 := by
  have h : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : (M : ℝ)^2 ≤ (M : ℝ)^50 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h4 : (4 : ℝ) ≤ (M : ℝ)^50 := by nlinarith
  unfold sourceEpsilon
  simpa only [one_div] using (inv_le_inv₀ (by linarith) (by norm_num)).mpr h4

theorem sourceRadialNormalizer_inv_le (M : ℕ) :
    (sourceRadialNormalizer M)⁻¹ ≤ Real.exp (sourceDelta M) := by
  have hd : 0 ≤ sourceDelta M := by unfold sourceDelta; positivity
  have he : Real.exp (-sourceDelta M) ≤ sourceRadialNormalizer M := by
    unfold sourceRadialNormalizer sourceEta
    nlinarith [Real.exp_pos (-sourceDelta M)]
  calc
    _ ≤ (Real.exp (-sourceDelta M))⁻¹ :=
      (inv_le_inv₀ (sourceRadialNormalizer_pos M) (Real.exp_pos _)).mpr he
    _ = _ := by rw [Real.exp_neg, inv_inv]

theorem plantedConeNormalizer_cancel {M : ℕ} (hM : 1 ≤ M) :
    plantedConeNormalizer M * (2 * sourceEpsilon M) = (sourceRadialNormalizer M)⁻¹ := by
  unfold plantedConeNormalizer
  field_simp [(sourceEpsilon_pos M hM).ne', (sourceRadialNormalizer_pos M).ne']

theorem lintegral_planted_pair_global_bound {M : ℕ} (hM : 2 ≤ M)
    {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    (∫⁻ p, ENNReal.ofReal (overlapGaussianRatio K p.1 p.2)
      ∂(sourceDensityLaw .planted M).prod (sourceDensityLaw .planted M)) ≤
      ENNReal.ofReal ((sourceRadialNormalizer M)⁻¹ ^ 2 *
        (Real.exp (2 * sourceEpsilon M ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
          overlapDeterminant K ^ (-(1 / 4 : ℝ)))) := by
  let B := Real.exp (2 * sourceEpsilon M ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
    overlapDeterminant K ^ (-(1 / 4 : ℝ))
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (overlapDeterminant_pos hK).le _)
  have hM1 : 1 ≤ M := by lia
  have he := (sourceEpsilon_pos M hM1).le
  apply (lintegral_planted_pair_le_cones hM _ (by fun_prop)).trans
  calc
    _ ≤ ENNReal.ofReal (plantedConeNormalizer M)^2 *
        ∫⁻ t in Icc (-sourceEpsilon M) (sourceEpsilon M),
          ∫⁻ s in Icc (-sourceEpsilon M) (sourceEpsilon M), ENNReal.ofReal B := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have ht' : |t| ≤ sourceEpsilon M := abs_le.mpr ht
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      have hs' : |s| ≤ sourceEpsilon M := abs_le.mpr hs
      have ht1 : |t| ≤ 1 := (ht'.trans (sourceEpsilon_le_quarter hM)).trans (by norm_num)
      have hs1 : |s| ≤ 1 := (hs'.trans (sourceEpsilon_le_quarter hM)).trans (by norm_num)
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_coneCorrelation hK ht1 hs1)
        (Filter.Eventually.of_forall fun p ↦ overlapGaussianRatio_nonneg hK p.1 p.2)]
      apply ENNReal.ofReal_le_ofReal
      apply (lemma_3_3 hK (ht'.trans (sourceEpsilon_le_quarter hM))
        (hs'.trans (sourceEpsilon_le_quarter hM))).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (overlapDeterminant_pos hK).le _)
      apply Real.exp_le_exp.mpr
      have htt : t^2 ≤ sourceEpsilon M ^ 2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) he).mpr ht'
      have hss : s^2 ≤ sourceEpsilon M ^ 2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) he).mpr hs'
      nlinarith
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      rw [show sourceEpsilon M - -sourceEpsilon M = 2 * sourceEpsilon M by ring]
      rw [← ENNReal.ofReal_pow (plantedConeNormalizer_nonneg hM1)]
      rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (mul_nonneg hB (by positivity)),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      have hc := plantedConeNormalizer_cancel hM1
      change plantedConeNormalizer M ^ 2 * (B * (2 * sourceEpsilon M) * (2 * sourceEpsilon M)) = _
      calc
        _ = (plantedConeNormalizer M * (2 * sourceEpsilon M))^2 * B := by ring
        _ = _ := by rw [hc]

theorem sourceDensityCorrelation_planted_global_bound {M : ℕ} (hM : 2 ≤ M)
    {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation .planted .planted M K ≤
      Real.exp (2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 -
        overlapOperatorNorm K ^ 2 / 2000) * overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
  have hle := lintegral_planted_pair_global_bound hM hK
  have hn : ∀ᵐ p ∂(sourceDensityLaw .planted M).prod (sourceDensityLaw .planted M),
      0 ≤ overlapGaussianRatio K p.1 p.2 :=
    Filter.Eventually.of_forall fun p ↦ overlapGaussianRatio_nonneg hK p.1 p.2
  have hi : Integrable (fun p : Signal 2 × Signal 2 ↦ overlapGaussianRatio K p.1 p.2)
      ((sourceDensityLaw .planted M).prod (sourceDensityLaw .planted M)) := by
    refine ⟨(continuous_overlapGaussianRatio K).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hn]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hle
  have hB : 0 ≤ Real.exp (2 * sourceEpsilon M ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
      overlapDeterminant K ^ (-(1 / 4 : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (overlapDeterminant_pos hK).le _)
  have h := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) hB)).mp hle
  apply h.trans
  calc
    _ ≤ Real.exp (sourceDelta M)^2 *
        (Real.exp (2 * sourceEpsilon M ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
          overlapDeterminant K ^ (-(1 / 4 : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact pow_le_pow_left₀ (inv_nonneg.mpr (sourceRadialNormalizer_pos M).le)
        (sourceRadialNormalizer_inv_le M) 2
    _ = _ := by rw [← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]; congr 2; ring

end NLA.FR05
