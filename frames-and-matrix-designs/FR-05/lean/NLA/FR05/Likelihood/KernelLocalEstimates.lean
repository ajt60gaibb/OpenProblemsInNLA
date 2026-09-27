import NLA.FR05.Likelihood.KernelMatrixAlgebra
import NLA.FR05.Likelihood.ScalarTaylor

/-!
# Local reference-kernel estimates and exponential remainders

The sections develop `KernelLocalEstimates`, `KernelExponentBounds`, `KernelExponentialMoments`,
`KernelLocalRemainder`, `KernelLocalExpansion`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section KernelLocalEstimates

open MeasureTheory Complex Real Matrix
open scoped BigOperators

theorem kernelTotalRadius_nonneg (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    0 ≤ kernelTotalRadius p :=
  add_nonneg (sourceRadiusSq_nonneg p.1) (sourceRadiusSq_nonneg p.2)

theorem kernelCross_abs_le (K : SourceOverlapMatrix)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    2 * |kernelCross K p| ≤ overlapOperatorNorm K * kernelTotalRadius p := by
  have hc := coneInner_cauchy p.1 (K *ᵥ p.2)
  have hv := sourceRadiusSq_mulVec_le K p.2
  have hm := mul_le_mul_of_nonneg_left hv (sourceRadiusSq_nonneg p.1)
  have hr : kernelCross K p ^ 2 ≤ Complex.normSq (coneInner p.1 (K *ᵥ p.2)) := by
    unfold kernelCross
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg (coneInner p.1 (K *ᵥ p.2)).im]
  apply (sq_le_sq₀ (by positivity) (mul_nonneg (overlapOperatorNorm_nonneg K) (kernelTotalRadius_nonneg p))).mp
  rw [mul_pow, sq_abs]
  have hd := mul_nonneg (sq_nonneg (overlapOperatorNorm K))
    (sq_nonneg (sourceRadiusSq p.1 - sourceRadiusSq p.2))
  unfold kernelTotalRadius
  nlinarith

theorem kernelEvenQuadratic_bounds (K : SourceOverlapMatrix)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    0 ≤ kernelEvenQuadratic K p ∧
      kernelEvenQuadratic K p ≤ overlapOperatorNorm K ^ 2 * kernelTotalRadius p := by
  have hl := sourceRadiusSq_mulVec_le Kᴴ p.1
  have hr := sourceRadiusSq_mulVec_le K p.2
  rw [overlapOperatorNorm_conjTranspose] at hl
  constructor
  · exact add_nonneg (sourceRadiusSq_nonneg _) (sourceRadiusSq_nonneg _)
  · unfold kernelEvenQuadratic kernelTotalRadius
    nlinarith

theorem overlapOperatorNorm_one : overlapOperatorNorm (1 : SourceOverlapMatrix) = 1 := by
  unfold overlapOperatorNorm
  rw [map_one, norm_one]

theorem kernelAdjugateResidual_sub_one (K : SourceOverlapMatrix) :
    kernelAdjugateResidual K - 1 =
      (-overlapFrobeniusSq K) • (1 : SourceOverlapMatrix) + Kᴴ * K := by
  unfold kernelAdjugateResidual
  ext i j
  simp [sub_smul, Matrix.smul_apply, Complex.ofReal_sub, Complex.real_smul]
  ring

theorem kernelAdjugateResidual_sub_one_norm (K : SourceOverlapMatrix) :
    overlapOperatorNorm (kernelAdjugateResidual K - 1) ≤ 3 * overlapOperatorNorm K ^ 2 := by
  rw [kernelAdjugateResidual_sub_one]
  apply (overlapOperatorNorm_add _ _).trans
  rw [overlapOperatorNorm_real_smul, abs_neg, abs_of_nonneg (overlapFrobeniusSq_nonneg K),
    overlapOperatorNorm_one, mul_one]
  have hm := overlapOperatorNorm_mul Kᴴ K
  rw [overlapOperatorNorm_conjTranspose] at hm
  have hf := overlapFrobeniusSq_le K
  nlinarith

theorem kernelAdjugateResidual_norm {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 2) :
    overlapOperatorNorm (kernelAdjugateResidual K) ≤ 2 := by
  have he : kernelAdjugateResidual K = (kernelAdjugateResidual K - 1) + 1 := by abel
  rw [he]
  apply (overlapOperatorNorm_add _ _).trans
  rw [overlapOperatorNorm_one]
  have h := kernelAdjugateResidual_sub_one_norm K
  have hn := overlapOperatorNorm_nonneg K
  nlinarith

theorem kernelOddNumerator_difference (K : SourceOverlapMatrix)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    |2 * (coneInner p.1 (K *ᵥ (kernelAdjugateResidual K *ᵥ p.2))).re -
        2 * kernelCross K p| ≤ 3 * overlapOperatorNorm K ^ 3 * kernelTotalRadius p := by
  have he : 2 * (coneInner p.1 (K *ᵥ (kernelAdjugateResidual K *ᵥ p.2))).re -
      2 * kernelCross K p = 2 * kernelCross (K * (kernelAdjugateResidual K - 1)) p := by
    simp only [kernelCross, Matrix.mul_one, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, coneInner, Pi.sub_apply, mul_sub, Complex.sub_re, Complex.add_re]
    ring
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply (kernelCross_abs_le _ p).trans
  have hn := overlapOperatorNorm_mul K (kernelAdjugateResidual K - 1)
  have h := mul_le_mul_of_nonneg_left (kernelAdjugateResidual_sub_one_norm K) (overlapOperatorNorm_nonneg K)
  have hm := mul_le_mul_of_nonneg_right (hn.trans h) (kernelTotalRadius_nonneg p)
  nlinarith

theorem kernelSmall_determinant {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 2) :
    1 / 2 ≤ overlapDeterminant K ∧ overlapDeterminant K ≤ 1 ∧
      Complex.normSq K.det ≤ overlapOperatorNorm K ^ 4 := by
  have hρ := overlapOperatorNorm_nonneg K
  have hF := overlapFrobeniusSq_nonneg K
  have hF' := overlapFrobeniusSq_le K
  have hG := Complex.normSq_nonneg K.det
  have hG' := overlap_det_normSq_le K
  have hFhalf : overlapFrobeniusSq K ≤ 1 / 2 := by nlinarith
  have hFsq : overlapFrobeniusSq K ^ 2 ≤ 4 * overlapOperatorNorm K ^ 4 := by
    nlinarith [sq_nonneg (2 * overlapOperatorNorm K ^ 2 - overlapFrobeniusSq K),
      mul_nonneg (sub_nonneg.mpr hF') hF]
  rw [overlapDeterminant_identity]
  constructor
  · linarith
  constructor
  · nlinarith [mul_nonneg hF (sub_nonneg.mpr hFhalf)]
  · nlinarith

theorem kernelSmall_inverse_bounds {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 2) :
    0 ≤ (overlapDeterminant K)⁻¹ ∧ (overlapDeterminant K)⁻¹ ≤ 2 ∧
      |(overlapDeterminant K)⁻¹ - 1| ≤ 4 * overlapOperatorNorm K ^ 2 ∧
      |(overlapDeterminant K)⁻¹ - 1 - overlapFrobeniusSq K| ≤ 16 * overlapOperatorNorm K ^ 4 := by
  obtain ⟨hΔ, hΔ', hG⟩ := kernelSmall_determinant hK
  have hΔpos : 0 < overlapDeterminant K := by linarith
  have hD : (overlapDeterminant K)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hΔpos).mpr (by linarith)
  have hD1 : 1 ≤ (overlapDeterminant K)⁻¹ := (one_le_inv₀ hΔpos).mpr hΔ'
  have hF := overlapFrobeniusSq_nonneg K
  have hF' := overlapFrobeniusSq_le K
  have hFn : overlapFrobeniusSq K ≤ 1 / 2 := by
    have hρ := overlapOperatorNorm_nonneg K
    nlinarith
  have hi : (overlapDeterminant K)⁻¹ - 1 =
      (overlapFrobeniusSq K - Complex.normSq K.det) * (overlapDeterminant K)⁻¹ := by
    field_simp [hΔpos.ne']
    rw [overlapDeterminant_identity]
    ring
  have hdiff : |(overlapDeterminant K)⁻¹ - 1| ≤ 4 * overlapOperatorNorm K ^ 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ (overlapDeterminant K)⁻¹ - 1), hi]
    calc
      _ ≤ overlapFrobeniusSq K * (overlapDeterminant K)⁻¹ :=
        mul_le_mul_of_nonneg_right (sub_le_self _ (Complex.normSq_nonneg _)) (inv_nonneg.mpr hΔpos.le)
      _ ≤ overlapFrobeniusSq K * 2 := mul_le_mul_of_nonneg_left hD hF
      _ ≤ _ := by linarith
  refine ⟨inv_nonneg.mpr hΔpos.le, hD, hdiff, ?_⟩
  have he : (overlapDeterminant K)⁻¹ - 1 - overlapFrobeniusSq K =
      (overlapFrobeniusSq K ^ 2 - Complex.normSq K.det * (1 + overlapFrobeniusSq K)) *
        (overlapDeterminant K)⁻¹ := by
    field_simp [hΔpos.ne']
    rw [overlapDeterminant_identity]
    ring
  rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr hΔpos.le)]
  have hb : |overlapFrobeniusSq K ^ 2 - Complex.normSq K.det * (1 + overlapFrobeniusSq K)| ≤
      overlapFrobeniusSq K ^ 2 + Complex.normSq K.det * (1 + overlapFrobeniusSq K) := by
    calc
      _ ≤ |overlapFrobeniusSq K ^ 2| + |Complex.normSq K.det * (1 + overlapFrobeniusSq K)| :=
        abs_sub _ _
      _ = _ := by
        rw [abs_of_nonneg (sq_nonneg (overlapFrobeniusSq K)),
          abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg K.det) (by linarith))]
  apply (mul_le_mul hb hD (inv_nonneg.mpr hΔpos.le) (add_nonneg (sq_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (by linarith)))).trans
  have hFsq : overlapFrobeniusSq K ^ 2 ≤ 4 * overlapOperatorNorm K ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hF') hF,
      sq_nonneg (2 * overlapOperatorNorm K ^ 2 - overlapFrobeniusSq K)]
  have hg := mul_le_mul_of_nonneg_left (show 1 + overlapFrobeniusSq K ≤ 2 by linarith)
    (Complex.normSq_nonneg K.det)
  nlinarith

end KernelLocalEstimates

section KernelExponentBounds

open Complex Real Matrix

theorem kernelEvenExponent_bounds {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 2)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    |kernelEvenExponent K p| ≤ 4 * overlapOperatorNorm K ^ 2 * kernelTotalRadius p ∧
    |kernelEvenExponent K p - kernelEvenQuadratic K p| ≤
      6 * overlapOperatorNorm K ^ 4 * kernelTotalRadius p := by
  obtain ⟨hD0, hD, hDdiff, _⟩ := kernelSmall_inverse_bounds hK
  obtain ⟨_, _, hG⟩ := kernelSmall_determinant hK
  obtain ⟨hE0, hE⟩ := kernelEvenQuadratic_bounds K p
  have hT := kernelTotalRadius_nonneg p
  have hρ := overlapOperatorNorm_nonneg K
  have hG0 := Complex.normSq_nonneg K.det
  have hρ2 : overlapOperatorNorm K ^ 2 ≤ 1 := by nlinarith
  have hρ4 : overlapOperatorNorm K ^ 4 ≤ overlapOperatorNorm K ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (overlapOperatorNorm K)) (sub_nonneg.mpr hρ2)]
  have he : kernelEvenExponent K p =
      (overlapDeterminant K)⁻¹ *
        (kernelEvenQuadratic K p - Complex.normSq K.det * kernelTotalRadius p) := by
    unfold kernelEvenExponent
    ring
  have habs : |kernelEvenQuadratic K p - Complex.normSq K.det * kernelTotalRadius p| ≤
      kernelEvenQuadratic K p + Complex.normSq K.det * kernelTotalRadius p := by
    simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg hE0,
      abs_of_nonneg (mul_nonneg hG0 hT)] using
      abs_add_le (kernelEvenQuadratic K p) (-(Complex.normSq K.det * kernelTotalRadius p))
  constructor
  · rw [he, abs_mul, abs_of_nonneg hD0]
    calc
      _ ≤ 2 * (kernelEvenQuadratic K p + Complex.normSq K.det * kernelTotalRadius p) :=
        mul_le_mul hD habs (abs_nonneg _) (by positivity)
      _ ≤ 2 * (overlapOperatorNorm K ^ 2 * kernelTotalRadius p +
          overlapOperatorNorm K ^ 2 * kernelTotalRadius p) := by
        gcongr
        exact hG.trans hρ4
      _ = _ := by ring
  · have hd : kernelEvenExponent K p - kernelEvenQuadratic K p =
        ((overlapDeterminant K)⁻¹ - 1) * kernelEvenQuadratic K p -
          (overlapDeterminant K)⁻¹ * Complex.normSq K.det * kernelTotalRadius p := by
      rw [he]
      ring
    rw [hd]
    calc
      _ ≤ |((overlapDeterminant K)⁻¹ - 1) * kernelEvenQuadratic K p| +
          |(overlapDeterminant K)⁻¹ * Complex.normSq K.det * kernelTotalRadius p| :=
        abs_sub _ _
      _ = |(overlapDeterminant K)⁻¹ - 1| * kernelEvenQuadratic K p +
          (overlapDeterminant K)⁻¹ * Complex.normSq K.det * kernelTotalRadius p := by
        rw [abs_mul, abs_of_nonneg hE0, abs_of_nonneg (mul_nonneg (mul_nonneg hD0 hG0) hT)]
      _ ≤ (4 * overlapOperatorNorm K ^ 2) *
          (overlapOperatorNorm K ^ 2 * kernelTotalRadius p) +
          2 * overlapOperatorNorm K ^ 4 * kernelTotalRadius p := by
        gcongr
      _ = _ := by ring

theorem kernelOddExponent_bounds {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 2)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    |kernelOddExponent K p| ≤ 4 * overlapOperatorNorm K * kernelTotalRadius p ∧
    |kernelOddExponent K p - 2 * kernelCross K p| ≤
      10 * overlapOperatorNorm K ^ 3 * kernelTotalRadius p := by
  obtain ⟨hD0, hD, hDdiff, _⟩ := kernelSmall_inverse_bounds hK
  have hρ := overlapOperatorNorm_nonneg K
  have hT := kernelTotalRadius_nonneg p
  have hL := kernelCross_abs_le K p
  have hN := kernelCross_abs_le (K * kernelAdjugateResidual K) p
  have hNC := (overlapOperatorNorm_mul K (kernelAdjugateResidual K)).trans
    (mul_le_mul_of_nonneg_left (kernelAdjugateResidual_norm hK) hρ)
  have hN' : |2 * kernelCross (K * kernelAdjugateResidual K) p| ≤
      2 * overlapOperatorNorm K * kernelTotalRadius p := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact hN.trans ((mul_le_mul_of_nonneg_right hNC hT).trans_eq (by ring))
  have he : kernelOddExponent K p =
      (overlapDeterminant K)⁻¹ * (2 * kernelCross (K * kernelAdjugateResidual K) p) := by
    simp only [kernelOddExponent, kernelCross, ← Matrix.mulVec_mulVec]
    ring
  have hNL : |2 * kernelCross (K * kernelAdjugateResidual K) p - 2 * kernelCross K p| ≤
      3 * overlapOperatorNorm K ^ 3 * kernelTotalRadius p := by
    simpa only [kernelCross, ← Matrix.mulVec_mulVec] using kernelOddNumerator_difference K p
  constructor
  · rw [he, abs_mul, abs_of_nonneg hD0]
    calc
      _ ≤ 2 * (2 * overlapOperatorNorm K * kernelTotalRadius p) :=
        mul_le_mul hD hN' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · have hd : kernelOddExponent K p - 2 * kernelCross K p =
        ((overlapDeterminant K)⁻¹ - 1) * (2 * kernelCross K p) +
          (overlapDeterminant K)⁻¹ *
            (2 * kernelCross (K * kernelAdjugateResidual K) p - 2 * kernelCross K p) := by
      rw [he]
      ring
    rw [hd]
    calc
      _ ≤ |((overlapDeterminant K)⁻¹ - 1) * (2 * kernelCross K p)| +
          |(overlapDeterminant K)⁻¹ *
            (2 * kernelCross (K * kernelAdjugateResidual K) p - 2 * kernelCross K p)| :=
        abs_add_le _ _
      _ = |(overlapDeterminant K)⁻¹ - 1| * (2 * |kernelCross K p|) +
          (overlapDeterminant K)⁻¹ *
            |2 * kernelCross (K * kernelAdjugateResidual K) p - 2 * kernelCross K p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_mul, abs_of_nonneg hD0]
      _ ≤ (4 * overlapOperatorNorm K ^ 2) *
          (overlapOperatorNorm K * kernelTotalRadius p) +
          2 * (3 * overlapOperatorNorm K ^ 3 * kernelTotalRadius p) := by
        gcongr
      _ = _ := by ring

end KernelExponentBounds

section KernelExponentialMoments

open MeasureTheory Complex Real
open scoped ENNReal

theorem integral_sourceDensityLaw (a : SourceDensityKind) (M : ℕ) (f : Signal 2 → ℝ) :
    (∫ z, f z ∂sourceDensityLaw a M) =
      ∫ z, sourceDensity a M z * f z ∂standardComplexGaussianTail 2 := by
  rw [sourceDensityLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_sourceDensity a M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceDensity_nonneg a M _), smul_eq_mul]

theorem integrable_sourceDensityLaw_iff (a : SourceDensityKind) (M : ℕ) (f : Signal 2 → ℝ) :
    Integrable f (sourceDensityLaw a M) ↔
      Integrable (fun z ↦ sourceDensity a M z * f z) (standardComplexGaussianTail 2) := by
  rw [sourceDensityLaw, integrable_withDensity_iff_integrable_smul'
    (measurable_sourceDensity a M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceDensity_nonneg a M _), smul_eq_mul]

theorem sourceDensityLaw_integrable_exp_quarter {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind) :
    Integrable (fun z ↦ Real.exp (sourceRadiusSq z / 4)) (sourceDensityLaw a M) :=
  (integrable_sourceDensityLaw_iff a M _).mpr (integrable_sourceDensity_exp_quarter hM a)

theorem sourceDensityLaw_exp_quarter {M : ℕ} (hM : 2 ≤ M) (a : SourceDensityKind) :
    (∫ z, Real.exp (sourceRadiusSq z / 4) ∂sourceDensityLaw a M) ≤ 4 * Real.exp 1 := by
  rw [integral_sourceDensityLaw]
  exact sourceDensity_exp_quarter_bound hM a

theorem kernel_polynomial_exp_bound (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (1 + T) ^ k * Real.exp (T / 8) ≤
      ((k.factorial : ℝ) * 8 ^ k * Real.exp (1 / 8)) * Real.exp (T / 4) := by
  have h := Real.pow_div_factorial_le_exp ((1 + T) / 8) (by positivity) k
  rw [div_pow, div_div] at h
  have hd : (0 : ℝ) < 8 ^ k * k.factorial := by positivity
  have hh := (div_le_iff₀ hd).mp h
  have hp := mul_le_mul_of_nonneg_right hh (Real.exp_pos (T / 8)).le
  have he : Real.exp ((1 + T) / 8) * Real.exp (T / 8) =
      Real.exp (1 / 8) * Real.exp (T / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (Real.exp ((1 + T) / 8) * (8 ^ k * k.factorial)) * Real.exp (T / 8) := hp
    _ = (k.factorial : ℝ) * 8 ^ k * (Real.exp ((1 + T) / 8) * Real.exp (T / 8)) := by ring
    _ = _ := by rw [he]; ring

theorem integrable_sourceDensityPair_exp {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    Integrable (fun p : Signal 2 × Signal 2 ↦
      Real.exp ((sourceRadiusSq p.1 + sourceRadiusSq p.2) / 4))
      ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) := by
  have he (p : Signal 2 × Signal 2) :
      Real.exp ((sourceRadiusSq p.1 + sourceRadiusSq p.2) / 4) =
        Real.exp (sourceRadiusSq p.1 / 4) * Real.exp (sourceRadiusSq p.2 / 4) := by
    rw [add_div, Real.exp_add]
  simp_rw [he]
  exact (sourceDensityLaw_integrable_exp_quarter hM a).mul_prod
    (sourceDensityLaw_integrable_exp_quarter hM b)

theorem sourceDensityPair_exp_bound {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    (∫ p : Signal 2 × Signal 2, Real.exp ((sourceRadiusSq p.1 + sourceRadiusSq p.2) / 4)
      ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M)) ≤ (4 * Real.exp 1) ^ 2 := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  let : IsProbabilityMeasure (sourceDensityLaw b M) := isProbabilityMeasure_sourceDensityLaw hM b
  simp_rw [add_div, Real.exp_add]
  rw [integral_prod_mul (fun z : Signal 2 ↦ Real.exp (sourceRadiusSq z / 4))
    (fun z : Signal 2 ↦ Real.exp (sourceRadiusSq z / 4))]
  exact (mul_le_mul (sourceDensityLaw_exp_quarter hM a) (sourceDensityLaw_exp_quarter hM b)
    (integral_nonneg fun _ ↦ (Real.exp_pos _).le) (by positivity)).trans_eq (by ring)

def kernelMomentConstant (k : ℕ) : ℝ :=
  ((k.factorial : ℝ) * 8 ^ k * Real.exp (1 / 8)) * (4 * Real.exp 1) ^ 2

theorem integrable_sourceDensityPair_polynomial_exp {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (k : ℕ) :
    Integrable (fun p : Signal 2 × Signal 2 ↦
      (1 + (sourceRadiusSq p.1 + sourceRadiusSq p.2)) ^ k *
        Real.exp ((sourceRadiusSq p.1 + sourceRadiusSq p.2) / 8))
      ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) := by
  apply ((integrable_sourceDensityPair_exp hM a b).const_mul
    ((k.factorial : ℝ) * 8 ^ k * Real.exp (1 / 8))).mono'
    (by apply Continuous.aestronglyMeasurable; unfold sourceRadiusSq; fun_prop)
  filter_upwards with p
  have hT := add_nonneg (sourceRadiusSq_nonneg p.1) (sourceRadiusSq_nonneg p.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact kernel_polynomial_exp_bound k
    (add_nonneg (sourceRadiusSq_nonneg p.1) (sourceRadiusSq_nonneg p.2))

theorem sourceDensityPair_polynomial_exp_bound {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (k : ℕ) :
    (∫ p : Signal 2 × Signal 2, (1 + (sourceRadiusSq p.1 + sourceRadiusSq p.2)) ^ k *
      Real.exp ((sourceRadiusSq p.1 + sourceRadiusSq p.2) / 8)
      ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M)) ≤ kernelMomentConstant k := by
  calc
    _ ≤ ∫ p : Signal 2 × Signal 2, ((k.factorial : ℝ) * 8 ^ k * Real.exp (1 / 8)) *
        Real.exp ((sourceRadiusSq p.1 + sourceRadiusSq p.2) / 4)
        ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M) :=
      integral_mono (integrable_sourceDensityPair_polynomial_exp hM a b k)
        ((integrable_sourceDensityPair_exp hM a b).const_mul _)
        (fun p ↦ kernel_polynomial_exp_bound k
          (add_nonneg (sourceRadiusSq_nonneg p.1) (sourceRadiusSq_nonneg p.2)))
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (sourceDensityPair_exp_bound hM a b) (by positivity)

end KernelExponentialMoments

section KernelLocalRemainder

open MeasureTheory Complex Real Matrix

theorem kernelEvenExponent_neg (K : SourceOverlapMatrix) (z w : Signal 2) :
    kernelEvenExponent K (-z, w) = kernelEvenExponent K (z, w) := by
  simp [kernelEvenExponent, kernelEvenQuadratic, kernelTotalRadius, Matrix.mulVec_neg,
    sourceRadiusSq, Complex.normSq_neg]

theorem kernelOddExponent_neg (K : SourceOverlapMatrix) (z w : Signal 2) :
    kernelOddExponent K (-z, w) = -kernelOddExponent K (z, w) := by
  simp only [kernelOddExponent, coneInner, Pi.neg_apply,
    star_neg, neg_mul, Complex.add_re, Complex.neg_re]
  ring

theorem overlapGaussianRatio_even {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (z w : Signal 2) :
    (overlapGaussianRatio K z w + overlapGaussianRatio K (-z) w) / 2 =
      (overlapDeterminant K)⁻¹ *
        kernelEvenExp (kernelEvenExponent K (z, w)) (kernelOddExponent K (z, w)) := by
  rw [overlapGaussianRatio_exponents hK, overlapGaussianRatio_exponents hK,
    kernelEvenExponent_neg, kernelOddExponent_neg]
  unfold kernelEvenExp
  simp only [sub_eq_add_neg]
  ring

theorem overlapGaussianRatio_even_remainder {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 128) (z w : Signal 2) :
    |(overlapGaussianRatio K z w + overlapGaussianRatio K (-z) w) / 2 -
        (1 + kernelQuadratic K (z, w))| ≤
      11000 * overlapFrobeniusSq K ^ 2 * (1 + kernelTotalRadius (z, w)) ^ 4 *
        Real.exp (kernelTotalRadius (z, w) / 8) := by
  have hhalf : overlapOperatorNorm K ≤ 1 / 2 := by linarith
  obtain ⟨hD0, hD, hDdiff, hD2⟩ := kernelSmall_inverse_bounds hhalf
  obtain ⟨hA, hAE⟩ := kernelEvenExponent_bounds hhalf (z, w)
  obtain ⟨hB, hBL⟩ := kernelOddExponent_bounds hhalf (z, w)
  have hL : |2 * kernelCross K (z, w)| ≤
      overlapOperatorNorm K * kernelTotalRadius (z, w) := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      using kernelCross_abs_le K (z, w)
  have h := kernel_scalar_remainder (overlapOperatorNorm_nonneg K) hK
    (kernelTotalRadius_nonneg (z, w)) hD0 hD hDdiff hD2 hA hAE hB hBL hL
  have he : 1 + overlapFrobeniusSq K - kernelEvenQuadratic K (z, w) +
      (2 * kernelCross K (z, w))^2 / 2 = 1 + kernelQuadratic K (z, w) := by
    unfold kernelQuadratic kernelEvenQuadratic
    ring
  rw [he, ← overlapGaussianRatio_even (by linarith : overlapOperatorNorm K < 1)] at h
  apply h.trans
  have hF := overlapOperatorNorm_sq_le_frobenius K
  have hF2 : overlapOperatorNorm K ^ 4 ≤ overlapFrobeniusSq K ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hF) (overlapFrobeniusSq_nonneg K),
      sq_nonneg (overlapFrobeniusSq K - overlapOperatorNorm K ^ 2)]
  gcongr

theorem overlapGaussianRatio_nonneg {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (z w : Signal 2) :
    0 ≤ overlapGaussianRatio K z w :=
  mul_nonneg (inv_nonneg.mpr (overlapDeterminant_pos hK).le) (Real.exp_pos _).le

theorem overlapGaussianRatio_local_bound {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 128) (z w : Signal 2) :
    overlapGaussianRatio K z w ≤ 2 * Real.exp (kernelTotalRadius (z, w) / 4) := by
  have hhalf : overlapOperatorNorm K ≤ 1 / 2 := by linarith
  obtain ⟨hD0, hD, _, _⟩ := kernelSmall_inverse_bounds hhalf
  have hA := (kernelEvenExponent_bounds hhalf (z, w)).1
  have hB := (kernelOddExponent_bounds hhalf (z, w)).1
  have hρ := overlapOperatorNorm_nonneg K
  have hT := kernelTotalRadius_nonneg (z, w)
  have hρ2 : overlapOperatorNorm K ^ 2 ≤ overlapOperatorNorm K := by nlinarith
  have hS : |kernelEvenExponent K (z, w)| + |kernelOddExponent K (z, w)| ≤
      kernelTotalRadius (z, w) / 4 := by
    have := mul_le_mul_of_nonneg_right hρ2 hT
    have := mul_le_mul_of_nonneg_right hK hT
    linarith
  rw [overlapGaussianRatio_exponents (by linarith : overlapOperatorNorm K < 1)]
  apply mul_le_mul hD ?_ (Real.exp_pos _).le (by norm_num)
  apply Real.exp_le_exp.mpr
  linarith [neg_le_abs (kernelEvenExponent K (z, w)),
    le_abs_self (kernelOddExponent K (z, w))]

def sourceDensityCorrelation (a b : SourceDensityKind) (M : ℕ) (K : SourceOverlapMatrix) : ℝ :=
  ∫ p : Signal 2 × Signal 2, overlapGaussianRatio K p.1 p.2
    ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M)

theorem integrable_sourceDensityCorrelation_local {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 128) :
    Integrable (fun p : Signal 2 × Signal 2 ↦ overlapGaussianRatio K p.1 p.2)
      ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) := by
  apply ((integrable_sourceDensityPair_exp hM a b).const_mul 2).mono'
    (continuous_overlapGaussianRatio K).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (overlapGaussianRatio_nonneg (by linarith) _ _)]
  exact overlapGaussianRatio_local_bound hK p.1 p.2

end KernelLocalRemainder

section KernelLocalExpansion

open MeasureTheory Complex Real

theorem sourceDensityLaw_map_neg (a : SourceDensityKind) (M : ℕ) :
    (sourceDensityLaw a M).map (fun z ↦ -z) = sourceDensityLaw a M := by
  convert sourceDensityLaw_map_coordinatePhase a M (fun _ ↦ -1) (by simp) using 1
  congr 1
  funext z i
  simp [coordinatePhase]

theorem sourceDensityPair_map_neg_fst {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    ((sourceDensityLaw a M).prod (sourceDensityLaw b M)).map
      (Prod.map (fun z ↦ -z) id) = (sourceDensityLaw a M).prod (sourceDensityLaw b M) := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  let : IsProbabilityMeasure (sourceDensityLaw b M) := isProbabilityMeasure_sourceDensityLaw hM b
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    sourceDensityLaw_map_neg, Measure.map_id]

theorem integral_sourceDensityPair_neg_fst {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    (f : Signal 2 × Signal 2 → ℝ) (hf : Continuous f) :
    (∫ p, f (-p.1, p.2) ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M)) =
      ∫ p, f p ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M) := by
  have h := integral_map (φ := Prod.map (fun z : Signal 2 ↦ -z) (id : Signal 2 → Signal 2))
    (μ := (sourceDensityLaw a M).prod (sourceDensityLaw b M))
    (by apply Measurable.aemeasurable; fun_prop)
    (f := f) hf.aestronglyMeasurable
  rw [sourceDensityPair_map_neg_fst hM a b] at h
  exact h.symm

theorem sourceDensityCorrelation_eq_even {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 128) :
    sourceDensityCorrelation a b M K =
      ∫ p : Signal 2 × Signal 2,
        (overlapGaussianRatio K p.1 p.2 + overlapGaussianRatio K (-p.1) p.2) / 2
        ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M) := by
  have hR := integrable_sourceDensityCorrelation_local hM a b hK
  have hneg : Integrable (fun p : Signal 2 × Signal 2 ↦ overlapGaussianRatio K (-p.1) p.2)
      ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) := by
    have hm : Measurable (Prod.map (fun z : Signal 2 ↦ -z) (id : Signal 2 → Signal 2)) := by fun_prop
    have hc : AEStronglyMeasurable (fun p : Signal 2 × Signal 2 ↦ overlapGaussianRatio K p.1 p.2)
        (((sourceDensityLaw a M).prod (sourceDensityLaw b M)).map
          (Prod.map (fun z : Signal 2 ↦ -z) (id : Signal 2 → Signal 2))) :=
      (continuous_overlapGaussianRatio K).aestronglyMeasurable
    have hi := (integrable_map_measure hc hm.aemeasurable)
    rw [sourceDensityPair_map_neg_fst hM a b] at hi
    exact hi.mp hR
  rw [integral_div, integral_add hR hneg,
    integral_sourceDensityPair_neg_fst hM a b _ (continuous_overlapGaussianRatio K)]
  unfold sourceDensityCorrelation
  ring

/-- The radius and remainder constant do not depend on the ambient dimension. -/
theorem sourceDensityCorrelation_local_expansion {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ 1 / 128) :
    |sourceDensityCorrelation a b M K -
        (1 + (1 - sourceVariance M)^2 * overlapFrobeniusSq K)| ≤
      (11000 * kernelMomentConstant 4) * overlapFrobeniusSq K ^ 2 := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  let : IsProbabilityMeasure (sourceDensityLaw b M) := isProbabilityMeasure_sourceDensityLaw hM b
  let μ := (sourceDensityLaw a M).prod (sourceDensityLaw b M)
  let f := fun p : Signal 2 × Signal 2 ↦
    (overlapGaussianRatio K p.1 p.2 + overlapGaussianRatio K (-p.1) p.2) / 2
  let g := fun p : Signal 2 × Signal 2 ↦ 1 + kernelQuadratic K p
  let bound := fun p : Signal 2 × Signal 2 ↦
    (11000 * overlapFrobeniusSq K ^ 2) *
      ((1 + kernelTotalRadius p)^4 * Real.exp (kernelTotalRadius p / 8))
  have hbound : Integrable bound μ :=
    (integrable_sourceDensityPair_polynomial_exp hM a b 4).const_mul _
  have hg : Integrable g μ := (integrable_const 1).add (integrable_kernelQuadratic hM a b K)
  have herr : Integrable (fun p ↦ f p - g p) μ := by
    apply hbound.mono'
    · apply Continuous.aestronglyMeasurable
      dsimp [f, g]
      unfold overlapGaussianRatio kernelQuadratic kernelCross sourceRadiusSq coneInner
      fun_prop
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      exact (overlapGaussianRatio_even_remainder hK p.1 p.2).trans_eq (by dsimp [bound]; ring)
  have hf : Integrable f μ := by
    have hh := herr.add hg
    exact hh.congr (Filter.Eventually.of_forall fun p ↦ sub_add_cancel (f p) (g p))
  have he : sourceDensityCorrelation a b M K -
      (1 + (1 - sourceVariance M)^2 * overlapFrobeniusSq K) =
      ∫ p, (f p - g p) ∂μ := by
    rw [integral_sub hf hg]
    exact congrArg₂ (· - ·) (sourceDensityCorrelation_eq_even hM a b hK)
      (integral_kernel_second_order hM a b K).symm
  rw [he, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ p, bound p ∂μ := norm_integral_le_of_norm_le hbound (by
      filter_upwards with p
      rw [Real.norm_eq_abs]
      exact (overlapGaussianRatio_even_remainder hK p.1 p.2).trans_eq (by dsimp [bound]; ring))
    _ ≤ _ := by
      dsimp [bound, μ, kernelTotalRadius]
      rw [integral_const_mul]
      calc
        _ ≤ (11000 * overlapFrobeniusSq K ^ 2) * kernelMomentConstant 4 :=
          mul_le_mul_of_nonneg_left (sourceDensityPair_polynomial_exp_bound hM a b 4) (by positivity)
        _ = _ := by ring

end KernelLocalExpansion

end NLA.FR05
