import NLA.FR05.Gaussian.GaussianSquaredRadius
import NLA.FR05.Densities.SourceSymmetry

/-!
# Planted radial laws and moments

The sections develop `SourcePlantedRadial`, `SourcePlantedMoments`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section SourcePlantedRadial

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

def magnitudeCone (δ ε : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if δ ≤ p.1 + p.2 ∧ |(p.1 - p.2) / (p.1 + p.2)| ≤ ε then f (p.1 + p.2) else 0

theorem measurable_magnitudeCone (δ ε : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (magnitudeCone δ ε f) := by
  unfold magnitudeCone
  apply Measurable.ite
  · have hsum : Measurable (fun p : ℝ × ℝ ↦ p.1 + p.2) := by fun_prop
    have habs : Measurable (fun p : ℝ × ℝ ↦ |(p.1 - p.2) / (p.1 + p.2)|) := by fun_prop
    exact (measurableSet_le measurable_const hsum).inter
      (measurableSet_le habs measurable_const)
  · fun_prop
  · fun_prop

theorem gammaPDFReal_one_one (s : ℝ) :
    gammaPDFReal 1 1 s = if 0 ≤ s then Real.exp (-s) else 0 := by
  simp [gammaPDFReal]

theorem exp_pair_withDensity :
    (expMeasure 1).prod (expMeasure 1) =
      (volume : Measure (ℝ × ℝ)).withDensity
        (fun p ↦ ENNReal.ofReal (gammaPDFReal 1 1 p.1 * gammaPDFReal 1 1 p.2)) := by
  change (volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal 1 1 x))).prod
      (volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal 1 1 x))) = _
  rw [prod_withDensity (measurable_gammaPDFReal 1 1).ennreal_ofReal
    (measurable_gammaPDFReal 1 1).ennreal_ofReal, Measure.volume_eq_prod]
  congr 1
  funext p
  rw [ENNReal.ofReal_mul (gammaPDFReal_nonneg zero_lt_one zero_lt_one _)]

theorem integrable_exp_pair_iff (f : ℝ × ℝ → ℝ) :
    Integrable f ((expMeasure 1).prod (expMeasure 1)) ↔
      Integrable (fun p ↦ gammaPDFReal 1 1 p.1 * gammaPDFReal 1 1 p.2 * f p) := by
  rw [exp_pair_withDensity, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg
    (gammaPDFReal_nonneg zero_lt_one zero_lt_one _)
    (gammaPDFReal_nonneg zero_lt_one zero_lt_one _)), smul_eq_mul]

theorem integral_exp_pair (f : ℝ × ℝ → ℝ) :
    (∫ p, f p ∂(expMeasure 1).prod (expMeasure 1)) =
      ∫ p, gammaPDFReal 1 1 p.1 * gammaPDFReal 1 1 p.2 * f p := by
  rw [exp_pair_withDensity, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg
    (gammaPDFReal_nonneg zero_lt_one zero_lt_one _)
    (gammaPDFReal_nonneg zero_lt_one zero_lt_one _)), smul_eq_mul]

theorem cone_interval_iff {s ε u : ℝ} (hs : 0 < s) :
    |(u - (s - u)) / s| ≤ ε ↔
      s * (1 - ε) / 2 ≤ u ∧ u ≤ s * (1 + ε) / 2 := by
  rw [abs_le, le_div_iff₀ hs, div_le_iff₀ hs]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem cone_interval_nonneg {s ε u : ℝ} (hs : 0 < s) (hε : ε ≤ 1)
    (hu : s * (1 - ε) / 2 ≤ u ∧ u ≤ s * (1 + ε) / 2) : 0 ≤ u ∧ 0 ≤ s - u := by
  have hh := mul_nonneg hs.le (sub_nonneg.mpr hε)
  constructor <;> nlinarith [hu.1, hu.2]

theorem magnitudeCone_shear {δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ 1)
    (f : ℝ → ℝ) (s u : ℝ) :
    gammaPDFReal 1 1 u * gammaPDFReal 1 1 (s - u) *
        magnitudeCone δ ε f (u, s - u) =
      if δ ≤ s then
        (Icc (s * (1 - ε) / 2) (s * (1 + ε) / 2)).indicator
          (fun _ ↦ Real.exp (-s) * f s) u
      else 0 := by
  have hadd : u + (s - u) = s := by ring
  by_cases hs : δ ≤ s
  · have hs' := hδ.trans_le hs
    by_cases hc : |(u - (s - u)) / s| ≤ ε
    · have hu := (cone_interval_iff hs').mp hc
      have hn := cone_interval_nonneg hs' hε hu
      simp only [magnitudeCone, hadd, hs, hc, and_self, ite_true,
        gammaPDFReal_one_one, hn.1, hn.2, indicator_of_mem (show u ∈ Icc (s * (1 - ε) / 2) (s * (1 + ε) / 2) from hu)]
      rw [← Real.exp_add]
      congr 2
      ring
    · have hu : u ∉ Icc (s * (1 - ε) / 2) (s * (1 + ε) / 2) :=
        fun hu ↦ hc ((cone_interval_iff hs').mpr hu)
      simp [magnitudeCone, hadd, hs, hc, indicator_of_notMem hu]
  · simp [magnitudeCone, hadd, hs]

theorem integral_magnitudeCone {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {f : ℝ → ℝ}
    (hi : Integrable (magnitudeCone δ ε f) ((expMeasure 1).prod (expMeasure 1))) :
    (∫ p, magnitudeCone δ ε f p ∂(expMeasure 1).prod (expMeasure 1)) =
      ∫ s in Ici δ, ε * s * Real.exp (-s) * f s := by
  let F : ℝ × ℝ → ℝ :=
    fun p ↦ gammaPDFReal 1 1 p.1 * gammaPDFReal 1 1 p.2 * magnitudeCone δ ε f p
  have hF : Integrable F := (integrable_exp_pair_iff _).mp hi
  have hT : MeasurePreserving (fun p : ℝ × ℝ ↦ (p.2, p.1 - p.2)) volume volume := by
    simpa only [Measure.volume_eq_prod] using
      measurePreserving_prod_sub_swap (volume : Measure ℝ) (volume : Measure ℝ)
  have hFT := hT.integrable_comp_of_integrable hF
  have he := integral_map hT.measurable.aemeasurable
    (show AEStronglyMeasurable F (volume.map (fun p : ℝ × ℝ ↦ (p.2, p.1 - p.2))) from by
      rw [hT.map_eq]; exact hF.aestronglyMeasurable)
  rw [hT.map_eq] at he
  rw [integral_exp_pair]
  change (∫ p, F p) = _
  rw [he, Measure.volume_eq_prod]
  rw [integral_prod (fun p : ℝ × ℝ ↦ F (p.2, p.1 - p.2))
    (by simpa only [Function.comp_def, Measure.volume_eq_prod] using hFT)]
  have hinner (s : ℝ) :
      (∫ u, F (u, s - u)) = (Ici δ).indicator (fun s ↦ ε * s * Real.exp (-s) * f s) s := by
    simp only [F, magnitudeCone_shear hδ hε1]
    by_cases hs : δ ≤ s
    · simp only [hs, ite_true, indicator_of_mem (show s ∈ Ici δ from hs)]
      rw [integral_indicator measurableSet_Icc, integral_const,
        measureReal_restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_real_Icc_of_le]
      · simp only [smul_eq_mul]
        ring
      · have := mul_nonneg hε0 (hδ.trans_le hs).le
        nlinarith
    · simp [hs, Set.indicator]
  simp_rw [hinner]
  exact integral_indicator measurableSet_Ici

theorem sourceEpsilon_le_one {M : ℕ} (hM : 1 ≤ M) : sourceEpsilon M ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by exact_mod_cast hM)

theorem sourcePlantedDensity_mul_radial_eq_cone {M : ℕ} (hM : 1 ≤ M)
    (f : ℝ → ℝ) (z : Signal 2) :
    sourcePlantedDensity M z * f (sourceRadiusSq z) =
      magnitudeCone (sourceDelta M) (sourceEpsilon M)
        (fun s ↦ (sourceEta + (1 - sourceEta) / s) /
          (sourceEpsilon M * sourceRadialNormalizer M) * f s)
        (Complex.normSq (z 0), Complex.normSq (z 1)) := by
  by_cases hz : z = 0
  · subst z
    have hd := sourceDelta_pos M hM
    simp [sourcePlantedDensity, sourceRadiusSq, magnitudeCone, not_le.mpr hd]
  · unfold sourcePlantedDensity magnitudeCone sourceImbalance sourceRadiusSq
    simp only [hz, ite_false]
    split_ifs <;> simp

theorem integral_sourcePlantedDensity_radial {M : ℕ} (hM : 1 ≤ M)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hi : Integrable (fun z ↦ sourcePlantedDensity M z * f (sourceRadiusSq z))
      (standardComplexGaussianTail 2)) :
    (∫ z, sourcePlantedDensity M z * f (sourceRadiusSq z) ∂standardComplexGaussianTail 2) =
      ∫ s in Ici (sourceDelta M),
        Real.exp (-s) * ((1 - sourceEta) + sourceEta * s) / sourceRadialNormalizer M * f s := by
  let F := magnitudeCone (sourceDelta M) (sourceEpsilon M)
    (fun s ↦ (sourceEta + (1 - sourceEta) / s) /
      (sourceEpsilon M * sourceRadialNormalizer M) * f s)
  have hF : Measurable F := by
    apply measurable_magnitudeCone
    fun_prop
  have he (z : Signal 2) :
      sourcePlantedDensity M z * f (sourceRadiusSq z) =
        F (Complex.normSq (z 0), Complex.normSq (z 1)) :=
    sourcePlantedDensity_mul_radial_eq_cone hM f z
  have hmap := standardComplexGaussianTail_map_normSq_pair
  have hiF : Integrable F ((expMeasure 1).prod (expMeasure 1)) := by
    rw [← hmap]
    apply (integrable_map_measure hF.aestronglyMeasurable (by fun_prop)).mpr
    simpa only [Function.comp_def, ← he] using hi
  simp_rw [he]
  rw [← integral_map (by fun_prop) hF.aestronglyMeasurable, hmap]
  rw [integral_magnitudeCone (sourceDelta_pos M hM)
    (sourceEpsilon_pos M hM).le (sourceEpsilon_le_one hM) hiF]
  apply setIntegral_congr_fun measurableSet_Ici
  intro s hs
  have hs' := (sourceDelta_pos M hM).trans_le hs
  have hε := (sourceEpsilon_pos M hM).ne'
  have hc := (sourceRadialNormalizer_pos M).ne'
  field_simp
  ring

theorem integrable_sourcePlantedDensity_mul_exp {M : ℕ} (hM : 1 ≤ M)
    {t : ℝ} (ht : t < 1) :
    Integrable (fun z ↦ sourcePlantedDensity M z * Real.exp (t * sourceRadiusSq z))
      (standardComplexGaussianTail 2) := by
  have he : Integrable (fun z : Signal 2 ↦ Real.exp (t * sourceRadiusSq z))
      (standardComplexGaussianTail 2) := by
    simpa only [sourceRadiusSq_eq_signalEnergy] using
      integrable_exp_standardComplexGaussian_energy 2 ht
  apply (he.const_mul (Real.exp 1 * (M : ℝ) ^ 52)).mono'
  · exact ((measurable_sourcePlantedDensity M).mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_sourceRadiusSq))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (sourcePlantedDensity_nonneg M z) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (sourcePlantedDensity_le hM z) (Real.exp_pos _).le

theorem integrable_sourcePlantedDensity_mul_radius_pow {M : ℕ} (hM : 1 ≤ M) (k : ℕ) :
    Integrable (fun z ↦ sourcePlantedDensity M z * sourceRadiusSq z ^ k)
      (standardComplexGaussianTail 2) := by
  have he : Integrable (fun z : Signal 2 ↦ sourceRadiusSq z ^ k)
      (standardComplexGaussianTail 2) := by
    simpa [sourceRadiusSq_eq_signalEnergy] using
      integrable_energy_pow_mul_exp_standardComplexGaussian 2 k (t := 0) (by norm_num)
  apply (he.const_mul (Real.exp 1 * (M : ℝ) ^ 52)).mono'
  · exact ((measurable_sourcePlantedDensity M).mul
      (measurable_sourceRadiusSq.pow_const k)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (sourcePlantedDensity_nonneg M z) (pow_nonneg (sourceRadiusSq_nonneg z) k))]
      exact mul_le_mul_of_nonneg_right (sourcePlantedDensity_le hM z)
        (pow_nonneg (sourceRadiusSq_nonneg z) k)

end SourcePlantedRadial

section SourcePlantedMoments

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem integrable_sourcePlantedDensity {M : ℕ} (hM : 1 ≤ M) :
    Integrable (sourcePlantedDensity M) (standardComplexGaussianTail 2) := by
  simpa using integrable_sourcePlantedDensity_mul_radius_pow hM 0

theorem integral_sourcePlantedDensity {M : ℕ} (hM : 1 ≤ M) :
    (∫ z, sourcePlantedDensity M z ∂standardComplexGaussianTail 2) = 1 := by
  have hrad := integral_sourcePlantedDensity_radial hM (f := fun _ ↦ 1) measurable_const
    (by simpa using integrable_sourcePlantedDensity hM)
  simp only [mul_one] at hrad
  rw [hrad, integral_div]
  have ht := (exponential_quadratic_tail
    (δ := sourceDelta M) (r := 1) (a := 1 - sourceEta) (b := sourceEta) (c := 0)
    (sourceDelta_pos M hM).le (by norm_num) (sub_nonneg.mpr sourceEta_lt_one.le)
    sourceEta_pos.le (by norm_num)).2
  norm_num at ht
  rw [ht, div_eq_one_iff_eq (sourceRadialNormalizer_pos M).ne']
  unfold sourceRadialNormalizer
  ring

theorem integral_sourcePlantedDensity_mul_radius {M : ℕ} (hM : 1 ≤ M) :
    (∫ z, sourcePlantedDensity M z * sourceRadiusSq z ∂standardComplexGaussianTail 2) =
      2 * sourceVariance M := by
  have hi : Integrable (fun z ↦ sourcePlantedDensity M z * sourceRadiusSq z)
      (standardComplexGaussianTail 2) := by
    simpa using integrable_sourcePlantedDensity_mul_radius_pow hM 1
  rw [integral_sourcePlantedDensity_radial hM (f := fun s ↦ s) measurable_id hi]
  have he (s : ℝ) :
      Real.exp (-s) * ((1 - sourceEta) + sourceEta * s) / sourceRadialNormalizer M * s =
        (Real.exp (-s) * ((1 - sourceEta) * s + sourceEta * s ^ 2)) /
          sourceRadialNormalizer M := by ring
  simp_rw [he]
  rw [integral_div]
  have ht := (exponential_quadratic_tail
    (δ := sourceDelta M) (r := 1) (a := 0) (b := 1 - sourceEta) (c := sourceEta)
    (sourceDelta_pos M hM).le (by norm_num) (by norm_num)
    (sub_nonneg.mpr sourceEta_lt_one.le) sourceEta_pos.le).2
  norm_num at ht
  rw [ht]
  unfold sourceVariance sourceRadialNormalizer
  have hd : 0 < 1 + sourceEta * sourceDelta M := by
    have := sourceEta_pos
    have := sourceDelta_pos M hM
    positivity
  field_simp [(Real.exp_pos (-sourceDelta M)).ne']
  ring

theorem integral_sourcePlantedDensity_mul_exp {M : ℕ} (hM : 1 ≤ M)
    {t : ℝ} (ht : t < 1) :
    (∫ z, sourcePlantedDensity M z * Real.exp (t * sourceRadiusSq z)
      ∂standardComplexGaussianTail 2) =
      Real.exp (-(1 - t) * sourceDelta M) / sourceRadialNormalizer M *
        ((1 - sourceEta) / (1 - t) +
          sourceEta * (sourceDelta M / (1 - t) + 1 / (1 - t) ^ 2)) := by
  rw [integral_sourcePlantedDensity_radial hM (f := fun s ↦ Real.exp (t * s)) (by fun_prop)
    (integrable_sourcePlantedDensity_mul_exp hM ht)]
  have he (s : ℝ) :
      Real.exp (-s) * ((1 - sourceEta) + sourceEta * s) / sourceRadialNormalizer M *
          Real.exp (t * s) =
        (Real.exp (-(1 - t) * s) * ((1 - sourceEta) + sourceEta * s)) /
          sourceRadialNormalizer M := by
    have hx : Real.exp (-s) * Real.exp (t * s) = Real.exp (-(1 - t) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp (-s) * Real.exp (t * s)) *
          ((1 - sourceEta) + sourceEta * s) / sourceRadialNormalizer M := by ring
      _ = _ := by rw [hx]
  simp_rw [he]
  rw [integral_div]
  have hv := (exponential_quadratic_tail
    (δ := sourceDelta M) (r := 1 - t) (a := 1 - sourceEta) (b := sourceEta) (c := 0)
    (sourceDelta_pos M hM).le (by linarith) (sub_nonneg.mpr sourceEta_lt_one.le)
    sourceEta_pos.le (by norm_num)).2
  simp only [zero_mul, add_zero] at hv
  rw [hv]
  ring

theorem sourcePlantedDensity_exp_quarter_bound {M : ℕ} (hM : 1 ≤ M) :
    (∫ z, sourcePlantedDensity M z * Real.exp (sourceRadiusSq z / 4)
      ∂standardComplexGaussianTail 2) ≤ 4 * Real.exp 1 := by
  have he : (fun z ↦ sourcePlantedDensity M z * Real.exp (sourceRadiusSq z / 4)) =
      fun z ↦ sourcePlantedDensity M z * Real.exp ((1 / 4) * sourceRadiusSq z) := by
    funext z; congr 2; ring
  rw [he, integral_sourcePlantedDensity_mul_exp hM (by norm_num : (1 / 4 : ℝ) < 1)]
  have hd := sourceDelta_le_one hM
  have hd0 := (sourceDelta_pos M hM).le
  have hc := sourceRadialNormalizer_pos M
  have hc' : (sourceRadialNormalizer M)⁻¹ ≤ Real.exp 1 := by
    have hh := (inv_le_inv₀ hc (Real.exp_pos (-1))).mpr (sourceRadialNormalizer_lower hM)
    simpa only [Real.exp_neg, inv_inv] using hh
  have hx : Real.exp (-(1 - (1 / 4 : ℝ)) * sourceDelta M) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hb : (1 - sourceEta) / (1 - (1 / 4 : ℝ)) +
      sourceEta * (sourceDelta M / (1 - (1 / 4 : ℝ)) + 1 / (1 - (1 / 4 : ℝ)) ^ 2) ≤ 4 := by
    norm_num [sourceEta]
    linarith
  calc
    _ ≤ (1 / sourceRadialNormalizer M) * 4 := by
      apply mul_le_mul (div_le_div_of_nonneg_right hx hc.le) hb
      · unfold sourceEta
        positivity
      · positivity
    _ = 4 * (sourceRadialNormalizer M)⁻¹ := by ring
    _ ≤ 4 * Real.exp 1 := mul_le_mul_of_nonneg_left hc' (by norm_num)

/-- The two-coordinate law with the literal density (3.1) relative to γ₂. -/
def sourcePlantedDensityLaw (M : ℕ) : Measure (Signal 2) :=
  (standardComplexGaussianTail 2).withDensity
    (fun z ↦ ENNReal.ofReal (sourcePlantedDensity M z))

theorem isProbabilityMeasure_sourcePlantedDensityLaw {M : ℕ} (hM : 1 ≤ M) :
    IsProbabilityMeasure (sourcePlantedDensityLaw M) where
  measure_univ := by
    rw [sourcePlantedDensityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_sourcePlantedDensity hM)
        (Filter.Eventually.of_forall fun z ↦ sourcePlantedDensity_nonneg M z),
      integral_sourcePlantedDensity hM]
    norm_num

theorem integral_sourcePlantedDensityLaw (M : ℕ) (f : Signal 2 → ℝ) :
    (∫ z, f z ∂sourcePlantedDensityLaw M) =
      ∫ z, sourcePlantedDensity M z * f z ∂standardComplexGaussianTail 2 := by
  rw [sourcePlantedDensityLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_sourcePlantedDensity M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourcePlantedDensity_nonneg M _), smul_eq_mul]

theorem integrable_sourcePlantedDensityLaw_iff (M : ℕ) (f : Signal 2 → ℝ) :
    Integrable f (sourcePlantedDensityLaw M) ↔
      Integrable (fun z ↦ sourcePlantedDensity M z * f z)
        (standardComplexGaussianTail 2) := by
  rw [sourcePlantedDensityLaw, integrable_withDensity_iff_integrable_smul'
    (measurable_sourcePlantedDensity M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourcePlantedDensity_nonneg M _), smul_eq_mul]

theorem sourcePlantedDensityLaw_map_coordinatePhase (M : ℕ) (c : Fin 2 → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) :
    (sourcePlantedDensityLaw M).map (coordinatePhase c) = sourcePlantedDensityLaw M := by
  apply map_withDensity_of_invariant
  · exact (measurable_sourcePlantedDensity M).ennreal_ofReal
  · unfold coordinatePhase; fun_prop
  · exact standardComplexGaussianTail_map_coordinatePhase c hc
  · intro z
    rw [sourcePlantedDensity_coordinatePhase M c hc]

theorem sourcePlantedDensityLaw_map_swapTwo (M : ℕ) :
    (sourcePlantedDensityLaw M).map swapTwo = sourcePlantedDensityLaw M := by
  apply map_withDensity_of_invariant
  · exact (measurable_sourcePlantedDensity M).ennreal_ofReal
  · unfold swapTwo; fun_prop
  · exact standardComplexGaussianTail_map_swapTwo
  · intro z
    rw [sourcePlantedDensity_swapTwo]

theorem sourcePlantedDensityLaw_integrable_radius_pow {M : ℕ} (hM : 1 ≤ M) (k : ℕ) :
    Integrable (fun z ↦ sourceRadiusSq z ^ k) (sourcePlantedDensityLaw M) :=
  (integrable_sourcePlantedDensityLaw_iff M _).mpr
    (integrable_sourcePlantedDensity_mul_radius_pow hM k)

theorem sourcePlantedDensityLaw_integrable_radius {M : ℕ} (hM : 1 ≤ M) :
    Integrable sourceRadiusSq (sourcePlantedDensityLaw M) := by
  simpa using sourcePlantedDensityLaw_integrable_radius_pow hM 1

theorem sourcePlantedDensityLaw_centered (M : ℕ) (i : Fin 2) :
    (∫ z, z i ∂sourcePlantedDensityLaw M) = 0 :=
  integral_coordinate_eq_zero_of_phase (sourcePlantedDensityLaw_map_coordinatePhase M) i

theorem sourcePlantedDensityLaw_pseudocovariance (M : ℕ) (i j : Fin 2) :
    (∫ z, z i * z j ∂sourcePlantedDensityLaw M) = 0 :=
  integral_coordinate_product_eq_zero_of_phase
    (sourcePlantedDensityLaw_map_coordinatePhase M) i j

theorem sourcePlantedDensityLaw_covariance {M : ℕ} (hM : 1 ≤ M) (i j : Fin 2) :
    (∫ z, z i * star (z j) ∂sourcePlantedDensityLaw M) =
      if i = j then (sourceVariance M : ℂ) else 0 := by
  rw [integral_coordinate_covariance_of_symmetry (sourcePlantedDensityLaw_integrable_radius hM)
    (sourcePlantedDensityLaw_map_coordinatePhase M) (sourcePlantedDensityLaw_map_swapTwo M),
    integral_sourcePlantedDensityLaw, integral_sourcePlantedDensity_mul_radius hM]
  congr 1
  norm_num

theorem sourcePlantedDensityLaw_exp_quarter_bound {M : ℕ} (hM : 1 ≤ M) :
    (∫ z, Real.exp (sourceRadiusSq z / 4) ∂sourcePlantedDensityLaw M) ≤ 4 * Real.exp 1 := by
  rw [integral_sourcePlantedDensityLaw]
  exact sourcePlantedDensity_exp_quarter_bound hM

theorem sourcePlantedDensityLaw_integrable_exp {M : ℕ} (hM : 1 ≤ M)
    {t : ℝ} (ht : t < 1) :
    Integrable (fun z ↦ Real.exp (t * sourceRadiusSq z)) (sourcePlantedDensityLaw M) :=
  (integrable_sourcePlantedDensityLaw_iff M _).mpr
    (integrable_sourcePlantedDensity_mul_exp hM ht)

theorem sourcePlantedDensityLaw_mgf {M : ℕ} (hM : 1 ≤ M)
    {t : ℝ} (ht : t < 1) :
    mgf sourceRadiusSq (sourcePlantedDensityLaw M) t =
      Real.exp (-(1 - t) * sourceDelta M) / sourceRadialNormalizer M *
        ((1 - sourceEta) / (1 - t) +
          sourceEta * (sourceDelta M / (1 - t) + 1 / (1 - t) ^ 2)) := by
  rw [mgf, integral_sourcePlantedDensityLaw]
  exact integral_sourcePlantedDensity_mul_exp hM ht

end SourcePlantedMoments

end NLA.FR05
