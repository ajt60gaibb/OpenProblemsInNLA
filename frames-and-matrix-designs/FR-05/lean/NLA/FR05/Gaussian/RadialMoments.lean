import NLA.FR05.Densities.PlantedLaw

/-!
# Gaussian radial moments, exponential tails, and gamma laws

The sections develop `RadialMoments`, `GammaEnergy`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section RadialMoments

/-! ## GaussianRadialMoments -/

section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem mgf_square_standardGaussian {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) t =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  unfold mgf
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul]
  unfold gaussianPDFReal
  norm_num
  have hi (x : ℝ) :
      (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * Real.exp (-x ^ 2 / 2) *
          Real.exp (t * x ^ 2) =
        ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
          Real.exp (-(1 / 2 - t) * x ^ 2) := by
    rw [mul_assoc _ _ (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  simp_rw [hi]
  rw [integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  have hs : Real.sqrt 2 * Real.sqrt (1 / 2 - t) = Real.sqrt (1 - 2 * t) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hp : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hb : Real.sqrt (1 / 2 - t) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  rw [← hs]
  field_simp

theorem integrable_exp_square_standardGaussian {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  apply mgf_pos_iff.mp
  rw [mgf_square_standardGaussian ht]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

theorem mgf_sum_square_product {ι : Type*} [Fintype ι] {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun x : ι → ℝ ↦ ∑ i, x i ^ 2)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) t =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ Fintype.card ι := by
  unfold mgf
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun _ x ↦ Real.exp (t * x ^ 2))]
  simp only [show (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ from mgf_square_standardGaussian ht]
  simp

/-- The radial Laplace transform of the branch's concrete complex Gaussian law. -/
theorem mgf_standardComplexGaussian_energy (n : ℕ) {t : ℝ} (ht : t < 1) :
    mgf (signalEnergy (n := n)) (standardComplexGaussianTail n) t =
      (1 - t)⁻¹ ^ n := by
  unfold mgf standardComplexGaussianTail
  rw [integral_map measurable_standardComplexGaussianTail_map.aemeasurable (by
    apply Measurable.aestronglyMeasurable
    unfold signalEnergy squaredEuclideanNorm
    fun_prop)]
  simp_rw [signalEnergy_standardComplexTail, ← mul_assoc]
  change mgf (fun x : (Fin n × Fin 2) → ℝ ↦ ∑ i, x i ^ 2)
    (Measure.pi (fun _ ↦ gaussianReal 0 1)) (t * (1 / 2)) = _
  rw [mgf_sum_square_product (by linarith), Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  have he : 1 - 2 * (t * (1 / 2)) = 1 - t := by ring
  rw [he, Nat.mul_comm n 2, pow_mul, inv_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - t)]

theorem integrable_exp_standardComplexGaussian_energy (n : ℕ) {t : ℝ} (ht : t < 1) :
    Integrable (fun z : Signal n ↦ Real.exp (t * signalEnergy z))
      (standardComplexGaussianTail n) := by
  apply mgf_pos_iff.mp
  rw [mgf_standardComplexGaussian_energy n ht]
  exact pow_pos (inv_pos.mpr (by linarith)) _

theorem mem_interior_integrableExpSet_standardComplexGaussian_energy
    (n : ℕ) {t : ℝ} (ht : t < 1) :
    t ∈ interior (integrableExpSet (signalEnergy (n := n)) (standardComplexGaussianTail n)) := by
  apply mem_interior.mpr
  exact ⟨Set.Iio 1, fun _ hs ↦ integrable_exp_standardComplexGaussian_energy n hs,
    isOpen_Iio, ht⟩

theorem integrable_energy_pow_mul_exp_standardComplexGaussian
    (n k : ℕ) {t : ℝ} (ht : t < 1) :
    Integrable (fun z : Signal n ↦ signalEnergy z ^ k * Real.exp (t * signalEnergy z))
      (standardComplexGaussianTail n) :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior_integrableExpSet_standardComplexGaussian_energy n ht) k

theorem integral_energy_mul_exp_standardComplexGaussian_two {t : ℝ} (ht : t < 1) :
    (∫ z : Signal 2, signalEnergy z * Real.exp (t * signalEnergy z)
      ∂standardComplexGaussianTail 2) = 2 * (1 - t)⁻¹ ^ 3 := by
  have hne : 1 - t ≠ 0 := by linarith
  have hd : HasDerivAt (fun s : ℝ ↦ (1 - s)⁻¹ ^ 2) (2 * (1 - t)⁻¹ ^ 3) t := by
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).inv hne).pow 2 using 1
    dsimp
    field_simp
    ring
  have heq : mgf (signalEnergy (n := 2)) (standardComplexGaussianTail 2) =ᶠ[𝓝 t]
      (fun s : ℝ ↦ (1 - s)⁻¹ ^ 2) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact mgf_standardComplexGaussian_energy 2 hs
  exact (hasDerivAt_mgf
    (mem_interior_integrableExpSet_standardComplexGaussian_energy 2 ht)).unique
      (hd.congr_of_eventuallyEq heq)

theorem integral_energy_sq_mul_exp_standardComplexGaussian_two {t : ℝ} (ht : t < 1) :
    (∫ z : Signal 2, signalEnergy z ^ 2 * Real.exp (t * signalEnergy z)
      ∂standardComplexGaussianTail 2) = 6 * (1 - t)⁻¹ ^ 4 := by
  have hne : 1 - t ≠ 0 := by linarith
  have hd : HasDerivAt (fun s : ℝ ↦ 2 * (1 - s)⁻¹ ^ 3) (6 * (1 - t)⁻¹ ^ 4) t := by
    convert! ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).inv hne).pow 3).const_mul 2
      using 1
    dsimp
    field_simp
    ring
  have heq : (fun s ↦ ∫ z : Signal 2, signalEnergy z ^ 1 * Real.exp (s * signalEnergy z)
      ∂standardComplexGaussianTail 2) =ᶠ[𝓝 t] (fun s : ℝ ↦ 2 * (1 - s)⁻¹ ^ 3) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    simpa only [pow_one] using integral_energy_mul_exp_standardComplexGaussian_two hs
  exact (hasDerivAt_integral_pow_mul_exp_real
    (mem_interior_integrableExpSet_standardComplexGaussian_energy 2 ht) 1).unique
      (hd.congr_of_eventuallyEq heq)

end

/-! ## ExponentialTailMoments -/

section

open MeasureTheory Filter Set
open scoped Topology

def exponentialTailPrimitive (r a b c x : ℝ) : ℝ :=
  -Real.exp (-r * x) * (a / r + b * (x / r + 1 / r ^ 2) +
    c * (x ^ 2 / r + 2 * x / r ^ 2 + 2 / r ^ 3))

theorem exponentialTailPrimitive_deriv {r : ℝ} (hr : r ≠ 0) (a b c x : ℝ) :
    HasDerivAt (exponentialTailPrimitive r a b c)
      (Real.exp (-r * x) * (a + b * x + c * x ^ 2)) x := by
  have hP : HasDerivAt
      (fun s : ℝ ↦ a / r + b * (s / r + 1 / r ^ 2) +
        c * (s ^ 2 / r + 2 * s / r ^ 2 + 2 / r ^ 3))
      (b / r + c * (2 * x / r + 2 / r ^ 2)) x := by
    have hB := (((hasDerivAt_id x).div_const r).add_const (1 / r ^ 2)).const_mul b
    have hC := (((((hasDerivAt_id x).pow 2).div_const r).add
      (((hasDerivAt_id x).const_mul 2).div_const (r ^ 2))).add_const (2 / r ^ 3)).const_mul c
    convert! ((hasDerivAt_const x (a / r)).add hB).add hC using 1
    dsimp
    ring
  convert! (((hasDerivAt_id x).const_mul (-r)).exp.neg.mul hP) using 1
  dsimp
  field_simp
  ring

theorem exponentialTailPrimitive_tendsto {r : ℝ} (hr : 0 < r) (a b c : ℝ) :
    Tendsto (exponentialTailPrimitive r a b c) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ ↦ Real.exp (-r * x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 r hr
  have h1 : Tendsto (fun x : ℝ ↦ x * Real.exp (-r * x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 r hr
  have h2 : Tendsto (fun x : ℝ ↦ x ^ 2 * Real.exp (-r * x)) atTop (𝓝 0) := by
    simpa [Real.rpow_two] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 r hr
  have h := ((h0.const_mul (-(a / r + b / r ^ 2 + 2 * c / r ^ 3))).add
    (h1.const_mul (-(b / r + 2 * c / r ^ 2)))).add (h2.const_mul (-(c / r)))
  convert h using 1
  · funext x
    unfold exponentialTailPrimitive
    ring
  · simp

theorem exponential_quadratic_tail {δ r a b c : ℝ} (hδ : 0 ≤ δ) (hr : 0 < r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    IntegrableOn (fun s ↦ Real.exp (-r * s) * (a + b * s + c * s ^ 2)) (Ici δ) ∧
      (∫ s in Ici δ, Real.exp (-r * s) * (a + b * s + c * s ^ 2)) =
        Real.exp (-r * δ) * (a / r + b * (δ / r + 1 / r ^ 2) +
          c * (δ ^ 2 / r + 2 * δ / r ^ 2 + 2 / r ^ 3)) := by
  have hd (x : ℝ) (_hx : x ∈ Ici δ) := exponentialTailPrimitive_deriv hr.ne' a b c x
  have hn (x : ℝ) (hx : x ∈ Ioi δ) :
      0 ≤ Real.exp (-r * x) * (a + b * x + c * x ^ 2) := by
    have hx' : 0 ≤ x := hδ.trans hx.le
    positivity
  have ht := exponentialTailPrimitive_tendsto hr a b c
  constructor
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_deriv_of_nonneg' hd hn ht
  · rw [integral_Ici_eq_integral_Ioi, integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht]
    simp [exponentialTailPrimitive]

end

end RadialMoments

section GammaEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem map_eq_of_mgf_on_Iio_one {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (hXi : ∀ t < 1, Integrable (fun x ↦ Real.exp (t * X x)) μ)
    (hYi : ∀ t < 1, Integrable (fun y ↦ Real.exp (t * Y y)) ν)
    (he : ∀ t < 1, mgf X μ t = mgf Y ν t) :
    μ.map X = ν.map Y := by
  have hXo {t : ℝ} (ht : t < 1) : t ∈ interior (integrableExpSet X μ) :=
    mem_interior.mpr ⟨Iio 1, fun s hs ↦ hXi s hs, isOpen_Iio, ht⟩
  have hYo {t : ℝ} (ht : t < 1) : t ∈ interior (integrableExpSet Y ν) :=
    mem_interior.mpr ⟨Iio 1, fun s hs ↦ hYi s hs, isOpen_Iio, ht⟩
  have hA : AnalyticOnNhd ℂ (complexMGF X μ) {z : ℂ | z.re < 1} :=
    analyticOnNhd_complexMGF.mono fun z hz ↦ hXo hz
  have hB : AnalyticOnNhd ℂ (complexMGF Y ν) {z : ℂ | z.re < 1} :=
    analyticOnNhd_complexMGF.mono fun z hz ↦ hYo hz
  have hr : ∃ᶠ t : ℝ in 𝓝[≠] 0,
      complexMGF X μ t = complexMGF Y ν t := by
    apply Filter.Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht
    rw [complexMGF_ofReal, complexMGF_ofReal, he t ht]
  have hc : Set.EqOn (complexMGF X μ) (complexMGF Y ν) {z : ℂ | z.re < 1} := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hA hB
      ((convex_Iio (1 : ℝ)).linear_preimage Complex.reLm).isPreconnected
      (z₀ := (0 : ℂ)) (by simp)
    rw [frequently_iff_seq_forall] at hr ⊢
    obtain ⟨xs, hx, hxs⟩ := hr
    refine ⟨fun k ↦ (xs k : ℂ), ?_, hxs⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    constructor
    · exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hx.1
    · simpa using hx.2
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  apply hc
  simp

theorem integral_gammaMeasure_one (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ s, f s ∂gammaMeasure a 1) =
      (Real.Gamma a)⁻¹ * ∫ s in Ioi (0 : ℝ), s ^ (a - 1) * Real.exp (-s) * f s := by
  change (∫ s, f s ∂volume.withDensity (fun s ↦ ENNReal.ofReal (gammaPDFReal a 1 s))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal a 1).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha zero_lt_one _), smul_eq_mul]
  have he (s : ℝ) : gammaPDFReal a 1 s * f s =
      (Ici (0 : ℝ)).indicator
        (fun s ↦ (Real.Gamma a)⁻¹ * (s ^ (a - 1) * Real.exp (-s) * f s)) s := by
    by_cases hs : 0 ≤ s <;> simp [gammaPDFReal, Set.indicator, hs, mul_assoc]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]

theorem mgf_gammaMeasure_one {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    mgf id (gammaMeasure a 1) t = (1 / (1 - t)) ^ a := by
  unfold mgf
  rw [integral_gammaMeasure_one a ha]
  have he (s : ℝ) :
      s ^ (a - 1) * Real.exp (-s) * Real.exp (t * s) =
        s ^ (a - 1) * Real.exp (-((1 - t) * s)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [id_eq]
  simp_rw [he]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)]
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

theorem standardComplexGaussianTail_map_energy {n : ℕ} (hn : 0 < n) :
    (standardComplexGaussianTail n).map signalEnergy = gammaMeasure n 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let : IsProbabilityMeasure (gammaMeasure n 1) := isProbabilityMeasure_gammaMeasure hn' zero_lt_one
  have h := map_eq_of_mgf_on_Iio_one
    (μ := standardComplexGaussianTail n) (ν := gammaMeasure n 1)
    (X := signalEnergy) (Y := id)
    (by apply Continuous.aemeasurable; unfold signalEnergy squaredEuclideanNorm; fun_prop) aemeasurable_id
    (fun t ht ↦ integrable_exp_standardComplexGaussian_energy n ht)
    (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · simpa using h
  · apply mgf_pos_iff.mp
    rw [mgf_gammaMeasure_one hn' ht]
    positivity
  · rw [mgf_standardComplexGaussian_energy n ht, mgf_gammaMeasure_one hn' ht,
      Real.rpow_natCast, one_div]

end GammaEnergy

end NLA.FR05
