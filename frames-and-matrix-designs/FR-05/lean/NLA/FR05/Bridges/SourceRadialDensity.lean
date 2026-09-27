/-
The exact density of the scalar radial sampling law used in (3.18).

This is the first measure-theoretic bridge between the coordinate sampler in
`PlantedLaw` and the density formulation used in Proposition 3.2.
-/
import NLA.FR05.Gaussian.GammaSimplexLaw

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- Before the lower-radius conditioning, the source radial sampler has the
literal density `exp (-s) * ((1 - eta) + eta * s)` on the positive half-line. -/
theorem sourceRadialBase_eq_density {eta : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    sourceRadialBase eta =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s ↦ ENNReal.ofReal
          (Real.exp (-s) * ((1 - eta) + eta * s))) := by
  have hgamma : gammaMeasure 2 1 =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s ↦ ENNReal.ofReal (gammaNatWeight 1 s)) := by
    convert gammaMeasure_nat_eq_density 1 using 1
    norm_num
  rw [sourceRadialBase, expMeasure_one_eq_density, hgamma]
  rw [← withDensity_smul (μ := volume.restrict (Ioi (0 : ℝ)))
      (ENNReal.ofReal (1 - eta)) (by fun_prop),
    ← withDensity_smul (μ := volume.restrict (Ioi (0 : ℝ)))
      (ENNReal.ofReal eta) (by fun_prop),
    ← withDensity_add_left (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, gammaNatWeight]
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr heta1),
    ← ENNReal.ofReal_mul heta0]
  have hleft : 0 ≤ (1 - eta) * Real.exp (-s) :=
    mul_nonneg (sub_nonneg.mpr heta1) (Real.exp_pos _).le
  have hright : 0 ≤ eta * (s ^ 1 / (Nat.factorial 1 : ℝ) * Real.exp (-s)) :=
    mul_nonneg heta0
      (mul_nonneg (div_nonneg (pow_nonneg hs.le _) (by norm_num))
        (Real.exp_pos _).le)
  have hsplit : Real.exp (-s) * ((1 - eta) + eta * s) =
      (1 - eta) * Real.exp (-s) +
        eta * (s ^ 1 / (Nat.factorial 1 : ℝ) * Real.exp (-s)) := by
    norm_num [Nat.factorial]
    ring
  rw [hsplit, ENNReal.ofReal_add hleft hright]

/-- The two real phase coordinates in the sampler push forward to normalized
Haar measure on the additive circle. -/
theorem sourceUniformInterval_zero_two_pi_map_conePhase :
    (sourceUniformInterval 0 (2 * Real.pi)).map
      (fun x : ℝ ↦ (x : ConePhase)) = AddCircle.haarAddCircle := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hperiod : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hmap : Measure.map (fun x : ℝ ↦ (x : ConePhase))
      (volume.restrict (Ioc 0 (2 * Real.pi))) = volume := by
    simpa using (AddCircle.measurePreserving_mk (2 * Real.pi) 0).map_eq
  unfold sourceUniformInterval ProbabilityTheory.cond
  rw [Real.volume_Icc, Measure.map_smul,
    ← Measure.restrict_congr_set Ioc_ae_eq_Icc,
    hmap, sub_zero,
    AddCircle.volume_eq_smul_haarAddCircle, ← smul_assoc, smul_eq_mul,
    ENNReal.inv_mul_cancel hperiod ENNReal.ofReal_ne_top, one_smul]

/-- A source interval sampler is the constant-density law on that interval. -/
theorem sourceUniformInterval_eq_density {a b : ℝ} (hab : a < b) :
    sourceUniformInterval a b =
      (volume.restrict (Icc a b)).withDensity
        (fun _ ↦ ENNReal.ofReal ((b - a)⁻¹)) := by
  unfold sourceUniformInterval ProbabilityTheory.cond
  rw [Real.volume_Icc, ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab),
    ← withDensity_const]

/-- The normalizing constant in the density formulation is exactly the mass
retained when the source radial sampler is conditioned at `sourceDelta M`. -/
theorem sourceRadialBase_sourceEta_apply_Ici {M : ℕ} (hM : 1 ≤ M) :
    sourceRadialBase sourceEta (Ici (sourceDelta M)) =
      ENNReal.ofReal (sourceRadialNormalizer M) := by
  let f : ℝ → ℝ := fun s ↦
    Real.exp (-s) * ((1 - sourceEta) + sourceEta * s)
  have hdelta : 0 ≤ sourceDelta M := (sourceDelta_pos M hM).le
  have hint : IntegrableOn f (Ici (sourceDelta M)) := by
    have h := (exponential_quadratic_tail (δ := sourceDelta M) (r := 1)
      (a := 1 - sourceEta) (b := sourceEta) (c := 0) hdelta (by norm_num)
      (sub_nonneg.mpr sourceEta_lt_one.le) sourceEta_pos.le (by norm_num)).1
    simpa [f] using h
  have htail : (∫ s in Ici (sourceDelta M), f s) = sourceRadialNormalizer M := by
    have h := (exponential_quadratic_tail (δ := sourceDelta M) (r := 1)
      (a := 1 - sourceEta) (b := sourceEta) (c := 0) hdelta (by norm_num)
      (sub_nonneg.mpr sourceEta_lt_one.le) sourceEta_pos.le (by norm_num)).2
    simp only [zero_mul, add_zero, div_one, one_pow] at h
    rw [show (1 - sourceEta) + sourceEta * (sourceDelta M + 1) =
        1 + sourceEta * sourceDelta M by ring] at h
    simpa [f, sourceRadialNormalizer] using h
  rw [sourceRadialBase_eq_density sourceEta_pos.le sourceEta_lt_one.le,
    withDensity_apply _ measurableSet_Ici]
  change ∫⁻ s, ENNReal.ofReal (f s) ∂
      ((volume.restrict (Ioi (0 : ℝ))).restrict (Ici (sourceDelta M))) = _
  rw [Measure.restrict_restrict_of_subset]
  · rw [← ofReal_integral_eq_lintegral_ofReal hint
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
        unfold f
        exact mul_nonneg (Real.exp_pos _).le
          (add_nonneg (sub_nonneg.mpr sourceEta_lt_one.le)
            (mul_nonneg sourceEta_pos.le (hdelta.trans hs)))), htail]
  · intro s hs
    exact (sourceDelta_pos M hM).trans_le hs

/-- Conditioning the source mixture at the manuscript cutoff gives precisely
the radial density used by the two-coordinate planted law. -/
theorem sourceRadialLaw_sourceEta_eq_density {M : ℕ} (hM : 1 ≤ M) :
    sourceRadialLaw sourceEta (sourceDelta M) =
      (volume.restrict (Ici (sourceDelta M))).withDensity
        (fun s ↦ ENNReal.ofReal (plantedRadiusDensity M s)) := by
  unfold sourceRadialLaw ProbabilityTheory.cond
  rw [sourceRadialBase_sourceEta_apply_Ici hM,
    sourceRadialBase_eq_density sourceEta_pos.le sourceEta_lt_one.le,
    restrict_withDensity measurableSet_Ici,
    Measure.restrict_restrict_of_subset]
  · rw [← withDensity_smul (μ := volume.restrict (Ici (sourceDelta M)))
      (ENNReal.ofReal (sourceRadialNormalizer M))⁻¹ (by fun_prop)]
    apply withDensity_congr_ae
    filter_upwards [] with s
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_inv_of_pos (sourceRadialNormalizer_pos M),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (sourceRadialNormalizer_pos M).le)]
    congr 1
    unfold plantedRadiusDensity
    field_simp [(sourceRadialNormalizer_pos M).ne']
  · intro s hs
    exact (sourceDelta_pos M hM).trans_le hs

end NLA.FR05
