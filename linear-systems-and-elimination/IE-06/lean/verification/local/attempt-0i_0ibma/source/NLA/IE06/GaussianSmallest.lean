/-
Gaussian radial building blocks for the smallest-singular-value argument.
Density proof structure adapted with permission from the user's local
AI-assisted RRF.Proofs.GaussianDensity; radial Gamma structure informed by
RRF.Proofs.GaussianRadial. Exact source identities and review are recorded in
source/gaussian-smallest-provenance.json and reviews/gaussian-smallest-specification.md.
No RRF module or theorem is imported. This does not assert the A2 tail bound.
-/
import NLA.IE06.GaussianFrobenius

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NLA.IE06.GaussianSmallest

abbrev E (q : ℕ) := EuclideanSpace ℝ (Fin q)

def density (q : ℕ) (x : E q) : ℝ :=
  (Real.sqrt (2 * Real.pi) ^ q)⁻¹ * Real.exp (-‖x‖ ^ 2 / 2)

theorem density_nonneg (q : ℕ) (x : E q) : 0 ≤ density q x := by
  unfold density
  positivity

theorem density_continuous (q : ℕ) : Continuous (density q) := by
  unfold density
  fun_prop

theorem pi_gaussian_density (q : ℕ) :
    Measure.pi (fun _ : Fin q => gaussianReal 0 1) =
      (Measure.pi (fun _ : Fin q => (volume : Measure ℝ))).withDensity
        (fun x => ENNReal.ofReal (∏ i : Fin q, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi : Integrable (fun x : Fin q → ℝ => ∏ i, gaussianPDFReal 0 1 (x i))
      (Measure.pi fun i : Fin q => (volume : Measure ℝ).restrict (s i)) :=
    Integrable.fintype_prod (fun i => (integrable_gaussianPDFReal 0 1).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i)))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (by norm_num) (s i)).symm

theorem product_density (q : ℕ) (x : Fin q → ℝ) :
    (∏ i : Fin q, gaussianPDFReal 0 1 (x i)) = density q (WithLp.toLp 2 x) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    inv_pow, ← Real.exp_sum, density, EuclideanSpace.real_norm_sq_eq]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → ℝ≥0∞)
    (hg : Measurable g) :
    (μ.withDensity (fun x => g (f x))).map f = (μ.map f).withDensity g := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hf]
  change (∫⁻ x, (h ∘ f) x ∂μ.withDensity (g ∘ f)) = _
  rw [
    lintegral_withDensity_eq_lintegral_mul μ (hg.comp hf) (hh.comp hf),
    lintegral_withDensity_eq_lintegral_mul (μ.map f) hg hh,
    lintegral_map (hg.mul hh) hf]
  rfl

theorem stdGaussian_density (q : ℕ) :
    stdGaussian (E q) = (volume : Measure (E q)).withDensity
      (fun x => ENNReal.ofReal (density q x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density]
  simp_rw [product_density]
  rw [map_withDensity_comp _ _ (PiLp.continuous_toLp 2 _).measurable _
    (density_continuous q).measurable.ennreal_ofReal]
  change ((volume : Measure (Fin q → ℝ)).map (WithLp.toLp 2)).withDensity _ = _
  rw [(PiLp.volume_preserving_toLp (Fin q)).map_eq]

theorem integral_stdGaussian (q : ℕ) (f : E q → ℝ) :
    (∫ x, f x ∂stdGaussian (E q)) =
      (Real.sqrt (2 * Real.pi) ^ q)⁻¹ *
        ∫ x : E q, Real.exp (-‖x‖ ^ 2 / 2) * f x := by
  rw [stdGaussian_density, integral_withDensity_eq_integral_toReal_smul
    (density_continuous q).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (density_nonneg q _), smul_eq_mul, density, mul_assoc]
  exact integral_const_mul _ _



open Set

private def radialIntegral (d : ℕ) (a : ℝ) : ℝ :=
  ∫ z : E d, ‖z‖ ^ a * Real.exp (-‖z‖ ^ 2 / 2)

private theorem radial_integrand (d : ℕ) (hd : 0 < d) (a y : ℝ) (hy : 0 < y) :
    y ^ (d - 1) * (y ^ a * Real.exp (-y ^ 2 / 2)) =
      y ^ ((d : ℝ) + a - 1) * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
  rw [← mul_assoc, ← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy]
  have he : ((d - 1 : ℕ) : ℝ) + a = (d : ℝ) + a - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [he]
  congr 2
  ring

private theorem radial_integrable (d : ℕ) (hd : 0 < d) (a : ℝ) (ha : -(d : ℝ) < a) :
    Integrable (fun z : E d => ‖z‖ ^ a * Real.exp (-‖z‖ ^ 2 / 2)) := by
  let : NeZero d := ⟨hd.ne'⟩
  apply (integrable_fun_norm_addHaar (volume : Measure (E d))
    (f := fun y : ℝ => y ^ a * Real.exp (-y ^ 2 / 2))).mpr
  simp only [E, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  apply IntegrableOn.congr_fun
    (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
      (s := (d : ℝ) + a - 1) (by linarith))
  · intro y hy
    exact (radial_integrand d hd a y hy).symm
  · exact measurableSet_Ioi

private theorem radialIntegral_gamma (d : ℕ) (hd : 0 < d) (a : ℝ) (ha : -(d : ℝ) < a) :
    radialIntegral d a = (d : ℝ) * (volume : Measure (E d)).real (Metric.ball 0 1) *
      ((1 / 2 : ℝ) ^ (-((d : ℝ) + a) / 2) * (1 / 2) * Real.Gamma (((d : ℝ) + a) / 2)) := by
  let : NeZero d := ⟨hd.ne'⟩
  have h := integral_fun_norm_addHaar (volume : Measure (E d))
    (fun y : ℝ => y ^ a * Real.exp (-y ^ 2 / 2))
  simp only [E, finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul] at h
  have hi : (∫ y : ℝ in Ioi 0, y ^ (d - 1) * (y ^ a * Real.exp (-y ^ 2 / 2))) =
      (1 / 2 : ℝ) ^ (-((d : ℝ) + a) / 2) * (1 / 2) * Real.Gamma (((d : ℝ) + a) / 2) := by
    have he := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (d : ℝ) + a - 1)
      (b := 1 / 2) (by norm_num) (by linarith) (by norm_num)
    rw [show (d : ℝ) + a - 1 + 1 = (d : ℝ) + a by ring] at he
    rw [← he]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simpa only [Real.rpow_two] using radial_integrand d hd a y hy
  rw [hi] at h
  simpa only [radialIntegral, mul_assoc] using h

private theorem radialIntegral_add_two (d : ℕ) (hd : 0 < d) (a : ℝ) (ha : -(d : ℝ) < a) :
    radialIntegral d (a + 2) = ((d : ℝ) + a) * radialIntegral d a := by
  rw [radialIntegral_gamma d hd (a + 2) (by linarith), radialIntegral_gamma d hd a ha]
  rw [show ((d : ℝ) + (a + 2)) / 2 = ((d : ℝ) + a) / 2 + 1 by ring,
    show -((d : ℝ) + (a + 2)) / 2 = -((d : ℝ) + a) / 2 + (-1) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2), Real.rpow_neg_one,
    Real.Gamma_add_one (by linarith : ((d : ℝ) + a) / 2 ≠ 0)]
  norm_num
  ring

private theorem gaussian_rpow_integrable (d : ℕ) (hd : 0 < d) (a : ℝ) (ha : -(d : ℝ) < a) :
    Integrable (fun z : E d => ‖z‖ ^ a) (stdGaussian (E d)) := by
  rw [stdGaussian_density]
  apply (integrable_withDensity_iff_integrable_smul'
    (density_continuous d).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp_rw [ENNReal.toReal_ofReal (density_nonneg d _)]
  simpa only [smul_eq_mul, density, mul_assoc, mul_comm, mul_left_comm] using
    (radial_integrable d hd a ha).const_mul ((Real.sqrt (2 * Real.pi) ^ d)⁻¹)

private theorem gaussian_rpow_integral (d : ℕ) (a : ℝ) :
    (∫ z : E d, ‖z‖ ^ a ∂stdGaussian (E d)) =
      (Real.sqrt (2 * Real.pi) ^ d)⁻¹ * radialIntegral d a := by
  rw [integral_stdGaussian]
  simp only [radialIntegral, mul_comm (Real.exp _) (‖_‖ ^ a)]

private theorem gaussian_rpow_add_two (d : ℕ) (hd : 0 < d) (a : ℝ) (ha : -(d : ℝ) < a) :
    (∫ z : E d, ‖z‖ ^ (a + 2) ∂stdGaussian (E d)) =
      ((d : ℝ) + a) * (∫ z : E d, ‖z‖ ^ a ∂stdGaussian (E d)) := by
  rw [gaussian_rpow_integral, gaussian_rpow_integral, radialIntegral_add_two d hd a ha]
  ring

/-- Exact all-order radial positive moments in Euclidean coordinates. -/
theorem gaussian_norm_moment (d q : ℕ) :
    Integrable (fun z : E d => ‖z‖ ^ (2 * q)) (stdGaussian (E d)) ∧
      (∫ z : E d, ‖z‖ ^ (2 * q) ∂stdGaussian (E d)) =
        ∏ j ∈ Finset.range q, ((d : ℝ) + 2 * j) := by
  constructor
  · simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian (E d)) (2 * q : ℕ) (by finiteness)).integrable_norm_pow'
  · by_cases hd : d = 0
    · subst d
      cases q with
      | zero => simp
      | succ q =>
        have hz (z : E 0) : z = 0 := Subsingleton.elim _ _
        have hp : (∏ j ∈ Finset.range (q + 1), ((0 : ℝ) + 2 * j)) = 0 := by
          apply Finset.prod_eq_zero (i := 0) <;> simp
        simp only [Nat.cast_zero]
        rw [hp]
        simp [hz]
    · have hd' := Nat.pos_of_ne_zero hd
      induction q with
      | zero => simp
      | succ q ih =>
        have ha : -(d : ℝ) < 2 * (q : ℝ) := by
          have h : (0 : ℝ) < d := Nat.cast_pos.mpr hd'
          have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
          linarith
        have hh := gaussian_rpow_add_two d hd' (2 * q) ha
        have hc (k : ℕ) (z : E d) : ‖z‖ ^ (2 * (k : ℝ)) = ‖z‖ ^ (2 * k) := by
          rw [show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
        rw [show (2 : ℝ) * q + 2 = 2 * ((q + 1 : ℕ) : ℝ) by push_cast; ring] at hh
        simp only [hc] at hh
        rw [hh, ih, Finset.prod_range_succ]
        ring

/-- Exact inverse radial moments. The strict dimension condition makes every
factor positive and guarantees genuine integrability. -/
theorem gaussian_inverse_norm_moment (d q : ℕ) (hdq : 2 * q < d) :
    Integrable (fun z : E d => (‖z‖ ^ (2 * q))⁻¹) (stdGaussian (E d)) ∧
      (∫ z : E d, (‖z‖ ^ (2 * q))⁻¹ ∂stdGaussian (E d)) =
        (∏ j ∈ Finset.range q, ((d : ℝ) - 2 * (j + 1)))⁻¹ := by
  have hd : 0 < d := by omega
  have ha : -(d : ℝ) < -(2 * (q : ℝ)) := by
    have h : (2 : ℝ) * q < d := by exact_mod_cast hdq
    linarith
  have hfun (z : E d) : (‖z‖ ^ (2 * q))⁻¹ = ‖z‖ ^ (-(2 * (q : ℝ))) := by
    rw [Real.rpow_neg (norm_nonneg z), show (2 : ℝ) * q = ((2 * q : ℕ) : ℝ) by norm_cast,
      Real.rpow_natCast]
  simp_rw [hfun]
  refine ⟨gaussian_rpow_integrable d hd _ ha, ?_⟩
  induction q with
  | zero => simp
  | succ q ih =>
    have hq : 2 * q < d := by omega
    have hfac : 0 < (d : ℝ) - 2 * ((q : ℝ) + 1) := by
      have h : (2 : ℝ) * (q + 1) < d := by exact_mod_cast hdq
      linarith
    have harg : -(d : ℝ) < -(2 * ((q : ℝ) + 1)) := by linarith
    have hh := gaussian_rpow_add_two d hd (-(2 * ((q : ℝ) + 1))) harg
    rw [show -(2 * ((q : ℝ) + 1)) + 2 = -(2 * (q : ℝ)) by ring] at hh
    have haq : -(d : ℝ) < -(2 * (q : ℝ)) := by
      have h : (2 : ℝ) * q < d := by exact_mod_cast hq
      linarith
    have hfq (z : E d) : (‖z‖ ^ (2 * q))⁻¹ = ‖z‖ ^ (-(2 * (q : ℝ))) := by
      rw [Real.rpow_neg (norm_nonneg z), show (2 : ℝ) * q = ((2 * q : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    rw [ih hq haq hfq] at hh
    rw [Finset.prod_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, mul_inv_rev]
    have he : (∫ z : E d, ‖z‖ ^ (-(2 * ((q : ℝ) + 1))) ∂stdGaussian (E d)) =
        (∏ j ∈ Finset.range q, ((d : ℝ) - 2 * (j + 1)))⁻¹ /
          ((d : ℝ) - 2 * ((q : ℝ) + 1)) := by
      apply (eq_div_iff hfac.ne').mpr
      linarith [hh]
    simpa only [div_eq_mul_inv, mul_comm] using he

/-- Squared Euclidean length in the literal product-law coordinates. -/
def sumSquares {d : ℕ} (z : Fin d → ℝ) : ℝ := ∑ i, z i ^ 2

private theorem sumSquares_pow {d : ℕ} (z : Fin d → ℝ) (q : ℕ) :
    sumSquares z ^ q = ‖WithLp.toLp 2 z‖ ^ (2 * q) := by
  rw [sumSquares, ← EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z), pow_mul]

/-- Exact positive moments under the concrete product standard Gaussian law,
including both zero dimension and zeroth moment. -/
theorem gaussian_sumSquares_moment (d q : ℕ) :
    Integrable (fun z : Fin d → ℝ => sumSquares z ^ q) (GaussianQuadratic.gaussianVector d) ∧
      (∫ z : Fin d → ℝ, sumSquares z ^ q ∂GaussianQuadratic.gaussianVector d) =
        ∏ j ∈ Finset.range q, ((d : ℝ) + 2 * j) := by
  have hmp : MeasurePreserving (WithLp.toLp 2) (GaussianQuadratic.gaussianVector d)
      (stdGaussian (E d)) := ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  obtain ⟨hi, he⟩ := gaussian_norm_moment d q
  constructor
  · simpa only [Function.comp_def, sumSquares_pow] using hmp.integrable_comp_of_integrable hi
  · rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)] at he
    simpa only [sumSquares_pow] using he

/-- Exact inverse moments under the concrete product standard Gaussian law. -/
theorem gaussian_inverse_sumSquares_moment (d q : ℕ) (hdq : 2 * q < d) :
    Integrable (fun z : Fin d → ℝ => (sumSquares z ^ q)⁻¹) (GaussianQuadratic.gaussianVector d) ∧
      (∫ z : Fin d → ℝ, (sumSquares z ^ q)⁻¹ ∂GaussianQuadratic.gaussianVector d) =
        (∏ j ∈ Finset.range q, ((d : ℝ) - 2 * (j + 1)))⁻¹ := by
  have hmp : MeasurePreserving (WithLp.toLp 2) (GaussianQuadratic.gaussianVector d)
      (stdGaussian (E d)) := ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  obtain ⟨hi, he⟩ := gaussian_inverse_norm_moment d q hdq
  constructor
  · simpa only [Function.comp_def, sumSquares_pow] using hmp.integrable_comp_of_integrable hi
  · rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)] at he
    simpa only [sumSquares_pow] using he

theorem inverse_moment_factor_pos (d q j : ℕ) (hdq : 2 * q < d) (hj : j < q) :
    0 < (d : ℝ) - 2 * ((j : ℝ) + 1) := by
  have h : 2 * (j + 1) < d := by omega
  have hr : (2 : ℝ) * ((j : ℝ) + 1) < d := by exact_mod_cast h
  linarith

#assert_trust kernel stdGaussian_density
#assert_trust kernel gaussian_norm_moment
#assert_trust kernel gaussian_inverse_norm_moment
#assert_trust kernel gaussian_sumSquares_moment
#assert_trust kernel gaussian_inverse_sumSquares_moment
#assert_trust kernel inverse_moment_factor_pos
#print axioms stdGaussian_density
#print axioms gaussian_norm_moment
#print axioms gaussian_inverse_norm_moment
#print axioms gaussian_sumSquares_moment
#print axioms gaussian_inverse_sumSquares_moment

end NLA.IE06.GaussianSmallest
