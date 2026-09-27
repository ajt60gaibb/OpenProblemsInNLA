import NLA.FR05.Gaussian.ScalarGaussianMoments

/-!
# Cone ray densities and their integrals

The sections develop `ConeRayDensity`, `ConeRayIntegral`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section ConeRayDensity

open MeasureTheory Complex Real Matrix
open scoped BigOperators

theorem overlapResidualMatrix_inverse (L : SourceOverlapMatrix) :
    (overlapResidualMatrix L)⁻¹ = (overlapDeterminant L : ℂ)⁻¹ •
      !![((1 - overlapColumnEnergy L 1 : ℝ) : ℂ), overlapColumnCross L;
        star (overlapColumnCross L), ((1 - overlapColumnEnergy L 0 : ℝ) : ℂ)] := by
  rw [Matrix.inv_def, overlapResidualMatrix_det, Ring.inverse_eq_inv,
    overlapResidualMatrix_eq, Matrix.adjugate_fin_two_of]
  simp only [neg_neg]

theorem cone_ray_quadratic (L : SourceOverlapMatrix)
    (hΔ : overlapDeterminant L ≠ 0) (x y : ℂ) :
    overlapDeterminant L *
      (sourceRadiusSq ![x, 0] +
        (coneInner (![y, 0] - Lᴴ *ᵥ ![x, 0])
          ((overlapResidualMatrix L)⁻¹ *ᵥ (![y, 0] - Lᴴ *ᵥ ![x, 0]))).re) =
      (coneSchurU L - Complex.normSq (L 1 0)) * Complex.normSq x +
      (coneSchurU L - Complex.normSq (L 0 1)) * Complex.normSq y -
      2 * (((coneSchurU L : ℂ) * L 0 0 + L 0 1 * star (L 1 1) * L 1 0) *
        star x * y).re := by
  rw [overlapResidualMatrix_inverse, ← Complex.ofReal_inv]
  simp only [sourceRadiusSq, coneInner, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, Pi.sub_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_zero, add_zero, sub_zero, zero_sub,
    Complex.normSq_zero, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, zero_mul,
    mul_neg, neg_mul, neg_neg]
  field_simp [hΔ]
  rw [overlapDeterminant_identity]
  simp [overlapFrobeniusSq, overlapColumnEnergy, overlapColumnCross, coneSchurU,
    Matrix.det_fin_two, Fin.sum_univ_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

def coneConditionalVariance (L : SourceOverlapMatrix) : ℝ :=
  overlapDeterminant L / (coneSchurU L * coneSchurFirst L)

theorem coneConditionalVariance_pos {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) : 0 < coneConditionalVariance L :=
  div_pos (overlapDeterminant_pos hL)
    (mul_pos (coneSchurU_pos hL) (coneSchurFirst_bounds hL).1)

theorem complex_complete_square {a b d : ℝ} (ha : a ≠ 0) (hd : d ≠ 0)
    (c x y : ℂ) (he : d = a * b - Complex.normSq c) :
    Complex.normSq x / a + Complex.normSq (y - star c / (a : ℂ) * x) / (d / a) =
      (b * Complex.normSq x + a * Complex.normSq y - 2 * (c * star x * y).re) / d := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  field_simp [ha, hd]
  rw [he]
  simp only [Complex.normSq_apply]
  ring

theorem cone_ray_schur_quadratic {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) (x y : ℂ) :
    sourceRadiusSq ![x, 0] +
      (coneInner (![y, 0] - Lᴴ *ᵥ ![x, 0])
        ((overlapResidualMatrix L)⁻¹ *ᵥ (![y, 0] - Lᴴ *ᵥ ![x, 0]))).re =
      Complex.normSq x / coneSchurFirst L +
        Complex.normSq (y - star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) /
          coneConditionalVariance L := by
  have hu := (coneSchurU_pos hL).ne'
  have ha := (coneSchurFirst_bounds hL).1.ne'
  have hΔ := (overlapDeterminant_pos hL).ne'
  have hd : overlapDeterminant L / coneSchurU L ≠ 0 := div_ne_zero hΔ hu
  have hv : coneConditionalVariance L =
      (overlapDeterminant L / coneSchurU L) / coneSchurFirst L := by
    unfold coneConditionalVariance
    ring
  rw [hv, complex_complete_square ha hd _ _ _
    (coneSchur_determinant L hu).symm]
  apply (mul_left_cancel₀ hΔ)
  rw [cone_ray_quadratic L hΔ]
  simp only [coneSchurFirst, coneSchurSecond, coneSchurCross,
    Complex.add_re, Complex.add_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp [hu, hΔ]
  ring

theorem cone_ray_density {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) (x y : ℂ) :
    scalarComplexDensity x * scalarComplexDensity y *
      overlapGaussianRatio L ![x, 0] ![y, 0] =
      (coneSchurU L)⁻¹ * scalarGaussianDensity (coneSchurFirst L) 0 x *
        scalarGaussianDensity (coneConditionalVariance L)
          (star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) y := by
  have hu := (coneSchurU_pos hL).ne'
  have ha := (coneSchurFirst_bounds hL).1.ne'
  have hΔ := (overlapDeterminant_pos hL).ne'
  have hquad := cone_ray_schur_quadratic hL x y
  simp only [sourceRadiusSq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.normSq_zero, add_zero] at hquad
  unfold scalarComplexDensity overlapGaussianRatio scalarGaussianDensity
  simp only [sourceRadiusSq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.normSq_zero, add_zero, sub_zero]
  have hexp :
      -Complex.normSq x - Complex.normSq y +
        (Complex.normSq y -
          (coneInner (![y, 0] - Lᴴ *ᵥ ![x, 0])
            ((overlapResidualMatrix L)⁻¹ *ᵥ (![y, 0] - Lᴴ *ᵥ ![x, 0]))).re) =
      -Complex.normSq x / coneSchurFirst L -
        Complex.normSq (y - star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) /
          coneConditionalVariance L := by
    simp only [neg_div]
    linarith
  calc
    _ = (Real.pi⁻¹ * Real.pi⁻¹ * (overlapDeterminant L)⁻¹) *
        Real.exp (-Complex.normSq x - Complex.normSq y +
          (Complex.normSq y -
            (coneInner (![y, 0] - Lᴴ *ᵥ ![x, 0])
              ((overlapResidualMatrix L)⁻¹ *ᵥ (![y, 0] - Lᴴ *ᵥ ![x, 0]))).re)) := by
      simp only [sub_eq_add_neg, Real.exp_add]
      ring
    _ = _ := by
      rw [hexp]
      simp only [sub_eq_add_neg, neg_div, Real.exp_add]
      unfold coneConditionalVariance
      field_simp [hu, ha, hΔ, Real.pi_ne_zero]

end ConeRayDensity

section ConeRayIntegral

open MeasureTheory Complex Real Matrix

def coneRadialWeight (z : ℂ) : ℝ := (1 - sourceEta) + sourceEta * Complex.normSq z

theorem integral_cone_conditional_weights {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) :
    (∫ x : ℂ, scalarGaussianDensity (coneSchurFirst L) 0 x * coneRadialWeight x *
      (∫ y : ℂ, scalarGaussianDensity (coneConditionalVariance L)
        (star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) y * coneRadialWeight y)) =
      (1 - sourceEta) ^ 2 + sourceEta * (1 - sourceEta) *
        (coneSchurFirst L + coneSchurSecond L) +
        sourceEta ^ 2 * (coneSchurFirst L * coneSchurSecond L +
          Complex.normSq (coneSchurCross L)) := by
  have ha := (coneSchurFirst_bounds hL).1
  have hv := coneConditionalVariance_pos hL
  have hu := coneSchurU_pos hL
  let a : ℂ := Real.sqrt (coneSchurFirst L)
  let b : ℂ := star (coneSchurCross L) / (coneSchurFirst L : ℂ) * a
  let c : ℂ := Real.sqrt (coneConditionalVariance L)
  have hna : Complex.normSq a = coneSchurFirst L := by
    simp [a, Real.mul_self_sqrt ha.le]
  have hnc : Complex.normSq c = coneConditionalVariance L := by
    simp [c, Real.mul_self_sqrt hv.le]
  have hnb : Complex.normSq b = Complex.normSq (coneSchurCross L) / coneSchurFirst L := by
    simp only [b, Complex.normSq_mul, Complex.normSq_div, Complex.normSq_conj,
      Complex.star_def, hna, Complex.normSq_ofReal]
    field_simp
  have hsum : Complex.normSq b + Complex.normSq c = coneSchurSecond L := by
    rw [hnb, hnc]
    have hd := coneSchur_determinant L hu.ne'
    unfold coneConditionalVariance
    field_simp [ha.ne', hu.ne'] at hd ⊢
    nlinarith
  have hfour : Complex.normSq a * (2 * Complex.normSq b + Complex.normSq c) =
      coneSchurFirst L * coneSchurSecond L + Complex.normSq (coneSchurCross L) := by
    rw [hna]
    have hb : coneSchurFirst L * Complex.normSq b = Complex.normSq (coneSchurCross L) := by
      rw [hnb]
      field_simp
    nlinarith
  have hinter (x : ℂ) :
      (∫ y : ℂ, scalarGaussianDensity (coneConditionalVariance L)
        (star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) y * coneRadialWeight y) =
      ∫ y, coneRadialWeight (Real.sqrt (coneConditionalVariance L) • y +
        star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) ∂scalarComplexGaussian :=
    integral_scalarGaussianDensity hv _ _
  simp_rw [hinter, mul_assoc]
  rw [integral_scalarGaussianDensity ha 0]
  simp only [add_zero]
  have he (x y : ℂ) :
      Real.sqrt (coneConditionalVariance L) • y +
        star (coneSchurCross L) / (coneSchurFirst L : ℂ) *
          (Real.sqrt (coneSchurFirst L) • x) = b * x + c * y := by
    simp only [b, a, c, Complex.real_smul]
    ring
  simp_rw [he]
  change (∫ x, ((1 - sourceEta) + sourceEta * Complex.normSq (a * x)) *
    (∫ y, ((1 - sourceEta) + sourceEta * Complex.normSq (b * x + c * y))
      ∂scalarComplexGaussian) ∂scalarComplexGaussian) = _
  rw [integral_scalarGaussian_radial_weights]
  have hsum' : Complex.normSq a + Complex.normSq b + Complex.normSq c =
      coneSchurFirst L + coneSchurSecond L := by rw [add_assoc, hsum, hna]
  rw [hsum']
  linear_combination sourceEta ^ 2 * hfour

theorem integral_cone_ray {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) :
    (∫ x, coneRadialWeight x *
      (∫ y, coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0]
        ∂scalarComplexGaussian) ∂scalarComplexGaussian) = coneRayMoment L := by
  rw [integral_scalarComplexGaussian]
  simp_rw [integral_scalarComplexGaussian]
  have hpoint (x : ℂ) :
      scalarComplexDensity x *
        (coneRadialWeight x * ∫ y : ℂ, scalarComplexDensity y *
          (coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0])) =
      (coneSchurU L)⁻¹ *
        (scalarGaussianDensity (coneSchurFirst L) 0 x * coneRadialWeight x *
          ∫ y : ℂ, scalarGaussianDensity (coneConditionalVariance L)
            (star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) y * coneRadialWeight y) := by
    rw [← mul_assoc, ← integral_const_mul, ← mul_assoc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have hd := cone_ray_density hL x y
    linear_combination coneRadialWeight x * coneRadialWeight y * hd
  simp_rw [hpoint]
  rw [integral_const_mul, integral_cone_conditional_weights hL]
  unfold coneRayMoment
  ring

theorem coneRadialWeight_pos (z : ℂ) : 0 < coneRadialWeight z := by
  have h := Complex.normSq_nonneg z
  unfold coneRadialWeight sourceEta
  positivity

theorem scalarComplexDensity_pos (z : ℂ) : 0 < scalarComplexDensity z := by
  unfold scalarComplexDensity
  positivity

theorem scalarGaussianDensity_pos {a : ℝ} (ha : 0 < a) (m z : ℂ) :
    0 < scalarGaussianDensity a m z := by
  unfold scalarGaussianDensity
  positivity

theorem coneRayMoment_pos {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) : 0 < coneRayMoment L := by
  have ha := (coneSchurFirst_bounds hL).1
  have hb := (coneSchurSecond_bounds hL).1
  have hu := coneSchurU_pos hL
  have hc := Complex.normSq_nonneg (coneSchurCross L)
  unfold coneRayMoment sourceEta
  positivity

theorem overlapGaussianRatio_pos {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) (z w : Fin 2 → ℂ) :
    0 < overlapGaussianRatio L z w := by
  have hΔ := overlapDeterminant_pos hL
  unfold overlapGaussianRatio
  positivity

theorem integral_scalarGaussianDensity_weight {a : ℝ} (ha : 0 < a) (m : ℂ) :
    (∫ z : ℂ, scalarGaussianDensity a m z * coneRadialWeight z) =
      (1 - sourceEta) + sourceEta * (Complex.normSq m + a) := by
  rw [integral_scalarGaussianDensity ha]
  have he (z : ℂ) : Real.sqrt a • z + m = m + (Real.sqrt a : ℂ) * z := by
    rw [Complex.real_smul, add_comm]
  simp_rw [he, coneRadialWeight]
  rw [integral_add (integrable_const _)
    ((integrable_scalarGaussian_affine_normSq _ _).const_mul _)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_scalarGaussian_affine_normSq]
  simp [Real.mul_self_sqrt ha.le]

theorem integral_cone_ray_inner_pos {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) (x : ℂ) :
    0 < ∫ y, coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0]
      ∂scalarComplexGaussian := by
  have hd (y : ℂ) :
      scalarComplexDensity x *
        (scalarComplexDensity y * (coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0])) =
      ((coneSchurU L)⁻¹ * scalarGaussianDensity (coneSchurFirst L) 0 x) *
        (scalarGaussianDensity (coneConditionalVariance L)
          (star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) y * coneRadialWeight y) := by
    linear_combination coneRadialWeight y * cone_ray_density hL x y
  have he : scalarComplexDensity x *
      (∫ y, coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0]
        ∂scalarComplexGaussian) =
      ((coneSchurU L)⁻¹ * scalarGaussianDensity (coneSchurFirst L) 0 x) *
        ((1 - sourceEta) + sourceEta *
          (Complex.normSq (star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x) +
            coneConditionalVariance L)) := by
    rw [integral_scalarComplexGaussian, ← integral_const_mul]
    simp_rw [hd]
    rw [integral_const_mul, integral_scalarGaussianDensity_weight (coneConditionalVariance_pos hL)]
  have hp : 0 < scalarComplexDensity x *
      (∫ y, coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0]
        ∂scalarComplexGaussian) := by
    rw [he]
    have hu := coneSchurU_pos hL
    have hp := scalarGaussianDensity_pos (coneSchurFirst_bounds hL).1 0 x
    have hv := coneConditionalVariance_pos hL
    have hn := Complex.normSq_nonneg (star (coneSchurCross L) / (coneSchurFirst L : ℂ) * x)
    unfold sourceEta
    positivity
  exact (mul_pos_iff_of_pos_left (scalarComplexDensity_pos x)).mp hp

theorem integrable_cone_ray {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) :
    Integrable (fun p : ℂ × ℂ ↦ coneRadialWeight p.1 * coneRadialWeight p.2 *
      overlapGaussianRatio L ![p.1, 0] ![p.2, 0])
      (scalarComplexGaussian.prod scalarComplexGaussian) := by
  have hi (x : ℂ) : Integrable (fun y ↦ coneRadialWeight y *
      overlapGaussianRatio L ![x, 0] ![y, 0]) scalarComplexGaussian := by
    by_contra h
    have hp := integral_cone_ray_inner_pos hL x
    rw [integral_undef h] at hp
    exact (lt_irrefl 0) hp
  have ho : Integrable (fun x ↦ coneRadialWeight x *
      (∫ y, coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0]
        ∂scalarComplexGaussian)) scalarComplexGaussian := by
    by_contra h
    have he := integral_cone_ray hL
    rw [integral_undef h] at he
    exact (coneRayMoment_pos hL).ne' he.symm
  apply (integrable_prod_iff
    (by apply Continuous.aestronglyMeasurable
        unfold coneRadialWeight overlapGaussianRatio coneInner sourceRadiusSq
        fun_prop)).mpr
  constructor
  · exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [mul_assoc] using (hi x).const_mul (coneRadialWeight x)
  · have he (x y : ℂ) :
        ‖coneRadialWeight x * coneRadialWeight y *
          overlapGaussianRatio L ![x, 0] ![y, 0]‖ =
        coneRadialWeight x *
          (coneRadialWeight y * overlapGaussianRatio L ![x, 0] ![y, 0]) := by
      rw [Real.norm_eq_abs, abs_of_pos
        (mul_pos (mul_pos (coneRadialWeight_pos x) (coneRadialWeight_pos y))
          (overlapGaussianRatio_pos hL _ _)), mul_assoc]
    simpa only [he, integral_const_mul] using ho

theorem integral_cone_ray_prod {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) :
    (∫ p : ℂ × ℂ, coneRadialWeight p.1 * coneRadialWeight p.2 *
      overlapGaussianRatio L ![p.1, 0] ![p.2, 0]
      ∂scalarComplexGaussian.prod scalarComplexGaussian) = coneRayMoment L := by
  rw [integral_prod _ (integrable_cone_ray hL)]
  simp_rw [mul_assoc, integral_const_mul]
  exact integral_cone_ray hL

end ConeRayIntegral

end NLA.FR05
