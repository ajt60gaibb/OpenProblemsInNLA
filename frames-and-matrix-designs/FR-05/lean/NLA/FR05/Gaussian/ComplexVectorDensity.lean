import NLA.FR05.Gaussian.SimplexProjectionLaw
import NLA.FR05.Gaussian.GaussianConditionalDensity

/-!
# Complex vector densities and elliptical sphere laws

The sections develop `ComplexVectorDensity`, `EllipticalSphereDensity`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section ComplexVectorDensity

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

theorem lintegral_complexVector_two (f : Signal 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z) = ∫⁻ x : ℂ, ∫⁻ y : ℂ, f ![x, y] := by
  have hv := (volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℂ)).symm.map_eq
  rw [← hv, lintegral_map hf (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℂ)).symm.measurable,
    Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
  rfl

theorem standardComplexGaussianTail_two_eq_density :
    standardComplexGaussianTail 2 = volume.withDensity
      (fun z ↦ ENNReal.ofReal (Real.pi⁻¹ ^ 2 * Real.exp (-signalEnergy z))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_standardComplexGaussianTail_two f hf,
    lintegral_withDensity_eq_lintegral_mul _ (by unfold signalEnergy squaredEuclideanNorm; fun_prop) hf,
    lintegral_complexVector_two _ (by unfold signalEnergy squaredEuclideanNorm; fun_prop)]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  congr 1
  rw [← ENNReal.ofReal_mul (by unfold scalarComplexDensity; positivity)]
  congr 1
  simp only [scalarComplexDensity, signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [neg_add, Real.exp_add]
  ring

def sphereLebesgueDensity (n : ℕ) (z : Signal 2) : ℝ :=
  if signalEnergy z < 1 then
    ((n + 1) * (n + 2) : ℝ) / Real.pi ^ 2 * (1 - signalEnergy z) ^ n else 0

@[fun_prop]
theorem measurable_sphereLebesgueDensity (n : ℕ) : Measurable (sphereLebesgueDensity n) := by
  unfold sphereLebesgueDensity
  apply Measurable.ite
  · apply measurableSet_lt _ measurable_const
    apply Continuous.measurable
    unfold signalEnergy squaredEuclideanNorm
    fun_prop
  · unfold signalEnergy squaredEuclideanNorm
    fun_prop
  · exact measurable_const

theorem sphereProjectionLaw_eq_density (n : ℕ) :
    sphereProjectionLaw n =
      volume.withDensity (fun z ↦ ENNReal.ofReal (sphereLebesgueDensity n z)) := by
  unfold sphereProjectionLaw
  rw [standardComplexGaussianTail_two_eq_density]
  have hm :
      (volume.withDensity
        (fun z : Signal 2 ↦ ENNReal.ofReal (Real.pi⁻¹ ^ 2 * Real.exp (-signalEnergy z)))).withDensity
        (fun z ↦ ENNReal.ofReal (sphereRadialWeight n (signalEnergy z))) =
      volume.withDensity (fun z ↦
        ENNReal.ofReal (Real.pi⁻¹ ^ 2 * Real.exp (-signalEnergy z)) *
          ENNReal.ofReal (sphereRadialWeight n (signalEnergy z))) :=
    (withDensity_mul _ (by unfold signalEnergy squaredEuclideanNorm; fun_prop)
      (by apply Measurable.ennreal_ofReal
          apply (measurable_sphereRadialWeight n).comp
          apply Continuous.measurable
          unfold signalEnergy squaredEuclideanNorm
          fun_prop)).symm
  rw [hm]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold sphereLebesgueDensity sphereRadialWeight
  split_ifs
  · rw [Real.exp_neg]
    field_simp
  · ring

end ComplexVectorDensity

section EllipticalSphereDensity

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

def ellipticalEnergy (a b : ℝ) (c : ℂ) (w : Signal 2) : ℝ :=
  Complex.normSq (w 0) / a + Complex.normSq (w 1 - c * w 0) / b

@[fun_prop]
theorem continuous_ellipticalEnergy (a b : ℝ) (c : ℂ) :
    Continuous (ellipticalEnergy a b c) := by
  unfold ellipticalEnergy
  fun_prop

theorem ellipticalEnergy_triangularGaussian {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c : ℂ) (z : Signal 2) :
    ellipticalEnergy a b c (triangularGaussian a b c 0 z) = signalEnergy z := by
  have he : Real.sqrt b • z 1 + c * (Real.sqrt a • z 0) -
      c * (Real.sqrt a • z 0) = Real.sqrt b • z 1 := by ring
  simp only [ellipticalEnergy, triangularGaussian, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, he]
  simp only [Complex.normSq_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  simp [signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two, Complex.normSq_eq_norm_sq,
    ha.ne', hb.ne']

theorem triangularGaussianDensity_eq_elliptical {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c : ℂ) (w : Signal 2) :
    triangularGaussianDensity a b c 0 w =
      (Real.pi ^ 2 * a * b)⁻¹ * Real.exp (-ellipticalEnergy a b c w) := by
  unfold triangularGaussianDensity scalarGaussianDensity ellipticalEnergy
  simp only [Pi.zero_apply, sub_zero, zero_add, neg_add, Real.exp_add]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne']

def ellipticalSphereDensity (n : ℕ) (a b : ℝ) (c : ℂ) (w : Signal 2) : ℝ :=
  if ellipticalEnergy a b c w < 1 then
    ((n + 1) * (n + 2) : ℝ) / (Real.pi ^ 2 * a * b) *
      (1 - ellipticalEnergy a b c w) ^ n else 0

@[fun_prop]
theorem measurable_ellipticalSphereDensity (n : ℕ) (a b : ℝ) (c : ℂ) :
    Measurable (ellipticalSphereDensity n a b c) := by
  unfold ellipticalSphereDensity
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) <;> fun_prop

theorem ellipticalSphereDensity_eq_weight (n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c : ℂ) (w : Signal 2) :
    ENNReal.ofReal (ellipticalSphereDensity n a b c w) =
      ENNReal.ofReal (triangularGaussianDensity a b c 0 w) *
        ENNReal.ofReal (sphereRadialWeight n (ellipticalEnergy a b c w)) := by
  rw [triangularGaussianDensity_eq_elliptical ha hb,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold ellipticalSphereDensity sphereRadialWeight
  split_ifs
  · rw [Real.exp_neg]
    field_simp
  · ring

theorem sphereProjectionLaw_map_triangular (n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c : ℂ) :
    (sphereProjectionLaw n).map (triangularGaussian a b c 0) =
      volume.withDensity (fun w ↦ ENNReal.ofReal (ellipticalSphereDensity n a b c w)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by unfold triangularGaussian; fun_prop),
    sphereProjectionLaw, lintegral_withDensity_eq_lintegral_mul _
      (g := fun z ↦ f (triangularGaussian a b c 0 z))
      (by apply Measurable.ennreal_ofReal
          apply (measurable_sphereRadialWeight n).comp
          apply Continuous.measurable
          unfold signalEnergy squaredEuclideanNorm
          fun_prop)
      (hf.comp (by unfold triangularGaussian; fun_prop)),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_ellipticalSphereDensity n a b c).ennreal_ofReal hf,
    lintegral_complexVector_two _ (by fun_prop)]
  simp only [Pi.mul_apply, ellipticalSphereDensity_eq_weight n ha hb, mul_assoc]
  rw [lintegral_triangularGaussian ha hb c 0
    (fun w ↦ ENNReal.ofReal (sphereRadialWeight n (ellipticalEnergy a b c w)) * f w)
    (by fun_prop)]
  simp_rw [ellipticalEnergy_triangularGaussian ha hb]

end EllipticalSphereDensity

end NLA.FR05
