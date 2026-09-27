import NLA.FR05.Gaussian.ComplexGaussianDensity

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory Complex Real
open scoped ENNReal

namespace NLA.FR05

theorem scalarGaussianDensity_nonneg (a : ℝ) (m z : ℂ) (ha : 0 ≤ a) :
    0 ≤ scalarGaussianDensity a m z := by
  unfold scalarGaussianDensity
  positivity

theorem scalarComplexGaussian_map_affine {a : ℝ} (ha : 0 < a) (m : ℂ) :
    scalarComplexGaussian.map (fun z ↦ Real.sqrt a • z + m) =
      volume.withDensity (fun z ↦ ENNReal.ofReal (scalarGaussianDensity a m z)) := by
  have hmass : (volume.withDensity (fun z ↦ ENNReal.ofReal (scalarGaussianDensity a m z))) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_scalarGaussianDensity ha m)
        (Filter.Eventually.of_forall fun z ↦ scalarGaussianDensity_nonneg a m z ha.le),
      scalarGaussianDensity_integral ha m]
    norm_num
  let : IsProbabilityMeasure (volume.withDensity
      (fun z ↦ ENNReal.ofReal (scalarGaussianDensity a m z))) := ⟨hmass⟩
  let : IsProbabilityMeasure (scalarComplexGaussian.map (fun z ↦ Real.sqrt a • z + m)) :=
    Measure.isProbabilityMeasure_map (by apply Measurable.aemeasurable; fun_prop)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (by apply Measurable.aemeasurable; fun_prop) f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by unfold scalarGaussianDensity; fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (scalarGaussianDensity_nonneg a m _ ha.le), smul_eq_mul]
  exact (integral_scalarGaussianDensity ha m f).symm

theorem lintegral_scalarGaussianDensity {a : ℝ} (ha : 0 < a) (m : ℂ)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℂ, ENNReal.ofReal (scalarGaussianDensity a m z) * f z) =
      ∫⁻ z, f (Real.sqrt a • z + m) ∂scalarComplexGaussian := by
  calc
    _ = ∫⁻ z, f z ∂volume.withDensity (fun z ↦ ENNReal.ofReal (scalarGaussianDensity a m z)) :=
      (lintegral_withDensity_eq_lintegral_mul (volume : Measure ℂ)
        (f := fun z ↦ ENNReal.ofReal (scalarGaussianDensity a m z))
        (by unfold scalarGaussianDensity; fun_prop) hf).symm
    _ = _ := by
      rw [← scalarComplexGaussian_map_affine ha m, lintegral_map hf (by fun_prop)]


theorem standardComplexGaussianTail_eq_map_pair :
    standardComplexGaussianTail 2 =
      (scalarComplexGaussian.prod scalarComplexGaussian).map
        (fun p : ℂ × ℂ ↦ ![p.1, p.2]) := by
  rw [standardComplexGaussianTail_eq_pi]
  exact (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ scalarComplexGaussian)).symm.map_eq.symm

theorem lintegral_standardComplexGaussianTail_two (f : Signal 2 → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, f z ∂standardComplexGaussianTail 2) =
      ∫⁻ x : ℂ, ∫⁻ y : ℂ,
        ENNReal.ofReal (scalarComplexDensity x) * ENNReal.ofReal (scalarComplexDensity y) *
          f ![x, y] := by
  rw [standardComplexGaussianTail_eq_map_pair, lintegral_map hf (by fun_prop),
    scalarComplexGaussian_eq_withDensity,
    prod_withDensity (by unfold scalarComplexDensity; fun_prop)
      (by unfold scalarComplexDensity; fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by unfold scalarComplexDensity; fun_prop)
      (by fun_prop), lintegral_prod _ (by apply Measurable.aemeasurable; dsimp; unfold scalarComplexDensity; fun_prop)]
  rfl


def triangularGaussian (a b : ℝ) (c : ℂ) (m ξ : Signal 2) : Signal 2 :=
  ![Real.sqrt a • ξ 0 + m 0,
    Real.sqrt b • ξ 1 + m 1 + c * (Real.sqrt a • ξ 0)]

def triangularGaussianDensity (a b : ℝ) (c : ℂ) (m w : Signal 2) : ℝ :=
  scalarGaussianDensity a (m 0) (w 0) *
    scalarGaussianDensity b (m 1 + c * (w 0 - m 0)) (w 1)

theorem lintegral_triangularGaussian {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c : ℂ) (m : Signal 2) (f : Signal 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : ℂ, ∫⁻ y : ℂ,
      ENNReal.ofReal (triangularGaussianDensity a b c m ![x, y]) * f ![x, y]) =
      ∫⁻ ξ, f (triangularGaussian a b c m ξ) ∂standardComplexGaussianTail 2 := by
  have he (x y : ℂ) : ENNReal.ofReal (triangularGaussianDensity a b c m ![x, y]) =
      ENNReal.ofReal (scalarGaussianDensity a (m 0) x) *
        ENNReal.ofReal (scalarGaussianDensity b (m 1 + c * (x - m 0)) y) := by
    simp only [triangularGaussianDensity, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, ENNReal.ofReal_mul (scalarGaussianDensity_nonneg a _ _ ha.le)]
  simp_rw [he, mul_assoc]
  have hinner (x : ℂ) :
      (∫⁻ y : ℂ, ENNReal.ofReal (scalarGaussianDensity a (m 0) x) *
        (ENNReal.ofReal (scalarGaussianDensity b (m 1 + c * (x - m 0)) y) * f ![x, y])) =
      ENNReal.ofReal (scalarGaussianDensity a (m 0) x) *
        ∫⁻ η, f ![x, Real.sqrt b • η + (m 1 + c * (x - m 0))] ∂scalarComplexGaussian := by
    rw [lintegral_const_mul _ (by unfold scalarGaussianDensity; fun_prop),
      lintegral_scalarGaussianDensity hb _ _ (by fun_prop)]
  simp_rw [hinner]
  rw [lintegral_scalarGaussianDensity ha (m 0) _
    (by apply Measurable.lintegral_prod_right; fun_prop)]
  rw [standardComplexGaussianTail_eq_map_pair,
    lintegral_map (by unfold triangularGaussian; fun_prop) (by fun_prop),
    lintegral_prod _ (by unfold triangularGaussian; fun_prop)]
  congr 1
  funext ξ
  congr 1
  funext η
  simp [triangularGaussian, add_assoc]

end NLA.FR05
