import NLA.FR05.Cone.ConeCorrelation

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Real
open scoped ENNReal

namespace NLA.FR05

theorem scalarComplexGaussian_map_normSq :
    scalarComplexGaussian.map Complex.normSq = expMeasure 1 := by
  rw [scalarComplexGaussian, Measure.map_map (by fun_prop) continuous_scalarComplexMap.measurable]
  convert gaussian_pair_radius_law using 2
  funext p
  simp [scalarComplexMap, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  nlinarith

theorem standardComplexGaussianTail_map_first :
    (standardComplexGaussianTail 2).map (fun z ↦ z 0) = scalarComplexGaussian := by
  have h := congrArg (Measure.map Prod.fst) standardComplexGaussianTail_map_pair
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod] at h
  simpa [Function.comp_def] using h

theorem scalarComplexGaussian_map_phase (c : ℂ) (hc : Complex.normSq c = 1) :
    scalarComplexGaussian.map (fun z ↦ c * z) = scalarComplexGaussian := by
  have h := standardComplexGaussianTail_map_coordinatePhase (fun _ : Fin 2 ↦ c) (fun _ ↦ hc)
  have h' := congrArg (Measure.map (fun z : Signal 2 ↦ z 0)) h
  rw [Measure.map_map (by fun_prop) (by unfold coordinatePhase; fun_prop),
    standardComplexGaussianTail_map_first] at h'
  rw [← standardComplexGaussianTail_map_first,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rw [standardComplexGaussianTail_map_first]
  simpa [Function.comp_def, coordinatePhase] using h'

theorem conePhasePoint_add (θ ψ : ConePhase) :
    conePhasePoint (θ + ψ) = conePhasePoint θ * conePhasePoint ψ := by
  simp [conePhasePoint, AddCircle.toCircle_add]

theorem conePhasePoint_arg (z : ℂ) :
    (‖z‖ : ℂ) * conePhasePoint (z.arg : ConePhase) = z := by
  simp [conePhasePoint, AddCircle.toCircle_apply_mk, Circle.coe_exp,
    ne_of_gt Real.pi_pos, Complex.norm_mul_exp_arg_mul_I]

theorem integral_phase_mul_eq_radius (f : ℂ → ℝ) (z : ℂ) :
    (∫ θ : ConePhase, f (conePhasePoint θ * z) ∂AddCircle.haarAddCircle) =
      ∫ θ : ConePhase, f ((Real.sqrt (Complex.normSq z) : ℂ) * conePhasePoint θ)
        ∂AddCircle.haarAddCircle := by
  have hs : Real.sqrt (Complex.normSq z) = ‖z‖ := by rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hs]
  have he (θ : ConePhase) : conePhasePoint θ * z =
      (‖z‖ : ℂ) * conePhasePoint (θ + (z.arg : ConePhase)) := by
    rw [conePhasePoint_add]
    rw [← mul_assoc, mul_comm (‖z‖ : ℂ), mul_assoc, conePhasePoint_arg]
  simp_rw [he]
  exact integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun θ : ConePhase ↦ f ((‖z‖ : ℂ) * conePhasePoint θ)) (z.arg : ConePhase)

def scalarPolarMap (p : ℝ × ConePhase) : ℂ :=
  (Real.sqrt p.1 : ℂ) * conePhasePoint p.2

@[fun_prop]
theorem continuous_scalarPolarMap : Continuous scalarPolarMap := by
  unfold scalarPolarMap
  fun_prop

theorem scalarComplexGaussian_eq_polar :
    scalarComplexGaussian = ((expMeasure 1).prod AddCircle.haarAddCircle).map scalarPolarMap := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  let : IsProbabilityMeasure (((expMeasure 1).prod AddCircle.haarAddCircle).map scalarPolarMap) :=
    Measure.isProbabilityMeasure_map continuous_scalarPolarMap.measurable.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hprod : Integrable (fun p : ℂ × ConePhase ↦ f (conePhasePoint p.2 * p.1))
      (scalarComplexGaussian.prod AddCircle.haarAddCircle) := by
    apply Integrable.of_bound (by apply Continuous.aestronglyMeasurable; fun_prop) ‖f‖
    exact Filter.Eventually.of_forall fun p ↦ f.norm_coe_le_norm _
  have hpolar : Integrable (fun p : ℝ × ConePhase ↦ f (scalarPolarMap p))
      ((expMeasure 1).prod AddCircle.haarAddCircle) := by
    apply Integrable.of_bound (by apply Continuous.aestronglyMeasurable; fun_prop) ‖f‖
    exact Filter.Eventually.of_forall fun p ↦ f.norm_coe_le_norm _
  have hrotate (θ : ConePhase) :
      (∫ z, f (conePhasePoint θ * z) ∂scalarComplexGaussian) =
        ∫ z, f z ∂scalarComplexGaussian := by
    have h := integral_map (φ := fun z ↦ conePhasePoint θ * z)
      (μ := scalarComplexGaussian) (by apply Measurable.aemeasurable; fun_prop)
      (f := f) f.continuous.aestronglyMeasurable
    rw [scalarComplexGaussian_map_phase _ (by simp [Complex.normSq_eq_norm_sq])] at h
    exact h.symm
  have hg : Measurable (fun s : ℝ ↦ ∫ θ : ConePhase,
      f ((Real.sqrt s : ℂ) * conePhasePoint θ) ∂AddCircle.haarAddCircle) := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    apply Continuous.stronglyMeasurable
    fun_prop
  calc
    _ = ∫ θ : ConePhase, ∫ z, f (conePhasePoint θ * z)
        ∂scalarComplexGaussian ∂AddCircle.haarAddCircle := by simp_rw [hrotate]; simp
    _ = ∫ z, ∫ θ : ConePhase, f (conePhasePoint θ * z)
        ∂AddCircle.haarAddCircle ∂scalarComplexGaussian := integral_integral_swap hprod.swap
    _ = ∫ z, ∫ θ : ConePhase, f ((Real.sqrt (Complex.normSq z) : ℂ) * conePhasePoint θ)
        ∂AddCircle.haarAddCircle ∂scalarComplexGaussian := by simp_rw [integral_phase_mul_eq_radius]
    _ = ∫ s, ∫ θ : ConePhase, f ((Real.sqrt s : ℂ) * conePhasePoint θ)
        ∂AddCircle.haarAddCircle ∂expMeasure 1 := by
      rw [← integral_map (φ := Complex.normSq) (μ := scalarComplexGaussian)
        (by fun_prop) hg.aestronglyMeasurable, scalarComplexGaussian_map_normSq]
    _ = _ := by
      rw [integral_map continuous_scalarPolarMap.measurable.aemeasurable f.continuous.aestronglyMeasurable,
        integral_prod _ hpolar]
      rfl

end NLA.FR05
