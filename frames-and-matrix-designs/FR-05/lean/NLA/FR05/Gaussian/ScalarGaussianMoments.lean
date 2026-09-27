import NLA.FR05.Gaussian.ComplexGaussianDensity

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Real

namespace NLA.FR05

theorem measurePreserving_gaussian_coordinate (i : Fin 2) :
    MeasurePreserving (fun z : Fin 2 → ℂ ↦ z i)
      (standardComplexGaussianTail 2) scalarComplexGaussian := by
  rw [standardComplexGaussianTail_eq_pi]
  exact measurePreserving_eval (μ := fun _ : Fin 2 ↦ scalarComplexGaussian) i

theorem integral_scalarGaussian_coordinate (i : Fin 2) (f : ℂ → ℝ) (hf : Continuous f) :
    (∫ z, f z ∂scalarComplexGaussian) =
      ∫ z, f (z i) ∂standardComplexGaussianTail 2 := by
  have h := measurePreserving_gaussian_coordinate i
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]

theorem integrable_scalarGaussian_normSq_pow (k : ℕ) :
    Integrable (fun z ↦ Complex.normSq z ^ k) scalarComplexGaussian := by
  apply ((measurePreserving_gaussian_coordinate 0).integrable_comp
    (by apply Continuous.aestronglyMeasurable; fun_prop)).mp
  exact integrable_gaussian_normSq_pow 0 k

theorem integral_scalarGaussian_normSq :
    (∫ z, Complex.normSq z ∂scalarComplexGaussian) = 1 := by
  rw [integral_scalarGaussian_coordinate 0 _ (by fun_prop), integral_gaussian_normSq]

theorem integral_scalarGaussian_normSq_sq :
    (∫ z, Complex.normSq z ^ 2 ∂scalarComplexGaussian) = 2 := by
  rw [integral_scalarGaussian_coordinate 0 _ (by fun_prop), integral_gaussian_normSq_sq]

theorem integrable_scalarGaussian_re (c : ℂ) :
    Integrable (fun z ↦ (c * z).re) scalarComplexGaussian := by
  have hn : Integrable (fun z ↦ Complex.normSq z) scalarComplexGaussian := by
    simpa using integrable_scalarGaussian_normSq_pow 1
  apply (((integrable_const 1).add hn).const_mul ‖c‖).mono'
    (by apply Continuous.aestronglyMeasurable; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ‖c * z‖ := Complex.abs_re_le_norm _
    _ = ‖c‖ * ‖z‖ := norm_mul _ _
    _ ≤ ‖c‖ * (1 + Complex.normSq z) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg c, sq_nonneg (‖z‖ - 1),
        mul_nonneg (norm_nonneg c) (sq_nonneg (‖z‖ - 1))]

theorem integral_scalarGaussian_re (c : ℂ) :
    (∫ z, (c * z).re ∂scalarComplexGaussian) = 0 := by
  rw [integral_scalarGaussian_coordinate 1 _ (by fun_prop)]
  apply integral_gaussian_odd_second _ (by fun_prop)
  intro z
  simp [coordinatePhase]

theorem scalarGaussian_affine_normSq (b c z : ℂ) :
    Complex.normSq (b + c * z) =
      Complex.normSq b + Complex.normSq c * Complex.normSq z +
        2 * (star b * c * z).re := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem integrable_scalarGaussian_affine_normSq (b c : ℂ) :
    Integrable (fun z ↦ Complex.normSq (b + c * z)) scalarComplexGaussian := by
  have hn : Integrable (fun z ↦ Complex.normSq z) scalarComplexGaussian := by
    simpa using integrable_scalarGaussian_normSq_pow 1
  simp_rw [scalarGaussian_affine_normSq]
  exact ((integrable_const _).add (hn.const_mul _)).add
    ((integrable_scalarGaussian_re (star b * c)).const_mul _)

theorem integral_scalarGaussian_affine_normSq (b c : ℂ) :
    (∫ z, Complex.normSq (b + c * z) ∂scalarComplexGaussian) =
      Complex.normSq b + Complex.normSq c := by
  have hn : Integrable (fun z ↦ Complex.normSq z) scalarComplexGaussian := by
    simpa using integrable_scalarGaussian_normSq_pow 1
  simp_rw [scalarGaussian_affine_normSq]
  have hfirst : Integrable (fun z ↦ Complex.normSq b + Complex.normSq c * Complex.normSq z)
      scalarComplexGaussian := (integrable_const _).add (hn.const_mul _)
  rw [integral_add hfirst ((integrable_scalarGaussian_re (star b * c)).const_mul 2),
    integral_add (integrable_const (Complex.normSq b)) (hn.const_mul (Complex.normSq c))]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_scalarGaussian_normSq, integral_scalarGaussian_re, mul_one, mul_zero, add_zero]

theorem integral_scalarGaussian_radial_weights (a b c : ℂ) (η : ℝ) :
    (∫ x, ((1 - η) + η * Complex.normSq (a * x)) *
      (∫ y, ((1 - η) + η * Complex.normSq (b * x + c * y))
        ∂scalarComplexGaussian) ∂scalarComplexGaussian) =
      (1 - η) ^ 2 + η * (1 - η) * (Complex.normSq a + Complex.normSq b + Complex.normSq c) +
        η ^ 2 * Complex.normSq a * (2 * Complex.normSq b + Complex.normSq c) := by
  have hn : Integrable (fun z ↦ Complex.normSq z) scalarComplexGaussian := by
    simpa using integrable_scalarGaussian_normSq_pow 1
  have hinner (x : ℂ) :
      (∫ y, ((1 - η) + η * Complex.normSq (b * x + c * y)) ∂scalarComplexGaussian) =
        (1 - η) + η * (Complex.normSq b * Complex.normSq x + Complex.normSq c) := by
    rw [integral_add (integrable_const _) ((integrable_scalarGaussian_affine_normSq _ _).const_mul _)]
    simp [integral_const_mul, integral_scalarGaussian_affine_normSq, Complex.normSq_mul]
  simp_rw [hinner, Complex.normSq_mul]
  have he (x : ℂ) :
      ((1 - η) + η * (Complex.normSq a * Complex.normSq x)) *
        ((1 - η) + η * (Complex.normSq b * Complex.normSq x + Complex.normSq c)) =
      ((1 - η) ^ 2 + η * (1 - η) * Complex.normSq c) +
        (η * (1 - η) * (Complex.normSq a + Complex.normSq b) +
          η ^ 2 * Complex.normSq a * Complex.normSq c) * Complex.normSq x +
        (η ^ 2 * Complex.normSq a * Complex.normSq b) * Complex.normSq x ^ 2 := by ring
  simp_rw [he]
  have hfirst : Integrable (fun x ↦ ((1 - η) ^ 2 + η * (1 - η) * Complex.normSq c) +
      (η * (1 - η) * (Complex.normSq a + Complex.normSq b) +
        η ^ 2 * Complex.normSq a * Complex.normSq c) * Complex.normSq x)
      scalarComplexGaussian := (integrable_const _).add (hn.const_mul _)
  rw [integral_add hfirst
    ((integrable_scalarGaussian_normSq_pow 2).const_mul (η ^ 2 * Complex.normSq a * Complex.normSq b)),
    integral_add (integrable_const ((1 - η) ^ 2 + η * (1 - η) * Complex.normSq c))
      (hn.const_mul (η * (1 - η) * (Complex.normSq a + Complex.normSq b) +
        η ^ 2 * Complex.normSq a * Complex.normSq c))]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_scalarGaussian_normSq, integral_scalarGaussian_normSq_sq]
  ring

end NLA.FR05
