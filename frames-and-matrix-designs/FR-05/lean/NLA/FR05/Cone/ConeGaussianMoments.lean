import NLA.FR05.Gaussian.GaussianSquaredRadius
import NLA.FR05.Densities.SourceSymmetry
import NLA.FR05.Cone.ConePhaseAverages

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Real Set
open scoped ENNReal NNReal

namespace NLA.FR05

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem integrable_gaussian_radius_pow (k : ℕ) :
    Integrable (fun z : Fin 2 → ℂ ↦ sourceRadiusSq z ^ k) (standardComplexGaussianTail 2) := by
  simpa only [sourceRadiusSq_eq_signalEnergy, zero_mul, Real.exp_zero, mul_one] using
    integrable_energy_pow_mul_exp_standardComplexGaussian 2 k (t := 0) (by norm_num)

theorem integral_expMeasure_one_id : (∫ s : ℝ, s ∂expMeasure 1) = 1 := by
  rw [integral_expMeasure_one, ← integral_Ici_eq_integral_Ioi]
  have h := (exponential_quadratic_tail (δ := 0) (r := 1) (a := 0) (b := 1) (c := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  simpa using h

theorem integral_expMeasure_one_sq : (∫ s : ℝ, s ^ 2 ∂expMeasure 1) = 2 := by
  rw [integral_expMeasure_one, ← integral_Ici_eq_integral_Ioi]
  have h := (exponential_quadratic_tail (δ := 0) (r := 1) (a := 0) (b := 0) (c := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  simpa using h

theorem integral_gaussian_normSq (i : Fin 2) :
    (∫ z, Complex.normSq (z i) ∂standardComplexGaussianTail 2) = 1 := by
  have he (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
      (∫ z, f (Complex.normSq (z 0), Complex.normSq (z 1)) ∂standardComplexGaussianTail 2) =
        ∫ p, f p ∂(expMeasure 1).prod (expMeasure 1) := by
    rw [← standardComplexGaussianTail_map_normSq_pair,
      integral_map (by fun_prop) hf.aestronglyMeasurable]
  fin_cases i
  · dsimp
    have h := he (fun p ↦ p.1) (by fun_prop)
    dsimp only at h
    rw [h, integral_fun_fst (fun x : ℝ ↦ x)]
    simp [integral_expMeasure_one_id]
  · dsimp
    have h := he (fun p ↦ p.2) (by fun_prop)
    dsimp only at h
    rw [h, integral_fun_snd (fun x : ℝ ↦ x)]
    simp [integral_expMeasure_one_id]

theorem integral_gaussian_normSq_sq (i : Fin 2) :
    (∫ z, Complex.normSq (z i) ^ 2 ∂standardComplexGaussianTail 2) = 2 := by
  have he (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
      (∫ z, f (Complex.normSq (z 0), Complex.normSq (z 1)) ∂standardComplexGaussianTail 2) =
        ∫ p, f p ∂(expMeasure 1).prod (expMeasure 1) := by
    rw [← standardComplexGaussianTail_map_normSq_pair,
      integral_map (by fun_prop) hf.aestronglyMeasurable]
  fin_cases i
  · dsimp
    have h := he (fun p ↦ p.1 ^ 2) (by fun_prop)
    dsimp only at h
    rw [h, integral_fun_fst (fun x : ℝ ↦ x ^ 2)]
    simp [integral_expMeasure_one_sq]
  · dsimp
    have h := he (fun p ↦ p.2 ^ 2) (by fun_prop)
    dsimp only at h
    rw [h, integral_fun_snd (fun x : ℝ ↦ x ^ 2)]
    simp [integral_expMeasure_one_sq]

theorem integral_gaussian_normSq_mul :
    (∫ z, Complex.normSq (z 0) * Complex.normSq (z 1) ∂standardComplexGaussianTail 2) = 1 := by
  have he := integral_map (μ := standardComplexGaussianTail 2)
    (φ := fun z : Fin 2 → ℂ ↦ (Complex.normSq (z 0), Complex.normSq (z 1)))
    (f := fun p : ℝ × ℝ ↦ p.1 * p.2) (by fun_prop)
    (by apply Continuous.aestronglyMeasurable; fun_prop)
  rw [standardComplexGaussianTail_map_normSq_pair] at he
  rw [← he, integral_prod_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x)]
  simp [integral_expMeasure_one_id]

theorem integral_gaussian_odd_second (f : (Fin 2 → ℂ) → ℝ) (hf : Continuous f)
    (hodd : ∀ z, f (coordinatePhase ![1, -1] z) = -f z) :
    (∫ z, f z ∂standardComplexGaussianTail 2) = 0 := by
  have hc : ∀ j : Fin 2, Complex.normSq (![1, -1] j) = 1 := by intro j; fin_cases j <;> simp
  have hm := standardComplexGaussianTail_map_coordinatePhase ![1, -1] hc
  have hi := integral_map (μ := standardComplexGaussianTail 2)
    (φ := coordinatePhase ![1, -1]) (f := f)
    (by apply Measurable.aemeasurable; unfold coordinatePhase; fun_prop) hf.aestronglyMeasurable
  rw [hm] at hi
  simp_rw [hodd] at hi
  rw [integral_neg] at hi
  linarith

theorem integral_gaussian_cross (c : ℂ) (k : ℕ) :
    (∫ z, Complex.normSq (z 0) ^ k * (c * z 0 * star (z 1)).re
      ∂standardComplexGaussianTail 2) = 0 := by
  apply integral_gaussian_odd_second _ (by fun_prop)
  intro z
  simp [coordinatePhase]
  ring

theorem integrable_gaussian_normSq_pow (i : Fin 2) (k : ℕ) :
    Integrable (fun z ↦ Complex.normSq (z i) ^ k) (standardComplexGaussianTail 2) := by
  apply (integrable_gaussian_radius_pow k).mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg _) _)]
  exact pow_le_pow_left₀ (Complex.normSq_nonneg _) (normSq_le_sourceRadiusSq z i) _

theorem integrable_gaussian_normSq_mul :
    Integrable (fun z ↦ Complex.normSq (z 0) * Complex.normSq (z 1)) (standardComplexGaussianTail 2) := by
  apply (integrable_gaussian_radius_pow 2).mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  have h0 := normSq_le_sourceRadiusSq z 0
  have h1 := normSq_le_sourceRadiusSq z 1
  nlinarith [Complex.normSq_nonneg (z 0), Complex.normSq_nonneg (z 1)]

theorem integrable_gaussian_cross (c : ℂ) (k : ℕ) :
    Integrable (fun z ↦ Complex.normSq (z 0) ^ k * (c * z 0 * star (z 1)).re)
      (standardComplexGaussianTail 2) := by
  apply ((integrable_gaussian_radius_pow (k + 1)).const_mul ‖c‖).mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
  filter_upwards with z
  have hp : ‖z 0‖ * ‖z 1‖ ≤ sourceRadiusSq z := by
    unfold sourceRadiusSq
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖z 0‖ - ‖z 1‖)]
  have hc : |(c * z 0 * star (z 1)).re| ≤ ‖c‖ * sourceRadiusSq z := by
    apply le_trans (Complex.abs_re_le_norm _)
    rw [norm_mul, norm_mul, norm_star]
    nlinarith [norm_nonneg c, mul_le_mul_of_nonneg_left hp (norm_nonneg c)]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg _) _)]
  calc
    _ ≤ sourceRadiusSq z ^ k * (‖c‖ * sourceRadiusSq z) :=
      mul_le_mul (pow_le_pow_left₀ (Complex.normSq_nonneg _) (normSq_le_sourceRadiusSq z 0) _)
        hc (abs_nonneg _) (pow_nonneg (sourceRadiusSq_nonneg _) _)
    _ = _ := by rw [pow_succ]; ring

theorem normSq_linear_pair (b c x y : ℂ) :
    Complex.normSq (b * x + c * y) =
      Complex.normSq b * Complex.normSq x + Complex.normSq c * Complex.normSq y +
        2 * (b * star c * x * star y).re := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem integrable_gaussian_linear_normSq (b c : ℂ) :
    Integrable (fun z ↦ Complex.normSq (b * z 0 + c * z 1))
      (standardComplexGaussianTail 2) := by
  simp_rw [normSq_linear_pair]
  have h0 : Integrable (fun z ↦ Complex.normSq (z 0)) (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_normSq_pow 0 1
  have h1 : Integrable (fun z ↦ Complex.normSq (z 1)) (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_normSq_pow 1 1
  have hc : Integrable (fun z ↦ (b * star c * z 0 * star (z 1)).re)
      (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_cross (b * star c) 0
  exact ((h0.const_mul _).add (h1.const_mul _)).add (hc.const_mul _)

theorem integral_gaussian_linear_normSq (b c : ℂ) :
    (∫ z, Complex.normSq (b * z 0 + c * z 1) ∂standardComplexGaussianTail 2) =
      Complex.normSq b + Complex.normSq c := by
  have h0 : Integrable (fun z ↦ Complex.normSq (z 0)) (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_normSq_pow 0 1
  have h1 : Integrable (fun z ↦ Complex.normSq (z 1)) (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_normSq_pow 1 1
  have hc : Integrable (fun z ↦ (b * star c * z 0 * star (z 1)).re)
      (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_cross (b * star c) 0
  have hc0 : (∫ z, (b * star c * z 0 * star (z 1)).re ∂standardComplexGaussianTail 2) = 0 := by
    simpa using integral_gaussian_cross (b * star c) 0
  have hsum : Integrable (fun z ↦ Complex.normSq b * Complex.normSq (z 0) +
      Complex.normSq c * Complex.normSq (z 1)) (standardComplexGaussianTail 2) :=
    (h0.const_mul _).add (h1.const_mul _)
  simp_rw [normSq_linear_pair]
  rw [integral_add hsum (hc.const_mul _), integral_add (h0.const_mul _) (h1.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_gaussian_normSq, integral_gaussian_normSq, hc0]
  ring

theorem gaussian_fourth_linear_identity (a b c : ℂ) (z : Fin 2 → ℂ) :
    Complex.normSq (a * z 0) * Complex.normSq (b * z 0 + c * z 1) =
      Complex.normSq a * Complex.normSq b * Complex.normSq (z 0) ^ 2 +
      Complex.normSq a * Complex.normSq c * (Complex.normSq (z 0) * Complex.normSq (z 1)) +
      (2 * Complex.normSq a) * (Complex.normSq (z 0) * (b * star c * z 0 * star (z 1)).re) := by
  rw [normSq_linear_pair, Complex.normSq_mul]
  ring

theorem integrable_gaussian_fourth_linear (a b c : ℂ) :
    Integrable (fun z ↦ Complex.normSq (a * z 0) * Complex.normSq (b * z 0 + c * z 1))
      (standardComplexGaussianTail 2) := by
  simp_rw [gaussian_fourth_linear_identity]
  have hc : Integrable (fun z ↦ Complex.normSq (z 0) * (b * star c * z 0 * star (z 1)).re)
      (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_cross (b * star c) 1
  exact (((integrable_gaussian_normSq_pow 0 2).const_mul _).add
    (integrable_gaussian_normSq_mul.const_mul _)).add (hc.const_mul _)

theorem integral_gaussian_fourth_linear (a b c : ℂ) :
    (∫ z, Complex.normSq (a * z 0) * Complex.normSq (b * z 0 + c * z 1)
      ∂standardComplexGaussianTail 2) =
        Complex.normSq a * (2 * Complex.normSq b + Complex.normSq c) := by
  have hc : Integrable (fun z ↦ Complex.normSq (z 0) * (b * star c * z 0 * star (z 1)).re)
      (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_cross (b * star c) 1
  have hc0 : (∫ z, Complex.normSq (z 0) * (b * star c * z 0 * star (z 1)).re
      ∂standardComplexGaussianTail 2) = 0 := by
    simpa using integral_gaussian_cross (b * star c) 1
  have hsum : Integrable (fun z ↦
      Complex.normSq a * Complex.normSq b * Complex.normSq (z 0) ^ 2 +
      Complex.normSq a * Complex.normSq c * (Complex.normSq (z 0) * Complex.normSq (z 1)))
      (standardComplexGaussianTail 2) :=
    ((integrable_gaussian_normSq_pow 0 2).const_mul _).add (integrable_gaussian_normSq_mul.const_mul _)
  simp_rw [gaussian_fourth_linear_identity]
  rw [integral_add hsum (hc.const_mul _),
    integral_add ((integrable_gaussian_normSq_pow 0 2).const_mul _)
      (integrable_gaussian_normSq_mul.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_gaussian_normSq_sq, integral_gaussian_normSq_mul, hc0]
  ring

theorem integral_gaussian_radial_weights (a b c : ℂ) (η : ℝ) :
    (∫ z, ((1 - η) + η * Complex.normSq (a * z 0)) *
      ((1 - η) + η * Complex.normSq (b * z 0 + c * z 1)) ∂standardComplexGaussianTail 2) =
      (1 - η) ^ 2 + η * (1 - η) * (Complex.normSq a + Complex.normSq b + Complex.normSq c) +
        η ^ 2 * Complex.normSq a * (2 * Complex.normSq b + Complex.normSq c) := by
  have hX : Integrable (fun z ↦ Complex.normSq (a * z 0)) (standardComplexGaussianTail 2) := by
    simpa using integrable_gaussian_linear_normSq a 0
  have hY := integrable_gaussian_linear_normSq b c
  have hXY := integrable_gaussian_fourth_linear a b c
  have he (z : Fin 2 → ℂ) :
      ((1 - η) + η * Complex.normSq (a * z 0)) * ((1 - η) + η * Complex.normSq (b * z 0 + c * z 1)) =
        ((1 - η) ^ 2 + η * (1 - η) * (Complex.normSq (a * z 0) + Complex.normSq (b * z 0 + c * z 1))) +
          η ^ 2 * (Complex.normSq (a * z 0) * Complex.normSq (b * z 0 + c * z 1)) := by ring
  have hsum : Integrable (fun z ↦ Complex.normSq (a * z 0) + Complex.normSq (b * z 0 + c * z 1))
      (standardComplexGaussianTail 2) := hX.add hY
  have hfirst : Integrable (fun z ↦ (1 - η) ^ 2 +
      η * (1 - η) * (Complex.normSq (a * z 0) + Complex.normSq (b * z 0 + c * z 1)))
      (standardComplexGaussianTail 2) := (integrable_const _).add (hsum.const_mul _)
  simp_rw [he]
  rw [integral_add hfirst (hXY.const_mul _),
    integral_add (integrable_const _) (hsum.const_mul _), integral_const,
    integral_const_mul, integral_const_mul, integral_add hX hY]
  have hXi : (∫ z, Complex.normSq (a * z 0) ∂standardComplexGaussianTail 2) = Complex.normSq a := by
    simpa using integral_gaussian_linear_normSq a 0
  rw [hXi, integral_gaussian_linear_normSq, integral_gaussian_fourth_linear]
  simp only [probReal_univ, one_smul]
  ring

end NLA.FR05
