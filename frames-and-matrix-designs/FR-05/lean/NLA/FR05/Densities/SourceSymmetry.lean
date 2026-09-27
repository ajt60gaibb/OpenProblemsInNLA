import NLA.FR05.Gaussian.GaussianGram
import NLA.FR05.Densities.SourceReferenceMoments

/-!
# Source symmetry and symmetric moments

The sections develop `SourceSymmetry`, `SourceSymmetricMoments`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section SourceSymmetry

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ENNReal

theorem map_withDensity_of_invariant {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (d : α → ℝ≥0∞) (T : α → α)
    (hd : Measurable d) (hT : Measurable T) (hμ : μ.map T = μ)
    (hinv : ∀ x, d (T x) = d x) :
    (μ.withDensity d).map T = μ.withDensity d := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf hT, lintegral_withDensity_eq_lintegral_mul μ hd (g := fun x ↦ f (T x)) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul μ hd hf]
  calc
    _ = ∫⁻ x, d (T x) * f (T x) ∂μ := by simp only [Pi.mul_apply, hinv]
    _ = ∫⁻ x, (d * f) x ∂μ.map T := (lintegral_map (hd.mul hf) hT).symm
    _ = _ := by rw [hμ]

def coordinatePhase {n : ℕ} (c : Fin n → ℂ) (z : Signal n) : Signal n :=
  fun j ↦ c j * z j

theorem standardComplexGaussianTail_map_coordinatePhase {n : ℕ} (c : Fin n → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) :
    (standardComplexGaussianTail n).map (coordinatePhase c) =
      standardComplexGaussianTail n := by
  have hU : (Matrix.diagonal c)ᴴ * Matrix.diagonal c = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp [← Complex.normSq_eq_conj_mul_self, hc]
    · simp [h]
  convert standardComplexGaussianTail_map_unitary (Matrix.diagonal c) hU using 2
  funext z
  ext j
  simp [coordinatePhase, diagonal_conjTranspose, mulVec_diagonal]

theorem sourceRadiusSq_coordinatePhase (c : Fin 2 → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) (z : Signal 2) :
    sourceRadiusSq (coordinatePhase c z) = sourceRadiusSq z := by
  simp [sourceRadiusSq, coordinatePhase, Complex.normSq_mul, hc]

theorem sourceImbalance_coordinatePhase (c : Fin 2 → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) (z : Signal 2) :
    sourceImbalance (coordinatePhase c z) = sourceImbalance z := by
  simp [sourceImbalance, sourceRadiusSq, coordinatePhase, Complex.normSq_mul, hc]

theorem coordinatePhase_eq_zero_iff (c : Fin 2 → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) (z : Signal 2) :
    coordinatePhase c z = 0 ↔ z = 0 := by
  have hn (j) : c j ≠ 0 := by
    intro h
    simpa [h] using hc j
  simp [funext_iff, coordinatePhase, hn]

theorem sourceReferenceDensity_coordinatePhase (M : ℕ) (c : Fin 2 → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) (z : Signal 2) :
    sourceReferenceDensity M (coordinatePhase c z) = sourceReferenceDensity M z := by
  simp [sourceReferenceDensity, sourceRadiusSq_coordinatePhase c hc]

theorem sourcePlantedDensity_coordinatePhase (M : ℕ) (c : Fin 2 → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) (z : Signal 2) :
    sourcePlantedDensity M (coordinatePhase c z) = sourcePlantedDensity M z := by
  simp [sourcePlantedDensity, coordinatePhase_eq_zero_iff c hc,
    sourceRadiusSq_coordinatePhase c hc, sourceImbalance_coordinatePhase c hc]

theorem sourceReferenceLaw_map_coordinatePhase (M : ℕ) (c : Fin 2 → ℂ)
    (hc : ∀ j, Complex.normSq (c j) = 1) :
    (sourceReferenceLaw M).map (coordinatePhase c) = sourceReferenceLaw M := by
  apply map_withDensity_of_invariant
  · exact (measurable_sourceReferenceDensity M).ennreal_ofReal
  · unfold coordinatePhase; fun_prop
  · exact standardComplexGaussianTail_map_coordinatePhase c hc
  · intro z
    rw [sourceReferenceDensity_coordinatePhase M c hc]

def swapTwo (z : Signal 2) : Signal 2 := ![z 1, z 0]

theorem standardComplexGaussianTail_map_swapTwo :
    (standardComplexGaussianTail 2).map swapTwo = standardComplexGaussianTail 2 := by
  let U : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  have hU : Uᴴ * U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [U, Matrix.mul_apply, Fin.sum_univ_two]
  convert standardComplexGaussianTail_map_unitary U hU using 2
  funext z
  ext j
  fin_cases j <;> simp [U, swapTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sourceRadiusSq_swapTwo (z : Signal 2) :
    sourceRadiusSq (swapTwo z) = sourceRadiusSq z := by
  simp [sourceRadiusSq, swapTwo, add_comm]

theorem sourceImbalance_swapTwo (z : Signal 2) :
    sourceImbalance (swapTwo z) = -sourceImbalance z := by
  simp [sourceImbalance, sourceRadiusSq, swapTwo]
  ring

theorem swapTwo_eq_zero_iff (z : Signal 2) : swapTwo z = 0 ↔ z = 0 := by
  simp [swapTwo, funext_iff, Fin.forall_fin_two, and_comm]

theorem sourceReferenceDensity_swapTwo (M : ℕ) (z : Signal 2) :
    sourceReferenceDensity M (swapTwo z) = sourceReferenceDensity M z := by
  simp [sourceReferenceDensity, sourceRadiusSq_swapTwo]

theorem sourcePlantedDensity_swapTwo (M : ℕ) (z : Signal 2) :
    sourcePlantedDensity M (swapTwo z) = sourcePlantedDensity M z := by
  simp [sourcePlantedDensity, swapTwo_eq_zero_iff, sourceRadiusSq_swapTwo,
    sourceImbalance_swapTwo]

theorem sourceReferenceLaw_map_swapTwo (M : ℕ) :
    (sourceReferenceLaw M).map swapTwo = sourceReferenceLaw M := by
  apply map_withDensity_of_invariant
  · exact (measurable_sourceReferenceDensity M).ennreal_ofReal
  · unfold swapTwo; fun_prop
  · exact standardComplexGaussianTail_map_swapTwo
  · intro z
    rw [sourceReferenceDensity_swapTwo]

end SourceSymmetry

section SourceSymmetricMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem normSq_le_sourceRadiusSq (z : Signal 2) (i : Fin 2) :
    Complex.normSq (z i) ≤ sourceRadiusSq z := by
  fin_cases i
  · exact le_add_of_nonneg_right (Complex.normSq_nonneg _)
  · exact le_add_of_nonneg_left (Complex.normSq_nonneg _)

theorem integrable_coordinate_normSq {μ : Measure (Signal 2)}
    (hS : Integrable sourceRadiusSq μ) (i : Fin 2) :
    Integrable (fun z ↦ Complex.normSq (z i)) μ := by
  apply hS.mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
  exact Filter.Eventually.of_forall fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
    exact normSq_le_sourceRadiusSq z i

theorem integrable_coordinate {μ : Measure (Signal 2)} [IsFiniteMeasure μ]
    (hS : Integrable sourceRadiusSq μ) (i : Fin 2) :
    Integrable (fun z ↦ z i) μ := by
  apply (hS.add (integrable_const (1 : ℝ))).mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
  exact Filter.Eventually.of_forall fun z ↦ by
    change ‖z i‖ ≤ sourceRadiusSq z + 1
    have h := normSq_le_sourceRadiusSq z i
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [sq_nonneg (‖z i‖ - 1)]

theorem integrable_coordinate_product {μ : Measure (Signal 2)}
    (hS : Integrable sourceRadiusSq μ) (i j : Fin 2) :
    Integrable (fun z ↦ z i * z j) μ := by
  apply hS.mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
  exact Filter.Eventually.of_forall fun z ↦ by
    rw [norm_mul]
    have hi := normSq_le_sourceRadiusSq z i
    have hj := normSq_le_sourceRadiusSq z j
    rw [Complex.normSq_eq_norm_sq] at hi hj
    nlinarith [sq_nonneg (‖z i‖ - ‖z j‖)]

theorem integrable_coordinate_conj_product {μ : Measure (Signal 2)}
    (hS : Integrable sourceRadiusSq μ) (i j : Fin 2) :
    Integrable (fun z ↦ z i * star (z j)) μ := by
  apply hS.mono' (by apply Continuous.aestronglyMeasurable; fun_prop)
  exact Filter.Eventually.of_forall fun z ↦ by
    rw [norm_mul, norm_star]
    have hi := normSq_le_sourceRadiusSq z i
    have hj := normSq_le_sourceRadiusSq z j
    rw [Complex.normSq_eq_norm_sq] at hi hj
    nlinarith [sq_nonneg (‖z i‖ - ‖z j‖)]

theorem integral_coordinate_eq_zero_of_phase {μ : Measure (Signal 2)}
    (hphase : ∀ c : Fin 2 → ℂ, (∀ j, Complex.normSq (c j) = 1) →
      μ.map (coordinatePhase c) = μ) (i : Fin 2) :
    (∫ z, z i ∂μ) = 0 := by
  have hp := hphase (fun _ ↦ -1) (by intro j; norm_num)
  have hi := integral_map (μ := μ)
    (φ := coordinatePhase (fun _ ↦ -1)) (f := fun z ↦ z i)
    (by apply Measurable.aemeasurable; unfold coordinatePhase; fun_prop) (by apply Continuous.aestronglyMeasurable; fun_prop)
  rw [hp] at hi
  simp only [coordinatePhase, neg_one_mul, integral_neg] at hi
  linear_combination (1 / 2 : ℂ) * hi

theorem integral_coordinate_product_eq_zero_of_phase {μ : Measure (Signal 2)}
    (hphase : ∀ c : Fin 2 → ℂ, (∀ j, Complex.normSq (c j) = 1) →
      μ.map (coordinatePhase c) = μ) (i j : Fin 2) :
    (∫ z, z i * z j ∂μ) = 0 := by
  have hp := hphase (fun _ ↦ Complex.I) (by intro k; norm_num)
  have hi := integral_map (μ := μ)
    (φ := coordinatePhase (fun _ ↦ Complex.I)) (f := fun z ↦ z i * z j)
    (by apply Measurable.aemeasurable; unfold coordinatePhase; fun_prop) (by apply Continuous.aestronglyMeasurable; fun_prop)
  rw [hp] at hi
  have he (z : Signal 2) :
      coordinatePhase (fun _ ↦ Complex.I) z i *
        coordinatePhase (fun _ ↦ Complex.I) z j = -(z i * z j) := by
    dsimp [coordinatePhase]
    calc
      _ = (Complex.I * Complex.I) * (z i * z j) := by ring
      _ = _ := by simp
  simp_rw [he, integral_neg] at hi
  linear_combination (1 / 2 : ℂ) * hi

theorem integral_coordinate_conj_product_eq_zero_of_phase {μ : Measure (Signal 2)}
    (hphase : ∀ c : Fin 2 → ℂ, (∀ j, Complex.normSq (c j) = 1) →
      μ.map (coordinatePhase c) = μ) {i j : Fin 2} (hij : i ≠ j) :
    (∫ z, z i * star (z j) ∂μ) = 0 := by
  let c : Fin 2 → ℂ := fun k ↦ if k = i then -1 else 1
  have hp := hphase c (by intro k; dsimp [c]; split_ifs <;> norm_num)
  have hi := integral_map (μ := μ) (φ := coordinatePhase c)
    (f := fun z ↦ z i * star (z j))
    (by apply Measurable.aemeasurable; unfold coordinatePhase; fun_prop) (by apply Continuous.aestronglyMeasurable; fun_prop)
  rw [hp] at hi
  simp only [coordinatePhase, c, if_pos rfl, if_neg hij.symm,
    one_mul, neg_mul, integral_neg] at hi
  linear_combination (1 / 2 : ℂ) * hi

theorem integral_coordinate_normSq_eq_half {μ : Measure (Signal 2)}
    (hS : Integrable sourceRadiusSq μ) (hswap : μ.map swapTwo = μ) (i : Fin 2) :
    (∫ z, Complex.normSq (z i) ∂μ) = (∫ z, sourceRadiusSq z ∂μ) / 2 := by
  have hi := integral_map (μ := μ) (φ := swapTwo)
    (f := fun z ↦ Complex.normSq (z 0)) (by unfold swapTwo; fun_prop) (by apply Continuous.aestronglyMeasurable; fun_prop)
  rw [hswap] at hi
  simp only [swapTwo, Matrix.cons_val_zero] at hi
  have hs : (∫ z, sourceRadiusSq z ∂μ) =
      (∫ z, Complex.normSq (z 0) ∂μ) + ∫ z, Complex.normSq (z 1) ∂μ :=
    integral_add (integrable_coordinate_normSq hS 0) (integrable_coordinate_normSq hS 1)
  fin_cases i <;> dsimp <;> linarith

theorem integral_coordinate_covariance_of_symmetry {μ : Measure (Signal 2)}
    (hS : Integrable sourceRadiusSq μ)
    (hphase : ∀ c : Fin 2 → ℂ, (∀ j, Complex.normSq (c j) = 1) →
      μ.map (coordinatePhase c) = μ) (hswap : μ.map swapTwo = μ) (i j : Fin 2) :
    (∫ z, z i * star (z j) ∂μ) =
      if i = j then (((∫ z, sourceRadiusSq z ∂μ) / 2 : ℝ) : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Complex.star_def, Complex.mul_conj, integral_complex_ofReal,
      integral_coordinate_normSq_eq_half hS hswap]
  · rw [if_neg hij]
    exact integral_coordinate_conj_product_eq_zero_of_phase hphase hij

theorem sourceReferenceLaw_integrable_radius (M : ℕ) :
    Integrable sourceRadiusSq (sourceReferenceLaw M) := by
  simpa using integrable_radius_pow_sourceReferenceLaw M 1

theorem sourceReferenceLaw_centered (M : ℕ) (i : Fin 2) :
    (∫ z, z i ∂sourceReferenceLaw M) = 0 :=
  integral_coordinate_eq_zero_of_phase (sourceReferenceLaw_map_coordinatePhase M) i

theorem sourceReferenceLaw_pseudocovariance (M : ℕ) (i j : Fin 2) :
    (∫ z, z i * z j ∂sourceReferenceLaw M) = 0 :=
  integral_coordinate_product_eq_zero_of_phase (sourceReferenceLaw_map_coordinatePhase M) i j

theorem sourceReferenceLaw_covariance (M : ℕ) (i j : Fin 2) :
    (∫ z, z i * star (z j) ∂sourceReferenceLaw M) =
      if i = j then (sourceVariance M : ℂ) else 0 := by
  rw [integral_coordinate_covariance_of_symmetry (sourceReferenceLaw_integrable_radius M)
    (sourceReferenceLaw_map_coordinatePhase M) (sourceReferenceLaw_map_swapTwo M),
    integral_radius_sourceReferenceLaw]
  congr 1
  norm_num

end SourceSymmetricMoments

end NLA.FR05
