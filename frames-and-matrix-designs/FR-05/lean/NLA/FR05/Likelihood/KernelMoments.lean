import NLA.FR05.Likelihood.SourceKernelMarginals
import NLA.FR05.Cone.ConeCorrelation

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Real Matrix
open scoped BigOperators ENNReal

namespace NLA.FR05

theorem integral_sourceDensityLaw_normSq {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (i : Fin 2) :
    (∫ z, Complex.normSq (z i) ∂sourceDensityLaw a M) = sourceVariance M := by
  have h : (∫ z, z i * star (z i) ∂sourceDensityLaw a M) = (sourceVariance M : ℂ) := by
    rw [integral_sourceDensityLaw_complex]
    simpa using integral_sourceDensity_coordinate_conj_product hM a i i
  simp only [Complex.star_def, Complex.mul_conj, integral_complex_ofReal] at h
  exact_mod_cast h

theorem integral_sourceDensityLaw_cross {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (c : ℂ) :
    (∫ z, (c * (z 0 * star (z 1))).re ∂sourceDensityLaw a M) = 0 := by
  have hi := (integrable_coordinate_conj_product (sourceDensityLaw_integrable_radius hM a) 0 1).const_mul c
  have hr := integral_re hi
  simp only [RCLike.re_eq_complex_re] at hr
  rw [hr, integral_const_mul]
  have h : (∫ z, z 0 * star (z 1) ∂sourceDensityLaw a M) = 0 := by
    rw [integral_sourceDensityLaw_complex]
    simpa using integral_sourceDensity_coordinate_conj_product hM a 0 1
  rw [h]
  simp

theorem coneInner_normSq_expansion (z v : Fin 2 → ℂ) :
    Complex.normSq (coneInner z v) =
      Complex.normSq (v 0) * Complex.normSq (z 0) +
      Complex.normSq (v 1) * Complex.normSq (z 1) +
      2 * ((star (v 0) * v 1) * (z 0 * star (z 1))).re := by
  simp [coneInner, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem integrable_coneInner_normSq {μ : Measure (Fin 2 → ℂ)}
    (hμ : Integrable sourceRadiusSq μ) (v : Fin 2 → ℂ) :
    Integrable (fun z ↦ Complex.normSq (coneInner z v)) μ := by
  apply (hμ.mul_const (sourceRadiusSq v)).mono'
    (by apply Continuous.aestronglyMeasurable; unfold coneInner; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact coneInner_cauchy z v

theorem integral_sourceDensityLaw_coneInner_normSq {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (v : Fin 2 → ℂ) :
    (∫ z, Complex.normSq (coneInner z v) ∂sourceDensityLaw a M) =
      sourceVariance M * sourceRadiusSq v := by
  have hS := sourceDensityLaw_integrable_radius hM a
  have h0 := (integrable_coordinate_normSq hS 0).const_mul (Complex.normSq (v 0))
  have h1 := (integrable_coordinate_normSq hS 1).const_mul (Complex.normSq (v 1))
  have hc : Integrable (fun z ↦ (2 : ℝ) * ((star (v 0) * v 1) * (z 0 * star (z 1))).re)
      (sourceDensityLaw a M) :=
    ((integrable_coordinate_conj_product hS 0 1).const_mul (star (v 0) * v 1)).re.const_mul (2 : ℝ)
  simp_rw [coneInner_normSq_expansion]
  have hs : Integrable (fun z ↦ Complex.normSq (v 0) * Complex.normSq (z 0) +
      Complex.normSq (v 1) * Complex.normSq (z 1)) (sourceDensityLaw a M) := h0.add h1
  rw [integral_add hs hc, integral_add h0 h1]
  simp only [integral_const_mul, integral_sourceDensityLaw_normSq hM,
    integral_sourceDensityLaw_cross hM, mul_zero, add_zero]
  unfold sourceRadiusSq
  ring

theorem integrable_coneInner_re_sq {μ : Measure (Fin 2 → ℂ)}
    (hμ : Integrable sourceRadiusSq μ) (v : Fin 2 → ℂ) :
    Integrable (fun z ↦ (coneInner z v).re ^ 2) μ := by
  apply (integrable_coneInner_normSq hμ v).mono'
    (by apply Continuous.aestronglyMeasurable; unfold coneInner; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg (coneInner z v).im]

theorem integral_sourceDensityLaw_coneInner_re_sq {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (v : Fin 2 → ℂ) :
    (∫ z, (coneInner z v).re ^ 2 ∂sourceDensityLaw a M) =
      sourceVariance M * sourceRadiusSq v / 2 := by
  have hS := sourceDensityLaw_integrable_radius hM a
  have hir := integrable_coneInner_re_sq hS v
  have hii : Integrable (fun z ↦ (coneInner z v).im ^ 2) (sourceDensityLaw a M) := by
    apply (integrable_coneInner_normSq hS v).mono'
      (by apply Continuous.aestronglyMeasurable; unfold coneInner; fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg (coneInner z v).re]
  have hp := sourceDensityLaw_map_coordinatePhase a M (fun _ ↦ Complex.I) (by intro j; norm_num)
  have he := integral_map (μ := sourceDensityLaw a M)
    (φ := coordinatePhase (fun _ ↦ Complex.I))
    (f := fun z ↦ (coneInner z v).re ^ 2)
    (by apply Measurable.aemeasurable; unfold coordinatePhase; fun_prop)
    (by apply Continuous.aestronglyMeasurable; unfold coneInner; fun_prop)
  rw [hp] at he
  have hr (z : Fin 2 → ℂ) :
      (coneInner (coordinatePhase (fun _ ↦ Complex.I) z) v).re = (coneInner z v).im := by
    simp [coneInner, coordinatePhase, Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [hr] at he
  have hn := integral_sourceDensityLaw_coneInner_normSq hM a v
  have hn' : (∫ z, Complex.normSq (coneInner z v) ∂sourceDensityLaw a M) =
      (∫ z, (coneInner z v).re ^ 2 ∂sourceDensityLaw a M) +
        ∫ z, (coneInner z v).im ^ 2 ∂sourceDensityLaw a M := by
    rw [← integral_add hir hii]
    apply integral_congr_ae
    filter_upwards with z
    simp [Complex.normSq_apply, pow_two]
  linarith

theorem sourceRadiusSq_mulVec_rows (K : SourceOverlapMatrix) (z : Fin 2 → ℂ) :
    sourceRadiusSq (K *ᵥ z) =
      Complex.normSq (coneInner z (fun j ↦ star (K 0 j))) +
      Complex.normSq (coneInner z (fun j ↦ star (K 1 j))) := by
  simp [sourceRadiusSq, coneInner, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem integrable_radius_mulVec {μ : Measure (Fin 2 → ℂ)}
    (hμ : Integrable sourceRadiusSq μ) (K : SourceOverlapMatrix) :
    Integrable (fun z ↦ sourceRadiusSq (K *ᵥ z)) μ := by
  simp_rw [sourceRadiusSq_mulVec_rows]
  exact (integrable_coneInner_normSq hμ _).add (integrable_coneInner_normSq hμ _)

theorem integral_sourceDensityLaw_radius_mulVec {M : ℕ} (hM : 2 ≤ M)
    (a : SourceDensityKind) (K : SourceOverlapMatrix) :
    (∫ z, sourceRadiusSq (K *ᵥ z) ∂sourceDensityLaw a M) =
      sourceVariance M * overlapFrobeniusSq K := by
  have hS := sourceDensityLaw_integrable_radius hM a
  simp_rw [sourceRadiusSq_mulVec_rows]
  rw [integral_add (integrable_coneInner_normSq hS _) (integrable_coneInner_normSq hS _),
    integral_sourceDensityLaw_coneInner_normSq hM, integral_sourceDensityLaw_coneInner_normSq hM]
  simp [sourceRadiusSq, overlapFrobeniusSq, Fin.sum_univ_two]
  ring

def kernelCross (K : SourceOverlapMatrix) (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℝ :=
  (coneInner p.1 (K *ᵥ p.2)).re

def kernelQuadratic (K : SourceOverlapMatrix) (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℝ :=
  overlapFrobeniusSq K - sourceRadiusSq (Kᴴ *ᵥ p.1) -
    sourceRadiusSq (K *ᵥ p.2) + 2 * kernelCross K p ^ 2

theorem overlapFrobeniusSq_conjTranspose (K : SourceOverlapMatrix) :
    overlapFrobeniusSq Kᴴ = overlapFrobeniusSq K := by
  simp [overlapFrobeniusSq, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

theorem kernelCross_sq_le (K : SourceOverlapMatrix) (z w : Fin 2 → ℂ) :
    kernelCross K (z, w) ^ 2 ≤ overlapFrobeniusSq K * (sourceRadiusSq z * sourceRadiusSq w) := by
  have hc := coneInner_cauchy z (K *ᵥ w)
  have hk := sourceRadiusSq_mulVec_le_frobenius K w
  have hp := mul_le_mul_of_nonneg_left hk (sourceRadiusSq_nonneg z)
  have hr : (coneInner z (K *ᵥ w)).re ^ 2 ≤ Complex.normSq (coneInner z (K *ᵥ w)) := by
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg (coneInner z (K *ᵥ w)).im]
  unfold kernelCross
  dsimp only
  nlinarith

theorem integrable_kernelCross_sq {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    Integrable (fun p ↦ kernelCross K p ^ 2) ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) := by
  apply (((sourceDensityLaw_integrable_radius hM a).mul_prod
    (sourceDensityLaw_integrable_radius hM b)).const_mul (overlapFrobeniusSq K)).mono'
    (by apply Continuous.aestronglyMeasurable; unfold kernelCross coneInner; fun_prop)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact kernelCross_sq_le K p.1 p.2

theorem integral_kernelCross_sq {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    (∫ p, kernelCross K p ^ 2 ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M)) =
      sourceVariance M ^ 2 * overlapFrobeniusSq K / 2 := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  let : IsProbabilityMeasure (sourceDensityLaw b M) := isProbabilityMeasure_sourceDensityLaw hM b
  rw [integral_prod_symm _ (integrable_kernelCross_sq hM a b K)]
  simp_rw [kernelCross, integral_sourceDensityLaw_coneInner_re_sq hM]
  rw [integral_div, integral_const_mul, integral_sourceDensityLaw_radius_mulVec hM]
  ring

theorem integrable_kernelQuadratic {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    Integrable (kernelQuadratic K) ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  let : IsProbabilityMeasure (sourceDensityLaw b M) := isProbabilityMeasure_sourceDensityLaw hM b
  exact (((integrable_const _).sub
    ((integrable_radius_mulVec (sourceDensityLaw_integrable_radius hM a) Kᴴ).comp_fst _)).sub
    ((integrable_radius_mulVec (sourceDensityLaw_integrable_radius hM b) K).comp_snd _)).add
    ((integrable_kernelCross_sq hM a b K).const_mul 2)

theorem integral_kernelQuadratic {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    (∫ p, kernelQuadratic K p ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M)) =
      (1 - sourceVariance M) ^ 2 * overlapFrobeniusSq K := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  let : IsProbabilityMeasure (sourceDensityLaw b M) := isProbabilityMeasure_sourceDensityLaw hM b
  have hleft : Integrable (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦
      sourceRadiusSq (Kᴴ *ᵥ p.1)) ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) :=
    (integrable_radius_mulVec (sourceDensityLaw_integrable_radius hM a) Kᴴ).comp_fst _
  have hright : Integrable (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦
      sourceRadiusSq (K *ᵥ p.2)) ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) :=
    (integrable_radius_mulVec (sourceDensityLaw_integrable_radius hM b) K).comp_snd _
  have hfirst : Integrable (fun p ↦ overlapFrobeniusSq K -
      sourceRadiusSq (Kᴴ *ᵥ p.1) - sourceRadiusSq (K *ᵥ p.2))
      ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) :=
    ((integrable_const _).sub hleft).sub hright
  have hbase : Integrable (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦
      overlapFrobeniusSq K - sourceRadiusSq (Kᴴ *ᵥ p.1))
      ((sourceDensityLaw a M).prod (sourceDensityLaw b M)) :=
    (integrable_const _).sub hleft
  unfold kernelQuadratic
  rw [integral_add hfirst ((integrable_kernelCross_sq hM a b K).const_mul 2),
    integral_sub hbase hright,
    integral_sub (integrable_const (overlapFrobeniusSq K)) hleft, integral_const_mul,
    integral_kernelCross_sq hM, integral_fun_fst (fun z ↦ sourceRadiusSq (Kᴴ *ᵥ z)),
    integral_fun_snd (fun w ↦ sourceRadiusSq (K *ᵥ w))]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_sourceDensityLaw_radius_mulVec hM, overlapFrobeniusSq_conjTranspose]
  ring

theorem integral_kernel_second_order {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    (∫ p, 1 + kernelQuadratic K p ∂(sourceDensityLaw a M).prod (sourceDensityLaw b M)) =
      1 + (1 - sourceVariance M) ^ 2 * overlapFrobeniusSq K := by
  let : IsProbabilityMeasure (sourceDensityLaw a M) := isProbabilityMeasure_sourceDensityLaw hM a
  let : IsProbabilityMeasure (sourceDensityLaw b M) := isProbabilityMeasure_sourceDensityLaw hM b
  rw [integral_add (integrable_const _) (integrable_kernelQuadratic hM a b K),
    integral_kernelQuadratic hM]
  simp


end NLA.FR05
