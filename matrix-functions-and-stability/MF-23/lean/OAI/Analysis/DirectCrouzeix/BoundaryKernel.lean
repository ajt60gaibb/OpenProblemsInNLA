import OAI.Analysis.DirectCrouzeix.FaberPolynomials

namespace OAI

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem continuous_circle_integral {α : Type u_108} {E : Type u_109} [TopologicalSpace α]
    [FirstCountableTopology α] [LocallyCompactSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → Angle → E} (hf : Continuous f.uncurry) :
    Continuous (fun x => ∫ t, f x t ∂angularMeasure) := by
  simpa using continuous_parametric_integral_of_continuous (μ := angularMeasure) hf isCompact_univ

theorem continuous_slice_left {α : Type u_110} {β : Type u_111} {E : Type u_112}
    [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace E] (f : α → β → E) (hf : Continuous f.uncurry) (y : β) :
    Continuous (fun x => f x y) := by
  simpa only [Function.comp_def,Function.uncurry] using! hf.comp (continuous_id.prodMk continuous_const)

theorem continuous_slice_right {α : Type u_113} {β : Type u_114} {E : Type u_115}
    [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace E] (f : α → β → E) (hf : Continuous f.uncurry) (x : α) :
    Continuous (f x) := by
  simpa only [Function.comp_def,Function.uncurry] using! hf.comp (continuous_const.prodMk continuous_id)

theorem fourierCoeff_integral_swap {E : Type u_116} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : Angle → Angle → E)
    (hf : Continuous f.uncurry) (k : ℤ) :
    fourierCoeff (fun s => ∫ t, f t s ∂angularMeasure) k =
      ∫ t, fourierCoeff (f t) k ∂angularMeasure := by
  unfold fourierCoeff
  simp_rw [← integral_smul]
  apply (integral_integral_swap _).symm
  exact integrable_of_continuous_compact _
    (((fourier (-k)).continuous.comp continuous_snd).smul hf)

theorem fourierCoeff_conjugate (f : Angle → ℂ) (k : ℤ) :
    fourierCoeff (fun t => conj (f t)) k = conj (fourierCoeff f (-k)) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp []

def boundary (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ := exterior c g (unitPoint t)

def boundaryCorrection (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℂ :=
  correction c g ((unitPoint t)⁻¹) ((unitPoint s)⁻¹)

def boundaryCoefficient (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (s : Angle) : ℂ :=
  fourierCoeff (fun t => boundaryCorrection c g t s) (-(k:ℤ))

def boundaryKernel (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℝ :=
  1 + 2*(boundaryCorrection c g t s).re

theorem unitPoint_ne_zero (t : Angle) : unitPoint t ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [unitPoint_norm]; norm_num)

theorem unitPoint_inv_mem {R : ℝ} (hR : 1 < R) (t : Angle) :
    (unitPoint t)⁻¹ ∈ ball (0:ℂ) R := by
  simpa only [mem_ball,dist_zero_right,norm_inv,unitPoint_norm,inv_one] using hR

theorem continuous_boundary {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (c : ℂ) : Continuous (boundary c g) := by
  have hi : Continuous (fun t => (unitPoint t)⁻¹) := unitPoint_continuous.inv₀ unitPoint_ne_zero
  exact (continuous_const.mul unitPoint_continuous).add
    (hg.continuousOn.comp_continuous hi (unitPoint_inv_mem hR))

theorem continuous_boundaryCorrection {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    Continuous (boundaryCorrection c g).uncurry := by
  have hi : Continuous (fun t => (unitPoint t)⁻¹) := unitPoint_continuous.inv₀ unitPoint_ne_zero
  let f : Angle × Angle → ℂ × ℂ := fun p => ((unitPoint p.1)⁻¹,(unitPoint p.2)⁻¹)
  have hf : Continuous f := (hi.comp continuous_fst).prodMk (hi.comp continuous_snd)
  have hmaps : MapsTo f univ (ball 0 R ×ˢ ball 0 R) :=
    fun p _ => ⟨unitPoint_inv_mem hR p.1,unitPoint_inv_mem hR p.2⟩
  have he : (boundaryCorrection c g).uncurry = (fun p : ℂ × ℂ => correction c g p.1 p.2) ∘ f := rfl
  rw [he]
  exact (continuousOn_correction isOpen_ball (convex_ball 0 R) hg hH).comp_continuous hf
    (fun p => hmaps (mem_univ p))

theorem continuous_boundaryCoefficient {c : ℂ} {g : ℂ → ℂ}
    (hS : Continuous (boundaryCorrection c g).uncurry) (k : ℕ) :
    Continuous (boundaryCoefficient c g k) := by
  have hs : Continuous (fun p : Angle × Angle => boundaryCorrection c g p.2 p.1) := by
    simpa only [Function.uncurry,Function.comp_def] using! hS.comp continuous_swap
  have hf : Continuous (fun p : Angle × Angle => fourier (-(-(k:ℤ))) p.2) :=
    (fourier (-(-(k:ℤ)))).continuous.comp continuous_snd
  have hh := continuous_circle_integral (f := fun s t => fourier (-(-(k:ℤ))) t • boundaryCorrection c g t s)
    (hf.smul hs)
  exact hh

theorem boundaryCorrection_left_coeff {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (s : Angle) (j : ℤ) :
    fourierCoeff (fun t => boundaryCorrection c g t s) j =
      if j ≤ 0 then taylorCoeff (fun u => correction c g u ((unitPoint s)⁻¹)) (-j).toNat else 0 := by
  exact fourierCoeff_of_antianalytic hR
    (analyticOnNhd_correction_left isOpen_ball (convex_ball 0 R) hg (unitPoint_inv_mem hR s)
      (fun u hu => hH u hu _ (unitPoint_inv_mem hR s))) j

theorem boundaryCorrection_right_coeff {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (t : Angle) (j : ℤ) :
    fourierCoeff (boundaryCorrection c g t) j =
      if j ≤ 0 then taylorCoeff (correction c g ((unitPoint t)⁻¹)) (-j).toNat else 0 := by
  exact fourierCoeff_of_antianalytic hR
    (analyticOnNhd_correction_right isOpen_ball (convex_ball 0 R) hg (unitPoint_inv_mem hR t)
      (fun v hv => hH _ (unitPoint_inv_mem hR t) v hv)) j

theorem boundaryCoefficient_eq_taylor {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (s : Angle) :
    boundaryCoefficient c g k s = taylorCoeff (fun u => correction c g u ((unitPoint s)⁻¹)) k := by
  simp [boundaryCoefficient,boundaryCorrection_left_coeff hR hg hH]

theorem boundaryCoefficient_zero {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) (s : Angle) :
    boundaryCoefficient c g 0 s = 0 := by
  rw [boundaryCoefficient_eq_taylor hR hg hH]; simp

theorem faberBasis_boundary {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (s : Angle) :
    (faberBasis c g k).eval (boundary c g s) = fourier (k:ℤ) s + boundaryCoefficient c g k s := by
  rw [boundaryCoefficient_eq_taylor hR hg hH]
  have he := faberBasis_exterior (by linarith : 0 < R) hg hc (unitPoint_inv_mem hR s)
    (inv_ne_zero (unitPoint_ne_zero s)) (fun u hu => hH u hu _ (unitPoint_inv_mem hR s)) k
  simpa only [inv_inv,unitPoint_pow,boundary] using he

theorem boundaryCoefficient_no_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (j : ℤ) (hj : 0 ≤ j) :
    fourierCoeff (boundaryCoefficient c g k) j = 0 := by
  have hS := continuous_boundaryCorrection hR hg hH
  have hcont : Continuous (fun p : Angle × Angle => fourier (k:ℤ) p.1 * boundaryCorrection c g p.1 p.2) :=
    ((fourier (k:ℤ)).continuous.comp continuous_fst).mul hS
  change fourierCoeff (fun s => ∫ t, fourier (-(-(k:ℤ))) t • boundaryCorrection c g t s ∂angularMeasure) j = 0
  simp only [neg_neg,smul_eq_mul]
  rw [fourierCoeff_integral_swap (fun t s => fourier (k:ℤ) t * boundaryCorrection c g t s) hcont]
  have hr (t : Angle) : fourierCoeff (boundaryCorrection c g t) j = 0 := by
    rw [boundaryCorrection_right_coeff hR hg hH]
    by_cases hj0 : j = 0
    · subst j; simp
    · rw [ite_eq_right (by omega)]
  have he (t : Angle) : fourierCoeff (fun s => fourier (k:ℤ) t * boundaryCorrection c g t s) j = 0 := by
    simp only [fourierCoeff,smul_eq_mul]
    rw [show (fun s => fourier (-j) s * (fourier (k:ℤ) t * boundaryCorrection c g t s)) =
      (fun s => fourier (k:ℤ) t * (fourier (-j) s * boundaryCorrection c g t s)) by funext s; ring,
      integral_const_mul]
    change fourier (k:ℤ) t * fourierCoeff (boundaryCorrection c g t) j = 0
    rw [hr,mul_zero]
  simp only [he,integral_zero]

theorem continuous_boundaryKernel {c : ℂ} {g : ℂ → ℂ}
    (hS : Continuous (boundaryCorrection c g).uncurry) : Continuous (boundaryKernel c g).uncurry := by
  exact continuous_const.add (continuous_const.mul (Complex.continuous_re.comp hS))

theorem boundaryCorrection_marginals {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    (∀ s, ∫ t, boundaryCorrection c g t s ∂angularMeasure = 0) ∧
      (∀ t, ∫ s, boundaryCorrection c g t s ∂angularMeasure = 0) := by
  constructor
  · intro s
    have he := boundaryCorrection_left_coeff hR hg hH s 0
    simpa [fourierCoeff] using he
  · intro t
    have he := boundaryCorrection_right_coeff hR hg hH t 0
    simpa [fourierCoeff] using he

theorem boundaryKernel_marginals {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    (∀ s, ∫ t, boundaryKernel c g t s ∂angularMeasure = 1) ∧
      (∀ t, ∫ s, boundaryKernel c g t s ∂angularMeasure = 1) := by
  have hS := continuous_boundaryCorrection hR hg hH
  have hm := boundaryCorrection_marginals hR hg hH
  have hint (f : Angle → ℂ) (hf : Continuous f) (hz : ∫ t, f t ∂angularMeasure = 0) :
      (∫ t, (1 + 2*(f t).re) ∂angularMeasure) = 1 := by
    have hfi := integrable_of_continuous_compact angularMeasure hf
    change (∫ t, (1 + 2*RCLike.re (f t)) ∂angularMeasure) = 1
    rw [integral_add (integrable_const 1) (hfi.re.const_mul 2),integral_const_mul,
      integral_re hfi,hz]
    simp
  constructor
  · intro s
    change (∫ t, 1+2*(boundaryCorrection c g t s).re ∂angularMeasure) = 1
    exact hint (fun t => boundaryCorrection c g t s) (continuous_slice_left _ hS s) (hm.1 s)
  · intro t
    change (∫ s, 1+2*(boundaryCorrection c g t s).re ∂angularMeasure) = 1
    exact hint (boundaryCorrection c g t) (continuous_slice_right _ hS t) (hm.2 t)

theorem boundaryKernel_complex (c : ℂ) (g : ℂ → ℂ) (t s : Angle) :
    (boundaryKernel c g t s : ℂ) = 1+boundaryCorrection c g t s+conj (boundaryCorrection c g t s) := by
  apply Complex.ext <;> simp [boundaryKernel] ; ring

theorem boundaryKernel_character {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (hk : k ≠ 0) (s : Angle) :
    (∫ t, (boundaryKernel c g t s : ℂ) * fourier (k:ℤ) t ∂angularMeasure) =
      boundaryCoefficient c g k s := by
  have hS : Continuous (fun t => boundaryCorrection c g t s) :=
    continuous_slice_left _ (continuous_boundaryCorrection hR hg hH) s
  have hf := (fourier (T := (1:ℝ)) (k:ℤ)).continuous
  have h1 : (∫ t : Angle, fourier (k:ℤ) t ∂angularMeasure) = 0 := by
    have he := integral_character_smul 0 (k:ℤ) (1:ℂ)
    simpa [hk] using he
  have h2 : (∫ t, boundaryCorrection c g t s * fourier (k:ℤ) t ∂angularMeasure) =
      boundaryCoefficient c g k s := by
    simp only [boundaryCoefficient,fourierCoeff,neg_neg,smul_eq_mul]
    congr 1; funext t; ring
  have h3 : (∫ t, conj (boundaryCorrection c g t s) * fourier (k:ℤ) t ∂angularMeasure) = 0 := by
    have he := fourierCoeff_conjugate (fun t => boundaryCorrection c g t s) (-(k:ℤ))
    rw [neg_neg,boundaryCorrection_left_coeff hR hg hH,ite_eq_right (by omega)] at he
    simpa only [fourierCoeff,neg_neg,smul_eq_mul,mul_comm,map_zero] using he
  have hi1 : Integrable (fun t : Angle => fourier (k:ℤ) t) angularMeasure := integrable_of_continuous_compact _ hf
  have hi2 : Integrable (fun t : Angle => boundaryCorrection c g t s * fourier (k:ℤ) t) angularMeasure :=
    integrable_of_continuous_compact _ (hS.mul hf)
  have hi3 : Integrable (fun t : Angle => conj (boundaryCorrection c g t s) * fourier (k:ℤ) t) angularMeasure := by
    simpa only [starRingEnd_apply] using! integrable_of_continuous_compact angularMeasure (hS.star.mul hf)
  have ha := integral_add (hi1.add hi2) hi3
  have hb := integral_add hi1 hi2
  simp only [Pi.add_apply] at ha hb
  simp_rw [boundaryKernel_complex,add_mul,one_mul]
  rw [ha,hb,h1,h2,h3,zero_add,add_zero]

end DirectCrouzeix.Faber

end

end

end OAI
