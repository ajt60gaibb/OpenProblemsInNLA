import OAI.Analysis.DirectCrouzeix.KernelContraction

namespace OAI

universe u_128 u_129

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def faberBoundarySeries {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, (faberBasis c g k).eval (boundary c g t) • C k

def boundaryRemainder {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, boundaryCoefficient c g k t • C k

def nonconstantCoefficients {N : ℕ} (C : Fin N → E) (k : Fin N) : E :=
  if (k:ℕ) = 0 then 0 else C k

theorem continuous_boundaryRemainder {E : Type u_128} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E)
    (hS : Continuous (boundaryCorrection c g).uncurry) : Continuous (boundaryRemainder c g C) := by
  exact continuous_finsetSum _ (fun k _ => (continuous_boundaryCoefficient hS k).smul continuous_const)

theorem faberBoundarySeries_decomp {E : Type u_128} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (t : Angle) :
    faberBoundarySeries c g C t = positiveSeries C t + boundaryRemainder c g C t := by
  simp only [faberBoundarySeries,faberBasis_boundary hR hg hc hH,add_smul,
    Finset.sum_add_distrib,positiveSeries,boundaryRemainder]

theorem boundaryRemainder_no_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (j : ℤ) (hj : 0 ≤ j) :
    fourierCoeff (boundaryRemainder c g C) j = 0 := by
  have hS := continuous_boundaryCorrection hR hg hH
  unfold boundaryRemainder
  rw [fourierCoeff_finite_smul _ (fun k => continuous_boundaryCoefficient hS k)]
  simp only [boundaryCoefficient_no_nonnegative hR hg hH _ j hj,zero_smul,Finset.sum_const_zero]

theorem boundaryKernel_action {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {N : ℕ} (C : Fin N → E) (s : Angle) :
    (∫ t, boundaryKernel c g t s • positiveSeries (nonconstantCoefficients C) t ∂angularMeasure) =
      boundaryRemainder c g C s := by
  have hK := continuous_slice_left _ (continuous_boundaryKernel (continuous_boundaryCorrection hR hg hH)) s
  simp only [positiveSeries,Finset.smul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : (k:ℕ) = 0
    · simp [nonconstantCoefficients,hk0,boundaryCoefficient_zero hR hg hH]
    · simp only [nonconstantCoefficients,ite_eq_right hk0]
      rw [show (fun t => boundaryKernel c g t s • (fourier (k:ℤ) t • C k)) =
        (fun t => ((boundaryKernel c g t s : ℂ)*fourier (k:ℤ) t) • C k) by
          funext t; rw [← smul_assoc,Complex.real_smul], integral_smul_const,
        boundaryKernel_character hR hg hH k hk0 s]
  · intro k hk
    exact integrable_of_continuous_compact _ (hK.smul ((fourier (k:ℤ)).continuous.smul continuous_const))

theorem faber_hilbert_coefficient_bounds {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hpositive : ∀ t s, 0 ≤ boundaryKernel c g t s)
    {N : ℕ} (C : Fin N → E) :
    (∑ k, ‖C k‖^2 ≤ ∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ∧
      ((∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ≤
        ∑ k : Fin N, (if (k:ℕ) = 0 then 1 else 2)*‖C k‖^2) := by
  have hS := continuous_boundaryCorrection hR hg hH
  have hr := continuous_boundaryRemainder c g C hS
  have he : (∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure := by
    simp_rw [faberBoundarySeries_decomp hR hg hc hH]
    exact energy_orthogonal_positiveSeries C _ hr (boundaryRemainder_no_nonnegative hR hg hH C)
  have hrnonneg : 0 ≤ ∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hrbound : (∫ t, ‖boundaryRemainder c g C t‖^2 ∂angularMeasure) ≤
      ∑ k, ‖nonconstantCoefficients C k‖^2 := by
    let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    have hm := boundaryKernel_marginals hR hg hH
    have ht := markov_kernel_contraction angularMeasure angularMeasure (boundaryKernel c g)
      (positiveSeries (nonconstantCoefficients C)) (continuous_boundaryKernel hS)
      (continuous_positiveSeries _) hpositive hm.1 hm.2
    simp_rw [boundaryKernel_action hR hg hH C,energy_positiveSeries] at ht
    exact ht
  have hw : (∑ k, ‖C k‖^2) + ∑ k, ‖nonconstantCoefficients C k‖^2 =
      ∑ k : Fin N, (if (k:ℕ) = 0 then 1 else 2)*‖C k‖^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : (k:ℕ) = 0 <;> simp [nonconstantCoefficients,hk0] ; ring
  constructor
  · rw [he]; linarith
  · rw [he,← hw]; linarith

end FaberHilbert

theorem re_circle_fraction {ζ μ : ℂ} (hζ : ‖ζ‖ = 1) (hμ : ‖μ‖ = 1)
    (hne : ζ ≠ μ) : 2 * (ζ / (ζ - μ)).re = 1 := by
  have hnζ : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq ζ = 1 by rw [Complex.normSq_eq_norm_sq, hζ]; norm_num)
  have hnμ : μ.re ^ 2 + μ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq μ = 1 by rw [Complex.normSq_eq_norm_sq, hμ]; norm_num)
  have hd : Complex.normSq (ζ - μ) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (sub_ne_zero.mpr hne)
  rw [Complex.div_re]
  field_simp
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith

def boundaryNormal (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ :=
  unitPoint t * (c-(unitPoint t)⁻¹^2*deriv g ((unitPoint t)⁻¹))

theorem scalarGenerating_exterior (c : ℂ) (g : ℂ → ℂ) (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    scalarGenerating c g z ζ⁻¹ = ζ*(c-ζ⁻¹^2*deriv g ζ⁻¹)/(exterior c g ζ-z) := by
  unfold scalarGenerating
  have he : c+ζ⁻¹*(g ζ⁻¹-z) = ζ⁻¹*(exterior c g ζ-z) := by
    simp only [exterior]; field_simp; ring
  rw [he,div_mul_eq_div_div,div_inv_eq_mul]
  ring

theorem reciprocal_fraction {ζ μ : ℂ} (hζ : ζ ≠ 0) (hμ : μ ≠ 0) :
    (1-ζ⁻¹/μ⁻¹)⁻¹ = ζ/(ζ-μ) := by
  have hquot : ζ⁻¹/μ⁻¹ = μ/ζ :=
    (div_eq_iff (inv_ne_zero hμ)).2 (by field_simp)
  have he : 1-ζ⁻¹/μ⁻¹ = (ζ-μ)/ζ := by rw [hquot]; field_simp
  rw [he,inv_div]

theorem unitPoint_injective : Function.Injective unitPoint := by
  intro t s h
  apply AddCircle.injective_toCircle (by norm_num : (1:ℝ) ≠ 0)
  apply Subtype.coe_injective
  simpa [unitPoint,fourier_apply] using h

theorem boundaryCorrection_identity {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {t s : Angle} (hts : t ≠ s) :
    boundaryCorrection c g t s = boundaryNormal c g t/(boundary c g t-boundary c g s) -
      unitPoint t/(unitPoint t-unitPoint s) := by
  have ht := unitPoint_inv_mem hR t
  have hs := unitPoint_inv_mem hR s
  have hn : (unitPoint t)⁻¹ ≠ (unitPoint s)⁻¹ :=
    fun he => hts (unitPoint_injective (inv_injective he))
  have he := correction_identity isOpen_ball (convex_ball 0 R) hg c ht hs
    (inv_ne_zero (unitPoint_ne_zero s)) hn (hH _ ht _ hs)
  change correction c g ((unitPoint t)⁻¹) ((unitPoint s)⁻¹) =
    scalarGenerating c g (exterior c g ((unitPoint s)⁻¹)⁻¹) ((unitPoint t)⁻¹) - _ at he
  rw [inv_inv,scalarGenerating_exterior c g _ (unitPoint_ne_zero t),
    reciprocal_fraction (unitPoint_ne_zero t) (unitPoint_ne_zero s)] at he
  exact he

theorem boundaryKernel_nonneg_off_diagonal {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hsupport : ∀ t s, 0 ≤ (conj (boundaryNormal c g t)*(boundary c g t-boundary c g s)).re)
    {t s : Angle} (hts : t ≠ s) : 0 ≤ boundaryKernel c g t s := by
  have hfrac := re_circle_fraction (unitPoint_norm t) (unitPoint_norm s)
    (fun he => hts (unitPoint_injective he))
  have hp : 0 ≤ (boundaryNormal c g t/(boundary c g t-boundary c g s)).re := by
    rw [Complex.div_re,← add_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simpa [Complex.mul_re] using hsupport t s
  rw [boundaryKernel,boundaryCorrection_identity hR hg hH hts,Complex.sub_re]
  linarith

theorem circle_nonneg_of_off_point (f : Angle → ℝ) (hf : Continuous f) (t : Angle)
    (h : ∀ s, s ≠ t → 0 ≤ f s) : 0 ≤ f t := by
  have hc : Continuous (fun x : ℝ => f (t+(x:Angle))) := hf.comp
    (continuous_const.add (AddCircle.continuous_mk' (1:ℝ)))
  have hlim : Tendsto (fun x : ℝ => f (t+(x:Angle))) (𝓝[>] 0) (𝓝 (f t)) := by
    simpa only [QuotientAddGroup.mk_zero,add_zero] using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx
  apply h
  intro he
  have hz : (x:Angle) = 0 := by simpa using add_left_cancel (he.trans (add_zero t).symm)
  have hx0 := (AddCircle.coe_eq_zero_iff_of_mem_Ico (show x ∈ Ico (0:ℝ) 1 from ⟨hx.1.le,hx.2⟩)).mp hz
  exact (ne_of_gt hx.1) hx0

theorem boundaryKernel_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hsupport : ∀ t s, 0 ≤ (conj (boundaryNormal c g t)*(boundary c g t-boundary c g s)).re) :
    ∀ t s, 0 ≤ boundaryKernel c g t s := by
  intro t s
  by_cases hts : t = s
  · subst s
    exact circle_nonneg_of_off_point _
      (continuous_slice_right _ (continuous_boundaryKernel (continuous_boundaryCorrection hR hg hH)) t) t
      (fun s hst => boundaryKernel_nonneg_off_diagonal hR hg hH hsupport (Ne.symm hst))
  · exact boundaryKernel_nonneg_off_diagonal hR hg hH hsupport hts

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

end BanachAlgebra

end DirectCrouzeix.Faber

end

end

end OAI
