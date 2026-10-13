import OAI.Analysis.DirectCrouzeix.HarmonicReflection

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

def logModulusUpper (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < z.im then Real.log ‖f z‖ else 0

theorem logModulusUpper_real {f : ℂ → ℂ} {z : ℂ} (hz : z.im = 0) :
    logModulusUpper f z = 0 := by simp [logModulusUpper, hz]

theorem logModulusUpper_continuous {R : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ContinuousOn (logModulusUpper f) (upperClosedBall R) := by
  unfold logModulusUpper
  apply ContinuousOn.if'
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    have ht : Tendsto (fun w => Real.log ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp (hl z hz.1.1 hz0)
    exact ht.mono_left (nhdsWithin_mono _ inter_subset_right)
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    exact tendsto_const_nhds
  · apply (hc.norm.log (fun z hz => norm_ne_zero_iff.mpr (hn z hz))).mono
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  · exact continuousOn_const

theorem upperBall_convex (R : ℝ) : Convex ℝ (upperBall R) :=
  (convex_ball (0 : ℂ) R).inter (convex_Ioi (0 : ℝ) |>.linear_preimage Complex.imCLM.toLinearMap)

theorem upperBall_half_radius {R : ℝ} (hR : 0 < R) :
    ((R / 2 : ℝ) : ℂ) * Complex.I ∈ upperBall R := by
  constructor
  · simp only [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hR)]
    linarith
  · simpa using half_pos hR

theorem circleAverage_pos_upper {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, 0 ≤ u z) (hp : 0 < u ((R : ℂ) * Complex.I)) :
    0 < Real.circleAverage u 0 R := by
  have hall (θ : ℝ) : circleMap 0 R θ ∈ sphere 0 R := by
    simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
  have hc : Continuous (fun θ => u (circleMap 0 R θ)) :=
    hu.comp_continuous (continuous_circleMap 0 R) hall
  have hip : 0 < ∫ θ in (0 : ℝ)..2 * Real.pi, u (circleMap 0 R θ) := by
    apply intervalIntegral.integral_pos Real.two_pi_pos hc.continuousOn
    · intro θ _
      exact hn _ (hall θ)
    · refine ⟨Real.pi / 2, ⟨by positivity, by nlinarith [Real.pi_pos]⟩, ?_⟩
      simpa only [circleMap_pi_div_two, zero_add] using hp
  exact mul_pos (inv_pos.mpr Real.two_pi_pos) hip

theorem herglotz_deriv_im_pos {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, u z * z.im ≤ 0)
    (hp : u ((R : ℂ) * Complex.I) < 0) :
    0 < (deriv (herglotzExtension R u) 0).im := by
  let d := fun ζ : ℂ => (2 / ζ) * (u ζ : ℂ)
  have hzne : ∀ ζ ∈ sphere 0 R, ζ ≠ (0 : ℂ) := by
    intro ζ hζ hz
    subst ζ
    exact hR.ne' (by simpa only [mem_sphere, dist_self, eq_comm] using hζ)
  have hd : ContinuousOn d (sphere 0 R) :=
    (continuousOn_const.div continuousOn_id hzne).mul (Complex.continuous_ofReal.comp_continuousOn hu)
  have hder := hasDerivAt_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hu).circleIntegrable hR.le)
    (by simpa [abs_of_pos hR] using hR.ne : (0 : ℂ) ∉ sphere 0 |R|)
  change HasDerivAt (herglotzExtension R u) _ _ at hder
  have hval : deriv (herglotzExtension R u) 0 = Real.circleAverage d 0 R := by
    rw [hder.deriv]
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    have hz : ζ ≠ 0 := hzne ζ (by simpa only [abs_of_pos hR] using hζ)
    dsimp [d]
    simp only [sub_zero]
    congr 1
    field_simp
  have he (ζ : ℂ) : (d ζ).im = -2 * (u ζ * ζ.im) / Complex.normSq ζ := by
    dsimp [d]
    simp [Complex.mul_im, Complex.div_im]
    ring
  have hnon : ∀ ζ ∈ sphere 0 R, 0 ≤ (d ζ).im := by
    intro ζ hζ
    rw [he]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hn ζ hζ))
      (Complex.normSq_nonneg ζ)
  have hpos : 0 < (d ((R : ℂ) * Complex.I)).im := by
    rw [he]
    have him : ((R : ℂ) * Complex.I).im = R := by simp
    rw [him]
    apply div_pos
    · exact mul_pos_of_neg_of_neg (by norm_num) (mul_neg_of_neg_of_pos hp hR)
    · rw [Complex.normSq_pos]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') Complex.I_ne_zero
  rw [hval]
  change 0 < Complex.imCLM (Real.circleAverage d 0 R)
  rw [← Complex.imCLM.circleAverage_comp_comm (hd.circleIntegrable hR.le)]
  exact circleAverage_pos_upper hR.le (Complex.continuous_im.comp_continuousOn hd) hnon hpos

theorem holomorphic_reflection_modulus {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hb : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, ‖f z‖ < 1)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 R) ∧ EqOn F f (upperBall R) ∧
      (∀ z ∈ ball 0 R, z.im = 0 → ‖F z‖ = 1) ∧ deriv F 0 ≠ 0 ∧
      (∀ z ∈ ball 0 R, ‖F z‖ < 1 ↔ 0 < z.im) := by
  let u := logModulusUpper f
  let v := oddUpper u
  let H := herglotzExtension R v
  have hu0 : ∀ z, z.im = 0 → u z = 0 := fun _ hz => logModulusUpper_real hz
  have huc := logModulusUpper_continuous hf.continuousOn hn hl
  have hvc : ContinuousOn v (sphere 0 R) := oddUpper_continuous_circle huc hu0
  have hH : AnalyticOnNhd ℂ H (ball 0 R) := herglotz_analytic hR.le hvc
  have hu : HarmonicOnNhd u (upperBall R) := by
    intro z hz
    have hzK : z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨ball_subset_closedBall hz.1, hz.2⟩
    have he : u =ᶠ[𝓝 z] (fun w => Real.log ‖f w‖) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz.2] with w hw
      simp only [u, logModulusUpper, hw, ↓reduceIte]
    rw [harmonicAt_congr_nhds he]
    exact (hf z hzK).harmonicAt_log_norm (hn z hzK)
  have hRe := harmonic_reflection hR hu huc hu0
  let k := fun z => f z * Complex.exp (-H z)
  have hk : DifferentiableOn ℂ k (upperBall R) := by
    apply (hf.differentiableOn.mono (by intro z hz; exact ⟨ball_subset_closedBall hz.1, hz.2⟩)).mul
    exact (hH.differentiableOn.mono inter_subset_left).neg.cexp
  have hkn : ∀ z ∈ upperBall R, ‖k z‖ = 1 := by
    intro z hz
    have hRe' : (H z).re = Real.log ‖f z‖ := by
      have hh : (H z).re = u z := hRe hz
      simpa only [u, logModulusUpper, ite_eq_left (show 0 < z.im from hz.2)] using hh
    have hnz := hn z ⟨ball_subset_closedBall hz.1, hz.2⟩
    dsimp [k]
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hRe', Real.exp_neg,
      Real.exp_log (norm_pos_iff.mpr hnz), mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnz)]
  let c : ℂ := ((R / 2 : ℝ) : ℂ) * Complex.I
  have hc : c ∈ upperBall R := upperBall_half_radius hR
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (upperBall_convex R).isPreconnected (upperBall_open R) hk hc
    (show IsMaxOn (norm ∘ k) (upperBall R) c from
      fun z hz => by
        change ‖k z‖ ≤ ‖k c‖
        rw [hkn z hz, hkn c hc])
  refine ⟨fun z => k c * Complex.exp (H z), analyticOnNhd_const.mul hH.cexp, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hh : k z = k c := hconst hz
    rw [← hh]
    simp [k, Complex.exp_neg, Complex.exp_ne_zero]
  · intro z hz hz0
    have hHz : (H z).re = 0 := by
      rw [show H z = herglotzExtension R v z from rfl, herglotz_re hR.le hvc hz]
      exact poisson_real_zero (oddUpper_conj hu0) hz0
    rw [norm_mul, hkn c hc, Complex.norm_exp, hHz, Real.exp_zero, mul_one]
  · have hvsign : ∀ z ∈ sphere 0 R, v z * z.im ≤ 0 := by
      intro z hz
      by_cases hi : 0 ≤ z.im
      · by_cases hi0 : z.im = 0
        · simp [hi0]
        · have hip : 0 < z.im := lt_of_le_of_ne hi (Ne.symm hi0)
          have hzK : z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨sphere_subset_closedBall hz, hip⟩
          have huNeg : u z < 0 := by
            simpa only [u, logModulusUpper, ite_eq_left hip] using
              Real.log_neg (norm_pos_iff.mpr (hn z hzK)) (hb z hzK)
          simpa only [v, oddUpper, ite_eq_left hi] using mul_nonpos_of_nonpos_of_nonneg huNeg.le hi
      · have hip : 0 < (conj z).im := by simpa only [Complex.conj_im] using neg_pos.mpr (lt_of_not_ge hi)
        have hzK : conj z ∈ closedBall 0 R ∩ {z | 0 < z.im} :=
          ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using sphere_subset_closedBall hz, hip⟩
        have huNeg : u (conj z) < 0 := by
          simpa only [u, logModulusUpper, ite_eq_left hip] using
            Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
        simpa only [v, oddUpper, ite_eq_right hi] using
          mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr huNeg.le) (le_of_not_ge hi)
    have hvpole : v ((R : ℂ) * Complex.I) < 0 := by
      have hip : 0 < ((R : ℂ) * Complex.I).im := by simpa using hR
      have hzK : (R : ℂ) * Complex.I ∈ closedBall 0 R ∩ {z | 0 < z.im} :=
        ⟨by simp [mem_closedBall, abs_of_pos hR], hip⟩
      simpa only [v, oddUpper, ite_eq_left hip.le, u, logModulusUpper, ite_eq_left hip] using
        Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
    have hdpos : 0 < (deriv H 0).im := herglotz_deriv_im_pos hR hvc hvsign hvpole
    have hdne : deriv H 0 ≠ 0 := by intro he; simp [he] at hdpos
    have hkc : k c ≠ 0 := by intro he; simpa [he] using hkn c hc
    have hderF := ((hH 0 (mem_ball_self hR)).differentiableAt.hasDerivAt.cexp).const_mul (k c)
    rw [hderF.deriv]
    exact mul_ne_zero hkc (mul_ne_zero (Complex.exp_ne_zero _) hdne)
  · intro z hz
    change ‖k c * Complex.exp (H z)‖ < 1 ↔ 0 < z.im
    by_cases hi : 0 < z.im
    · have hh : k z = k c := hconst ⟨hz, hi⟩
      have he : k c * Complex.exp (H z) = f z := by
        rw [← hh]
        simp [k, Complex.exp_neg, Complex.exp_ne_zero]
      rw [he]
      exact iff_of_true (hb z ⟨ball_subset_closedBall hz, hi⟩) hi
    · by_cases hi0 : z.im = 0
      · have hHz : (H z).re = 0 := by
          rw [show H z = herglotzExtension R v z from rfl, herglotz_re hR.le hvc hz]
          exact poisson_real_zero (oddUpper_conj hu0) hi0
        simp only [norm_mul, hkn c hc, Complex.norm_exp, hHz, Real.exp_zero, mul_one,
          lt_self_iff_false, hi0]
      · have hic : 0 < (conj z).im := by
          simpa only [Complex.conj_im] using
            (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hi) hi0))
        have hzcb : conj z ∈ ball 0 R := by simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
        have hzK : conj z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨ball_subset_closedBall hzcb, hic⟩
        have hRc : (H (conj z)).re = Real.log ‖f (conj z)‖ := by
          have hh : (H (conj z)).re = u (conj z) := hRe ⟨hzcb, hic⟩
          simpa only [u, logModulusUpper, ite_eq_left hic] using hh
        have ho : (H (conj z)).re = -(H z).re := by
          change (herglotzExtension R v (conj z)).re = -(herglotzExtension R v z).re
          rw [herglotz_re hR.le hvc hzcb, herglotz_re hR.le hvc hz]
          exact poisson_odd (oddUpper_conj hu0) z
        have hpos : 0 < (H z).re := by
          have hnlog := Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
          linarith
        have hlarge : 1 < ‖k c * Complex.exp (H z)‖ := by
          rw [norm_mul, hkn c hc, one_mul, Complex.norm_exp]
          exact Real.one_lt_exp_iff.mpr hpos
        exact iff_of_false (not_lt_of_ge hlarge.le) hi

end Conformal

end DirectCrouzeix

end

end

end

end OAI
