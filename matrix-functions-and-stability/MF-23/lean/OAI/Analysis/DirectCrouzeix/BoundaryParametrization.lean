import OAI.Analysis.DirectCrouzeix.ExponentialLevels

namespace OAI

universe u_137

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_137} [Fintype ι]

theorem expLevel_boundary_parametrization (v : ι → ℂ) (b : ι → ℝ) {p a : ℂ}
    (hp : expLevel v b p = 1) (ha : expLevel v b a < 1) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = p ∧ deriv H 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, (expLevel v b (H z) < 1 ↔ 0 < z.im) ∧
        (1 < expLevel v b (H z) ↔ z.im < 0)) := by
  let q := expGradient v b p
  have hq : q ≠ 0 := expGradient_ne_zero v b hp ha
  let ξ := -Complex.I*q
  have hξ : ξ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hq
  have hIξ : Complex.I*ξ = q := by simp [ξ,← mul_assoc]
  have hqξ : inner ℝ q ξ = 0 := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply,ξ,Complex.mul_re,Complex.mul_im]
    ring
  let α := fun i => inner ℝ (v i) ξ
  let β := fun i => inner ℝ (v i) q
  let γ := fun i => inner ℝ (v i) p+b i
  have hα : ∑ i, Real.exp (γ i)*α i = 0 := by
    rw [← hqξ]
    dsimp only [q,expGradient]
    rw [sum_inner]
    simp only [real_inner_smul_left,α,γ]
  have hβ : ∑ i, Real.exp (γ i)*β i = ‖q‖^2 := by
    rw [← real_inner_self_eq_norm_sq,show q = expGradient v b p from rfl]
    conv_rhs => rw [expGradient]
    rw [sum_inner]
    simp only [real_inner_smul_left,β,γ,q,expGradient]
  have hF0 : expComplex α β γ 0 = 1 := by rw [expComplex_zero]; exact_mod_cast hp
  have hFd : HasFDerivAt (expComplex α β γ)
      (((‖q‖^2:ℝ):ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
    convert! expComplex_hasFDerivAt_zero α β γ using 1
    rw [hα,hβ]
    simp only [Complex.ofReal_zero]
    apply ContinuousLinearMap.ext
    intro z
    change _ = (0:ℂ)*z.1 + (‖q‖^2:ℝ)*z.2
    simp
  obtain ⟨g,hg,hg0,hgd,hge,hgc⟩ := normalized_implicit_graph (expComplex_analytic α β γ 0) hF0
    (sq_pos_of_pos (norm_pos_iff.mpr hq)) hFd (fun z => expComplex_conj α β γ z)
  let H := fun z : ℂ => p+ξ*(-z+Complex.I*g (-z))
  have hH0 : H 0 = p := by simp [H,hg0]
  have hHa : AnalyticAt ℂ H 0 := by
    exact analyticAt_const.add (analyticAt_const.mul (analyticAt_id.neg.add
      (analyticAt_const.mul ((show AnalyticAt ℂ g (-(0:ℂ)) from by simpa using hg).comp (f := fun z : ℂ => -z) analyticAt_id.neg))))
  have hHd : HasDerivAt H (-ξ) 0 := by
    have hdg : HasDerivAt (fun z : ℂ => g (-z)) 0 0 := by
      convert! (show HasDerivAt g (deriv g 0) (-(0:ℂ)) from by simpa using hg.differentiableAt.hasDerivAt).comp 0 (hasDerivAt_id (0:ℂ)).neg using 1
      simp [hgd]
    convert! (((hasDerivAt_id (0:ℂ)).neg.add (hdg.const_mul Complex.I)).const_mul ξ).const_add p using 1 ; simp
  have hreal : ∀ᶠ x : ℝ in 𝓝 0, expLevel v b (H (x:ℂ)) = 1 := by
    have ht : Tendsto (fun x : ℝ => -(x:ℂ)) (𝓝 0) (𝓝 0) := by convert! Complex.continuous_ofReal.neg.tendsto (0:ℝ) using 1 ; simp
    filter_upwards [ht.eventually hge,ht.eventually hgc] with x hx hxc
    have hi : (g (-(x:ℂ))).im = 0 := by
      simp only [map_neg,Complex.conj_ofReal] at hxc
      have hh := congrArg Complex.im hxc
      simp only [Complex.conj_im] at hh
      linarith
    have hgR : g (-(x:ℂ)) = ((g (-(x:ℂ))).re:ℂ) := by
      apply Complex.ext <;> simp [hi]
    have he : (expLevel v b (H (x:ℂ)):ℂ) = expComplex α β γ (-(x:ℂ),g (-(x:ℂ))) := by
      rw [hgR]
      rw [show -(x:ℂ) = ((-x:ℝ):ℂ) by simp,expComplex_real]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hHz : H (x:ℂ) = p+(-x) • ξ+(g (-(x:ℂ))).re • q := by
        dsimp only [H]
        rw [hgR]
        simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_re]
        rw [← hIξ]
        ring
      rw [hHz]
      simp only [inner_add_right,real_inner_smul_right,α,β,γ,Complex.ofReal_neg]
      ring
    rw [hx] at he
    exact_mod_cast he
  let f := fun z => expLevel v b (H z)
  have hf : ContDiffAt ℝ 1 f 0 :=
    ((expLevel_contDiff v b).of_le (by simp)).contDiffAt.comp 0 (hHa.contDiffAt.restrict_scalars ℝ)
  have hdf : fderiv ℝ f 0 Complex.I = -‖q‖^2 := by
    have hdφ : HasFDerivAt (expLevel v b) (innerSL ℝ q) (H 0) := by rw [hH0]; exact expLevel_hasFDerivAt v b p
    have hdcomp := hdφ.comp 0 (hHd.hasFDerivAt.restrictScalars ℝ)
    change fderiv ℝ (expLevel v b ∘ H) 0 Complex.I = _
    rw [hdcomp.fderiv]
    change inner ℝ q (Complex.I*(-ξ)) = _
    have he : Complex.I*(-ξ) = -q := by rw [mul_neg,hIξ]
    rw [he,inner_neg_right,real_inner_self_eq_norm_sq]
  obtain ⟨r,hr,hside⟩ := negative_vertical_level_side hf (by rw [hdf]; exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hq))) hreal
  refine ⟨H,hHa,hH0,?_,?_⟩
  · rw [hHd.deriv]; exact neg_ne_zero.mpr hξ
  · exact Filter.mem_of_superset (ball_mem_nhds (0:ℂ) hr) hside

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end OAI
