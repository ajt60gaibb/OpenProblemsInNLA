import OAI.Analysis.DirectCrouzeix.InverseExterior

namespace OAI

universe u_138 u_139

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

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem exterior_laurent_form {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hinj : InjOn f (ball 0 R))
    (hf0 : f 0 = 0) (hd : ∀ u ∈ ball 0 R, deriv f u ≠ 0) (a : ℂ) :
    ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → c*ζ+g ζ⁻¹ = a+(f ζ⁻¹)⁻¹) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) := by
  have h0 : (0:ℂ) ∈ ball 0 R := mem_ball_self hR
  let J := dslope f 0
  have hJ : AnalyticOnNhd ℂ J (ball 0 R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) hR)).mpr hf.differentiableOn |>.analyticOnNhd isOpen_ball
  have hJ0 : J 0 = deriv f 0 := dslope_same _ _
  have hfn (u : ℂ) (hu : u ∈ ball 0 R) (hu0 : u ≠ 0) : f u ≠ 0 := by
    intro he
    exact hu0 (hinj hu h0 (he.trans hf0.symm))
  have hJn (u : ℂ) (hu : u ∈ ball 0 R) : J u ≠ 0 := by
    by_cases hu0 : u = 0
    · subst u; rw [hJ0]; exact hd 0 h0
    · dsimp only [J]
      rw [dslope_of_ne _ hu0]
      simp only [slope_def_field,hf0,sub_zero]
      exact div_ne_zero (hfn u hu hu0) hu0
  let F := fun u => (J u)⁻¹
  have hF : AnalyticOnNhd ℂ F (ball 0 R) := fun u hu => (hJ u hu).inv (hJn u hu)
  let c := F 0
  have hc : c ≠ 0 := inv_ne_zero (hJn 0 h0)
  let g := fun u => a+dslope F 0 u
  have hg : AnalyticOnNhd ℂ g (ball 0 R) := by
    have hs : AnalyticOnNhd ℂ (dslope F 0) (ball 0 R) :=
      (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) hR)).mpr hF.differentiableOn |>.analyticOnNhd isOpen_ball
    exact analyticOnNhd_const.add hs
  have he (ζ : ℂ) (hζ : ζ ≠ 0) : c*ζ+g ζ⁻¹ = a+(f ζ⁻¹)⁻¹ := by
    have hu : ζ⁻¹ ≠ 0 := inv_ne_zero hζ
    dsimp only [g]
    rw [dslope_of_ne _ hu,slope_def_field]
    dsimp only [F,J,c]
    rw [dslope_of_ne _ hu,slope_def_field,hf0]
    simp only [sub_zero,div_inv_eq_mul]
    field_simp
    ring
  have hder (ζ : ℂ) (hζ : ζ ≠ 0) (hu : ζ⁻¹ ∈ ball 0 R) :
      HasDerivAt (fun ζ => a+(f ζ⁻¹)⁻¹)
        (- (deriv f ζ⁻¹ * (-1/ζ^2))/(f ζ⁻¹)^2) ζ := by
    have hi : HasDerivAt (fun ζ : ℂ => ζ⁻¹) (-1/ζ^2) ζ := by
      convert! (hasDerivAt_id ζ).inv hζ using 1
    have hh := ((hf _ hu).differentiableAt.hasDerivAt.comp ζ hi).inv (hfn _ hu (inv_ne_zero hζ))
    convert! hh.const_add a using 1
  refine ⟨c,g,hc,hg,he,?_,?_⟩
  · intro ζ hζ η hη hh
    have hζ0 : ζ ≠ 0 := hζ.2
    have hη0 : η ≠ 0 := hη.2
    change c*ζ+g ζ⁻¹ = c*η+g η⁻¹ at hh
    rw [he ζ hζ0,he η hη0,add_right_inj] at hh
    exact inv_injective (hinj hζ.1 hη.1 (inv_injective hh))
  · intro ζ hζ hu
    have hev : (fun ζ => c*ζ+g ζ⁻¹) =ᶠ[𝓝 ζ] (fun ζ => a+(f ζ⁻¹)⁻¹) := by
      filter_upwards [continuousAt_id.eventually_ne hζ] with z hz
      exact he z hz
    rw [((hder ζ hζ hu).congr_of_eventuallyEq hev).deriv]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (hd _ hu)
      (div_ne_zero (by norm_num) (pow_ne_zero _ hζ)))) (pow_ne_zero _ (hfn _ hu (inv_ne_zero hζ)))

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem inverseExterior_analytic_boundary {ι : Type u_138} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | expLevel v b z ≤ 1})
    {a : ℂ} (ha : expLevel v b a < 1) :
    Conformal.HasAnalyticBoundary (inverseExterior (expLevel v b) a) := by
  intro w hw
  obtain ⟨hw0,hlevel⟩ := inverseExterior_frontier_level (expLevel_contDiff v b).continuous hc hw
  obtain ⟨H,hHa,hH0,hHd,hside⟩ := expLevel_boundary_parametrization v b hlevel ha
  let k := fun z : ℂ => (H (-z)-a)⁻¹
  have hpa : H 0-a ≠ 0 := by rw [hH0,add_sub_cancel_left]; exact inv_ne_zero hw0
  have hk0 : k 0 = w := by simp [k,hH0]
  have hHneg : AnalyticAt ℂ (fun z : ℂ => H (-z)) 0 := by
    exact (show AnalyticAt ℂ H (-(0:ℂ)) from by simpa using hHa).comp analyticAt_id.neg
  have hka : AnalyticAt ℂ k 0 := (hHneg.sub analyticAt_const).inv (by simpa using hpa)
  have hkder : HasDerivAt k (deriv H 0/(H 0-a)^2) 0 := by
    have hdn := (show HasDerivAt H (deriv H 0) (-(0:ℂ)) from by simpa using hHa.differentiableAt.hasDerivAt).comp 0 (hasDerivAt_id (0:ℂ)).neg
    convert! (hdn.sub_const a).inv (by simpa using hpa) using 1 ; simp
  have hkdn : deriv k 0 ≠ 0 := by rw [hkder.deriv]; exact div_ne_zero hHd (pow_ne_zero _ hpa)
  have hkP : ∀ᶠ z in 𝓝 (0:ℂ), k z ∈ inverseExterior (expLevel v b) a ↔ 0 < z.im := by
    have ht : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℂ)
    have hne : ∀ᶠ z in 𝓝 (0:ℂ), H (-z)-a ≠ 0 :=
      (hHneg.continuousAt.sub continuousAt_const).eventually_ne (by simpa using hpa)
    filter_upwards [ht.eventually hside,hne] with z hz hzne
    rw [mem_inverseExterior_iff (show k z ≠ 0 from inv_ne_zero hzne)]
    dsimp only [k]
    rw [inv_inv,add_sub_cancel]
    simpa only [Complex.neg_im,neg_lt_zero] using hz.2
  obtain ⟨C,hC,hC0,hCa,hCi,hCd,hCP⟩ := analytic_complex_chart hka hkdn hkP
  exact ⟨⟨C,hC0,by rw [hC,hk0],hCa,hCi,by rwa [hk0] at hCd,by simpa only [hC] using hCP⟩⟩

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem exists_expLevel_exterior {ι : Type u_139} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | expLevel v b z ≤ 1})
    {a : ℂ} (ha : expLevel v b a < 1) :
    ∃ R > 1, ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) ∧
      (∀ ζ : ℂ, ‖ζ‖ = 1 → expLevel v b (c*ζ+g ζ⁻¹) = 1) ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → 1 < expLevel v b (c*ζ+g ζ⁻¹)) := by
  let U := inverseExterior (expLevel v b) a
  have hct := (expLevel_contDiff v b).continuous
  have hU : IsOpen U := inverseExterior_isOpen hct hc a
  obtain ⟨R,hR,f,hfa,hfi,hopen,hclosed,hf0,hfd⟩ := Conformal.exists_riemann_collar hU
    (inverseExterior_simplyConnected (expLevel_convex v b) ha)
    (inverseExterior_proper hct ha) (inverseExterior_compact_closure hct ha)
    (inverseExterior_analytic_boundary v b hc ha) (zero_mem_inverseExterior _ a)
  obtain ⟨c,g,hc0,hg,he,hi,hd⟩ := exterior_laurent_form (by linarith : 0 < R) hfa hfi hf0 hfd a
  refine ⟨R,hR,c,g,hc0,hg,hi,hd,?_,?_⟩
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := by intro hh; norm_num [hh] at hζ
    have hη : ‖ζ⁻¹‖ = 1 := by simp [norm_inv,hζ]
    have hηR : ζ⁻¹ ∈ ball 0 R := mem_ball_zero_iff.mpr (by rw [hη]; exact hR)
    have hfu : f ζ⁻¹ ∈ frontier U := by
      rw [frontier,hU.interior_eq]
      refine ⟨?_,?_⟩
      · rw [← hclosed]
        exact mem_image_of_mem f (mem_closedBall_zero_iff.mpr (by rw [hη]))
      · intro hh
        rw [← hopen] at hh
        obtain ⟨z,hz,hze⟩ := hh
        have hzR := ball_subset_ball hR.le hz
        have hez : z = ζ⁻¹ := hfi hzR hηR hze
        have hzlt := mem_ball_zero_iff.mp hz
        rw [hez,hη] at hzlt
        exact lt_irrefl _ hzlt
    obtain ⟨hfn,hfl⟩ := inverseExterior_frontier_level hct hc hfu
    rw [he ζ hζ0]
    exact hfl
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := by intro hh; norm_num [hh] at hζ
    have hηB : ζ⁻¹ ∈ ball 0 1 := by
      rw [mem_ball_zero_iff,norm_inv]
      exact inv_lt_one_of_one_lt₀ hζ
    have hηR := ball_subset_ball hR.le hηB
    have hfn : f ζ⁻¹ ≠ 0 := by
      intro hh
      have hη0 := hfi hηR (mem_ball_self (by linarith)) (hh.trans hf0.symm)
      exact (inv_ne_zero hζ0) hη0
    have hfu : f ζ⁻¹ ∈ U := by rw [← hopen]; exact mem_image_of_mem f hηB
    rw [he ζ hζ0]
    exact (mem_inverseExterior_iff hfn).mp hfu

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

end

end

end OAI
