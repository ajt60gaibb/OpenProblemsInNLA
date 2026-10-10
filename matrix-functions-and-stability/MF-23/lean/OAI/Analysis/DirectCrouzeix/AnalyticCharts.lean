import OAI.Analysis.DirectCrouzeix.ConformalCollar

namespace OAI

universe u_133 u_134 u_135

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

namespace DirectCrouzeix.Geometry

theorem analytic_inverse_chart {E : Type u_133} {F : Type u_134} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x : E} (ha : AnalyticAt ℂ f x) (e : E ≃L[ℂ] F)
    (hd : HasFDerivAt f e.toContinuousLinearMap x) :
    ∃ U : OpenPartialHomeomorph E F, (U : E → F) = f ∧ x ∈ U.source ∧
      AnalyticAt ℂ U.symm (f x) := by
  have hsd : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [← hd.fderiv]
    exact ha.hasStrictFDerivAt
  let U := hsd.toOpenPartialHomeomorph f
  have hU : (U : E → F) = f := hsd.toOpenPartialHomeomorph_coe
  have hx : x ∈ U.source := hsd.mem_toOpenPartialHomeomorph_source
  refine ⟨U,hU,hx,?_⟩
  obtain ⟨p,hp⟩ := ha
  have hc : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm e.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hp.hasFDerivAt.unique hd
  have hpU : HasFPowerSeriesAt U p x := hU ▸ hp
  simpa only [hU] using (U.hasFPowerSeriesAt_symm hx hpU hc).analyticAt

def conjugatePair (z : ℂ × ℂ) : ℂ × ℂ := (conj z.1,conj z.2)

theorem conjugatePair_continuous : Continuous conjugatePair :=
  (Complex.continuous_conj.comp continuous_fst).prodMk (Complex.continuous_conj.comp continuous_snd)

@[simp] theorem conjugatePair_zero : conjugatePair 0 = 0 := by simp [conjugatePair]

theorem normalized_implicit_graph {F : ℂ × ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = 1) {b : ℝ} (hb : 0 < b)
    (hd : HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0)
    (hconj : ∀ z, F (conjugatePair z) = conj (F z)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
      (∀ᶠ z in 𝓝 0, F (z,g z) = 1) ∧
      (∀ᶠ z in 𝓝 0, g (conj z) = conj (g z)) := by
  let H := fun z : ℂ × ℂ => (z.1,F z-1)
  have hH0 : H 0 = 0 := by simp [H,hF0]
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr
    (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (b:ℂ) hbC))
  have hH : AnalyticAt ℂ H 0 := analyticAt_fst.prod (hF.sub analyticAt_const)
  have hHd : HasFDerivAt H e.toContinuousLinearMap 0 := by
    convert! (hasFDerivAt_fst (𝕜 := ℂ) (p := (0:ℂ × ℂ))).prodMk (hd.sub_const 1) using 1
    ext <;> simp [e]
  obtain ⟨U,hU,h0,hUi⟩ := analytic_inverse_chart hH e hHd
  rw [hH0] at hUi
  have hU0 : U 0 = 0 := by rw [hU]; exact hH0
  have hi0 : U.symm 0 = 0 := by simpa only [hU0] using U.left_inv h0
  have ht0 : (0:ℂ × ℂ) ∈ U.target := hU0 ▸ U.map_source h0
  let V := fun z : ℂ => U.symm (z,0)
  have hV : AnalyticAt ℂ V 0 := hUi.comp (f := fun z : ℂ => (z,0)) (analyticAt_id.prod analyticAt_const)
  have hV0 : V 0 = 0 := hi0
  let g := fun z => (V z).2
  have hg : AnalyticAt ℂ g 0 := analyticAt_snd.comp hV
  have hvT : ∀ᶠ z in 𝓝 (0:ℂ), (z,0) ∈ U.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (U.open_target.mem_nhds ht0)
  have hvEq : ∀ᶠ z in 𝓝 (0:ℂ), H (V z) = (z,0) := by
    filter_upwards [hvT] with z hz
    exact hU ▸ U.right_inv hz
  have hvfst : ∀ᶠ z in 𝓝 (0:ℂ), (V z).1 = z := by
    filter_upwards [hvEq] with z hz
    exact congrArg Prod.fst hz
  have heq : ∀ᶠ z in 𝓝 (0:ℂ), F (z,g z) = 1 := by
    filter_upwards [hvEq,hvfst] with z hz hzf
    have hs : F (V z)-1 = 0 := congrArg Prod.snd hz
    have hev : V z = (z,g z) := Prod.ext hzf rfl
    simpa only [hev,sub_eq_zero] using hs
  have hg0 : g 0 = 0 := congrArg Prod.snd hV0
  have hgd : deriv g 0 = 0 := by
    have hdcomp := (show HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) (0,g 0) by simpa only [hg0,Prod.zero_eq_mk] using hd).comp 0 ((hasDerivAt_id (0:ℂ)).prodMk hg.differentiableAt.hasDerivAt).hasFDerivAt
    have hdconst : HasDerivAt (fun z => F (z,g z)) (b*deriv g 0) 0 := by
      convert! hdcomp.hasDerivAt using 1 ; simp [ContinuousLinearMap.comp_apply]
    have heder := hdconst.congr_of_eventuallyEq (show (fun _ : ℂ => (1:ℂ)) =ᶠ[𝓝 0] (fun z => F (z,g z)) from by filter_upwards [heq] with z hz; exact hz.symm)
    have hzero := heder.unique (hasDerivAt_const (0:ℂ) (1:ℂ))
    exact (mul_eq_zero.mp hzero).resolve_left hbC
  have hconjH (z : ℂ × ℂ) : H (conjugatePair z) = conjugatePair (H z) := by
    change (conj z.1,F (conjugatePair z)-1) = (conj z.1,conj (F z-1))
    rw [hconj]; simp
  have hvSC : ∀ᶠ z in 𝓝 (0:ℂ), conjugatePair (V z) ∈ U.source := by
    have hc : ContinuousAt (fun z => conjugatePair (V z)) 0 := conjugatePair_continuous.continuousAt.comp hV.continuousAt
    have he0 : conjugatePair (V 0) = 0 := by rw [hV0]; simp
    exact hc.preimage_mem_nhds (he0 ▸ U.open_source.mem_nhds h0)
  have htconj : ∀ᶠ z in 𝓝 (0:ℂ), (conj z,0) ∈ U.target := by
    have ht : Tendsto (conj : ℂ → ℂ) (𝓝 0) (𝓝 0) := by simpa using Complex.continuous_conj.tendsto (0:ℂ)
    exact ht.eventually hvT
  refine ⟨g,hg,hg0,hgd,heq,?_⟩
  filter_upwards [hvEq,hvSC,htconj] with z hz hzS hzT
  have he : V (conj z) = conjugatePair (V z) := by
    apply U.injOn (U.map_target hzT) hzS
    rw [hU]
    rw [hconjH,hz]
    simpa [conjugatePair] using (show H (U.symm (conj z,0)) = (conj z,0) from hU ▸ U.right_inv hzT)
  exact congrArg Prod.snd he

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem negative_vertical_level_side {f : ℂ → ℝ}
    (hf : ContDiffAt ℝ 1 f 0) (hd : fderiv ℝ f 0 Complex.I < 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, f (x:ℂ) = 1) :
    ∃ r > 0, ∀ z ∈ ball (0:ℂ) r, (f z < 1 ↔ 0 < z.im) ∧ (1 < f z ↔ z.im < 0) := by
  have he : ∀ᶠ z in 𝓝 (0:ℂ), DifferentiableAt ℝ f z ∧ fderiv ℝ f z Complex.I < 0 := by
    have hc : ContinuousAt (fun z => fderiv ℝ f z Complex.I) 0 :=
      (hf.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
    filter_upwards [hf.eventually (by norm_num),hc.eventually_lt continuousAt_const hd] with z hz hzn
    exact ⟨hz.differentiableAt (by norm_num),hzn⟩
  obtain ⟨d,hd0,hdB⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨e,he0,heB⟩ := Metric.mem_nhds_iff.mp hreal
  let r := min (d/3) e
  have hr : 0 < r := lt_min (by positivity) he0
  have hrd : 3*r ≤ d := by dsimp [r]; have := min_le_left (d/3) e; linarith
  have hre : r ≤ e := min_le_right _ _
  refine ⟨r,hr,?_⟩
  intro z hz
  have hzN : ‖z‖ < r := mem_ball_zero_iff.mp hz
  have hx : |z.re| < r := lt_of_le_of_lt (Complex.abs_re_le_norm z) hzN
  have hy : |z.im| < r := lt_of_le_of_lt (Complex.abs_im_le_norm z) hzN
  have hyI : z.im ∈ Ioo (-r) r := abs_lt.mp hy
  have h0I : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  let v := fun y : ℝ => (z.re:ℂ)+(y:ℂ)*Complex.I
  have hvB (y : ℝ) (hy : y ∈ Ioo (-r) r) : v y ∈ ball (0:ℂ) d := by
    rw [mem_ball_zero_iff]
    calc
      ‖v y‖ ≤ ‖(z.re:ℂ)‖+‖(y:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = |z.re|+|y| := by simp [Complex.norm_real,Real.norm_eq_abs]
      _ < r+r := add_lt_add hx (abs_lt.mpr hy)
      _ < d := by linarith
  have hvd (y : ℝ) : HasDerivAt v Complex.I y := by
    simpa [v] using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I |>.const_add (z.re:ℂ)
  have hder (y : ℝ) (hy : y ∈ Ioo (-r) r) :
      HasDerivAt (fun y => f (v y)) (fderiv ℝ f (v y) Complex.I) y :=
    (hdB (hvB y hy)).1.hasFDerivAt.comp_hasDerivAt y (hvd y)
  have hanti : StrictAntiOn (fun y => f (v y)) (Ioo (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro y hy
      exact (hder y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hder y (interior_subset hy)).deriv]
      exact (hdB (hvB y (interior_subset hy))).2
  have hbase : f (v 0) = 1 := by
    simpa [v] using heB (show z.re ∈ ball (0:ℝ) e from mem_ball_zero_iff.mpr (by simpa [Real.norm_eq_abs] using lt_of_lt_of_le hx hre))
  have hvz : v z.im = z := Complex.re_add_im z
  constructor
  · have hh := hanti.lt_iff_gt hyI h0I
    change (f (v z.im) < f (v 0) ↔ 0 < z.im) at hh
    rwa [hbase,hvz] at hh
  · have hh := hanti.lt_iff_gt h0I hyI
    change (f (v 0) < f (v z.im) ↔ z.im < 0) at hh
    rwa [hbase,hvz] at hh

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem analytic_complex_chart {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : deriv f 0 ≠ 0) {P : ℂ → Prop} (hP : ∀ᶠ z in 𝓝 0, P z) :
    ∃ U : OpenPartialHomeomorph ℂ ℂ, (U : ℂ → ℂ) = f ∧ 0 ∈ U.source ∧
      AnalyticOnNhd ℂ U U.source ∧ AnalyticOnNhd ℂ U.symm U.target ∧
      deriv U.symm (f 0) ≠ 0 ∧ (∀ z ∈ U.source, P z) := by
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f 0) hd)
  have hed : HasFDerivAt f e.toContinuousLinearMap 0 := by
    convert! hf.differentiableAt.hasDerivAt.hasFDerivAt using 1
  obtain ⟨U,hU,h0,hi⟩ := analytic_inverse_chart hf e hed
  have he : ∀ᶠ z in 𝓝 (0:ℂ), AnalyticAt ℂ f z ∧ AnalyticAt ℂ U.symm (f z) ∧ P z := by
    filter_upwards [hf.eventually_analyticAt,hf.continuousAt.eventually hi.eventually_analyticAt,hP] with z hz hzi hzP
    exact ⟨hz,hzi,hzP⟩
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp he
  let V := U.restr (ball 0 r)
  have hs : V.source = U.source ∩ ball 0 r := by simp [V,isOpen_ball.interior_eq]
  have ht : V.target = U.target ∩ U.symm ⁻¹' ball 0 r := by simp [V,isOpen_ball.interior_eq]
  have hV : (V : ℂ → ℂ) = f := by simpa [V] using hU
  have hVi : (V.symm : ℂ → ℂ) = U.symm := rfl
  have ht0 : f 0 ∈ U.target := hU ▸ U.map_source h0
  have hui0 : U.symm (f 0) = 0 := by simpa only [hU] using U.left_inv h0
  have hdi := U.hasDerivAt_symm ht0 hd (show HasDerivAt U (deriv f 0) (U.symm (f 0)) by
    rw [hui0,hU]; exact hf.differentiableAt.hasDerivAt)
  refine ⟨V,hV,?_,?_,?_,?_,?_⟩
  · rw [hs]; exact ⟨h0,mem_ball_self hr⟩
  · intro z hz
    rw [hV]
    exact (hrB ((hs ▸ hz).2)).1
  · intro z hz
    rw [hVi]
    have hzS := U.map_target ((ht ▸ hz).1)
    have hi := (hrB ((ht ▸ hz).2)).2.1
    rw [← hU,U.right_inv ((ht ▸ hz).1)] at hi
    exact hi
  · rw [hVi,hdi.deriv]
    exact inv_ne_zero hd
  · intro z hz
    exact (hrB ((hs ▸ hz).2)).2.2

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

def expLevel (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) : ℝ :=
  ∑ i, Real.exp (inner ℝ (v i) z+b i)

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI
