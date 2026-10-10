import OAI.Analysis.DirectCrouzeix.Continuation

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

structure AnalyticBoundaryChart (U : Set ℂ) (p : ℂ) where
  chart : OpenPartialHomeomorph ℂ ℂ
  zero_mem : 0 ∈ chart.source
  at_zero : chart 0 = p
  analytic : AnalyticOnNhd ℂ chart chart.source
  inverse_analytic : AnalyticOnNhd ℂ chart.symm chart.target
  inverse_derivative : deriv chart.symm p ≠ 0
  side : ∀ z ∈ chart.source, chart z ∈ U ↔ 0 < z.im

def HasAnalyticBoundary (U : Set ℂ) : Prop :=
  ∀ p ∈ frontier U, Nonempty (AnalyticBoundaryChart U p)

theorem local_riemann_extension {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U)
    (C : AnalyticBoundaryChart U p) :
    ∃ r > 0, ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball p (3*r)) ∧
      EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0 := by
  have hphia : C.chart 0 ≠ a := by rw [C.at_zero]; intro he; exact hp (he ▸ ha)
  have hcn := (C.analytic 0 C.zero_mem).continuousAt
  have hav : ∀ᶠ z in 𝓝 (0 : ℂ), C.chart z ≠ a :=
    hcn.eventually (isClosed_singleton.isOpen_compl.mem_nhds hphia)
  obtain ⟨R,hR,hRB⟩ : ∃ R > 0, closedBall (0 : ℂ) R ⊆
      C.chart.source ∩ {z | C.chart z ≠ a} :=
    nhds_basis_closedBall.mem_iff.mp
      (inter_mem (C.chart.open_source.mem_nhds C.zero_mem) hav)
  have hRU : ∀ z ∈ closedBall (0 : ℂ) R, 0 < z.im → C.chart z ∈ U :=
    fun z hz hi => (C.side z (hRB hz).1).mpr hi
  have hfa : AnalyticOnNhd ℂ f U := hf.holomorphic.analyticOnNhd hU
  have hfcomp : AnalyticOnNhd ℂ (f ∘ C.chart) (closedBall 0 R ∩ {z | 0 < z.im}) := by
    intro z hz
    exact (hfa _ (hRU z hz.1 hz.2)).comp (C.analytic z (hRB hz.1).1)
  have hncomp : ∀ z ∈ closedBall 0 R ∩ {z : ℂ | 0 < z.im}, (f ∘ C.chart) z ≠ 0 := by
    intro z hz he
    exact (hRB hz.1).2 (hf.injective (hRU z hz.1 hz.2) ha (he.trans hf.normalized.symm))
  have hbcomp : ∀ z ∈ closedBall 0 R ∩ {z : ℂ | 0 < z.im}, ‖(f ∘ C.chart) z‖ < 1 := by
    intro z hz
    exact mem_ball_zero_iff.mp (hf.disk (hRU z hz.1 hz.2))
  have hlcomp : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖(f ∘ C.chart) w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1) := by
    intro z hz hi
    have hzS := (hRB hz).1
    have hpU : C.chart z ∉ U := by
      rw [C.side z hzS, hi]
      exact lt_irrefl _
    apply (norm_tendsto_one_boundary hU hf hs hpU).comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(C.analytic z hzS).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [(nhdsWithin_le_nhds : 𝓝[{w : ℂ | 0 < w.im}] z ≤ 𝓝 z)
      (C.chart.open_source.mem_nhds hzS), self_mem_nhdsWithin] with w hwS hwIm
    exact (C.side w hwS).mpr hwIm
  obtain ⟨G,hG,hGe,hGreal,hGd,hGside⟩ :=
    holomorphic_reflection_modulus hR hfcomp hncomp hbcomp hlcomp
  have hpT : p ∈ C.chart.target := by
    simpa only [C.at_zero] using C.chart.map_source C.zero_mem
  have hInv : C.chart.symm p = 0 :=
    (congrArg C.chart.symm C.at_zero.symm).trans (C.chart.left_inv C.zero_mem)
  have hNear : {z : ℂ | z ∈ C.chart.target ∧ C.chart.symm z ∈ ball 0 R} ∈ 𝓝 p := by
    apply inter_mem (C.chart.open_target.mem_nhds hpT)
    have := (C.inverse_analytic p hpT).continuousAt.preimage_mem_nhds
      (ball_mem_nhds (C.chart.symm p) hR)
    change C.chart.symm ⁻¹' ball (0 : ℂ) R ∈ 𝓝 p
    simpa only [hInv] using this
  obtain ⟨S,hS,hSB⟩ := Metric.mem_nhds_iff.mp hNear
  let E : ℂ → ℂ := G ∘ C.chart.symm
  have hE : AnalyticOnNhd ℂ E (ball p S) := by
    intro z hz
    exact (hG _ (hSB hz).2).comp (C.inverse_analytic z (hSB hz).1)
  have hEs : ∀ z ∈ ball p S, ‖E z‖ < 1 ↔ z ∈ U := by
    intro z hz
    have ht := (hSB hz).1
    change ‖G (C.chart.symm z)‖ < 1 ↔ z ∈ U
    rw [hGside _ (hSB hz).2, ← C.side _ (C.chart.map_target ht), C.chart.right_inv ht]
  have hEe : EqOn E f (ball p S ∩ U) := by
    intro z hz
    have ht := (hSB hz.1).1
    have him : 0 < (C.chart.symm z).im := by
      apply (C.side _ (C.chart.map_target ht)).mp
      rw [C.chart.right_inv ht]
      exact hz.2
    change G (C.chart.symm z) = f z
    rw [hGe ⟨(hSB hz.1).2,him⟩]
    simp only [Function.comp_apply, C.chart.right_inv ht]
  have hEd : deriv E p ≠ 0 := by
    have hGc := (hG 0 (mem_ball_self hR)).differentiableAt.hasDerivAt
    have hiC := (C.inverse_analytic p hpT).differentiableAt.hasDerivAt
    have hGc' : HasDerivAt G (deriv G 0) (C.chart.symm p) := by
      simpa only [hInv] using hGc
    have hh := hGc'.comp p hiC
    change deriv (G ∘ C.chart.symm) p ≠ 0
    rw [hh.deriv]
    exact mul_ne_zero hGd C.inverse_derivative
  refine ⟨S/3,by positivity,E,?_,?_,?_,hEd⟩
  · simpa only [show 3*(S/3) = S by ring] using hE
  · simpa only [show 3*(S/3) = S by ring] using hEe
  · simpa only [show 3*(S/3) = S by ring] using hEs

theorem inverse_riemann_collar {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUB : HasAnalyticBoundary U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) :
    ∃ R > 1, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧ InjOn g (ball 0 R) ∧
      g '' ball 0 1 = U ∧ g '' closedBall 0 1 = closure U ∧ g 0 = a ∧
      (∀ z ∈ ball 0 R, deriv g z ≠ 0) := by
  have hloc : ∀ p ∈ closure U, ∃ r > 0, ∃ E : ℂ → ℂ,
      AnalyticOnNhd ℂ E (ball p (3*r)) ∧ EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0 := by
    intro p hp
    by_cases hpin : p ∈ U
    · obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU p hpin
      refine ⟨r/3,by positivity,f,?_,fun _ _ => rfl,?_,hf.derivative p hpin⟩
      · simpa only [show 3*(r/3)=r by ring] using
          (hf.holomorphic.analyticOnNhd hU).mono hrU
      · intro z hz
        have hzU : z ∈ U := hrU (by simpa only [show 3*(r/3)=r by ring] using hz)
        exact iff_of_true (mem_ball_zero_iff.mp (hf.disk hzU)) hzU
    · have hpB : p ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hp,hpin⟩
      obtain ⟨C⟩ := hUB p hpB
      exact local_riemann_extension hU ha hf hs hpin C
  obtain ⟨V,F,hV,hUV,hF,hFf,hside,hd⟩ := patch_boundary_germs hU hloc
  have hi : InjOn F U := by
    intro x hx y hy he
    apply hf.injective hx hy
    simpa only [hFf hx,hFf hy] using he
  have hm : F '' U = ball 0 1 := hFf.image_eq.trans hs
  obtain ⟨W,hW,hUW,hWV,hiW,hFW,hmW⟩ :=
    univalent_neighborhood_of_disk_side hV hUV hUc hF hi hm hside hd
  let Z := W ∩ interior {z | deriv F z ≠ 0}
  have hZ : IsOpen Z := hW.inter isOpen_interior
  have hUZ : closure U ⊆ Z := by
    intro z hz
    refine ⟨hUW hz,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact ((hF z (hUV hz)).deriv.continuousAt).eventually
      (isClosed_singleton.isOpen_compl.mem_nhds (hd z hz))
  have hZF : AnalyticOnNhd ℂ F Z := hFW.mono inter_subset_left
  have hdZ : ∀ z ∈ Z, deriv F z ≠ 0 := fun z hz => interior_subset hz.2
  have hiZ : InjOn F Z := hiW.mono inter_subset_left
  have hImage : IsOpen (F '' Z) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z,hz,rfl⟩
    rw [← (hZF z hz).hasStrictDerivAt.map_nhds_eq (hdZ z hz)]
    exact Filter.image_mem_map (hZ.mem_nhds hz)
  have hSmall : closedBall (0 : ℂ) 1 ⊆ F '' Z := by
    rw [← hmW]
    exact image_mono hUZ
  obtain ⟨δ,hδ,hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hImage hSmall
  rw [thickening_closedBall hδ (by norm_num : (0 : ℝ) ≤ 1)] at hδsub
  let R := δ + 1
  have hR : 1 < R := by dsimp [R]; linarith
  have hball : ball (0 : ℂ) R ⊆ F '' Z := hδsub
  let g := Function.invFunOn F Z
  have hgr : ∀ z ∈ F '' Z, F (g z) = z := fun z hz => Function.invFunOn_eq hz
  have hgl : ∀ z ∈ Z, g (F z) = z := fun z hz => hiZ.leftInvOn_invFunOn hz
  have hgm : ∀ z ∈ F '' Z, g z ∈ Z := fun z hz => Function.invFunOn_mem hz
  have hgder : ∀ z ∈ ball (0 : ℂ) R,
      HasStrictDerivAt g (deriv F (g z))⁻¹ z := by
    intro z hz
    have hzI := hball hz
    have hh := inverse_hasStrictDerivAt hZ hZF.differentiableOn hiZ (hgm z hzI) (hdZ _ (hgm z hzI))
    simpa only [g,hgr z hzI] using hh
  have hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    exact fun z hz => (hgder z hz).hasDerivAt.differentiableAt.differentiableWithinAt
  refine ⟨R,hR,g,hg,?_,?_,?_,?_,?_⟩
  · intro x hx y hy he
    calc
      x = F (g x) := (hgr x (hball hx)).symm
      _ = F (g y) := congrArg F he
      _ = y := hgr y (hball hy)
  · apply Subset.antisymm
    · rintro w ⟨z,hz,rfl⟩
      have hzR := ball_subset_ball hR.le hz
      have hzI := hball hzR
      apply (hside _ (hWV (hgm z hzI).1)).mp
      rw [hgr z hzI]
      exact mem_ball_zero_iff.mp hz
    · intro z hz
      refine ⟨F z,?_,hgl z (hUZ (subset_closure hz))⟩
      rw [← hm]
      exact mem_image_of_mem F hz
  · apply Subset.antisymm
    · rintro w ⟨z,hz,rfl⟩
      rw [← hmW] at hz
      obtain ⟨y,hy,rfl⟩ := hz
      simpa only [hgl y (hUZ hy)] using hy
    · intro z hz
      refine ⟨F z,?_,hgl z (hUZ hz)⟩
      rw [← hmW]
      exact mem_image_of_mem F hz
  · have haZ := hUZ (subset_closure ha)
    have hFa : F a = 0 := (hFf ha).trans hf.normalized
    simpa only [hFa] using hgl a haZ
  · intro z hz
    rw [(hgder z hz).hasDerivAt.deriv]
    exact inv_ne_zero (hdZ _ (hgm z (hball hz)))

theorem exists_riemann_collar {U : Set ℂ} (hU : IsOpen U)
    (hUs : IsSimplyConnected U) (hproper : U ≠ univ)
    (hUc : IsCompact (closure U)) (hUB : HasAnalyticBoundary U)
    {a : ℂ} (ha : a ∈ U) :
    ∃ R > 1, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧ InjOn g (ball 0 R) ∧
      g '' ball 0 1 = U ∧ g '' closedBall 0 1 = closure U ∧ g 0 = a ∧
      (∀ z ∈ ball 0 R, deriv g z ≠ 0) := by
  obtain ⟨f,hf,hs⟩ := exists_riemannMap hU hUs hproper ha
  exact inverse_riemann_collar hU hUc hUB ha hf hs

end Conformal

end DirectCrouzeix

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end OAI
