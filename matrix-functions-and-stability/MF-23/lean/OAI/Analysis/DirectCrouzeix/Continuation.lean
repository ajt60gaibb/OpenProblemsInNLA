import OAI.Analysis.DirectCrouzeix.HolomorphicReflection

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

theorem boundary_germs_compatible {U : Set ℂ} (hU : IsOpen U)
    {p q z : ℂ} (hp : p ∈ closure U) (hq : q ∈ closure U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hzp : z ∈ ball p r) (hzq : z ∈ ball q s)
    {E G f : ℂ → ℂ}
    (hE : AnalyticOnNhd ℂ E (ball p (3*r)))
    (hG : AnalyticOnNhd ℂ G (ball q (3*s)))
    (he : EqOn E f (ball p (3*r) ∩ U))
    (hg : EqOn G f (ball q (3*s) ∩ U)) : E z = G z := by
  let V := ball p (3*r) ∩ ball q (3*s)
  have hVo : IsOpen V := isOpen_ball.inter isOpen_ball
  have hmeet : (V ∩ closure U).Nonempty := by
    have hd : dist p q < r + s := by
      have := dist_triangle p z q
      rw [dist_comm p z] at this
      have hpz := mem_ball.mp hzp
      have hqz := mem_ball.mp hzq
      linarith
    rcases le_total r s with hrs | hsr
    · refine ⟨p, ⟨mem_ball_self (by positivity), ?_⟩, hp⟩
      rw [mem_ball]
      linarith
    · refine ⟨q, ⟨?_, mem_ball_self (by positivity)⟩, hq⟩
      rw [mem_ball, dist_comm]
      linarith
  obtain ⟨b, hbV, hbU⟩ := hmeet
  obtain ⟨a, haV, haU⟩ := mem_closure_iff_nhds.mp hbU V (hVo.mem_nhds hbV)
  have heq : E =ᶠ[𝓝 a] G := by
    filter_upwards [(hVo.inter hU).mem_nhds ⟨haV, haU⟩] with w hw
    exact (he ⟨hw.1.1, hw.2⟩).trans (hg ⟨hw.1.2, hw.2⟩).symm
  exact (hE.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono inter_subset_right)
    ((convex_ball p (3*r)).inter (convex_ball q (3*s))).isPreconnected haV heq
    ⟨ball_subset_ball (by linarith) hzp, ball_subset_ball (by linarith) hzq⟩

theorem patch_boundary_germs {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hloc : ∀ p ∈ closure U, ∃ r > 0, ∃ E : ℂ → ℂ,
      AnalyticOnNhd ℂ E (ball p (3*r)) ∧ EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0) :
    ∃ V : Set ℂ, ∃ F : ℂ → ℂ, IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ F V ∧ EqOn F f U ∧
      (∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U) ∧ (∀ p ∈ closure U, deriv F p ≠ 0) := by
  classical
  choose r hr E hE he hside hd using hloc
  let V : Set ℂ := ⋃ p : closure U, ball (p : ℂ) (r p p.property)
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_ball
  have hUV : closure U ⊆ V := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, mem_ball_self (hr p hp)⟩
  have hchoose : ∀ z ∈ V, ∃ p : closure U, z ∈ ball (p : ℂ) (r p p.property) := by
    intro z hz
    exact mem_iUnion.mp hz
  let F : ℂ → ℂ := fun z => if hz : z ∈ V then
    E (hchoose z hz).choose (hchoose z hz).choose.property z else f z
  have hFE : ∀ p : closure U, EqOn F (E p p.property) (ball (p : ℂ) (r p p.property)) := by
    intro p z hz
    have hzV : z ∈ V := mem_iUnion.mpr ⟨p,hz⟩
    dsimp only [F]
    rw [dite_eq_left hzV]
    exact boundary_germs_compatible hU (hchoose z hzV).choose.property p.property
      (hr _ _) (hr _ _) (hchoose z hzV).choose_spec hz
      (hE _ _) (hE _ _) (he _ _) (he _ _)
  refine ⟨V,F,hV,hUV,?_,?_,?_,?_⟩
  · intro z hz
    obtain ⟨p,hp⟩ := hchoose z hz
    apply (hE p p.property z (ball_subset_ball (by linarith [hr p p.property]) hp)).congr
    filter_upwards [isOpen_ball.mem_nhds hp] with w hw
    exact (hFE p hw).symm
  · intro z hz
    exact (hFE ⟨z,subset_closure hz⟩ (mem_ball_self (hr _ _))).trans
      (he z (subset_closure hz) ⟨mem_ball_self (by linarith [hr z (subset_closure hz)]),hz⟩)
  · intro z hz
    obtain ⟨p,hp⟩ := hchoose z hz
    rw [hFE p hp]
    exact hside p p.property z (ball_subset_ball (by linarith [hr p p.property]) hp)
  · intro p hp
    have hevent : F =ᶠ[𝓝 p] E p hp := by
      filter_upwards [ball_mem_nhds p (hr p hp)] with z hz
      exact hFE ⟨p,hp⟩ hz
    rw [hevent.deriv_eq]
    exact hd p hp

theorem injective_closure_of_disk_side {U V : Set ℂ} (hV : IsOpen V)
    (hUV : closure U ⊆ V) {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F V)
    (hi : InjOn F U) (hm : F '' U = ball 0 1)
    (hside : ∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U)
    (hd : ∀ p ∈ closure U, deriv F p ≠ 0) : InjOn F (closure U) := by
  intro p hp q hq he
  by_contra hpq
  obtain ⟨S,T,hS,hT,hpS,hqT,hST⟩ := t2_separation hpq
  have hpN : S ∩ V ∈ 𝓝 p := (hS.inter hV).mem_nhds ⟨hpS,hUV hp⟩
  have hqN : T ∩ V ∈ 𝓝 q := (hT.inter hV).mem_nhds ⟨hqT,hUV hq⟩
  have hpI : F '' (S ∩ V) ∈ 𝓝 (F p) := by
    rw [← (hF p (hUV hp)).hasStrictDerivAt.map_nhds_eq (hd p hp)]
    exact Filter.image_mem_map hpN
  have hqI : F '' (T ∩ V) ∈ 𝓝 (F p) := by
    rw [he, ← (hF q (hUV hq)).hasStrictDerivAt.map_nhds_eq (hd q hq)]
    exact Filter.image_mem_map hqN
  have hpCl : F p ∈ closure (ball (0 : ℂ) 1) := by
    rw [← hm]
    exact mem_closure_image (hF p (hUV hp)).continuousAt hp
  obtain ⟨w,hwI,hwD⟩ := mem_closure_iff_nhds.mp hpCl _ (inter_mem hpI hqI)
  obtain ⟨a,haS,haw⟩ := hwI.1
  obtain ⟨b,hbT,hbw⟩ := hwI.2
  have haU : a ∈ U := (hside a haS.2).mp (by rw [haw]; exact mem_ball_zero_iff.mp hwD)
  have hbU : b ∈ U := (hside b hbT.2).mp (by rw [hbw]; exact mem_ball_zero_iff.mp hwD)
  have hab : a = b := hi haU hbU (haw.trans hbw.symm)
  exact Set.disjoint_left.mp hST haS.1 (hab ▸ hbT.1)

theorem univalent_neighborhood_of_disk_side {U V : Set ℂ} (hV : IsOpen V)
    (hUV : closure U ⊆ V) (hUc : IsCompact (closure U))
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F V)
    (hi : InjOn F U) (hm : F '' U = ball 0 1)
    (hside : ∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U)
    (hd : ∀ p ∈ closure U, deriv F p ≠ 0) :
    ∃ W, IsOpen W ∧ closure U ⊆ W ∧ W ⊆ V ∧
      InjOn F W ∧ AnalyticOnNhd ℂ F W ∧ F '' closure U = closedBall 0 1 := by
  have hic := injective_closure_of_disk_side hV hUV hF hi hm hside hd
  have hlocal : ∀ p ∈ closure U, ∃ S ∈ 𝓝 p, InjOn F S := by
    intro p hp
    let d := (hF p (hUV hp)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hd p hp)
    exact ⟨(d.toOpenPartialHomeomorph F).source,
      (d.toOpenPartialHomeomorph F).open_source.mem_nhds d.mem_toOpenPartialHomeomorph_source,
      (d.toOpenPartialHomeomorph F).injOn⟩
  obtain ⟨W,hW,hUW,hiW⟩ := hic.exists_isOpen_superset hUc
    (fun p hp => (hF p (hUV hp)).continuousAt) hlocal
  refine ⟨W ∩ V,hW.inter hV,fun z hz => ⟨hUW hz,hUV hz⟩,inter_subset_right,
    hiW.mono inter_subset_left,hF.mono inter_subset_right,?_⟩
  apply Subset.antisymm
  · rintro w ⟨z,hz,rfl⟩
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), ← hm]
    exact mem_closure_image (hF z (hUV hz)).continuousAt hz
  · have hc : IsClosed (F '' closure U) :=
      (hUc.image_of_continuousOn (hF.continuousOn.mono hUV)).isClosed
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    apply hc.closure_subset_iff.mpr
    rw [← hm]
    exact image_mono subset_closure

end Conformal

end DirectCrouzeix

end

end

end

end OAI
