import OAI.Analysis.DirectCrouzeix.ExteriorCollar

namespace OAI

universe u_131

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

theorem zero_or_nonvanishing_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFn : ∀ n z, z ∈ U → F n z ≠ 0)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    EqOn g 0 U ∨ ∀ z ∈ U, g z ≠ 0 := by
  have hg : AnalyticOnNhd ℂ g U :=
    (hl.differentiableOn (Eventually.of_forall hF) hU).analyticOnNhd hU
  by_cases hz : EqOn g 0 U
  · exact Or.inl hz
  right
  intro a ha hga
  have hlocal : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro he
    exact hz (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha he)
  have hp := ((hg a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hlocal
  obtain ⟨r, hr, hBU, hBn⟩ : ∃ r > 0, closedBall a r ⊆ U ∧
      ∀ z ∈ closedBall a r, z ≠ a → g z ≠ 0 := by
    simpa only [ofPred_and, subset_inter_iff] using!
      nhds_basis_closedBall.mem_iff.mp ((show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds ha).and
        (eventually_nhdsWithin_iff.mp hp))
  have hgR : ContinuousOn (fun z => ‖g z‖) (sphere a r) :=
    hg.continuousOn.norm.mono (sphere_subset_closedBall.trans hBU)
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hgR
  have hd : 0 < ‖g b‖ := norm_pos_iff.mpr
    (hBn b (sphere_subset_closedBall hb) (ne_of_mem_sphere hb hr.ne'))
  have hlu : TendstoUniformlyOn F g atTop (sphere a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hl (sphere a r)
      (sphere_subset_closedBall.trans hBU) (isCompact_sphere a r)
  have hclose : ∀ᶠ n in atTop, ∀ z ∈ sphere a r, dist (F n z) (g z) < ‖g b‖ / 2 :=
    by simpa only [dist_comm] using (Metric.tendstoUniformlyOn_iff.mp hlu) _ (half_pos hd)
  have hlow : ∀ᶠ n in atTop, ‖g b‖ / 2 ≤ ‖F n a‖ := by
    filter_upwards [hclose] with n hn
    have hinv : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball a r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball a hr.ne']
      exact ((hF n).inv (hFn n)).mono hBU
    have hbnd : ∀ z ∈ frontier (ball a r), ‖(F n z)⁻¹‖ ≤ (‖g b‖ / 2)⁻¹ := by
      intro z hz
      rw [frontier_ball a hr.ne'] at hz
      have hlo : ‖g b‖ / 2 ≤ ‖F n z‖ := by
        have ht := norm_sub_norm_le (g z) (F n z)
        rw [← dist_eq_norm, dist_comm] at ht
        have hm : ‖g b‖ ≤ ‖g z‖ := hmin hz
        have hc := hn z hz
        linarith
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le (half_pos hd) hlo) (half_pos hd)).mpr hlo
    have hc := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball :
      Bornology.IsBounded (ball a r)) hinv hbnd
      (show a ∈ closure (ball a r) from subset_closure (mem_ball_self hr))
    rw [norm_inv] at hc
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hFn n a ha)) (half_pos hd)).mp hc
  have hcenter : Tendsto (fun n => ‖F n a‖) atTop (𝓝 0) := by
    simpa [hga] using (hl.tendsto_at ha).norm
  have hle := ge_of_tendsto hcenter hlow
  exact (not_le_of_gt (half_pos hd)) hle

theorem constant_or_injective_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFi : ∀ n, InjOn (F n) U)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    (∃ c : ℂ, EqOn g (fun _ => c) U) ∨ InjOn g U := by
  have hg := (hl.differentiableOn (Eventually.of_forall hF) hU).analyticOnNhd hU
  by_cases hc : ∃ c : ℂ, EqOn g (fun _ => c) U
  · exact Or.inl hc
  right
  intro a ha b hb hab
  by_contra hne
  have hV : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
  have hbV : b ∈ U \ {a} := ⟨hb, by simpa [eq_comm] using hne⟩
  obtain ⟨r, hr, hBr⟩ := Metric.isOpen_iff.mp hV b hbV
  have hBU : ball b r ⊆ U := hBr.trans sdiff_subset
  have hzero : ∀ n z, z ∈ ball b r → F n z - F n a ≠ 0 := by
    intro n z hz he
    have hza := hBr hz
    have heq := hFi n hza.1 ha (sub_eq_zero.mp he)
    exact hza.2 (by simpa using heq)
  have hlc : TendstoLocallyUniformlyOn (fun n z => F n z - F n a)
      (fun z => g z - g a) atTop (ball b r) := by
    exact (hl.sub (hl.tendsto_at ha).tendstoUniformly_const.tendstoLocallyUniformly.tendstoLocallyUniformlyOn).mono hBU
  have hh := zero_or_nonvanishing_limit isOpen_ball (convex_ball b r).isPreconnected
    (fun n => ((hF n).sub_const (F n a)).mono hBU) hzero hlc
  have he : EqOn (fun z => g z - g a) 0 (ball b r) := hh.resolve_right (by
    intro hn
    exact hn b (mem_ball_self hr) (sub_eq_zero.mpr hab.symm))
  have heg : g =ᶠ[𝓝 b] (fun _ => g a) := by
    filter_upwards [ball_mem_nhds b hr] with z hz
    exact sub_eq_zero.mp (he hz)
  exact hc ⟨g a, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hb heg⟩

def extend (U : Set ℂ) (f : U → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ U then f ⟨z, h⟩ else 0

@[simp] theorem extend_coe {U : Set ℂ} (f : U → ℂ) (z : U) : extend U f z = f z := by
  simp [extend, z.property]

theorem continuousMap_limit {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → C(U, ℂ)} {g : C(U, ℂ)} (hl : Tendsto F atTop (𝓝 g)) :
    TendstoLocallyUniformlyOn (fun n => extend U (F n)) (extend U g) atTop U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [extend_coe, Function.comp_def] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hl

theorem bounded_holomorphic_equicontinuous {U : Set ℂ} (hU : IsOpen U)
    {ι : Type u_131} (F : ι → ℂ → ℂ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hbound : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) :
    Equicontinuous (fun i (z : U) => F i z) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R, hR, hBR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds x.property)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hd (i : ι) (z : ℂ) (hz : z ∈ ball (x : ℂ) r) : ‖deriv (F i) z‖ ≤ 1 / r := by
    have hsub : closedBall z r ⊆ U := by
      intro w hw
      apply hBR
      have ht := dist_triangle w z (x : ℂ)
      have hw' := mem_closedBall.mp hw
      have hz' := mem_ball.mp hz
      change dist w (x : ℂ) ≤ R
      dsimp [r] at hw' hz'
      linarith
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hr.ne']
      exact (hF i).mono hsub
    · intro w hw
      exact hbound i w (hsub (sphere_subset_closedBall hw))
  have hbU : ball (x : ℂ) r ⊆ U := by
    intro z hz
    apply hBR
    exact mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by dsimp [r]; linarith))
  refine ⟨min r (ε * r), lt_min hr (mul_pos hε hr), ?_⟩
  intro y hy i
  have hy' : dist (y : ℂ) (x : ℂ) < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hxy : ‖F i y - F i x‖ ≤ (1 / r) * ‖(y : ℂ) - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hF i).differentiableAt (hU.mem_nhds (hbU hz)))
      (hd i) (convex_ball (x : ℂ) r) (mem_ball_self hr) hy'
  rw [dist_comm, dist_eq_norm]
  apply lt_of_le_of_lt hxy
  rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ hr]
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le hy (min_le_right _ _)

theorem bounded_holomorphic_compact {U : Set ℂ} (hU : IsOpen U)
    (S : Set C(U, ℂ))
    (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1) :
    IsCompact (closure S) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : T2Space (UniformOnFun U ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      ext x
      simp only [mem_sUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨{x}, isCompact_singleton, mem_singleton x⟩)
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun f : C(U, ℂ) => (f : U → ℂ)) (𝔖 := {K | IsCompact K})
    (fun _ hK => hK)
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  · intro K hK
    have he := bounded_holomorphic_equicontinuous hU
      (fun f : S => extend U (f : C(U, ℂ)))
      (fun f => (hS f f.property).1)
      (fun f z hz => by simpa [extend, hz] using (hS f f.property).2 ⟨z, hz⟩)
    simpa only [Function.comp_def, extend_coe] using he.equicontinuousOn K
  · intro K hK z hz
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun f hf => by
      simpa using (hS f hf).2 z⟩

theorem bounded_holomorphic_closure {U : Set ℂ} (hU : IsOpen U)
    {S : Set C(U, ℂ)}
    (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1)
    {g : C(U, ℂ)} (hg : g ∈ closure S) :
    DifferentiableOn ℂ (extend U g) U ∧ ∀ z : U, ‖g z‖ ≤ 1 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨F, hF, hl⟩ := mem_closure_iff_seq_limit.mp hg
  have hl' := continuousMap_limit hU hl
  refine ⟨hl'.differentiableOn (Eventually.of_forall (fun n => (hS _ (hF n)).1)) hU, ?_⟩
  intro z
  have ht := (hl'.tendsto_at z.property).norm
  simpa only [extend_coe] using le_of_tendsto ht
    (Eventually.of_forall (fun n => by simpa only [extend_coe] using (hS _ (hF n)).2 z))

theorem derivative_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {S : Set C(U, ℂ)} (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U)
    {a : ℂ} (ha : a ∈ U) :
    ContinuousOn (fun f : C(U, ℂ) => deriv (extend U f) a) S := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro F g hl
  have ht : Tendsto (fun n => (F n : C(U, ℂ))) atTop (𝓝 (g : C(U, ℂ))) :=
    continuous_subtype_val.continuousAt.tendsto.comp hl
  have hlu := (continuousMap_limit hU ht).deriv
    (Eventually.of_forall (fun n => hS _ (F n).property)) hU
  exact hlu.tendsto_at ha

theorem strict_bound_of_normalized {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hb : ∀ z ∈ U, ‖f z‖ ≤ 1) {a : ℂ} (ha : a ∈ U) (hfa : f a = 0) :
    MapsTo f U (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff]
  by_contra hn
  have he : ‖f z‖ = 1 := le_antisymm (hb _ hz) (le_of_not_gt hn)
  have hm : IsMaxOn (norm ∘ f) U z := fun w hw => by
    change ‖f w‖ ≤ ‖f z‖
    rw [he]
    exact hb w hw
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hUc hU hf hz hm ha
  simp [hfa, he] at heq

open Function Complex

open scoped Pointwise

end Conformal

end DirectCrouzeix

end

end

end

end OAI
