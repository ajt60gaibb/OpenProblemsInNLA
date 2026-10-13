import OAI.Analysis.DirectCrouzeix.DomainCore

namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem integrable_of_continuous_compact {α : Type u_87} {E : Type u_88} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuousOn_integral_compact {α : Type u_89} {β : Type u_90} {E : Type u_91}
    [MetricSpace α] [ProperSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {s : Set α} (hs : IsOpen s)
    {f : α → β → E} (hf : ContinuousOn f.uncurry (s ×ˢ univ)) :
    ContinuousOn (fun x => ∫ t, f x t ∂μ) s := by
  intro x hx
  obtain ⟨ε,hε,hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
  have hc : Continuous (fun p : closedBall x ε × β => f p.1 p.2) := by
    apply hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    intro p
    exact ⟨hsub p.1.property,mem_univ _⟩
  have hi : Continuous (fun y : closedBall x ε => ∫ t, f y t ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ
  have hi' : ContinuousOn (fun y => ∫ t, f y t ∂μ) (closedBall x ε) :=
    continuousOn_iff_continuous_domRestrict.mpr hi
  exact (hi'.continuousAt (closedBall_mem_nhds x hε)).continuousWithinAt

theorem hasDerivAt_integral_compact {α : Type u_92} {E : Type u_93}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [CompactSpace α] [SecondCountableTopology α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] {s : Set ℂ} (hs : IsOpen s)
    {f f' : ℂ → α → E}
    (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hf' : ContinuousOn f'.uncurry (s ×ˢ univ))
    (hd : ∀ z ∈ s, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ s) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by
  obtain ⟨ε,hε,hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  have hcf (w : ℂ) (hw : w ∈ s) : Continuous (f w) := by
    exact hf.comp_continuous (continuous_const.prodMk continuous_id) (fun t => ⟨hw,mem_univ _⟩)
  have hcf' (w : ℂ) (hw : w ∈ s) : Continuous (f' w) := by
    exact hf'.comp_continuous (continuous_const.prodMk continuous_id) (fun t => ⟨hw,mem_univ _⟩)
  obtain ⟨B,hB⟩ := ((isCompact_closedBall z ε).prod isCompact_univ).exists_bound_of_continuousOn
    (hf'.mono (prod_mono hsub Subset.rfl))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := closedBall z ε) (bound := fun _ => B) (closedBall_mem_nhds z hε)
    ?_ (integrable_of_continuous_compact μ (hcf z hz))
    (hcf' z hz).aestronglyMeasurable ?_ (integrable_const B) ?_).2
  · filter_upwards [hs.mem_nhds hz] with w hw
    exact (hcf w hw).aestronglyMeasurable
  · exact ae_of_all μ (fun t w hw => hB (w,t) ⟨hw,mem_univ _⟩)
  · exact ae_of_all μ (fun t w hw => hd w (hsub hw) t)

abbrev Parameter := Set.Icc (0 : ℝ) 1

def chord (u v : ℂ) (t : ℝ) : ℂ := (1-t) • u + t • v

theorem chord_mem {s : Set ℂ} (hs : Convex ℝ s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : chord u v t ∈ s :=
  hs hu hv (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)

theorem continuous_chord : Continuous (fun p : (ℂ × ℂ) × ℝ => chord p.1.1 p.1.2 p.2) := by
  unfold chord
  fun_prop

def chordIntegral (f : ℂ → ℂ) (w : Parameter → ℂ) (u v : ℂ) : ℂ :=
  ∫ t : Parameter, w t * f (chord u v t)

theorem continuousOn_chordIntegral {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : ContinuousOn f s) {w : Parameter → ℂ} (hw : Continuous w) :
    ContinuousOn (fun p : ℂ × ℂ => chordIntegral f w p.1 p.2) (s ×ˢ s) := by
  apply continuousOn_integral_compact volume (hs.prod hs)
  apply (hw.comp continuous_snd).continuousOn.mul
  apply hf.comp
  · exact (continuous_chord.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).continuousOn
  · intro p hp
    exact chord_mem hconv hp.1.1 hp.1.2 p.2.property

theorem hasDerivAt_chord_left (u v : ℂ) (t : ℝ) :
    HasDerivAt (fun z => chord z v t) ((1-t : ℝ) : ℂ) u := by
  simpa [chord] using ((hasDerivAt_id u).const_smul (1-t : ℝ)).add_const (t • v)

theorem hasDerivAt_chord_right (u v : ℂ) (t : ℝ) :
    HasDerivAt (fun z => chord u z t) (t : ℂ) v := by
  simpa [chord] using ((hasDerivAt_id v).const_smul t).const_add ((1-t) • u)

theorem hasDerivAt_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => chordIntegral f w z v)
      (chordIntegral (deriv f) (fun t => w t * ((1-(t : ℝ) : ℝ) : ℂ)) u v) u := by
  have hc : ContinuousOn (fun p : ℂ × Parameter => chord p.1 v p.2) (s ×ˢ univ) := by
    unfold chord
    fun_prop
  have hm : MapsTo (fun p : ℂ × Parameter => chord p.1 v p.2) (s ×ˢ univ) s :=
    fun p hp => chord_mem hconv hp.1 hv p.2.property
  apply hasDerivAt_integral_compact volume hs
    ((hw.comp continuous_snd).continuousOn.mul (hf.continuousOn.comp hc hm))
    (((hw.comp continuous_snd).continuousOn.mul
      (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_subtype_val.comp continuous_snd))).continuousOn).mul
        (hf.deriv.continuousOn.comp hc hm)) ?_ hu
  intro z hz t
  have hd := ((hf _ (chord_mem hconv hz hv t.property)).differentiableAt.hasDerivAt.comp z
    (hasDerivAt_chord_left z v t)).const_mul (w t)
  simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using hd

theorem hasDerivAt_chordIntegral_right {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => chordIntegral f w u z)
      (chordIntegral (deriv f) (fun t => w t * ((t : ℝ) : ℂ)) u v) v := by
  have hc : ContinuousOn (fun p : ℂ × Parameter => chord u p.1 p.2) (s ×ˢ univ) := by
    unfold chord
    fun_prop
  have hm : MapsTo (fun p : ℂ × Parameter => chord u p.1 p.2) (s ×ˢ univ) s :=
    fun p hp => chord_mem hconv hu hp.1 p.2.property
  apply hasDerivAt_integral_compact volume hs
    ((hw.comp continuous_snd).continuousOn.mul (hf.continuousOn.comp hc hm))
    (((hw.comp continuous_snd).continuousOn.mul
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).continuousOn).mul
        (hf.deriv.continuousOn.comp hc hm)) ?_ hv
  intro z hz t
  have hd := ((hf _ (chord_mem hconv hu hz t.property)).differentiableAt.hasDerivAt.comp z
    (hasDerivAt_chord_right u z t)).const_mul (w t)
  simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using hd

theorem chordIntegral_one_eq_interval (f : ℂ → ℂ) (u v : ℂ) :
    chordIntegral f (fun _ => 1) u v = ∫ t in (0:ℝ)..1, f (chord u v t) := by
  simp only [chordIntegral, one_mul]
  rw [show (∫ t : Parameter, f (chord u v t)) = ∫ t in Icc (0:ℝ) 1, f (chord u v t) from
      integral_subtype measurableSet_Icc (fun t : ℝ => f (chord u v t)),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem hasDerivAt_chord_time (u v : ℂ) (t : ℝ) :
    HasDerivAt (chord u v) (v-u) t := by
  have hi : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := t))
  have hd := ((hi.const_sub 1).mul_const u).add (hi.mul_const v)
  change HasDerivAt (fun y => chord u v y) (v-u) t
  simpa [chord, Complex.real_smul, sub_eq_add_neg, add_comm] using! hd

theorem chordIntegral_deriv_mul {s : Set ℂ} (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    chordIntegral (deriv f) (fun _ => 1) u v * (v-u) = f v - f u := by
  rw [chordIntegral_one_eq_interval, ← intervalIntegral.integral_mul_const]
  have hc : ContinuousOn (fun t : ℝ => chord u v t) (Icc 0 1) := by unfold chord; fun_prop
  have hm : MapsTo (fun t : ℝ => chord u v t) (Icc 0 1) s := fun t ht => chord_mem hconv hu hv ht
  have hi : IntervalIntegrable (fun t : ℝ => deriv f (chord u v t) * (v-u)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (hf.deriv.continuousOn.comp hc hm).mul_const _
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := fun t => f (chord u v t))
    (f' := fun t => deriv f (chord u v t) * (v-u)) (fun t ht => by
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      simpa only [smul_eq_mul, mul_comm, Function.comp_def] using
        ((hf _ (hm ht')).differentiableAt.hasDerivAt.scomp t (hasDerivAt_chord_time u v t))) hi
  simpa [chord] using ht

theorem chordIntegral_deriv_eq_dslope {s : Set ℂ} (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    chordIntegral (deriv f) (fun _ => 1) u v = dslope f v u := by
  by_cases huv : u = v
  · subst u
    have he (t : ℝ) : chord v v t = v := by
      rw [chord, ← add_smul, sub_add_cancel, one_smul]
    simp [chordIntegral, he, dslope_same]
  · rw [dslope_of_ne f huv, slope, smul_eq_mul]
    simp only [vsub_eq_sub]
    have hm := chordIntegral_deriv_mul hconv hf hu hv
    field_simp
    linear_combination -hm

theorem analyticOnNhd_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {v : ℂ} (hv : v ∈ s) : AnalyticOnNhd ℂ (fun u => chordIntegral f w u v) s := by
  apply DifferentiableOn.analyticOnNhd _ hs
  intro u hu
  exact (hasDerivAt_chordIntegral_left hs hconv hf hw hu hv).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_chordIntegral_right {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u : ℂ} (hu : u ∈ s) : AnalyticOnNhd ℂ (chordIntegral f w u) s := by
  apply DifferentiableOn.analyticOnNhd _ hs
  intro v hv
  exact (hasDerivAt_chordIntegral_right hs hconv hf hw hu hv).differentiableAt.differentiableWithinAt

end DirectCrouzeix.Faber

end

end

end OAI
