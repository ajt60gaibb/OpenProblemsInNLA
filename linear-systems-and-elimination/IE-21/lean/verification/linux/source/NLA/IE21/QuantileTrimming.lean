import NLA.IE21.PopulationTrimming

/-!
Quantiles with possible atoms and fractional lower-tail selectors for IE-21.
This module will supply the scalar analytic input to empirical trimming.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21

/-- Every real probability law has a quantile straddling any interior mass,
including laws with atoms. No continuity of its distribution is assumed. -/
theorem exists_quantile_mass (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ b : ℝ, ν.real (Iio b) ≤ θ ∧ θ ≤ ν.real (Iic b) := by
  let S : Set ℝ := {x | θ ≤ cdf ν x}
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds hθ.1)).exists
  obtain ⟨c, hc⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds hθ.2)).exists
  have hs : S.Nonempty := ⟨c, hc.le⟩
  have hbelow : BddBelow S := by
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hax
    have hxa : x < a := lt_of_not_ge hax
    have hlt := ((monotone_cdf ν) hxa.le).trans_lt ha
    exact not_lt_of_ge hx hlt
  let b := sInf S
  have hright (x : ℝ) (hx : b < x) : θ ≤ cdf ν x := by
    obtain ⟨y, hy, hyx⟩ := (csInf_lt_iff hbelow hs).mp hx
    exact le_trans hy ((monotone_cdf ν) hyx.le)
  have hleft (x : ℝ) (hx : x < b) : cdf ν x < θ := by
    by_contra hxt
    have hxS : x ∈ S := le_of_not_gt hxt
    have hb := csInf_le hbelow hxS
    exact not_le_of_gt hx hb
  have hθb : θ ≤ cdf ν b := by
    apply ge_of_tendsto
      ((continuousWithinAt_Ioi_iff_Ici.mpr ((cdf ν).right_continuous b)).tendsto)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hright x hx
  have hlim : Function.leftLim (cdf ν) b ≤ θ := by
    apply le_of_tendsto ((monotone_cdf ν).tendsto_leftLim b)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hleft x hx).le
  have hnonneg : 0 ≤ Function.leftLim (cdf ν) b :=
    ge_of_tendsto ((monotone_cdf ν).tendsto_leftLim b)
      (Eventually.of_forall (fun x => cdf_nonneg ν x))
  refine ⟨b, ?_, ?_⟩
  · rw [measureReal_def, ← measure_cdf ν,
      (cdf ν).measure_Iio (tendsto_cdf_atBot ν), sub_zero,
      ENNReal.toReal_ofReal hnonneg]
    exact hlim
  · rwa [cdf_eq_real] at hθb

/-- A nonnegative mean-one variable has a quantile no larger than
`1/(1-θ)`, without any atomlessness hypothesis. -/
theorem exists_bounded_quantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hmean : (∫ ω, Y ω ∂μ) = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 / (1 - θ) ∧
      μ.real {ω | Y ω < b} ≤ θ ∧ θ ≤ μ.real {ω | Y ω ≤ b} := by
  have : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  obtain ⟨b, hbelow, habove⟩ := exists_quantile_mass (μ.map Y) θ hθ
  rw [map_measureReal_apply hYmeas measurableSet_Iio] at hbelow
  rw [map_measureReal_apply hYmeas measurableSet_Iic] at habove
  change μ.real {ω | Y ω < b} ≤ θ at hbelow
  change θ ≤ μ.real {ω | Y ω ≤ b} at habove
  have hb : 0 ≤ b := by
    by_contra hb
    have hempty : {ω | Y ω ≤ b} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hb) (hY0 ω))
    rw [hempty, measureReal_empty] at habove
    exact not_le_of_gt hθ.1 habove
  have hmass : 1 - θ ≤ μ.real {ω | b ≤ Y ω} := by
    have h := measureReal_add_measureReal_compl
      (μ := μ) (show MeasurableSet {ω | Y ω < b} by measurability)
    have heq : {ω | Y ω < b}ᶜ = {ω | b ≤ Y ω} := by
      ext ω
      simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
    rw [heq, probReal_univ] at h
    linarith
  have hmul : μ.real {ω | b ≤ Y ω} * b ≤ 1 := by
    have h := integral_mono ((integrable_const b).indicator
      (show MeasurableSet {ω | b ≤ Y ω} by measurability)) hY (fun ω => ?_)
    · rw [integral_indicator_const b (by measurability), hmean] at h
      exact h
    · by_cases hω : b ≤ Y ω
      · rw [indicator_of_mem (show ω ∈ {ω | b ≤ Y ω} from hω)]
        exact hω
      · rw [indicator_of_notMem (show ω ∉ {ω | b ≤ Y ω} from hω)]
        exact hY0 ω
  refine ⟨b, hb, ?_, hbelow, habove⟩
  apply (le_div_iff₀ (sub_pos.mpr hθ.2)).mpr
  have h := mul_le_mul_of_nonneg_right hmass hb
  nlinarith

/-- A feasible fractional selector aligned with a nonnegative threshold attains
the dual. This permits exact mass θ at atoms, without assuming continuity. -/
theorem populationTrim_eq_weighted {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y W : Ω → ℝ)
    (hY : Integrable Y μ) (hW : Integrable W μ)
    (hYW : Integrable (fun ω => Y ω * W ω) μ)
    (hWbounds : ∀ ω, 0 ≤ W ω ∧ W ω ≤ 1)
    (θ : ℝ) (hθ : θ ≤ 1) (hmean : (∫ ω, W ω ∂μ) = θ)
    (b : ℝ) (hb : 0 ≤ b)
    (halign : ∀ ω, max (b - Y ω) 0 = (b - Y ω) * W ω) :
    populationTrim θ μ Y = ∫ ω, Y ω * W ω ∂μ := by
  have hint (t : ℝ) : Integrable (fun ω => (t - Y ω) * W ω) μ := by
    have := (hW.const_mul t).sub hYW
    convert this using 1
    ext ω
    simp only [Pi.sub_apply]
    ring
  have hval (t : ℝ) : (∫ ω, (t - Y ω) * W ω ∂μ) =
      θ * t - ∫ ω, Y ω * W ω ∂μ := by
    have heq : (fun ω => (t - Y ω) * W ω) =
        fun ω => t * W ω - Y ω * W ω := by ext ω; ring
    rw [heq, integral_sub (hW.const_mul t) hYW, integral_const_mul, hmean]
    ring
  have hupper (t : ℝ) : θ * t - ∫ ω, max (t - Y ω) 0 ∂μ ≤
      ∫ ω, Y ω * W ω ∂μ := by
    have hi := integral_mono (hint t) (trimming_hinge_integrable hY t) (fun ω => ?_)
    · rw [hval] at hi
      linarith
    · rcases hWbounds ω with ⟨hw0, hw1⟩
      by_cases hty : 0 ≤ t - Y ω
      · rw [max_eq_left hty]
        nlinarith
      · rw [max_eq_right (le_of_not_ge hty)]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hty) hw0
  apply le_antisymm
  · apply csSup_le (populationTrim_objectives_nonempty θ Y)
    rintro z ⟨t, _, rfl⟩
    exact hupper t
  · have ht := trimming_objective_le_populationTrim hθ hY hb
    have heq : (∫ ω, max (b - Y ω) 0 ∂μ) =
        θ * b - ∫ ω, Y ω * W ω ∂μ := by
      rw [integral_congr_ae (ae_of_all _ halign), hval]
    rw [heq] at ht
    linarith

/-- A quantile straddling θ supplies a measurable fractional selector of exactly
that mass, equal to one strictly below the threshold and zero strictly above it. -/
theorem exists_fractional_selector {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) (hY : Integrable Y μ)
    (θ : ℝ) (hθ : θ ≤ 1) (b : ℝ) (hb : 0 ≤ b)
    (hlower : μ.real {ω | Y ω < b} ≤ θ)
    (hupper : θ ≤ μ.real {ω | Y ω ≤ b}) :
    ∃ W : Ω → ℝ, Measurable W ∧ Integrable W μ ∧
      Integrable (fun ω => Y ω * W ω) μ ∧
      (∀ ω, 0 ≤ W ω ∧ W ω ≤ 1) ∧
      (∀ ω, Y ω < b → W ω = 1) ∧
      (∀ ω, b < Y ω → W ω = 0) ∧
      (∫ ω, W ω ∂μ) = θ ∧
      populationTrim θ μ Y = ∫ ω, Y ω * W ω ∂μ := by
  classical
  let s : Set Ω := {ω | Y ω < b}
  let e : Set Ω := {ω | Y ω = b}
  have hs : MeasurableSet s := by measurability
  have he : MeasurableSet e := by measurability
  let p := μ.real s
  let q := μ.real e
  have hp : p ≤ θ := hlower
  have hq : 0 ≤ q := measureReal_nonneg
  have hcdf : μ.real {ω | Y ω ≤ b} = p + q := by
    have heq : {ω | Y ω ≤ b} = s ∪ e := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, s, e]
      exact le_iff_lt_or_eq
    have hd : Disjoint s e := by
      apply Set.disjoint_left.mpr
      intro ω hω heω
      exact ne_of_lt hω heω
    rw [heq, measureReal_union hd he]
  have hpq : θ ≤ p + q := by rwa [hcdf] at hupper
  let α := (θ - p) / q
  have hα : 0 ≤ α ∧ α ≤ 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hp) hq, ?_⟩
    by_cases hq0 : q = 0
    · simp [α, hq0]
    · apply (div_le_one (lt_of_le_of_ne hq (Ne.symm hq0))).mpr
      linarith
  have hαq : α * q = θ - p := by
    by_cases hq0 : q = 0
    · have hθp : θ = p := by linarith
      simp [α, hq0, hθp]
    · exact div_mul_cancel₀ (θ - p) hq0
  let W : Ω → ℝ := fun ω => s.indicator (fun _ => (1 : ℝ)) ω +
    e.indicator (fun _ => α) ω
  have hWmeas : Measurable W :=
    (measurable_const.indicator hs).add (measurable_const.indicator he)
  have hWint : Integrable W μ :=
    ((integrable_const (1 : ℝ)).indicator hs).add ((integrable_const α).indicator he)
  have hWbelow (ω : Ω) (hω : Y ω < b) : W ω = 1 := by
    have hωs : ω ∈ s := hω
    have hωe : ω ∉ e := ne_of_lt hω
    simp [W, indicator_of_mem hωs, indicator_of_notMem hωe]
  have hWabove (ω : Ω) (hω : b < Y ω) : W ω = 0 := by
    have hωs : ω ∉ s := not_lt_of_gt hω
    have hωe : ω ∉ e := ne_of_gt hω
    simp [W, indicator_of_notMem hωs, indicator_of_notMem hωe]
  have hWat (ω : Ω) (hω : Y ω = b) : W ω = α := by
    have hωs : ω ∉ s := by change ¬Y ω < b; rw [hω]; exact lt_irrefl _
    have hωe : ω ∈ e := hω
    simp [W, indicator_of_notMem hωs, indicator_of_mem hωe]
  have hWbounds (ω : Ω) : 0 ≤ W ω ∧ W ω ≤ 1 := by
    rcases lt_trichotomy (Y ω) b with hω | hω | hω
    · rw [hWbelow ω hω]; norm_num
    · rw [hWat ω hω]; exact hα
    · rw [hWabove ω hω]; norm_num
  have hYW : Integrable (fun ω => Y ω * W ω) μ :=
    hY.mul_bdd hWmeas.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWbounds ω).1]
        exact (hWbounds ω).2))
  have hmean : (∫ ω, W ω ∂μ) = θ := by
    change (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω + e.indicator (fun _ => α) ω ∂μ) = θ
    rw [integral_add ((integrable_const (1 : ℝ)).indicator hs)
      ((integrable_const α).indicator he), integral_indicator_const _ hs,
      integral_indicator_const _ he]
    change p * 1 + q * α = θ
    nlinarith [hαq]
  refine ⟨W, hWmeas, hWint, hYW, hWbounds, hWbelow, hWabove, hmean, ?_⟩
  apply populationTrim_eq_weighted μ Y W hY hWint hYW hWbounds θ hθ hmean b hb
  intro ω
  rcases lt_trichotomy (Y ω) b with hω | hω | hω
  · rw [hWbelow ω hω, mul_one, max_eq_left (by linarith)]
  · rw [hω, sub_self, max_self, zero_mul]
  · rw [hWabove ω hω, mul_zero, max_eq_right (by linarith)]

end NLA.IE21
