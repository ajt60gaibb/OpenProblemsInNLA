import NLA.IE21.GaussianTrimming

/-!
Law-invariant lower-tail optimization for IE-21. These analytic lemmas concern
the literal threshold-dual definition in the frozen boundary. They do not
assume concentration, quantiles, or the spherical/Gaussian comparison.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y Z : Ω → ℝ} {θ : ℝ}

/-- Integrability of the threshold hinge follows from ordinary first-moment integrability. -/
theorem trimming_hinge_integrable (hY : Integrable Y μ) (t : ℝ) :
    Integrable (fun ω => max (t - Y ω) 0) μ := by
  exact ((integrable_const t).sub hY).sup (integrable_const 0)

/-- Every admissible dual objective is bounded above by the full first moment. -/
theorem trimming_objective_le_integral (hθ : θ ≤ 1) (hY : Integrable Y μ)
    {t : ℝ} (ht : 0 ≤ t) :
    θ * t - ∫ ω, max (t - Y ω) 0 ∂μ ≤ ∫ ω, Y ω ∂μ := by
  have hi := integral_mono ((integrable_const t).sub hY) (trimming_hinge_integrable hY t)
    (fun ω => le_max_left (t - Y ω) 0)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const t) hY] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hmul := mul_le_mul_of_nonneg_right hθ ht
  linarith

theorem populationTrim_objectives_bddAbove (hθ : θ ≤ 1) (hY : Integrable Y μ) :
    BddAbove {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ ω, max (t - Y ω) 0 ∂μ} := by
  refine ⟨∫ ω, Y ω ∂μ, ?_⟩
  rintro z ⟨t, ht, rfl⟩
  exact trimming_objective_le_integral hθ hY ht

omit [IsProbabilityMeasure μ] in
theorem populationTrim_objectives_nonempty (θ : ℝ) (Y : Ω → ℝ) :
    {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ ω, max (t - Y ω) 0 ∂μ}.Nonempty :=
  ⟨_, 0, le_rfl, rfl⟩

theorem trimming_objective_le_populationTrim (hθ : θ ≤ 1) (hY : Integrable Y μ)
    {t : ℝ} (ht : 0 ≤ t) :
    θ * t - ∫ ω, max (t - Y ω) 0 ∂μ ≤ populationTrim θ μ Y := by
  exact le_csSup (populationTrim_objectives_bddAbove hθ hY) ⟨t, ht, rfl⟩

theorem populationTrim_le_integral (hθ : θ ≤ 1) (hY : Integrable Y μ) :
    populationTrim θ μ Y ≤ ∫ ω, Y ω ∂μ := by
  apply csSup_le (populationTrim_objectives_nonempty θ Y)
  rintro z ⟨t, ht, rfl⟩
  exact trimming_objective_le_integral hθ hY ht

theorem populationTrim_nonneg (hθ : θ ≤ 1) (hY : Integrable Y μ)
    (hY0 : 0 ≤ᵐ[μ] Y) : 0 ≤ populationTrim θ μ Y := by
  have heq : (∫ ω, max (0 - Y ω) 0 ∂μ) = 0 := by
    convert integral_congr_ae (show (fun ω => max (0 - Y ω) 0) =ᵐ[μ] fun _ => (0 : ℝ) from ?_) using 1
    · simp
    · filter_upwards [hY0] with ω hω
      change 0 ≤ Y ω at hω
      exact max_eq_right (by linarith)
  have h := trimming_objective_le_populationTrim hθ hY (t := 0) le_rfl
  simpa only [mul_zero, heq, sub_zero] using h

omit [IsProbabilityMeasure μ] in
/-- The dual depends only on the distribution of the observed scalar variable. -/
theorem populationTrim_map {Ξ : Type*} [MeasurableSpace Ξ]
    (f : Ω → Ξ) (hf : AEMeasurable f μ) (V : Ξ → ℝ) (hV : Measurable V) :
    populationTrim θ (μ.map f) V = populationTrim θ μ (fun ω => V (f ω)) := by
  have heq (t : ℝ) : (∫ ω, max (t - V ω) 0 ∂μ.map f) =
      ∫ ω, max (t - V (f ω)) 0 ∂μ := by
    exact integral_map hf (by fun_prop)
  unfold populationTrim
  simp_rw [heq]

private theorem populationTrim_le_add_distance (hθ : θ ≤ 1)
    (hY : Integrable Y μ) (hZ : Integrable Z μ) :
    populationTrim θ μ Y ≤ populationTrim θ μ Z + ∫ ω, |Y ω - Z ω| ∂μ := by
  apply csSup_le (populationTrim_objectives_nonempty θ Y)
  rintro z ⟨t, ht, rfl⟩
  have hdist : Integrable (fun ω => |Y ω - Z ω|) μ := (hY.sub hZ).abs
  have hi := integral_mono (trimming_hinge_integrable hZ t)
    ((trimming_hinge_integrable hY t).add hdist) (fun ω => ?_)
  · simp only [Pi.add_apply] at hi
    rw [integral_add (trimming_hinge_integrable hY t) hdist] at hi
    have hz := trimming_objective_le_populationTrim hθ hZ ht
    linarith
  · change max (t - Z ω) 0 ≤ max (t - Y ω) 0 + |Y ω - Z ω|
    have h := (le_abs_self (max (t - Z ω) 0 - max (t - Y ω) 0)).trans
      (abs_max_sub_max_le_abs (t - Z ω) (t - Y ω) 0)
    have heq : t - Z ω - (t - Y ω) = Y ω - Z ω := by ring
    rw [heq] at h
    linarith

/-- Coupling Lipschitz bound, proved directly for the dual without selector axioms. -/
theorem populationTrim_coupling_lipschitz (hθ : θ ≤ 1)
    (hY : Integrable Y μ) (hZ : Integrable Z μ) :
    |populationTrim θ μ Y - populationTrim θ μ Z| ≤ ∫ ω, |Y ω - Z ω| ∂μ := by
  have h1 := populationTrim_le_add_distance hθ hY hZ
  have h2 := populationTrim_le_add_distance hθ hZ hY
  simp only [abs_sub_comm (Z _) (Y _)] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem integral_threshold_indicator (hY : Integrable Y μ)
    {s : Set Ω} (hs : MeasurableSet s) (t : ℝ) :
    (∫ ω, s.indicator (fun ω => t - Y ω) ω ∂μ) =
      μ.real s * t - ∫ ω in s, Y ω ∂μ := by
  rw [integral_indicator hs, integral_sub (integrable_const t) hY.integrableOn]
  simp only [setIntegral_const, smul_eq_mul]

/-- An exact lower-tail quantile attains the genuine population dual. This lemma
allows atoms as long as the displayed lower-tail mass equals the requested mass. -/
theorem populationTrim_eq_setIntegral (hθ : θ ≤ 1) (hY : Integrable Y μ)
    (b : ℝ) (hb : 0 ≤ b) (hs : MeasurableSet {ω | Y ω ≤ b})
    (hprob : μ.real {ω | Y ω ≤ b} = θ) :
    populationTrim θ μ Y = ∫ ω in {ω | Y ω ≤ b}, Y ω ∂μ := by
  let s := {ω | Y ω ≤ b}
  have hi (t : ℝ) : (∫ ω, s.indicator (fun ω => t - Y ω) ω ∂μ) =
      θ * t - ∫ ω in s, Y ω ∂μ := by
    rw [integral_threshold_indicator hY hs t, hprob]
  have hupper (t : ℝ) : θ * t - ∫ ω, max (t - Y ω) 0 ∂μ ≤ ∫ ω in s, Y ω ∂μ := by
    have hmono := integral_mono (((integrable_const t).sub hY).indicator hs)
      (trimming_hinge_integrable hY t) (fun ω => ?_)
    · change (∫ ω, s.indicator (fun ω => t - Y ω) ω ∂μ) ≤ _ at hmono
      rw [hi] at hmono
      linarith
    · change s.indicator (fun ω => t - Y ω) ω ≤ max (t - Y ω) 0
      by_cases hω : ω ∈ s
      · rw [indicator_of_mem hω]
        exact le_max_left _ _
      · rw [indicator_of_notMem hω]
        exact le_max_right _ _
  have hattain : (∫ ω, max (b - Y ω) 0 ∂μ) = θ * b - ∫ ω in s, Y ω ∂μ := by
    rw [← hi b]
    apply integral_congr_ae
    filter_upwards with ω
    by_cases hω : Y ω ≤ b
    · rw [indicator_of_mem (show ω ∈ s from hω), max_eq_left (by linarith)]
    · rw [indicator_of_notMem (show ω ∉ s from hω), max_eq_right (by linarith)]
  apply le_antisymm
  · apply csSup_le (populationTrim_objectives_nonempty θ Y)
    rintro z ⟨t, _, rfl⟩
    exact hupper t
  · have h := trimming_objective_le_populationTrim hθ hY hb
    rw [hattain] at h
    linarith

/-- The frozen population dual agrees exactly with the canonical Gaussian
trimmed moment, not merely with an auxiliary convention for a quantile. -/
theorem populationTrim_gaussian (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    populationTrim θ (gaussianReal 0 1) (fun g : ℝ => g ^ 2) = gaussianTrim θ := by
  have hc := gaussian_constant θ hθ
  have hs : {g : ℝ | g ^ 2 ≤ gaussianCutoff θ ^ 2} =
      {g : ℝ | |g| ≤ gaussianCutoff θ} := by
    ext g
    simp only [mem_ofPred_eq]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg g) hc.1.le)
  have h := populationTrim_eq_setIntegral hθ.2.le gaussian_square_integrable
    (gaussianCutoff θ ^ 2) (sq_nonneg _) (by measurability) (by rw [hs]; exact hc.2.1)
  rw [h, hs, ← gaussianTrim_eq_truncated]

end NLA.IE21
