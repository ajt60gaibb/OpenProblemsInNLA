import Mathlib

open MeasureTheory Filter
open scoped Topology

namespace MD01Bridge

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem unifIntegrable_of_uniform_L2_bound
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (X n) μ)
    (hL2 : ∃ C : NNReal, ∀ n, eLpNorm (X n) 2 μ ≤ C) :
    UnifIntegrable X 1 μ := by
  obtain ⟨C, hC⟩ := hL2
  intro ε hε
  refine ⟨(ε / ((C : ℝ) + 1)) ^ 2, by positivity, ?_⟩
  intro n s hs hμs
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have hmeas' : AEStronglyMeasurable (X n) (μ.restrict s) := (hmeas n).restrict
  have hHolder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict s) (f := X n) (p := 1) (q := 2) (by norm_num) hmeas'
  have hHolder' : eLpNorm (X n) 1 (μ.restrict s) ≤
      eLpNorm (X n) 2 (μ.restrict s) * (μ s) ^ (1 / 2 : ℝ) := by
    norm_num [hs] at hHolder ⊢
    exact hHolder
  have hL2restr : eLpNorm (X n) 2 (μ.restrict s) ≤ C :=
    (eLpNorm_mono_measure (X n) Measure.restrict_le_self).trans (hC n)
  calc
    eLpNorm (X n) 1 (μ.restrict s)
        ≤ eLpNorm (X n) 2 (μ.restrict s) * (μ s) ^ (1 / 2 : ℝ) := hHolder'
    _ ≤ (C : ENNReal) * (ENNReal.ofReal ((ε / ((C : ℝ) + 1)) ^ 2)) ^
          (1 / 2 : ℝ) := mul_le_mul' hL2restr (by gcongr)
    _ ≤ ENNReal.ofReal ε := by
      have ht : 0 ≤ ε / ((C : ℝ) + 1) := by positivity
      rw [← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
        ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg ht,
        ← ENNReal.ofReal_mul C.coe_nonneg]
      apply ENNReal.ofReal_le_ofReal
      have hden : 0 < (C : ℝ) + 1 := by positivity
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      nlinarith [hε.le]

theorem expectation_limit_of_uniform_integrability
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Integrable (X n) μ)
    (hUI : UnifIntegrable X 1 μ)
    (hprob : TendstoInMeasure μ X atTop (fun _ => (1 : ℝ))) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (𝓝 (1 : ℝ)) := by
  have hL1 : Tendsto (fun n => eLpNorm (X n - fun _ => (1 : ℝ)) 1 μ)
      atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl ENNReal.one_ne_top
    · exact fun n => (hX n).aestronglyMeasurable
    · exact (memLp_one_iff_integrable).2 (integrable_const (1 : ℝ))
    · exact hUI
    · exact hprob
  have h := tendsto_integral_of_L1' (fun _ : Ω => (1 : ℝ))
    (aestronglyMeasurable_const) (Filter.Eventually.of_forall hX) hL1
  simpa using h

theorem expectation_limit_of_uniform_L2_bound
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (X n) μ)
    (hL2 : ∃ C : NNReal, ∀ n, eLpNorm (X n) 2 μ ≤ C)
    (hprob : TendstoInMeasure μ X atTop (fun _ => (1 : ℝ))) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (𝓝 (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := hL2
  have hLp2 (n : ℕ) : MemLp (X n) 2 μ :=
    ⟨hmeas n, lt_of_le_of_lt (hC n) ENNReal.coe_lt_top⟩
  have hX (n : ℕ) : Integrable (X n) μ :=
    (memLp_one_iff_integrable).mp ((hLp2 n).mono_exponent (by norm_num))
  exact expectation_limit_of_uniform_integrability μ X hX
    (unifIntegrable_of_uniform_L2_bound μ X hmeas ⟨C, hC⟩) hprob

#print axioms unifIntegrable_of_uniform_L2_bound
#print axioms expectation_limit_of_uniform_integrability
#print axioms expectation_limit_of_uniform_L2_bound

end MD01Bridge
