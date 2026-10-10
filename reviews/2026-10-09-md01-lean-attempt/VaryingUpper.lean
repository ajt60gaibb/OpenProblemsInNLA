import Mathlib

open MeasureTheory Filter
open scoped Topology

-- Local probability-measure instances are proof values; the `haveI` style is
-- required here to supply typeclass inference within each varying space.
set_option linter.style.haveILetI false

namespace MD01FullBridge

variable (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
variable (μ : (n : ℕ) → Measure (Ω n))
variable (X : (n : ℕ) → Ω n → ℝ)

/-- A uniform `L²` bound controls the `L¹` contribution of a small set,
even when the underlying space changes with `n`. -/
theorem varying_small_set_L1_bound
    (hmeas : ∀ n, AEStronglyMeasurable (X n) (μ n))
    (C : NNReal) (hL2 : ∀ n, eLpNorm (X n) 2 (μ n) ≤ C)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (s : Set (Ω n))
    (hs : MeasurableSet s)
    (hμs : μ n s ≤ ENNReal.ofReal ((ε / ((C : ℝ) + 1)) ^ 2)) :
    eLpNorm (s.indicator (X n)) 1 (μ n) ≤ ENNReal.ofReal ε := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have hmeas' : AEStronglyMeasurable (X n) ((μ n).restrict s) := (hmeas n).restrict
  have hHolder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := (μ n).restrict s) (f := X n) (p := 1) (q := 2) (by norm_num) hmeas'
  have hHolder' : eLpNorm (X n) 1 ((μ n).restrict s) ≤
      eLpNorm (X n) 2 ((μ n).restrict s) * (μ n s) ^ (1 / 2 : ℝ) := by
    norm_num [hs] at hHolder ⊢
    exact hHolder
  have hL2restr : eLpNorm (X n) 2 ((μ n).restrict s) ≤ C :=
    (eLpNorm_mono_measure (X n) Measure.restrict_le_self).trans (hL2 n)
  calc
    eLpNorm (X n) 1 ((μ n).restrict s)
        ≤ eLpNorm (X n) 2 ((μ n).restrict s) * (μ n s) ^ (1 / 2 : ℝ) := hHolder'
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

/-- On varying probability spaces, convergence in probability to `1` and a
uniform `L²` bound force the expectations to converge to `1`. -/
theorem varying_expectation_of_L2_and_probability
    (hprobMeas : ∀ n, IsProbabilityMeasure (μ n))
    (hmeas : ∀ n, Measurable (X n))
    (hL2 : ∃ C : NNReal, ∀ n, eLpNorm (X n) 2 (μ n) ≤ C)
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω - 1|}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := hL2
  let Y : (n : ℕ) → Ω n → ℝ := fun n ω => X n ω - 1
  have hYmeas (n : ℕ) : Measurable (Y n) := (hmeas n).sub measurable_const
  have hY2 (n : ℕ) : eLpNorm (Y n) 2 (μ n) ≤ (C + 1 : NNReal) := by
    haveI : IsProbabilityMeasure (μ n) := hprobMeas n
    have hone : eLpNorm (fun _ : Ω n => (1 : ℝ)) 2 (μ n) = 1 := by
      rw [eLpNorm_const' (1 : ℝ) (by norm_num) (by norm_num)]
      simp [measure_univ]
    calc
      eLpNorm (Y n) 2 (μ n)
          ≤ eLpNorm (X n) 2 (μ n) + eLpNorm (fun _ : Ω n => (1 : ℝ)) 2 (μ n) :=
            eLpNorm_sub_le (hmeas n).aestronglyMeasurable aestronglyMeasurable_const (by norm_num)
      _ ≤ (C + 1 : NNReal) := by rw [hone]; exact_mod_cast add_le_add (hC n) (le_refl (1 : ENNReal))
  rw [Metric.tendsto_atTop]
  intro ε hε
  let r : ℝ := ε / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hd : 0 < r / (((C + 1 : NNReal) : ℝ) + 1) := by positivity
  have hδ : 0 < ENNReal.ofReal ((r / (((C + 1 : NNReal) : ℝ) + 1)) ^ 2) :=
    ENNReal.ofReal_pos.mpr (sq_pos_of_pos hd)
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp (hconv r hr) _ hδ
  refine ⟨N, fun n hn => ?_⟩
  haveI : IsProbabilityMeasure (μ n) := hprobMeas n
  let s : Set (Ω n) := {ω | r ≤ |Y n ω|}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_le measurable_const (hYmeas n).abs
  have hmass : μ n s ≤ ENNReal.ofReal ((r / (((C + 1 : NNReal) : ℝ) + 1)) ^ 2) := by
    simpa [s, Y] using hN n hn
  have hbad : eLpNorm (s.indicator (Y n)) 1 (μ n) ≤ ENNReal.ofReal r :=
    varying_small_set_L1_bound Ω μ Y (fun k => (hYmeas k).aestronglyMeasurable)
      (C + 1) hY2 hr n s hs hmass
  have hgood : eLpNorm (sᶜ.indicator (Y n)) 1 (μ n) ≤ ENNReal.ofReal r := by
    have hb : ∀ ω : Ω n, ‖sᶜ.indicator (Y n) ω‖ ≤ r := by
      intro ω
      by_cases hw : ω ∈ s
      · have hc : ω ∉ sᶜ := by simpa using hw
        simp [Set.indicator_of_notMem hc, hr.le]
      · have hc : ω ∈ sᶜ := by simpa using hw
        rw [Set.indicator_of_mem hc, Real.norm_eq_abs]
        exact (lt_of_not_ge hw).le
    have h := eLpNorm_le_of_ae_bound (μ := μ n) (p := (1 : ENNReal))
      (Eventually.of_forall hb)
    simpa [measure_univ] using h
  have hY1 : eLpNorm (Y n) 1 (μ n) ≤ ENNReal.ofReal (r + r) := by
    rw [← Set.indicator_self_add_compl s (Y n)]
    calc
      eLpNorm (s.indicator (Y n) + sᶜ.indicator (Y n)) 1 (μ n)
        ≤ eLpNorm (s.indicator (Y n)) 1 (μ n) +
          eLpNorm (sᶜ.indicator (Y n)) 1 (μ n) :=
            eLpNorm_add_le ((hYmeas n).aestronglyMeasurable.indicator hs)
              ((hYmeas n).aestronglyMeasurable.indicator hs.compl) le_rfl
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add hbad hgood
      _ = ENNReal.ofReal (r + r) := (ENNReal.ofReal_add hr.le hr.le).symm
  have hXmem : MemLp (X n) 2 (μ n) :=
    ⟨(hmeas n).aestronglyMeasurable, (hC n).trans_lt ENNReal.coe_lt_top⟩
  have hXint : Integrable (X n) (μ n) := hXmem.integrable (by norm_num)
  have honeint : Integrable (fun _ : Ω n => (1 : ℝ)) (μ n) := integrable_const _
  have hdist : dist (∫ ω, X n ω ∂μ n) 1 ≤ (eLpNorm (Y n) 1 (μ n)).toReal := by
    have h := dist_integral_le_lintegral_edist hXint honeint
    simpa [Y, eLpNorm_one_eq_lintegral_enorm, edist_eq_enorm_sub] using h
  have hnorm : (eLpNorm (Y n) 1 (μ n)).toReal ≤ r + r :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hY1
  have hrr : r + r < ε := by dsimp [r]; linarith
  exact (hdist.trans hnorm).trans_lt hrr

#print axioms varying_small_set_L1_bound
#print axioms varying_expectation_of_L2_and_probability

end MD01FullBridge
