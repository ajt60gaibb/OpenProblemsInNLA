import ProofProject.SourcePieceOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Strong convergence of the actual source-piece sums

The scalar cutoff differences telescope and eventually stabilize at each
integration point. An integrable exponential majorant then passes their
strong vector integrals to the actual infinite tail. No operator-valued
measurability or separability hypothesis is used.
-/

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology

namespace ProofProject

/-- The actual kernel remaining after the fixed initial cutoff. -/
def sourceOscillatoryTailKernel (t σ u : ℝ) : ℂ :=
  (dampedPower (-3 / 4) t u : ℂ) *
    ((1 - sourcePieceChi (u / 32) : ℝ) : ℂ) *
    Complex.exp (((σ * 2 * Real.sqrt u : ℝ) : ℂ) * Complex.I)

/-- A common scalar majorant for every partial sum and its pointwise limit. -/
def sourcePieceTailMajorant (t : ℝ) : ℝ → ℝ :=
  (Ioi (32 : ℝ)).indicator (fun u => Real.exp (-u / t))

theorem sourcePieceTailMajorant_nonneg (t u : ℝ) :
    0 ≤ sourcePieceTailMajorant t u := by
  exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

theorem sourcePieceTailMajorant_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (sourcePieceTailMajorant t) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  have h := integrableOn_exp_mul_Ioi
    (show -1 / t < 0 from div_neg_of_neg_of_pos (by norm_num) ht) (32 : ℝ)
  have heq : (fun u : ℝ => Real.exp (-u / t)) =
      (fun u => Real.exp ((-1 / t) * u)) := by
    funext u
    congr 1
    ring
  change IntegrableOn (fun u : ℝ => Real.exp (-u / t)) (Ioi 32)
  rw [heq]
  exact h

theorem tendsto_sourcePieceScale_atTop : Tendsto sourcePieceScale atTop atTop := by
  apply tendsto_atTop_mono sourcePieceScale_geometric_lower
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop
    (by norm_num)

/-- The telescoping is eventually exact at each fixed scalar argument. -/
theorem eventually_sum_sourcePieceKernel_eq (t σ u : ℝ) :
    ∀ᶠ n : ℕ in atTop, (∑ q ∈ range n, sourcePieceKernel q t σ u) =
      sourceOscillatoryTailKernel t σ u := by
  have hs : Tendsto (fun n => 2 * sourcePieceScale n) atTop atTop :=
    tendsto_sourcePieceScale_atTop.const_mul_atTop (by norm_num)
  filter_upwards [hs.eventually_ge_atTop u] with n hn
  rw [sum_sourcePieceKernel]
  rw [sourcePieceChi_eq_one ((div_le_one
    (by have := sourcePieceScale_pos n; positivity)).mpr hn)]
  rfl

theorem tendsto_sum_sourcePieceKernel (t σ u : ℝ) :
    Tendsto (fun n : ℕ => ∑ q ∈ range n, sourcePieceKernel q t σ u)
      atTop (𝓝 (sourceOscillatoryTailKernel t σ u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_sum_sourcePieceKernel_eq t σ u] with n hn
  exact hn.symm

theorem norm_sum_sourcePieceKernel_le (n : ℕ) (t σ u : ℝ) :
    ‖∑ q ∈ range n, sourcePieceKernel q t σ u‖ ≤ sourcePieceTailMajorant t u := by
  by_cases hu : 32 < u
  · have hu0 : 0 < u := by linarith
    have hd0 : 0 ≤ sourcePieceChi (u / (2 * sourcePieceScale n)) -
        sourcePieceChi (u / 32) := by
      rw [← sum_sourcePieceCutoff]
      exact sum_nonneg (fun q _ => sourcePieceCutoff_nonneg q u)
    have hd1 : sourcePieceChi (u / (2 * sourcePieceScale n)) -
        sourcePieceChi (u / 32) ≤ 1 := by
      linarith [sourcePieceChi_le_one (u / (2 * sourcePieceScale n)),
        sourcePieceChi_nonneg (u / 32)]
    have hp0 : 0 ≤ dampedPower (-3 / 4) t u := by
      unfold dampedPower
      positivity
    have hp1 : dampedPower (-3 / 4) t u ≤ Real.exp (-u / t) := by
      unfold dampedPower
      exact mul_le_of_le_one_left (Real.exp_pos _).le
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
    rw [sourcePieceTailMajorant, indicator_of_mem (show u ∈ Ioi (32 : ℝ) from hu),
      sum_sourcePieceKernel, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hp0, abs_of_nonneg hd0]
    exact (mul_le_of_le_one_right hp0 hd1).trans hp1
  · have hz : (∑ q ∈ range n, sourcePieceKernel q t σ u) = 0 := by
      apply sum_eq_zero
      intro q _
      apply (oscillatoryKernel_eq_zero_iff σ _ u).mpr
      apply sourcePieceAmplitude_eq_zero_of_le q t
      have := sourcePieceScale_ge_sixteen q
      linarith
    rw [hz, norm_zero, sourcePieceTailMajorant,
      indicator_of_notMem (show u ∉ Ioi (32 : ℝ) from hu)]

theorem norm_sourceOscillatoryTailKernel_le (t σ u : ℝ) :
    ‖sourceOscillatoryTailKernel t σ u‖ ≤ sourcePieceTailMajorant t u := by
  obtain ⟨n, hn⟩ := (eventually_sum_sourcePieceKernel_eq t σ u).exists
  rw [← hn]
  exact norm_sum_sourcePieceKernel_le n t σ u

theorem sourceOscillatoryTailKernel_eq_zero_of_le (t σ : ℝ) {u : ℝ}
    (hu : u ≤ 32) : sourceOscillatoryTailKernel t σ u = 0 := by
  have hc : sourcePieceChi (u / 32) = 1 :=
    sourcePieceChi_eq_one ((div_le_one (by norm_num : (0 : ℝ) < 32)).mpr hu)
  simp only [sourceOscillatoryTailKernel, hc, sub_self, Complex.ofReal_zero,
    mul_zero, zero_mul]

theorem sourceOscillatoryTailKernel_aestronglyMeasurable (t σ : ℝ) :
    AEStronglyMeasurable (sourceOscillatoryTailKernel t σ) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (integrable_finsetSum (range n)
      (fun q _ => sourcePieceKernel_integrable q t σ)).aestronglyMeasurable)
  exact Eventually.of_forall (tendsto_sum_sourcePieceKernel t σ)

theorem sourceOscillatoryTailKernel_integrable {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    Integrable (sourceOscillatoryTailKernel t σ) :=
  (sourcePieceTailMajorant_integrable ht).mono'
    (sourceOscillatoryTailKernel_aestronglyMeasurable t σ)
    (Eventually.of_forall (norm_sourceOscillatoryTailKernel_le t σ))

namespace BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The actual infinite oscillatory tail, defined by strong scalar-kernel integration. -/
def sourceOscillatoryTailOperator (S : BoundedSemigroup M H) (t σ : ℝ)
    (ht : 0 < t) : H →L[ℂ] H :=
  S.kernelOperator (sourceOscillatoryTailKernel t σ)
    (sourceOscillatoryTailKernel_integrable ht σ)

theorem sourceOscillatoryTailOperator_apply (S : BoundedSemigroup M H)
    (t σ : ℝ) (ht : 0 < t) (x : H) :
    S.sourceOscillatoryTailOperator t σ ht x =
      ∫ s : ℝ, sourceOscillatoryTailKernel t σ s • S.op s x :=
  S.kernelOperator_apply_of_nonneg_support _ _
    (fun _ hs => sourceOscillatoryTailKernel_eq_zero_of_le t σ (by linarith)) x

theorem sourceOscillatoryTailOperator_orbit_integrable (S : BoundedSemigroup M H)
    (t σ : ℝ) (ht : 0 < t) (x : H) :
    Integrable (fun s : ℝ => sourceOscillatoryTailKernel t σ s • S.op s x) := by
  apply (S.kernelOrbit_integrable (sourceOscillatoryTailKernel_integrable ht σ) x).congr
  filter_upwards [] with s
  by_cases hs : 0 ≤ s
  · simp only [positiveOrbit, max_eq_left hs]
  · simp only [sourceOscillatoryTailKernel_eq_zero_of_le t σ (by linarith : s ≤ 32),
      zero_smul]

/-- The finite operator sums converge on each vector in every complex Hilbert space. -/
theorem tendsto_sum_sourcePieceOperator (S : BoundedSemigroup M H)
    (t σ : ℝ) (ht : 0 < t) (x : H) :
    Tendsto (fun n : ℕ => (∑ q ∈ range n, S.sourcePieceOperator q t σ) x)
      atTop (𝓝 (S.sourceOscillatoryTailOperator t σ ht x)) := by
  have heq (n : ℕ) : (∑ q ∈ range n, S.sourcePieceOperator q t σ) x =
      ∫ s : ℝ, (∑ q ∈ range n, sourcePieceKernel q t σ s) • S.positiveOrbit x s := by
    simp only [_root_.sum_apply, sourcePieceOperator, kernelOperator_apply]
    rw [← integral_finsetSum (range n)
      (fun q _ => S.kernelOrbit_integrable (sourcePieceKernel_integrable q t σ) x)]
    simp only [sum_smul]
  simp_rw [heq]
  change Tendsto _ atTop (𝓝 (∫ s : ℝ,
    sourceOscillatoryTailKernel t σ s • S.positiveOrbit x s))
  apply tendsto_integral_of_dominated_convergence
    (fun s => sourcePieceTailMajorant t s * (M * ‖x‖))
  · intro n
    exact (S.kernelOrbit_integrable (integrable_finsetSum (range n)
      (fun q _ => sourcePieceKernel_integrable q t σ)) x).aestronglyMeasurable
  · exact (sourcePieceTailMajorant_integrable ht).mul_const _
  · intro n
    exact Eventually.of_forall fun s => by
      rw [norm_smul]
      exact mul_le_mul (norm_sum_sourcePieceKernel_le n t σ s)
        (S.positiveOrbit_norm_le x s) (norm_nonneg _)
        (sourcePieceTailMajorant_nonneg t s)
  · exact Eventually.of_forall fun s =>
      (tendsto_sum_sourcePieceKernel t σ s).smul_const (S.positiveOrbit x s)

end BoundedSemigroup

end ProofProject
