/-
The algebraic final step of Proposition 3.2 in Li's source.

The source first obtains pairwise second-moment estimates by integrating its
cone kernels against the two-frame overlap law. This module proves, with no
analytic placeholders, that those two estimates imply the desired squared
L² likelihood estimate. Constructing the source-specific likelihoods and
proving their pairwise estimates remain separate obligations.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace NLA.FR05

/-- The algebraic final step in the source's Proposition 3.2: if the gg and
gr second moments are both close to the rr moment, the two likelihoods are
close in L². -/
theorem likelihood_l2_le_three_mul_of_second_moment_comparisons_proved
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Lg Lr : Ω → ℝ)
    (hgg : Integrable (fun ω ↦ Lg ω * Lg ω) μ)
    (hrr : Integrable (fun ω ↦ Lr ω * Lr ω) μ)
    (hgr : Integrable (fun ω ↦ Lg ω * Lr ω) μ)
    {ε : ℝ}
    (hgg_rr : |(∫ ω, Lg ω * Lg ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)| ≤ ε)
    (hgr_rr : |(∫ ω, Lg ω * Lr ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)| ≤ ε) :
    ∫ ω, (Lg ω - Lr ω) ^ 2 ∂μ ≤ 3 * ε := by
  have hexpand :
      (∫ ω, (Lg ω - Lr ω) ^ 2 ∂μ) =
        (∫ ω, Lg ω * Lg ω ∂μ) + (∫ ω, Lr ω * Lr ω ∂μ) -
          2 * (∫ ω, Lg ω * Lr ω ∂μ) := by
    calc
      (∫ ω, (Lg ω - Lr ω) ^ 2 ∂μ) =
          ∫ ω, (Lg ω * Lg ω + Lr ω * Lr ω) - 2 * (Lg ω * Lr ω) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            ring
      _ = (∫ ω, Lg ω * Lg ω + Lr ω * Lr ω ∂μ) -
          ∫ ω, 2 * (Lg ω * Lr ω) ∂μ := by
            simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
              (integral_sub (hgg.add hrr) (hgr.const_mul (2 : ℝ)))
      _ = (∫ ω, Lg ω * Lg ω ∂μ) + (∫ ω, Lr ω * Lr ω ∂μ) -
          2 * (∫ ω, Lg ω * Lr ω ∂μ) := by
            rw [integral_add hgg hrr, integral_const_mul]
  rw [hexpand]
  have hrearrange :
      (∫ ω, Lg ω * Lg ω ∂μ) + (∫ ω, Lr ω * Lr ω ∂μ) -
          2 * (∫ ω, Lg ω * Lr ω ∂μ) =
        ((∫ ω, Lg ω * Lg ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)) -
          2 * ((∫ ω, Lg ω * Lr ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)) := by
    ring
  rw [hrearrange]
  calc
    ((∫ ω, Lg ω * Lg ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)) -
        2 * ((∫ ω, Lg ω * Lr ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)) ≤
      |(∫ ω, Lg ω * Lg ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)| +
        2 * |(∫ ω, Lg ω * Lr ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ)| := by
          have hfirst := le_abs_self ((∫ ω, Lg ω * Lg ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ))
          have hsecond := neg_le_abs ((∫ ω, Lg ω * Lr ω ∂μ) - (∫ ω, Lr ω * Lr ω ∂μ))
          linarith
    _ ≤ 3 * ε := by
      linarith

/-- An eventual version of the preceding lemma, in the exact C/M form
used by Proposition 3.2 after its kernel estimates have been established. -/
theorem eventual_likelihood_l2_le_of_second_moment_comparisons_proved
    {Ω : ℕ → Type*} [∀ M, MeasurableSpace (Ω M)]
    (μ : ∀ M, Measure (Ω M)) (Lg Lr : ∀ M, Ω M → ℝ)
    (D : ℕ) (C : ℝ)
    (hcomparisons : ∀ M : ℕ, D ≤ M →
      Integrable (fun ω ↦ Lg M ω * Lg M ω) (μ M) ∧
      Integrable (fun ω ↦ Lr M ω * Lr M ω) (μ M) ∧
      Integrable (fun ω ↦ Lg M ω * Lr M ω) (μ M) ∧
      |(∫ ω, Lg M ω * Lg M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M ∧
      |(∫ ω, Lg M ω * Lr M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M) :
    ∀ M : ℕ, D ≤ M →
      (∫ ω, (Lg M ω - Lr M ω) ^ 2 ∂μ M) ≤ 3 * C / M := by
  intro M hM
  rcases hcomparisons M hM with ⟨hgg, hrr, hgr, hgg_rr, hgr_rr⟩
  calc
    (∫ ω, (Lg M ω - Lr M ω) ^ 2 ∂μ M) ≤ 3 * (C / M) :=
      likelihood_l2_le_three_mul_of_second_moment_comparisons_proved
        (μ M) (Lg M) (Lr M) hgg hrr hgr hgg_rr hgr_rr
    _ = 3 * C / M := by
      ring

end NLA.FR05
