import ProofProject.InverseGenerator
import ProofProject.ScalarExamples
import ProofProject.Rescaling

/-! Finiteness and monotonicity of the envelope, without a sharp asymptotic bound. -/

noncomputable section

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H]

/-- The usual exponential norm estimate, also valid on the zero space. -/
lemma norm_operator_exp_le (C : H →L[ℂ] H) :
    ‖NormedSpace.exp C‖ ≤ Real.exp ‖C‖ := by
  rw [Real.exp_eq_exp_ℝ]
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) C).norm_le_of_bounded
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖C‖)
  intro n
  have hpow : ‖C ^ n‖ ≤ ‖C‖ ^ n := by
    cases n with
    | zero =>
      change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    | succ n => exact norm_pow_le' C (Nat.succ_pos n)
  have hc : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, smul_eq_mul] using
    mul_le_mul_of_nonneg_left hpow hc

/-- A coarse uniform bound ensures the supremum is an ordinary finite real. -/
lemma IsGeneratorInverse.evolution_norm_le {T : StableSemigroup M H} {B : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) (hM : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖inverseEvolution B t‖ ≤ Real.exp (t * M) := by
  calc
    ‖inverseEvolution B t‖ ≤ Real.exp ‖(t : ℂ) • B‖ := norm_operator_exp_le _
    _ = Real.exp (t * ‖B‖) := by simp [norm_smul, abs_of_nonneg ht]
    _ ≤ Real.exp (t * M) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB.norm_le hM) ht)

/-- The real supremum is bounded above at every nonnegative time. -/
theorem attainableNorms_bddAbove {M t : ℝ} (hM : 1 ≤ M) (ht : 0 ≤ t) :
    BddAbove (attainableNorms.{u} M t) := by
  refine ⟨Real.exp (t * M), ?_⟩
  rintro r ⟨H, hN, hI, hC, T, B, hB, rfl⟩
  exact hB.evolution_norm_le (zero_le_one.trans hM) ht

lemma growthEnvelope_le_exp {M t : ℝ} (hM : 1 ≤ M) (ht : 0 ≤ t) :
    growthEnvelope.{u} M t ≤ Real.exp (t * M) := by
  apply csSup_le (attainableNorms_nonempty M t hM)
  rintro r ⟨H, hN, hI, hC, T, B, hB, rfl⟩
  exact hB.evolution_norm_le (zero_le_one.trans hM) ht

lemma growthEnvelope_ge_one {M t : ℝ} (hM : 1 ≤ M) (ht : 0 ≤ t) :
    1 ≤ growthEnvelope.{u} M t :=
  one_le_growthEnvelope M t hM (attainableNorms_bddAbove hM ht)

/-- The source's monotonicity argument via generator time acceleration. -/
lemma growthEnvelope_mono_pos {M s t : ℝ} (hM : 1 ≤ M) (hs : 0 < s) (hst : s ≤ t) :
    growthEnvelope.{u} M s ≤ growthEnvelope.{u} M t := by
  exact csSup_le_csSup (attainableNorms_bddAbove hM (hs.le.trans hst))
    (attainableNorms_nonempty M s hM)
    (attainableNorms_mono_time (zero_le_one.trans hM) hs hst)

end ProofProject
