import ProofProject.BasisEnergy
import ProofProject.MetricMargin

/-!
# The source finite model after metric perturbation

The conclusions are pointwise energy and norm-ratio estimates on the original
space, without an additional norm instance.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] {N : ℕ}

/-- The squared norm prescribed by the source's perturbed Gram metric. -/
def roundedModelEnergy (M : ℝ) (f : Fin N → H) (c : Fin N → ℂ) : ℝ :=
  perturbedEnergy (metricEta M N) (fun d => ‖finiteSynthesis f d‖ ^ 2) coefficientEnergy c

/-- A nonzero coefficient vector has strictly positive perturbed energy. -/
theorem roundedModelEnergy_pos (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) {c : Fin N → ℂ} (hc : c ≠ 0) :
    0 < roundedModelEnergy M f c := by
  exact add_pos_of_nonneg_of_pos (sq_nonneg _)
    (mul_pos (metricEta_pos hM hN) (coefficientEnergy_pos hc))

/-- The elementary-pattern bounds imply the two-sided metric comparison. -/
theorem roundedModelEnergy_comparison (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (c : Fin N → ℂ) :
    ‖finiteSynthesis f c‖ ^ 2 ≤ roundedModelEnergy M f c ∧
      roundedModelEnergy M f c ≤ 2 * ‖finiteSynthesis f c‖ ^ 2 := by
  constructor
  · exact le_perturbedEnergy (q := fun d => ‖finiteSynthesis f d‖ ^ 2)
      hM hN coefficientEnergy_nonneg c
  · apply perturbedEnergy_le_twice hM hN _ c
    intro d
    exact coefficientEnergy_le_of_elementaryPattern_bound f d M (by linarith) hf (hpattern d)

/-- Every source pattern gains the same strict squared-norm margin. -/
theorem roundedModelEnergy_pattern (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (i : Fin N) (z : ℂ) (hz : ‖z‖ ≤ 1) (c : Fin N → ℂ) :
    roundedModelEnergy M f (elementaryPattern i z c) ≤
      (M ^ 2 - metricGamma M N) * roundedModelEnergy M f c := by
  apply perturbedEnergy_contraction hM hN
    (fun d => finiteSynthesis_norm_sq_le f d hf) (elementaryPattern i z) _ _ c
  · intro d
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (hpattern d i z hz) 2
  · intro d
    exact coefficientEnergy_elementaryPattern_le i z d hz

/-- Existing squared-gain witnesses survive with loss at most two. -/
theorem roundedModelEnergy_gain (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (S : (Fin N → ℂ) → (Fin N → ℂ)) {a : ℝ} (ha : 0 ≤ a)
    {c : Fin N → ℂ} (hc : a * ‖finiteSynthesis f c‖ ^ 2 ≤ ‖finiteSynthesis f (S c)‖ ^ 2) :
    (a / 2) * roundedModelEnergy M f c ≤ roundedModelEnergy M f (S c) := by
  apply perturbedEnergy_preserves_gain hM hN coefficientEnergy_nonneg _ S ha hc
  intro d
  exact coefficientEnergy_le_of_elementaryPattern_bound f d M (by linarith) hf (hpattern d)

/-- A nonzero old gain witness yields an actual perturbed energy ratio. -/
theorem roundedModelEnergy_gain_ratio (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (S : (Fin N → ℂ) → (Fin N → ℂ)) {a : ℝ} (ha : 0 ≤ a)
    {c : Fin N → ℂ} (hc : c ≠ 0)
    (hgain : a * ‖finiteSynthesis f c‖ ^ 2 ≤ ‖finiteSynthesis f (S c)‖ ^ 2) :
    a / 2 ≤ roundedModelEnergy M f (S c) / roundedModelEnergy M f c := by
  apply (le_div_iff₀ (roundedModelEnergy_pos f hM hN hc)).mpr
  exact roundedModelEnergy_gain f hM hN hf hpattern S ha hgain

end ProofProject
