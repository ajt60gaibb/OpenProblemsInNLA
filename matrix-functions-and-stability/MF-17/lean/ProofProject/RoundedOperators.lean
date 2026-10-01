import ProofProject.RoundedSpace
import ProofProject.BasisPatterns

/-!
# Operator bounds in the rounded Hilbert space

The strict energy margin is an actual operator-norm margin on `RoundedSpace`.
Tail and coordinate projection estimates are proved in this new norm, so the
coordinate constant remains `2M` without any distortion loss.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}

/-- Coefficients of an elementary pattern in the new Hilbert space are exactly
the elementary pattern of the original coefficients. -/
lemma roundedCoefficients_pattern (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (i : Fin N) (z : ℂ) (x : RoundedSpace f η) :
    roundedCoefficients f hη (basisPattern (roundedBasis f hη) i z x) =
      elementaryPattern i z (roundedCoefficients f hη x) := by
  apply (roundedCoefficients f hη).symm.injective
  rw [LinearEquiv.symm_apply_apply, ← roundedBasis_finiteSynthesis,
    ← basisPattern_finiteSynthesis, roundedBasis_synthesis_coefficients]

/-- Arbitrary diagonal operators retain their exact coefficient action. -/
lemma roundedCoefficients_diagonal (f : Fin N → H) {η : ℝ} (hη : 0 < η)
    (a : Fin N → ℂ) (x : RoundedSpace f η) :
    roundedCoefficients f hη (basisDiagonal (roundedBasis f hη) a x) =
      a * roundedCoefficients f hη x := by
  funext j
  rw [← roundedBasis_repr, basisDiagonal_repr, roundedBasis_repr]
  rfl

/-- The metric perturbation supplies the promised strict operator-norm margin. -/
theorem norm_roundedPattern_le (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (i : Fin N) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖basisPattern (roundedBasis f (metricEta_pos hM hN)) i z‖ ≤
      Real.sqrt (M ^ 2 - metricGamma M N) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (zero_le_one.trans (one_le_metricMargin_sq hM)),
    roundedSpace_norm_sq_eq_model f hM hN, roundedSpace_norm_sq_eq_model f hM hN,
    roundedCoefficients_pattern]
  exact roundedModelEnergy_pattern f hM hN hf hpattern i z hz _

/-- The strict rounded pattern bound is, in particular, at most the original M. -/
theorem norm_roundedPattern_le_original (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (i : Fin N) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖basisPattern (roundedBasis f (metricEta_pos hM hN)) i z‖ ≤ M := by
  apply (norm_roundedPattern_le f hM hN hf hpattern i z hz).trans
  apply Real.sqrt_le_iff.mpr
  exact ⟨by linarith, sub_le_self _ (metricGamma_pos hM).le⟩

/-- Tail projections have norm at most M in the new Hilbert structure. -/
theorem norm_roundedTail_le (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (k : ℕ) : ‖basisTail (roundedBasis f (metricEta_pos hM hN)) k‖ ≤ M :=
  norm_basisTail_le _ (by linarith) (norm_roundedPattern_le_original f hM hN hf hpattern) k

/-- The coordinate bound is rederived from new-norm tails, preserving `2M`. -/
theorem norm_roundedCoordinate_le (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (i : Fin N) : ‖basisCoordinate (roundedBasis f (metricEta_pos hM hN)) i‖ ≤ 2 * M :=
  norm_basisCoordinate_le_of_patterns _ (by linarith)
    (norm_roundedPattern_le_original f hM hN hf hpattern) i

/-- A nonzero coefficient gain witness gives an actual operator-norm lower
bound after perturbation. No norm-attainment assertion is needed. -/
theorem roundedDiagonal_norm_sq_lower (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (a : Fin N → ℂ) {r : ℝ} (hr : 0 ≤ r) {c : Fin N → ℂ} (hc : c ≠ 0)
    (hgain : r * ‖finiteSynthesis f c‖ ^ 2 ≤ ‖finiteSynthesis f (a * c)‖ ^ 2) :
    r / 2 ≤ ‖basisDiagonal (roundedBasis f (metricEta_pos hM hN)) a‖ ^ 2 := by
  let x := (roundedCoefficients f (metricEta_pos hM hN)).symm c
  let D := basisDiagonal (roundedBasis f (metricEta_pos hM hN)) a
  have hx : roundedCoefficients f (metricEta_pos hM hN) x = c := by simp [x]
  have hxpos : 0 < ‖x‖ ^ 2 := by
    rw [roundedSpace_norm_sq_eq_model f hM hN, hx]
    exact roundedModelEnergy_pos f hM hN hc
  have hD : roundedCoefficients f (metricEta_pos hM hN) (D x) = a * c := by
    dsimp only [D]
    rw [roundedCoefficients_diagonal, hx]
  have hg : (r / 2) * ‖x‖ ^ 2 ≤ ‖D x‖ ^ 2 := by
    rw [roundedSpace_norm_sq_eq_model f hM hN, roundedSpace_norm_sq_eq_model f hM hN,
      hx, hD]
    exact roundedModelEnergy_gain f hM hN hf hpattern (fun d => a * d) hr hgain
  have hop : ‖D x‖ ^ 2 ≤ ‖D‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (D.le_opNorm x) 2
  exact (mul_le_mul_iff_left₀ hxpos).mp (hg.trans hop)

/-- The squared gain statement in the ordinary operator-norm form. -/
theorem roundedDiagonal_norm_lower (f : Fin N → H) {M : ℝ}
    (hM : 1 < M) (hN : 0 < N) (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (a : Fin N → ℂ) {r : ℝ} (hr : 0 ≤ r) {c : Fin N → ℂ} (hc : c ≠ 0)
    (hgain : r * ‖finiteSynthesis f c‖ ^ 2 ≤ ‖finiteSynthesis f (a * c)‖ ^ 2) :
    Real.sqrt (r / 2) ≤ ‖basisDiagonal (roundedBasis f (metricEta_pos hM hN)) a‖ := by
  exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _,
    roundedDiagonal_norm_sq_lower f hM hN hf hpattern a hr hc hgain⟩

end ProofProject
