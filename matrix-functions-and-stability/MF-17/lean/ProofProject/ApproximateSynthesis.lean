import ProofProject.AugmentedSynthesis
import ProofProject.ApproximateSeparation
import ProofProject.TailGeometry
import ProofProject.GrowthExponentPerturbation

/-!
# Approximate synthesis from sharp Hilbert geometry

The analytic geometry statement is retained as an explicit premise. The
passage from approximate separating operators to synthesis is proved here,
including zero input vectors and the exact exponent for errors at most `1/n`.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- Only the nonempty proper cuts require separating operators. -/
def HasApproximateSeparators (Z : Fin n → H →L[ℂ] H) (M ε : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → k < n →
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ M ∧ separationError Z R k ≤ ε

theorem augmentedFamily_hasTailBound (Z : Fin n → H →L[ℂ] H) (x : Fin n → H)
    {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε) (hsep : HasApproximateSeparators Z M ε) :
    HasSynthesisTailBound (augmentedFamily (fun j => Z j (x j)) (fun j => ‖x j‖)) (M + ε) := by
  intro c k
  by_cases hk0 : k = 0
  · subst k
    rw [synthesisTail_zero]
    exact le_mul_of_one_le_left (norm_nonneg _) (by linarith)
  by_cases hkn : n ≤ k
  · rw [synthesisTail_eq_zero_of_length_le _ _ hkn, norm_zero]
    exact mul_nonneg (by linarith) (norm_nonneg _)
  obtain ⟨R, hR, herr⟩ := hsep k (by omega) (by omega)
  exact augmentedFamily_tail_bound _ _ hM hε R hR c k
    (synthesisTail_separation_error Z R x c k herr)

/-- The augmented vectors have the source's uniform diagonal-energy bound. -/
lemma augmentedFamily_sum_norm_sq_le (Z : Fin n → H →L[ℂ] H) (x : Fin n → H)
    {B : ℝ} (hZ : ∀ j, ‖Z j‖ ≤ B) :
    (∑ j, ‖augmentedFamily (fun j => Z j (x j)) (fun j => ‖x j‖) j‖ ^ 2) ≤
      (B ^ 2 + 1) * ∑ j, ‖x j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [augmentedFamily_norm_sq]
  have hjbound := (Z j).le_opNorm (x j)
  have hnorm := hjbound.trans (mul_le_mul_of_nonneg_right (hZ j) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow] at hsq
  nlinarith

/-- The source approximate-synthesis implication, conditional only on the
sharp Hilbert geometry estimate. The constant is uniform in all vectors,
operators, dimensions, and Hilbert spaces in the fixed universe. -/
theorem approximate_synthesis_of_tail_geometry {C M ε B : ℝ}
    (hgeometry : HasSharpTailGeometry.{u} C) (hM : 1 ≤ M)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (Z : Fin n → H →L[ℂ] H)
    (hZ : ∀ j, ‖Z j‖ ≤ B) (hsep : HasApproximateSeparators Z M ε)
    (x : Fin n → H) :
    ‖∑ j, Z j (x j)‖ ^ 2 ≤
      C * (M + 1) ^ 2 * (B ^ 2 + 1) * (n : ℝ) ^ growthExponent (M + ε) *
        ∑ j, ‖x j‖ ^ 2 := by
  have hC := hgeometry.1
  let f := augmentedFamily (fun j => Z j (x j)) (fun j => ‖x j‖)
  have htail := augmentedFamily_hasTailBound Z x hM hε0.le hsep
  have hg := hgeometry.2 (by linarith : 1 < M + ε) f htail
  have hin : ‖∑ j, Z j (x j)‖ ^ 2 ≤ ‖finiteSynthesis f (fun _ => 1)‖ ^ 2 := by
    rw [augmentedFamily_synthesis_norm_sq]
    simp only [finiteSynthesis, one_smul]
    exact le_add_of_nonneg_right (augmentedCoefficientEnergy_nonneg _ _)
  have htrace := augmentedFamily_sum_norm_sq_le Z x hZ
  have hnα : 0 ≤ (n : ℝ) ^ growthExponent (M + ε) := Real.rpow_nonneg (by positivity) _
  have hk : (M + ε) ^ 2 ≤ (M + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc
    _ ≤ C * (M + ε) ^ 2 * (n : ℝ) ^ growthExponent (M + ε) * ∑ j, ‖f j‖ ^ 2 := hin.trans hg
    _ ≤ C * (M + ε) ^ 2 * (n : ℝ) ^ growthExponent (M + ε) *
        ((B ^ 2 + 1) * ∑ j, ‖x j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left htrace (mul_nonneg (mul_nonneg hgeometry.1 (sq_nonneg _)) hnα)
    _ ≤ C * (M + 1) ^ 2 * (n : ℝ) ^ growthExponent (M + ε) *
        ((B ^ 2 + 1) * ∑ j, ‖x j‖ ^ 2) := by
      gcongr
    _ = _ := by ring

/-- With separation error at most `1/n`, the exponent is exactly α(M).
Only a fixed multiplicative constant is lost; no fixed enlargement of M is
substituted into the growth exponent. -/
theorem approximate_synthesis_exact_exponent {C M ε B : ℝ}
    (hgeometry : HasSharpTailGeometry.{u} C) (hM : 1 < M)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε : ε ≤ 1 / (n : ℝ))
    (Z : Fin n → H →L[ℂ] H) (hZ : ∀ j, ‖Z j‖ ≤ B)
    (hsep : HasApproximateSeparators Z M ε) (x : Fin n → H) :
    ‖∑ j, Z j (x j)‖ ^ 2 ≤
      (C * (M + 1) ^ 2 * Real.exp (growthExponentLipschitzConstant M)) *
        (B ^ 2 + 1) * (n : ℝ) ^ growthExponent M * ∑ j, ‖x j‖ ^ 2 := by
  have hC := hgeometry.1
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hε1 : ε ≤ 1 := hε.trans (by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnreal)
  have hp := growthExponent_rpow_perturbation hM hnreal hε0.le hε
  calc
    _ ≤ C * (M + 1) ^ 2 * (B ^ 2 + 1) * (n : ℝ) ^ growthExponent (M + ε) *
        ∑ j, ‖x j‖ ^ 2 := approximate_synthesis_of_tail_geometry hgeometry hM.le hε0 hε1 Z hZ hsep x
    _ ≤ C * (M + 1) ^ 2 * (B ^ 2 + 1) *
        (Real.exp (growthExponentLipschitzConstant M) * (n : ℝ) ^ growthExponent M) *
        ∑ j, ‖x j‖ ^ 2 := by
      gcongr
    _ = _ := by ring

end ProofProject
