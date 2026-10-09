import ProofProject.SchurContraction
import ProofProject.ToeplitzBoundary

/-!
# Finite Schur interpolation by a rational function

A contractive finite Toeplitz symbol has a rational interpolant bounded by
one on the closed unit disk, whose denominator has no zero there. Only the
prescribed coefficient prefix is constrained; the original polynomial may
have arbitrary degree.
-/

noncomputable section

namespace ProofProject

open Polynomial

theorem exists_finiteSchurInterpolant (N : ℕ) (P : Polynomial ℂ)
    (hP : HasFiniteToeplitzBound P.coeff N 1) :
    ∃ A B : Polynomial ℂ,
      (∀ z : ℂ, ‖z‖ ≤ 1 → B.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖A.eval z‖ ≤ ‖B.eval z‖) ∧
      X ^ N ∣ A - B * P := by
  induction N generalizing P with
  | zero =>
      refine ⟨0, 1, ?_, ?_, ?_⟩
      · intro z hz
        simp
      · intro z hz
        simp
      · simp
  | succ m ih =>
      have ha : ‖P.coeff 0‖ ≤ 1 := hP.coeff_zero_norm_le_one
      rcases ha.eq_or_lt with ha | ha
      · refine ⟨C (P.coeff 0), 1, ?_, ?_, ?_⟩
        · intro z hz
          simp
        · intro z hz
          simpa only [eval_C, eval_one, norm_one] using ha.le
        · simpa only [one_mul, neg_sub] using
            dvd_neg.mpr (hP.X_pow_dvd_sub_C_of_norm_zero_eq_one ha)
      · obtain ⟨S, hS⟩ := exists_schurData_congruence m P rfl ha
        have hbound := schurData_toeplitz_contraction rfl ha hP hS
        obtain ⟨A₁, B₁, hB₁, hAB₁, hdiv⟩ := ih S hbound
        refine ⟨schurFractionNumerator (P.coeff 0) A₁ B₁,
          schurFractionDenominator (P.coeff 0) A₁ B₁, ?_, ?_, ?_⟩
        · intro z hz
          exact schurFraction_denominator_ne_zero ha A₁ B₁ hB₁ hAB₁ hz
        · intro z hz
          exact schurFraction_norm_le ha.le A₁ B₁ hAB₁ hz
        · exact schurFraction_congruence m (P.coeff 0) A₁ B₁ P S hS hdiv

end ProofProject
