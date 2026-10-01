import ProofProject.ApproximateSynthesis
import ProofProject.FactorizedSynthesis

/-! The two approximate synthesis bounds give the exact exponent for a sum. -/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {n : ℕ}

/-- Assuming sharp geometry, approximately separated factors give the source's
operator-sum bound. Constructing the factors and their separators is a separate
obligation; no polar decomposition is assumed implicitly by this theorem. -/
theorem separated_factor_sum_norm_le {C M ε B : ℝ}
    (hgeometry : HasSharpTailGeometry.{u} C) (hM : 1 < M)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε : ε ≤ 1 / (n : ℝ))
    (X Y : Fin n → H →L[ℂ] H)
    (hX : ∀ j, ‖(X j).adjoint‖ ≤ B) (hY : ∀ j, ‖Y j‖ ≤ B)
    (hsepX : HasApproximateSeparators (fun j => (X j).adjoint) M ε)
    (hsepY : HasApproximateSeparators Y M ε) :
    ‖∑ j, (Y j).comp (X j)‖ ≤
      (C * (M + 1) ^ 2 * Real.exp (growthExponentLipschitzConstant M)) *
        (B ^ 2 + 1) * (n : ℝ) ^ growthExponent M := by
  have hC := hgeometry.1
  apply factorized_synthesis_norm_le X Y (by positivity)
  · intro y
    exact approximate_synthesis_exact_exponent hgeometry hM hn hε0 hε Y hY hsepY y
  · intro y
    exact approximate_synthesis_exact_exponent hgeometry hM hn hε0 hε
      (fun j => (X j).adjoint) hX hsepX y

end ProofProject
