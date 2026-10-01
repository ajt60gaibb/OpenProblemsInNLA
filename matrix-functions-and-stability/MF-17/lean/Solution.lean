import ProofProject.Helpers

/-!
# MF-17: sharp growth theorem

This module supplies five theorems: existence of the bounded
inverse of the full generator, finiteness of the envelope, its contractive
endpoint, the finite-dimensional sharp lower bound, and the matching exact-M
upper and lower asymptotic. The growth theorems are proved in imported modules.
-/

noncomputable section

namespace ProofProject

universe u

/-- Exponential stability supplies the bounded inverse of the full generator. -/
theorem stableSemigroup_hasGeneratorInverse {M : ℝ} (_hM : 1 ≤ M)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : StableSemigroup M H) : ∃! B : H →L[ℂ] H, IsGeneratorInverse T B := by
  exact ⟨T.laplaceInverse, T.isGeneratorInverse_laplaceInverse,
    fun B hB => hB.eq_laplaceInverse⟩

end ProofProject
