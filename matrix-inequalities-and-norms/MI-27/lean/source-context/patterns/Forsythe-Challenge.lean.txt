import ProofProject.Definitions

/-!
# Theorem statements for Comparator

The signatures below correspond to the manuscript's statements. Comparator
compares them with the proofs in `Solution.lean` in separate environments.
The `sorry` bodies serve as statement placeholders. The proof module imports
the shared definitions independently.
-/

namespace ProofProject

/-- Part A / Theorem A.1.1: Forsythe's conjecture at restart length two. -/
theorem forsytheConjecture_restartLengthTwo : ForsytheConvergenceAt 2 := by
  sorry

/-- Part B / Theorem B.1.1: Forsythe's conjecture at restart length three. -/
theorem forsytheConjecture_restartLengthThree : ForsytheConvergenceAt 3 := by
  sorry

/-- Lemma C.3.1 after exact characteristic reduction: the minimized
theorem-bearing restart-four algebraic Hopf certificate. -/
theorem restartFourAlgebraicHopfCertificate : RestartFourAlgebraicHopfCertificate := by
  sorry

/-- Theorem C.1.1 exactly as printed: SPD counterexamples in dimension `s+4`. -/
theorem counterexamples_restartLengthAtLeastFour :
    ∀ s : ℕ, 4 ≤ s → HasForsytheCounterexample s := by
  sorry

/-- Theorem 1.1: restart length four is the sharp threshold. -/
theorem forsytheSharpClassification :
    ∀ s : ℕ, 2 ≤ s →
      ((s = 2 ∨ s = 3) → ForsytheConvergenceAt s) ∧
      (4 ≤ s → HasDiagonalForsytheCounterexample s) := by
  sorry

end ProofProject
