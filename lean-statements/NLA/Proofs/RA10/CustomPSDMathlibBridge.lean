import NLA.Proofs.RA10.SelectedCompressionPSD
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! RA-10: exact finite real PSD predicate bridge to pinned Mathlib.
The source compression is thereby Mathlib positive semidefinite. An ordered
spectral decomposition of that compression and the full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

private theorem source_quadratic_eq_dotProduct {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j) =
      x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.dot_mulVec_eq_sum_sum]
  exact Finset.sum_comm

theorem sourcePositiveSemidefinite_iff_mathlibPosSemidef {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.PositiveSemidefinite M ↔ Matrix.PosSemidef M := by
  constructor
  · intro h
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · apply Matrix.IsHermitian.ext_iff.mpr
      intro i j
      simpa using h.1 j i
    · intro x
      have hstar : star x = x := by
        ext i
        simp
      rw [hstar, ← source_quadratic_eq_dotProduct]
      exact h.2 x
  · intro h
    obtain ⟨hHerm, hquad⟩ := Matrix.posSemidef_iff_dotProduct_mulVec.mp h
    constructor
    · intro i j
      have hij := Matrix.IsHermitian.apply hHerm j i
      simpa using hij
    · intro x
      have hstar : star x = x := by
        ext i
        simp
      have hnonneg := hquad x
      rw [hstar] at hnonneg
      rw [source_quadratic_eq_dotProduct]
      exact hnonneg

theorem selectedCompression_mathlibPosSemidef {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    Matrix.PosSemidef
      (selectedProjection k QAhat * A * selectedProjection k QAhat) := by
  exact (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (selectedCompression_positiveSemidefinite (k := k) hA hAhat)

#assert_trust kernel sourcePositiveSemidefinite_iff_mathlibPosSemidef
#assert_trust kernel selectedCompression_mathlibPosSemidef
#print axioms selectedCompression_mathlibPosSemidef

end NLA.Proofs.RA10
