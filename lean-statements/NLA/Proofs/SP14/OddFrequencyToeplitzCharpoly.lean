import NLA.Proofs.SP14.BaseOffdiagonalCharpoly

/-!
Finite odd-frequency Toeplitz sections have an exact characteristic
polynomial quotient in the variable `w² - 1`. This is the algebraic
"no division ambiguity" assertion used by the SP-14 source's jet equations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Polynomial

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- Vanishing of all even-frequency coefficients of the frozen real-interval
Fourier integral. -/
def OddFourierSupport (a : Circle → ℂ) : Prop :=
  ∀ p : ℤ, FourierCoefficient a (2 * p) = 0

noncomputable def oddB (a : Circle → ℂ) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin m) ℂ :=
  fun i j => FourierCoefficient a
    ((2 * (i.val : ℤ)) - (2 * (j.val : ℤ) + 1))

noncomputable def oddC (a : Circle → ℂ) (m : ℕ) :
    Matrix (Fin m) (Fin (m + 1)) ℂ :=
  fun i j => FourierCoefficient a
    ((2 * (i.val : ℤ) + 1) - 2 * (j.val : ℤ))

noncomputable def oddQuotient (a : Circle → ℂ) (m : ℕ) : Polynomial ℂ :=
  (oddC a m * oddB a m).charpoly

noncomputable def oddJetPolynomial (a : Circle → ℂ) (m : ℕ) : Polynomial ℂ :=
  (oddQuotient a m).comp (Polynomial.X + 1)

theorem oddQuotient_zero (a : Circle → ℂ) : oddQuotient a 0 = 1 := by
  simp [oddQuotient]

/-- Parity reindexing of the actual frozen Toeplitz section, under exact
even-Fourier vanishing. -/
theorem toeplitz_odd_parity_blocks (a : Circle → ℂ) (m : ℕ)
    (hOdd : OddFourierSupport a) :
    Matrix.reindex (baseParityEquiv m).symm (baseParityEquiv m).symm
      (Toeplitz a (2 * m + 1)) =
        Matrix.fromBlocks 0 (oddB a m) (oddC a m) 0 := by
  classical
  have hEven := hOdd
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, Toeplitz]
      have hfreq :
          ((baseParityEquiv m (Sum.inl i)).val : ℤ) -
            ((baseParityEquiv m (Sum.inl j)).val : ℤ) =
          2 * ((i.val : ℤ) - (j.val : ℤ)) := by simp; ring
      rw [hfreq, hEven]
    | inr j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₁₂, Toeplitz, oddB]
      congr 1
  | inr i =>
    cases y with
    | inl j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₂₁, Toeplitz, oddC]
      congr 1
    | inr j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Toeplitz]
      have hfreq :
          ((baseParityEquiv m (Sum.inr i)).val : ℤ) -
            ((baseParityEquiv m (Sum.inr j)).val : ℤ) =
          2 * ((i.val : ℤ) - (j.val : ℤ)) := by simp; ring
      rw [hfreq, hEven]

/-- The explicit quotient in `u=w²` is `charpoly(oddC*oddB)`. -/
theorem toeplitz_odd_charpoly (a : Circle → ℂ) (m : ℕ)
    (hOdd : OddFourierSupport a) :
    (Toeplitz a (2 * m + 1)).charpoly =
      Polynomial.X * (oddQuotient a m).comp (Polynomial.X ^ 2) := by
  have hblocks := toeplitz_odd_parity_blocks a m hOdd
  calc
    (Toeplitz a (2 * m + 1)).charpoly =
        (Matrix.reindex (baseParityEquiv m).symm (baseParityEquiv m).symm
          (Toeplitz a (2 * m + 1))).charpoly :=
      (Matrix.charpoly_reindex (baseParityEquiv m).symm
        (Toeplitz a (2 * m + 1))).symm
    _ = (Matrix.fromBlocks
          (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
          (oddB a m) (oddC a m) (0 : Matrix (Fin m) (Fin m) ℂ)).charpoly := by
      rw [hblocks]
    _ = Polynomial.X * (oddQuotient a m).comp (Polynomial.X ^ 2) := by
      exact charpoly_offdiagonal_succ m (oddB a m) (oddC a m)

/-- The same quotient expressed in the source's jet coordinate `t=w²-1`. -/
theorem toeplitz_odd_charpoly_in_jet (a : Circle → ℂ) (m : ℕ)
    (hOdd : OddFourierSupport a) :
    (Toeplitz a (2 * m + 1)).charpoly =
      Polynomial.X * (oddJetPolynomial a m).comp (Polynomial.X ^ 2 - 1) := by
  rw [toeplitz_odd_charpoly a m hOdd]
  simp [oddJetPolynomial, Polynomial.comp_assoc]

#assert_trust kernel toeplitz_odd_parity_blocks
#assert_trust kernel oddQuotient_zero
#assert_trust kernel toeplitz_odd_charpoly
#assert_trust kernel toeplitz_odd_charpoly_in_jet
#print axioms toeplitz_odd_charpoly_in_jet

end NLA.Proofs.SP14
