import NLA.Proofs.RA10.SelectedProjectionBasic
import NLA.Proofs.RA10.SpectralQuadratic

/-! RA-10: the source compression `C = P * A * P` has the exact finite
quadratic form and satisfies the frozen real PSD predicate. An ordered
spectral decomposition of C and the full transfer target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

private theorem compression_quadratic_eq_dotProduct {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j) =
      x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.dot_mulVec_eq_sum_sum]
  exact Finset.sum_comm

theorem selectedCompression_quadratic_form {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (x : Fin n → ℝ) :
    let P := selectedProjection k QAhat
    let C := P * A * P
    let y := P *ᵥ x
    (∑ i : Fin n, ∑ j : Fin n, x i * C i j * x j) =
      ∑ i : Fin n, ∑ j : Fin n, y i * A i j * y j := by
  dsimp
  let P := selectedProjection k QAhat
  have hPt : P.transpose = P := selectedProjection_transpose k QAhat
  rw [compression_quadratic_eq_dotProduct,
    compression_quadratic_eq_dotProduct]
  change x ⬝ᵥ ((P * A * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ x))
  have hmul : (P * A * P) *ᵥ x = P *ᵥ (A *ᵥ (P *ᵥ x)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hmul]
  have htranspose := Matrix.dotProduct_transpose_mulVec P (A *ᵥ (P *ᵥ x)) x
  rw [hPt] at htranspose
  rw [← htranspose]
  exact dotProduct_comm _ _

theorem selectedCompression_positiveSemidefinite {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    NLA.Statements.RA10.PositiveSemidefinite
      (selectedProjection k QAhat * A * selectedProjection k QAhat) := by
  let P := selectedProjection k QAhat
  let C := P * A * P
  have hApsd := orderedPSDSpectralDecomposition_positiveSemidefinite hA
  have hAt : A.transpose = A := by
    ext i j
    exact hApsd.1 j i
  have hPt : P.transpose = P := selectedProjection_transpose k QAhat
  have hCt : C.transpose = C := by
    dsimp [C]
    simp only [Matrix.transpose_mul, hPt, hAt, Matrix.mul_assoc]
  constructor
  · intro i j
    exact (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hCt).symm
  · intro x
    have hq := selectedCompression_quadratic_form (k := k) (A := A) hAhat x
    change (∑ i : Fin n, ∑ j : Fin n, x i * C i j * x j) =
      ∑ i : Fin n, ∑ j : Fin n, (P *ᵥ x) i * A i j * (P *ᵥ x) j at hq
    rw [hq]
    exact hApsd.2 (P *ᵥ x)

#assert_trust kernel selectedCompression_quadratic_form
#assert_trust kernel selectedCompression_positiveSemidefinite
#print axioms selectedCompression_positiveSemidefinite

end NLA.Proofs.RA10
