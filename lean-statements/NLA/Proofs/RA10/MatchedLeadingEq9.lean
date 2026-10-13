import NLA.Proofs.RA10.NuclearNormTriangle
import NLA.Proofs.RA10.SelectedProjectionBasic

/-! RA-10 source Equation (9): exact coefficient-one triangle accounting for
the actual selected compression and the same frozen best-rank tail. This is a
partial theorem, not the full transfer Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem matchedLeading_compression_excess_le {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
      eigenvaluesA QAhat
    let C := P * A * P
    let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
    let R := NLA.Statements.RA10.NuclearNorm (B₀ - C)
    let e₀ := NLA.Statements.RA10.NuclearNorm (A - B₀) - τ
    let e_C := NLA.Statements.RA10.NuclearNorm (A - C) - τ
    e_C ≤ e₀ + R := by
  let P := selectedProjection k QAhat
  let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
    eigenvaluesA QAhat
  let C := P * A * P
  let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
  change NLA.Statements.RA10.NuclearNorm (A - C) - τ ≤
    (NLA.Statements.RA10.NuclearNorm (A - B₀) - τ) +
      NLA.Statements.RA10.NuclearNorm (B₀ - C)
  have hmatrix : A - C = (A - B₀) + (B₀ - C) := by abel
  rw [hmatrix]
  have htriangle := nuclearNorm_add_le (A - B₀) (B₀ - C)
  linarith

#assert_trust kernel matchedLeading_compression_excess_le
#print axioms matchedLeading_compression_excess_le

end NLA.Proofs.RA10
