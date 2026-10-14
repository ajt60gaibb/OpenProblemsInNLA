import NLA.Proofs.RA10.MatchedLeadingSupport

/-! RA-10 source Equation (14) for the actual compression `C = P * A * P`.
This is its exact resolvent identity with the selected left factor and literal
nuclear norm equality. The nuclear ideal estimate and full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem matchedLeading_ridgeProduct_restricted_right {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC =
        s • ((P * RB * P) * (B₀ - C) * RC) := by
  dsimp
  have hproduct := matchedLeading_ridgeProduct_right (k := k) hs hA hAhat hC
  have hrestrict := matchedLeading_leftResolvent_restriction (k := k) hs hA hAhat
  dsimp at hrestrict
  rw [hrestrict] at hproduct
  exact hproduct

theorem matchedLeading_ridgeProduct_restricted_nuclearNorm {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    NLA.Statements.RA10.NuclearNorm
      (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) =
      NLA.Statements.RA10.NuclearNorm
        (s • ((P * RB * P) * (B₀ - C) * RC)) := by
  exact congrArg NLA.Statements.RA10.NuclearNorm
    (matchedLeading_ridgeProduct_restricted_right (k := k) hs hA hAhat hC)

#assert_trust kernel matchedLeading_ridgeProduct_restricted_right
#assert_trust kernel matchedLeading_ridgeProduct_restricted_nuclearNorm
#print axioms matchedLeading_ridgeProduct_restricted_nuclearNorm

end NLA.Proofs.RA10
