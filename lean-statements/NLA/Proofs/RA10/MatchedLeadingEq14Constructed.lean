import NLA.Proofs.RA10.MatchedLeadingEq14Restricted
import NLA.Proofs.RA10.SelectedCompressionOrderedSpectral

/-! RA-10 source Equation (14), with the actual compression's ordered PSD
spectral witness constructed from the original A and Ahat hypotheses. The
nuclear ideal inequality and complete transfer target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem matchedLeading_ridgeProduct_constructed {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    ∃ (eigenvaluesC : Fin n → ℝ) (QC : Matrix (Fin n) (Fin n) ℝ),
      NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC ∧
      NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC =
          s • ((P * RB * P) * (B₀ - C) * RC) ∧
      NLA.Statements.RA10.NuclearNorm
        (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
          NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) =
        NLA.Statements.RA10.NuclearNorm
          (s • ((P * RB * P) * (B₀ - C) * RC)) := by
  dsimp
  obtain ⟨eigenvaluesC, QC, hC⟩ :=
    selectedCompression_exists_orderedPSD (k := k) hA hAhat
  refine ⟨eigenvaluesC, QC, hC, ?_, ?_⟩
  · exact matchedLeading_ridgeProduct_restricted_right (k := k) hs hA hAhat hC
  · exact matchedLeading_ridgeProduct_restricted_nuclearNorm (k := k) hs hA hAhat hC

#assert_trust kernel matchedLeading_ridgeProduct_constructed
#print axioms matchedLeading_ridgeProduct_constructed

end NLA.Proofs.RA10
