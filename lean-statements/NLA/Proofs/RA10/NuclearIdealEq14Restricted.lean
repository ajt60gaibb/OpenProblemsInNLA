import NLA.Proofs.RA10.NuclearIdealEq14Product
import NLA.Proofs.RA10.MatchedLeadingEq14Restricted

/-! RA-10 source Equation (14): the exact restricted ridge-difference
nuclear bound for the actual selected compression C=PAP. This remains a
partial gate toward the full RA-10 transfer Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

theorem matchedLeading_ridge_nuclear_le {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (j : Fin n) (hj : j.val + 1 = k) :
    NLA.Statements.RA10.NuclearNorm
      (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) ≤
      (1 / (s + eigenvaluesA j)) *
        NLA.Statements.RA10.NuclearNorm
          (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat -
            selectedProjection k QAhat * A * selectedProjection k QAhat) := by
  calc
    NLA.Statements.RA10.NuclearNorm
        (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
          NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) =
        NLA.Statements.RA10.NuclearNorm
          (s • ((selectedProjection k QAhat *
            (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
              NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
                eigenvaluesA QAhat)⁻¹ * selectedProjection k QAhat) *
            (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
              eigenvaluesA QAhat -
              selectedProjection k QAhat * A * selectedProjection k QAhat) *
            (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
              selectedProjection k QAhat * A * selectedProjection k QAhat)⁻¹)) :=
      matchedLeading_ridgeProduct_restricted_nuclearNorm (k := k) hs hA hAhat hC
    _ ≤ (1 / (s + eigenvaluesA j)) *
        NLA.Statements.RA10.NuclearNorm
          (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
            eigenvaluesA QAhat -
            selectedProjection k QAhat * A * selectedProjection k QAhat) :=
      matchedLeading_ridge_nuclear_product_le hs hk hkn hA hAhat hC j hj

#assert_trust kernel matchedLeading_ridge_nuclear_le
#print axioms matchedLeading_ridge_nuclear_le

end NLA.Proofs.RA10
